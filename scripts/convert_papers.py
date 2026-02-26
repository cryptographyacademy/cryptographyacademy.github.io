#!/usr/bin/env python3
"""Convert markdown papers from data/markdown/eprint/ to .astro pages.

Reads markdown content and conversion_info.json from the in-repo data
directory, generates .astro pages with proper header, content, and
crawler metadata.

Usage:
    python3 scripts/convert_papers.py           # new papers only
    python3 scripts/convert_papers.py --force   # reconvert all
    python3 scripts/convert_papers.py --paper 2001_107  # single paper
"""

import argparse
import html
import html.entities
from html.parser import HTMLParser
import json
import re
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path

import mistune

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data" / "markdown" / "eprint"
OUTPUT_DIR = ROOT / "web" / "src" / "pages" / "papers"


# ---------------------------------------------------------------------------
# TOC parsing from _meta.json
# ---------------------------------------------------------------------------

# Regex for numbered sections: "2.1 CICO problem"
_RE_NUMBERED = re.compile(
    r"^(\d+(?:\.\d+)*)\s+(.+)", re.DOTALL
)
# Regex for appendix sections: "A On Sponges", "A.1 Subsection"
_RE_APPENDIX = re.compile(
    r"^([A-Z])(\.\d+(?:\.\d+)*)?\s+(.+)", re.DOTALL
)


@dataclass
class TocEntry:
    """A single entry in the table of contents."""

    sec_id: str  # e.g. "sec-1", "sec-2.1", "app-a", "abstract"
    title: str  # display title (without section number)
    level: int  # 1 = top-level, 2 = subsection, etc.
    kind: str  # "numbered", "appendix", "special"


def parse_toc(meta: dict | None) -> list[TocEntry]:
    """Parse table_of_contents from _meta.json into TocEntry list."""
    if not meta:
        return []
    toc_raw = meta.get("table_of_contents", [])
    if not toc_raw:
        return []

    entries: list[TocEntry] = []
    seen_first = False

    for item in toc_raw:
        raw_title = item.get("title", "").strip()
        # Normalize newlines in title
        raw_title = re.sub(r"\s*\n\s*", " ", raw_title)

        if not raw_title:
            continue

        # Skip first entry (paper title)
        if not seen_first:
            seen_first = True
            continue

        # Skip "Contents" entries
        if raw_title.lower() in ("contents",):
            continue

        # Special sections
        lower = raw_title.lower()
        if lower == "abstract":
            entries.append(TocEntry(
                sec_id="abstract",
                title="Abstract",
                level=1,
                kind="special",
            ))
            continue
        if lower.startswith("acknowledg"):
            entries.append(TocEntry(
                sec_id="acknowledgements",
                title="Acknowledgements",
                level=1,
                kind="special",
            ))
            continue
        if lower.startswith("reference"):
            entries.append(TocEntry(
                sec_id="references",
                title="References",
                level=1,
                kind="special",
            ))
            continue

        # Numbered section: "2.1 CICO problem"
        m = _RE_NUMBERED.match(raw_title)
        if m:
            num = m.group(1)
            title = m.group(2).strip()
            dots = num.count(".")
            entries.append(TocEntry(
                sec_id=f"sec-{num}",
                title=title,
                level=dots + 1,
                kind="numbered",
            ))
            continue

        # Appendix: "A On Sponges", "A.1 Subsection"
        m = _RE_APPENDIX.match(raw_title)
        if m:
            letter = m.group(1)
            sub = m.group(2) or ""
            title = m.group(3).strip()
            # Filter false headings: skip if title looks like
            # a sentence (contains colon + more than 5 words)
            if ":" in title and len(title.split()) > 6:
                continue
            sec_id = f"app-{letter.lower()}{sub}"
            dots = sub.count(".") if sub else 0
            entries.append(TocEntry(
                sec_id=sec_id,
                title=title,
                level=dots + 1,
                kind="appendix",
            ))
            continue

        # Unrecognized entry (false heading from OCR, author name,
        # "Summary of Changes", theorem titles, etc.) - skip

    return entries


# ---------------------------------------------------------------------------
# TOC HTML generation
# ---------------------------------------------------------------------------


def _toc_link(entry: TocEntry) -> str:
    """Generate a single TOC anchor link."""
    title_safe = unicode_to_html_entities(html.escape(entry.title))
    # Escape curly braces for Astro/JSX (they would be
    # interpreted as JS expressions otherwise)
    title_safe = title_safe.replace("{", "&#123;")
    title_safe = title_safe.replace("}", "&#125;")
    return (
        f'<a href="#{entry.sec_id}" '
        f'class="hover:text-white">{title_safe}</a>'
    )


def generate_toc_html(entries: list[TocEntry]) -> str:
    """Generate the TOC nav element matching hand-curated style."""
    if not entries:
        return ""

    # Split entries into groups
    numbered: list[TocEntry] = []
    appendices: list[TocEntry] = []
    special: list[TocEntry] = []

    for e in entries:
        if e.kind == "numbered":
            numbered.append(e)
        elif e.kind == "appendix":
            appendices.append(e)
        elif e.sec_id == "abstract":
            # Abstract goes at the top of numbered list
            numbered.insert(0, e)
        else:
            special.append(e)

    lines: list[str] = []
    lines.append(
        '    <nav id="toc" class="mb-10 p-6 rounded-lg"'
        ' style="background: rgba(255,255,255,0.03);'
        " border: 1px solid"
        ' rgba(255,255,255,0.06);">'
    )
    lines.append(
        '      <h2 class="text-lg font-bold mb-4">'
        "Table of Contents</h2>"
    )

    # Numbered sections
    if numbered:
        lines.append(
            '      <ol class="space-y-1 text-sm text-gray-300'
            '\n        list-decimal list-inside">'
        )
        _render_toc_list(numbered, lines, indent=8)
        lines.append("      </ol>")

    # Appendices
    if appendices:
        lines.append(
            '      <p class="text-xs text-gray-500 mt-4'
            ' mb-1 font-semibold">'
        )
        lines.append("        Appendices")
        lines.append("      </p>")
        lines.append(
            '      <ol class="space-y-1 text-sm text-gray-400'
            '\n        list-[upper-alpha] list-inside">'
        )
        _render_toc_list(appendices, lines, indent=8)
        lines.append("      </ol>")

    # Special sections (acknowledgements, references)
    if special:
        lines.append(
            '      <p class="text-xs text-gray-500 mt-4'
            ' mb-1 font-semibold">'
        )
        lines.append("        Additional")
        lines.append("      </p>")
        lines.append(
            '      <ul class="space-y-1 text-sm text-gray-400'
            '\n        list-disc list-inside">'
        )
        for e in special:
            lines.append(
                f"        <li>{_toc_link(e)}</li>"
            )
        lines.append("      </ul>")

    lines.append("    </nav>\n")
    return "\n".join(lines)


def _render_toc_list(
    entries: list[TocEntry],
    lines: list[str],
    indent: int,
) -> None:
    """Render a flat list of TocEntry into nested HTML lists."""
    pad = " " * indent
    i = 0
    while i < len(entries):
        e = entries[i]
        if e.level == 1 or e.kind == "special":
            # Collect children (level > 1)
            children: list[TocEntry] = []
            j = i + 1
            while j < len(entries) and entries[j].level > 1:
                children.append(entries[j])
                j += 1
            if children:
                lines.append(f"{pad}<li>")
                lines.append(f"{pad}  {_toc_link(e)}")
                lines.append(
                    f'{pad}  <ol class="ml-6 mt-1 space-y-1'
                    f" list-decimal\n{pad}    "
                    f'list-inside text-gray-400">'
                )
                for child in children:
                    lines.append(
                        f"{pad}    <li>"
                        f"{_toc_link(child)}</li>"
                    )
                lines.append(f"{pad}  </ol>")
                lines.append(f"{pad}</li>")
            else:
                lines.append(
                    f"{pad}<li>{_toc_link(e)}</li>"
                )
            i = j
        else:
            # Orphan subsection (no parent), render directly
            lines.append(
                f"{pad}<li>{_toc_link(e)}</li>"
            )
            i += 1


# ---------------------------------------------------------------------------
# Abstract HTML generation
# ---------------------------------------------------------------------------


def generate_abstract_html(eprint: dict) -> str:
    """Generate abstract section HTML from eprint metadata.

    Returns HTML that will be placed inside a JS template literal
    (as part of CONTENT), so curly braces are safe.
    """
    abstract_text = eprint.get("abstract", "")
    if not abstract_text:
        return ""

    abstract_safe = unicode_to_html_entities(
        html.escape(abstract_text)
    )
    keywords = eprint.get("keywords", [])

    parts = [
        '    <section id="abstract" class="mb-10">',
        '      <h2 class="text-2xl font-bold">Abstract</h2>',
        f'      <p class="text-gray-300">{abstract_safe}</p>',
    ]

    if keywords:
        kw_safe = [
            unicode_to_html_entities(html.escape(k))
            for k in keywords
        ]
        kw_str = " &middot; ".join(kw_safe)
        parts.append(
            f'      <p class="text-gray-300">'
            f"<strong>Keywords:</strong> {kw_str}</p>"
        )

    parts.append("    </section>\n")
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Preamble stripping
# ---------------------------------------------------------------------------


def strip_preamble(md_content: str, has_abstract: bool) -> str:
    """Remove title/authors/abstract preamble from markdown.

    When we have eprint metadata, these are rendered from _meta.json
    instead, so we strip them from the body to avoid duplication.
    """
    if not has_abstract:
        return md_content

    lines = md_content.split("\n")

    # Find first numbered section heading
    for i, line in enumerate(lines):
        if re.match(r"^#{1,4}\s*\d+\s+", line):
            return "\n".join(lines[i:])

    # Fallback: find first ## that is not the title (skip first ##)
    found_first_h2 = False
    for i, line in enumerate(lines):
        if re.match(r"^##\s+", line):
            if not found_first_h2:
                found_first_h2 = True
                continue
            return "\n".join(lines[i:])

    # No headings found, return as-is
    return md_content


# ---------------------------------------------------------------------------
# Unicode to HTML entities
# ---------------------------------------------------------------------------

# Build reverse map: codepoint -> named entity
_CODEPOINT_TO_ENTITY: dict[int, str] = {}
for _name, _cp in html.entities.name2codepoint.items():
    _CODEPOINT_TO_ENTITY[_cp] = _name


def unicode_to_html_entities(text: str) -> str:
    """Convert non-ASCII characters to HTML entities.

    Uses named entities when available (e.g. &ouml;),
    falls back to numeric &#NNN; for others.
    """
    result: list[str] = []
    for ch in text:
        cp = ord(ch)
        if cp < 128:
            result.append(ch)
        elif cp in _CODEPOINT_TO_ENTITY:
            result.append(f"&{_CODEPOINT_TO_ENTITY[cp]};")
        else:
            result.append(f"&#{cp};")
    return "".join(result)


# ---------------------------------------------------------------------------
# HTML tag handling
# ---------------------------------------------------------------------------


class _TextExtractor(HTMLParser):
    """Extract plain text from HTML, discarding all tags."""

    def __init__(self) -> None:
        super().__init__()
        self._parts: list[str] = []

    def handle_data(self, data: str) -> None:
        self._parts.append(data)

    def get_text(self) -> str:
        return "".join(self._parts).strip()


def strip_html_tags(text: str) -> str:
    """Strip all HTML tags from text, keeping only content."""
    extractor = _TextExtractor()
    extractor.feed(text)
    return extractor.get_text()


def strip_marker_spans(text: str) -> str:
    """Remove Marker page-anchor spans like <span id="page-3-3">.

    These are inserted by the Marker PDF converter and carry
    no useful content for the rendered page.
    """
    return re.sub(
        r'<span\s+id="page-[^"]*">\s*</span>', "", text
    )


# ---------------------------------------------------------------------------
# Custom mistune renderer with Tailwind classes
# ---------------------------------------------------------------------------

# Regex to extract section number from heading text
_RE_SEC_NUM = re.compile(r"^(\d+(?:\.\d+)*)\s+(.+)", re.DOTALL)
_RE_APP_NUM = re.compile(
    r"^([A-Z])(\.\d+(?:\.\d+)*)?\s+(.+)", re.DOTALL
)


class TailwindRenderer(mistune.HTMLRenderer):
    """Render markdown to HTML with Tailwind CSS classes."""

    def __init__(self) -> None:
        super().__init__(escape=False)
        self._misc_counter = 0
        self._section_open = False
        self._in_references = False
        self._skip_h1 = True

    def reset(self) -> None:
        """Reset per-document state."""
        self._misc_counter = 0
        self._section_open = False
        self._in_references = False

    def finalize(self) -> str:
        """Close the last open section. Call after rendering."""
        if self._section_open:
            self._section_open = False
            return "    </section>\n"
        return ""

    def _close_section(self) -> str:
        """Return closing tag if a section is open."""
        if self._section_open:
            return "    </section>\n\n"
        return ""

    def heading(self, text: str, level: int, **attrs: object) -> str:
        if level == 1 and self._skip_h1:
            return ""

        # Use HTML parser to get plain text for classification
        plain = strip_html_tags(text)
        # Remove Marker page-anchor spans from display text
        clean_text = strip_marker_spans(text).strip()

        # Check for numbered section: "2.1 CICO problem"
        m = _RE_SEC_NUM.match(plain)
        if m:
            num = m.group(1)
            dots = num.count(".")
            sec_id = f"sec-{num}"
            return self._render_heading(
                clean_text, sec_id, dots, is_top=(dots == 0)
            )

        # Check for appendix: "A On Sponges", "A.1 Sub"
        m = _RE_APP_NUM.match(plain)
        if m:
            letter = m.group(1)
            sub = m.group(2) or ""
            sec_id = f"app-{letter.lower()}{sub}"
            dots = sub.count(".") if sub else 0
            return self._render_heading(
                clean_text, sec_id, dots, is_top=(dots == 0)
            )

        # Special sections
        lower = plain.lower()
        if lower.startswith("acknowledg"):
            return self._render_heading(
                clean_text, "acknowledgements", 0, is_top=True
            )
        if lower.startswith("reference"):
            return self._render_heading(
                clean_text, "references", 0, is_top=True
            )

        # Fallback
        self._misc_counter += 1
        sec_id = f"sec-misc-{self._misc_counter}"
        size = {
            2: "text-2xl font-bold",
            3: "text-xl font-semibold mt-8",
            4: "text-lg font-semibold mt-6",
            5: "text-base font-semibold mt-4",
            6: "text-base font-medium mt-4",
        }.get(level, "text-base font-semibold mt-4")
        return (
            f'    <h{level} id="{sec_id}" '
            f'class="{size}">{clean_text}</h{level}>\n\n'
        )

    def _render_heading(
        self,
        text: str,
        sec_id: str,
        depth: int,
        is_top: bool,
    ) -> str:
        """Render a heading with proper section wrapping."""
        result = ""

        if is_top:
            # Track whether we are in the references section
            self._in_references = sec_id == "references"
            # Close previous section, open new one
            result += self._close_section()
            result += (
                f'    <section id="{sec_id}" class="mb-10">\n'
            )
            self._section_open = True
            result += (
                f'      <h2 class="text-2xl font-bold">'
                f"{text}</h2>\n\n"
            )
        elif depth == 1:
            result += (
                f'      <h3 id="{sec_id}" '
                f'class="text-xl font-semibold mt-8">'
                f"{text}</h3>\n\n"
            )
        else:
            result += (
                f'      <h4 id="{sec_id}" '
                f'class="text-lg font-semibold mt-6">'
                f"{text}</h4>\n\n"
            )

        return result

    def paragraph(self, text: str) -> str:
        return f'    <p class="text-gray-300">{text}</p>\n\n'

    def list(self, text: str, ordered: bool, **attrs: object) -> str:
        if self._in_references:
            return (
                f'    <ul class="space-y-2 text-gray-400'
                f' text-sm list-none">\n'
                f"{text}    </ul>\n\n"
            )
        if ordered:
            return (
                f'    <ol class="list-decimal list-inside'
                f' space-y-1 text-gray-300 my-2 ml-4">\n'
                f"{text}    </ol>\n\n"
            )
        return (
            f'    <ul class="list-disc list-inside'
            f' space-y-1 text-gray-300 my-2 ml-4">\n'
            f"{text}    </ul>\n\n"
        )

    def list_item(self, text: str, **attrs: object) -> str:
        return f"      <li>{text.strip()}</li>\n"

    def block_quote(self, text: str) -> str:
        return (
            f'    <blockquote class="border-l-4'
            f" border-gray-600 pl-4 my-4 text-gray-400"
            f' italic">\n{text}'
            f"    </blockquote>\n\n"
        )

    def block_code(self, code: str, **attrs: object) -> str:
        info = attrs.get("info", "text") or "text"
        lang = info.split()[0] if info else "text"
        escaped = html.escape(code)
        return (
            f'    <pre><code class="language-{lang}">'
            f"{escaped}</code></pre>\n\n"
        )

    def table(self, text: str) -> str:
        return (
            f'    <div class="overflow-x-auto my-4">\n'
            f'      <table class="min-w-full text-sm'
            f' text-gray-300">\n{text}'
            f"      </table>\n"
            f"    </div>\n\n"
        )

    def table_head(self, text: str) -> str:
        return f"        <thead>\n{text}        </thead>\n"

    def table_body(self, text: str) -> str:
        return f"        <tbody>\n{text}        </tbody>\n"

    def table_row(self, text: str) -> str:
        return f"          <tr>\n{text}          </tr>\n"

    def table_cell(
        self,
        text: str,
        align: str | None = None,
        head: bool = False,
    ) -> str:
        tag = "th" if head else "td"
        border = "border-gray-600" if head else "border-gray-700"
        extra = " font-semibold" if head else ""
        align_cls = ""
        if align:
            align_cls = f" text-{align}"
        return (
            f'            <{tag} class="px-3 py-2'
            f" border-b {border}{extra}"
            f' text-left{align_cls}">{text}</{tag}>\n'
        )

    def thematic_break(self) -> str:
        return '    <hr class="my-8 border-gray-700" />\n\n'

    def image(
        self, text: str, url: str, title: str | None = None
    ) -> str:
        alt = html.escape(text or "")
        return (
            f'    <img src="{url}" alt="{alt}" '
            f'class="my-4 max-w-full" />\n'
        )

    def link(
        self, text: str, url: str, title: str | None = None
    ) -> str:
        if url.startswith("http://") or url.startswith("https://"):
            return (
                f'<a href="{url}" target="_blank" '
                f'rel="noopener noreferrer">{text}</a>'
            )
        return f'<a href="{url}">{text}</a>'

    def block_math(self, text: str) -> str:
        escaped = html.escape(text)
        return (
            f'    <div class="my-4 text-center">'
            f'<span class="math-block">'
            f"{escaped}</span></div>\n\n"
        )

    def inline_math(self, text: str) -> str:
        escaped = html.escape(text)
        return f'<span class="math">{escaped}</span>'


def create_markdown_parser() -> (
    tuple[mistune.Markdown, TailwindRenderer]
):
    """Create a mistune Markdown parser with math plugin.

    Returns both the parser and renderer so the renderer can
    be reset between documents.
    """
    renderer = TailwindRenderer()
    md = mistune.create_markdown(
        escape=False,
        renderer=renderer,
        plugins=["math", "table", "strikethrough"],
    )
    return md, renderer


# ---------------------------------------------------------------------------
# Title / author extraction from markdown
# ---------------------------------------------------------------------------


def extract_title_and_authors(
    md_content: str,
) -> tuple[str, str]:
    """Extract title (H1) and authors from markdown content.

    The title is the first H1 heading. The authors are the first
    non-empty line after the H1.
    """
    lines = md_content.split("\n")
    title = ""
    authors = ""

    for i, line in enumerate(lines):
        m = re.match(r"^#\s+(.+)", line)
        if m:
            title = m.group(1).strip()
            # Remove HTML tags like <sup>...</sup>
            title = re.sub(r"<[^>]+>", "", title)
            title = title.strip()
            # Look for authors in subsequent non-empty lines
            for j in range(i + 1, min(i + 10, len(lines))):
                candidate = lines[j].strip()
                if not candidate:
                    continue
                # Skip if it looks like a heading or section
                if candidate.startswith("#"):
                    break
                # Skip if it looks like a date or abstract
                if re.match(
                    r"^(abstract|keywords|date|january"
                    r"|february|march|april|may|june"
                    r"|july|august|september|october"
                    r"|november|december)",
                    candidate.lower(),
                ):
                    break
                # This is likely the authors line
                authors = candidate
                break
            break

    if not title:
        title = "Untitled"

    return title, authors


# ---------------------------------------------------------------------------
# Slug generation
# ---------------------------------------------------------------------------


def title_to_slug(title: str) -> str:
    """Convert a paper title to a kebab-case slug.

    Removes LaTeX, special chars, normalizes unicode,
    and truncates to a reasonable length.
    """
    # Remove LaTeX math
    s = re.sub(r"\$[^$]+\$", "", title)
    # Remove HTML tags
    s = re.sub(r"<[^>]+>", "", s)
    # Normalize unicode (e.g. accented chars)
    s = unicodedata.normalize("NFKD", s)
    s = s.encode("ascii", "ignore").decode("ascii")
    # Lowercase
    s = s.lower()
    # Replace non-alphanumeric with hyphens
    s = re.sub(r"[^a-z0-9]+", "-", s)
    # Strip leading/trailing hyphens
    s = s.strip("-")
    # Truncate to ~60 chars at word boundary
    if len(s) > 60:
        s = s[:60].rsplit("-", 1)[0]
    return s


# ---------------------------------------------------------------------------
# .astro page generation
# ---------------------------------------------------------------------------


def escape_js_string(s: str) -> str:
    """Escape a string for embedding in a JS single-quoted str."""
    s = s.replace("\\", "\\\\")
    s = s.replace("'", "\\'")
    s = s.replace("\n", "\\n")
    return s


def generate_astro_page(
    eprint_id: str,
    title: str,
    authors: str,
    year: str,
    number: str,
    content_html: str,
    toc_html: str = "",
    crawler: str = "marker",
    converted_date: str = "2026-02-16",
    slug: str = "",
) -> str:
    """Generate a complete .astro page for a paper."""
    title_html = unicode_to_html_entities(html.escape(title))
    # For the BaseLayout title attr, use a short form
    short_title = title[:60] + "..." if len(title) > 60 else title
    short_title_escaped = html.escape(short_title)
    authors_html = unicode_to_html_entities(html.escape(authors))

    # Escape for JS single-quoted strings in frontmatter
    title_js = escape_js_string(title_html)
    authors_js = escape_js_string(authors_html)

    # Escape content for embedding in a JS template literal:
    # backticks and ${} must be escaped
    content_for_js = content_html.replace("\\", "\\\\")
    content_for_js = content_for_js.replace("`", "\\`")
    content_for_js = content_for_js.replace("${", "\\${")

    # TOC goes as static Astro HTML (no user content, safe)
    toc_section = ""
    if toc_html:
        toc_section = "\n" + toc_html + "\n"

    return f"""\
---
import BaseLayout from '../../layouts/BaseLayout.astro';
import PaperDisclaimer from '../../components/PaperDisclaimer.astro';
import PaperHistory from '../../components/PaperHistory.astro';

const EPRINT_URL = 'https://eprint.iacr.org/{year}/{number}';
const CRAWLER = '{crawler}';
const CONVERTED_DATE = '{converted_date}';
const TITLE_HTML = '{title_js}';
const AUTHORS_HTML = '{authors_js}';

const CONTENT = `{content_for_js}`;
---

<BaseLayout title="{short_title_escaped} ({year}/{number})">
  <article class="max-w-4xl mx-auto article-prose">
    <nav class="mb-8">
      <a href="/papers" class="text-blue-400 hover:text-blue-300">
        &larr; Back to Papers
      </a>
    </nav>

    <header class="mb-12">
      <h1 class="text-3xl font-bold mb-4"
        set:html={{TITLE_HTML}} />
      <p class="text-gray-400 mb-2"
        set:html={{AUTHORS_HTML}} />
      <p class="text-gray-500 text-sm mb-4">
        {year} &middot; eprint {year}/{number}
      </p>
      <div class="flex gap-4 text-sm">
        <a
          href={{EPRINT_URL}}
          target="_blank"
          rel="noopener noreferrer"
          class="text-blue-400 hover:text-blue-300"
        >
          Paper (eprint) &rarr;
        </a>
      </div>
      <PaperDisclaimer eprintUrl={{EPRINT_URL}} />
      <p class="mt-1 text-xs text-gray-600">
        Converted with: {{CRAWLER}} &middot; {{CONVERTED_DATE}}
      </p>
    </header>
{toc_section}
    <Fragment set:html={{CONTENT}} />

    <PaperHistory slug="{slug}" />
  </article>
</BaseLayout>
"""


# ---------------------------------------------------------------------------
# Paper processing
# ---------------------------------------------------------------------------


def load_conversion_info(paper_dir: Path) -> dict:
    """Load conversion_info.json from a paper directory."""
    ci_path = paper_dir / "conversion_info.json"
    if not ci_path.exists():
        return {}
    with open(ci_path, encoding="utf-8") as f:
        return json.load(f)


def process_paper(
    paper_id: str,
    md_parser: mistune.Markdown,
    renderer: TailwindRenderer,
    existing_map: dict[str, Path],
    force: bool = False,
) -> str | None:
    """Process a single paper. Returns output filename or None."""
    year, number = paper_id.split("_", 1)
    eprint_id = f"{year}/{number}"

    paper_dir = DATA_DIR / paper_id
    md_file = paper_dir / f"{paper_id}.md"
    if not md_file.exists():
        print(
            f"  SKIP {eprint_id}: no markdown file",
            file=sys.stderr,
        )
        return None

    # Check if this eprint ID already has an .astro file
    existing_path = existing_map.get(eprint_id)
    if existing_path is not None and not force:
        return None

    md_content = md_file.read_text(encoding="utf-8")

    # Load _meta.json
    meta_path = paper_dir / f"{paper_id}_meta.json"
    meta: dict | None = None
    eprint: dict = {}
    eprint_title = ""
    eprint_authors = ""

    if meta_path.exists():
        with open(meta_path, encoding="utf-8") as f:
            meta = json.load(f)
        eprint = meta.get("eprint", {}) if meta else {}
        eprint_title = eprint.get("title", "")
        if eprint.get("authors"):
            eprint_authors = ", ".join(
                a["name"] for a in eprint["authors"]
            )

    if eprint_title:
        title = eprint_title
        authors = eprint_authors or "Unknown authors"
    else:
        title, authors = extract_title_and_authors(md_content)
        if not authors:
            authors = "Unknown authors"

    # Read crawler backend from conversion_info.json
    conv_info = load_conversion_info(paper_dir)
    crawler = conv_info.get("backend", "marker")

    # Read converted date from conversion_info.json
    converted_at = conv_info.get("converted_at", "2026-02-16")
    # Extract just the date part (YYYY-MM-DD)
    converted_date = converted_at[:10]

    # Determine output path: reuse existing filename if
    # force-reconverting, otherwise generate from title
    if existing_path is not None and force:
        output_path = existing_path
        filename = existing_path.name
    else:
        slug = title_to_slug(title)
        if not slug:
            slug = paper_id.replace("_", "-")
        filename = f"{slug}-{year}.astro"
        output_path = OUTPUT_DIR / filename

        # Check for filename collisions with a different paper
        if output_path.exists():
            existing_text = output_path.read_text(
                encoding="utf-8"
            )
            if (
                f"eprint.iacr.org/{year}/{number}"
                not in existing_text
            ):
                filename = f"{slug}-{year}-{number}.astro"
                output_path = OUTPUT_DIR / filename

    # Strip preamble if we have eprint abstract
    has_abstract = bool(eprint.get("abstract"))
    md_content = strip_preamble(md_content, has_abstract)

    # Convert markdown to HTML
    renderer.reset()
    content_html = md_parser(md_content)
    content_html += renderer.finalize()

    # Strip Marker page-anchor spans from body content
    content_html = strip_marker_spans(content_html)

    # Apply unicode-to-entity conversion on rendered content
    content_html = unicode_to_html_entities(content_html)

    # Generate structured sections from _meta.json
    toc_entries = parse_toc(meta) if meta else []
    toc_html = generate_toc_html(toc_entries)
    abstract_html = generate_abstract_html(eprint)

    # Prepend abstract to content (inside JS template literal
    # to avoid JSX parsing issues with LaTeX curly braces)
    if abstract_html:
        content_html = abstract_html + "\n" + content_html

    # Determine the slug (filename without .astro)
    page_slug = filename.removesuffix(".astro")

    # Generate page
    page = generate_astro_page(
        eprint_id=eprint_id,
        title=title,
        authors=authors,
        year=year,
        number=number,
        content_html=content_html,
        toc_html=toc_html,
        crawler=crawler,
        converted_date=converted_date,
        slug=page_slug,
    )

    output_path.write_text(page, encoding="utf-8")
    return filename


def get_existing_eprint_map() -> dict[str, Path]:
    """Map eprint IDs to their existing .astro file paths."""
    result: dict[str, Path] = {}
    for f in OUTPUT_DIR.glob("*.astro"):
        if f.name == "index.astro":
            continue
        text = f.read_text(encoding="utf-8")
        m = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", text)
        if m:
            result[m.group(1)] = f
    return result


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Convert markdown papers to .astro pages"
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help=(
            "Reconvert all papers"
            " (ignores existing .astro files)"
        ),
    )
    parser.add_argument(
        "--paper",
        type=str,
        help="Convert a single paper (e.g. 2001_107)",
    )
    args = parser.parse_args()

    md_parser, renderer = create_markdown_parser()
    existing_map = get_existing_eprint_map()
    print(f"Existing papers: {len(existing_map)}")

    if args.paper:
        # Single paper mode
        paper_id = args.paper
        if not re.match(r"^\d{4}_\d+$", paper_id):
            print(
                f"Invalid paper ID: {paper_id}"
                " (expected YYYY_NNNN)",
                file=sys.stderr,
            )
            sys.exit(1)
        result = process_paper(
            paper_id,
            md_parser,
            renderer,
            existing_map,
            force=True,
        )
        if result:
            print(f"Converted: {result}")
        else:
            print("No output generated", file=sys.stderr)
            sys.exit(1)
        return

    # Batch mode
    paper_dirs = sorted(DATA_DIR.iterdir())
    new_count = 0
    skip_count = 0
    error_count = 0

    for paper_dir in paper_dirs:
        if not paper_dir.is_dir():
            continue
        paper_id = paper_dir.name
        if not re.match(r"^\d{4}_\d+$", paper_id):
            continue

        year, number = paper_id.split("_", 1)
        eprint_id = f"{year}/{number}"

        if not args.force and eprint_id in existing_map:
            skip_count += 1
            continue

        try:
            result = process_paper(
                paper_id,
                md_parser,
                renderer,
                existing_map,
                force=args.force,
            )
            if result:
                new_count += 1
                if new_count % 50 == 0:
                    print(f"  Processed {new_count}...")
            else:
                skip_count += 1
        except Exception as e:
            print(
                f"  ERROR {paper_id}: {e}",
                file=sys.stderr,
            )
            error_count += 1

    print(
        f"\nDone: {new_count} new,"
        f" {skip_count} skipped,"
        f" {error_count} errors"
    )


if __name__ == "__main__":
    main()
