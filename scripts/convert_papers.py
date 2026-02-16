#!/usr/bin/env python3
"""Convert markdown papers from poseidon-formalization to .astro pages.

Reads metadata JSON and markdown content, generates .astro pages
with proper header, content, and crawler metadata.
"""

import html
import json
import re
import sys
import unicodedata
from pathlib import Path

PAPYRUS_DIR = Path("/Users/soc/codes/dannywillems/poseidon-formalization/data")
MARKDOWN_DIR = PAPYRUS_DIR / "markdown"
METADATA_DIR = PAPYRUS_DIR / "metadata"
OUTPUT_DIR = Path(
    "/Users/soc/codes/badaas/cryptographyacademy.github.io/web/src/pages/papers"
)

# Existing eprint IDs (already have .astro pages)
EXISTING_IDS: set[str] = set()


def load_existing_ids() -> None:
    """Scan existing .astro files for their eprint IDs."""
    for f in OUTPUT_DIR.glob("*.astro"):
        if f.name == "index.astro":
            continue
        text = f.read_text()
        m = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", text)
        if m:
            EXISTING_IDS.add(m.group(1))


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


def md_to_html(md_content: str) -> str:
    """Convert markdown to HTML suitable for .astro embedding.

    Handles:
    - Headings (h1-h6) with IDs
    - Paragraphs
    - Bold/italic
    - Links
    - Images
    - Code blocks
    - Blockquotes
    - Lists
    - Math ($...$ and $$...$$)
    - Tables
    """
    lines = md_content.split("\n")
    html_parts: list[str] = []
    in_code_block = False
    code_lang = ""
    code_lines: list[str] = []
    in_list = False
    list_type = ""
    in_blockquote = False
    bq_lines: list[str] = []
    in_table = False
    table_lines: list[str] = []
    sec_counter = 0

    def flush_blockquote() -> None:
        nonlocal in_blockquote, bq_lines
        if bq_lines:
            content = "\n".join(bq_lines)
            content = process_inline(content)
            html_parts.append(
                f'    <blockquote class="border-l-4'
                f" border-gray-600 pl-4 my-4 text-gray-400"
                f' italic">\n      <p>{content}</p>\n'
                f"    </blockquote>"
            )
            bq_lines = []
        in_blockquote = False

    def flush_list() -> None:
        nonlocal in_list, list_type
        if in_list:
            tag = "ol" if list_type == "ol" else "ul"
            html_parts.append(f"    </{tag}>")
            in_list = False

    def flush_table() -> None:
        nonlocal in_table, table_lines
        if not table_lines:
            in_table = False
            return
        html_parts.append('    <div class="overflow-x-auto my-4">')
        html_parts.append('      <table class="min-w-full text-sm text-gray-300">')
        # First line is header
        headers = [c.strip() for c in table_lines[0].strip("|").split("|")]
        html_parts.append("        <thead>")
        html_parts.append("          <tr>")
        for h in headers:
            h = process_inline(h)
            html_parts.append(
                f'            <th class="px-3 py-2'
                f" text-left font-semibold"
                f' border-b border-gray-600">{h}</th>'
            )
        html_parts.append("          </tr>")
        html_parts.append("        </thead>")
        html_parts.append("        <tbody>")
        # Skip separator line (index 1), process data rows
        for row in table_lines[2:]:
            cells = [c.strip() for c in row.strip("|").split("|")]
            html_parts.append("          <tr>")
            for c in cells:
                c = process_inline(c)
                html_parts.append(
                    f'            <td class="px-3 py-2'
                    f' border-b border-gray-700">'
                    f"{c}</td>"
                )
            html_parts.append("          </tr>")
        html_parts.append("        </tbody>")
        html_parts.append("      </table>")
        html_parts.append("    </div>")
        table_lines = []
        in_table = False

    def process_inline(text: str) -> str:
        """Process inline markdown elements."""
        # Display math $$...$$ (do before inline)
        text = re.sub(
            r"\$\$(.+?)\$\$",
            lambda m: '<span class="math-block">' + html.escape(m.group(1)) + "</span>",
            text,
            flags=re.DOTALL,
        )
        # Inline math $...$
        text = re.sub(
            r"(?<!\$)\$(?!\$)(.+?)(?<!\$)\$(?!\$)",
            lambda m: '<span class="math">' + html.escape(m.group(1)) + "</span>",
            text,
        )
        # Bold **...**
        text = re.sub(
            r"\*\*(.+?)\*\*",
            r"<strong>\1</strong>",
            text,
        )
        # Italic *...*
        text = re.sub(
            r"(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)",
            r"<em>\1</em>",
            text,
        )
        # Links [text](url)
        text = re.sub(
            r"\[([^\]]+)\]\(([^)]+)\)",
            r'<a href="\2">\1</a>',
            text,
        )
        # Inline code `...`
        text = re.sub(
            r"`([^`]+)`",
            lambda m: "<code>" + html.escape(m.group(1)) + "</code>",
            text,
        )
        # Superscript <sup>
        # (already HTML, pass through)
        # Images ![alt](src)
        text = re.sub(
            r"!\[([^\]]*)\]\(([^)]+)\)",
            r'<img src="\2" alt="\1"'
            r' class="my-4 max-w-full" />',
            text,
        )
        return text

    i = 0
    while i < len(lines):
        line = lines[i]

        # Code blocks
        if line.startswith("```"):
            if in_code_block:
                code = html.escape("\n".join(code_lines))
                html_parts.append(
                    f'    <pre><code class="language-{code_lang}">{code}</code></pre>'
                )
                in_code_block = False
                code_lines = []
                code_lang = ""
            else:
                flush_blockquote()
                flush_list()
                flush_table()
                in_code_block = True
                code_lang = line[3:].strip() or "text"
            i += 1
            continue

        if in_code_block:
            code_lines.append(line)
            i += 1
            continue

        # Table detection
        if "|" in line and not line.startswith(">"):
            cells = line.strip("| \t").split("|")
            if len(cells) >= 2:
                if not in_table:
                    flush_blockquote()
                    flush_list()
                    in_table = True
                table_lines.append(line)
                i += 1
                continue
            else:
                flush_table()

        if in_table and ("|" not in line):
            flush_table()

        # Blank line
        if not line.strip():
            flush_blockquote()
            flush_list()
            i += 1
            continue

        # Headings
        m = re.match(r"^(#{1,6})\s+(.+)", line)
        if m:
            flush_blockquote()
            flush_list()
            flush_table()
            level = len(m.group(1))
            text = m.group(2)
            # Remove span IDs from heading text
            text = re.sub(r'<span id="[^"]*"></span>\s*', "", text)
            # Generate section ID
            sec_counter += 1
            sec_id = f"sec-{sec_counter}"
            text_processed = process_inline(text)
            if level == 1:
                # Skip H1 (title already in header)
                i += 1
                continue
            size = {
                2: "text-2xl font-bold",
                3: "text-xl font-semibold mt-8",
                4: "text-lg font-semibold mt-6",
                5: "text-base font-semibold mt-4",
                6: "text-base font-medium mt-4",
            }.get(level, "text-base font-semibold mt-4")
            html_parts.append(
                f'    <h{level} id="{sec_id}"'
                f' class="{size}">'
                f"{text_processed}</h{level}>"
            )
            i += 1
            continue

        # Blockquote
        if line.startswith(">"):
            flush_list()
            flush_table()
            in_blockquote = True
            bq_lines.append(line[1:].strip())
            i += 1
            continue

        if in_blockquote and not line.startswith(">"):
            flush_blockquote()

        # Unordered list
        m = re.match(r"^(\s*)[-*+]\s+(.+)", line)
        if m:
            flush_blockquote()
            flush_table()
            if not in_list or list_type != "ul":
                flush_list()
                in_list = True
                list_type = "ul"
                html_parts.append(
                    '    <ul class="list-disc list-inside'
                    ' space-y-1 text-gray-300 my-2 ml-4">'
                )
            content = process_inline(m.group(2))
            html_parts.append(f"      <li>{content}</li>")
            i += 1
            continue

        # Ordered list
        m = re.match(r"^(\s*)\d+[.)]\s+(.+)", line)
        if m:
            flush_blockquote()
            flush_table()
            if not in_list or list_type != "ol":
                flush_list()
                in_list = True
                list_type = "ol"
                html_parts.append(
                    '    <ol class="list-decimal'
                    " list-inside space-y-1"
                    ' text-gray-300 my-2 ml-4">'
                )
            content = process_inline(m.group(2))
            html_parts.append(f"      <li>{content}</li>")
            i += 1
            continue

        # Horizontal rule
        if re.match(r"^[-*_]{3,}\s*$", line):
            flush_blockquote()
            flush_list()
            flush_table()
            html_parts.append('    <hr class="my-8 border-gray-700" />')
            i += 1
            continue

        # Regular paragraph
        flush_list()
        flush_table()
        para_lines = [line]
        while (
            i + 1 < len(lines)
            and lines[i + 1].strip()
            and not lines[i + 1].startswith("#")
            and not lines[i + 1].startswith("```")
            and not lines[i + 1].startswith(">")
            and not re.match(r"^\s*[-*+]\s+", lines[i + 1])
            and not re.match(r"^\s*\d+[.)]\s+", lines[i + 1])
            and not re.match(r"^[-*_]{3,}\s*$", lines[i + 1])
            and "|" not in lines[i + 1]
        ):
            i += 1
            para_lines.append(lines[i])

        text = " ".join(para_lines)

        # Check for display math blocks ($$...$$)
        if text.strip().startswith("$$") and text.strip().endswith("$$"):
            math = text.strip()[2:-2].strip()
            math_escaped = html.escape(math)
            html_parts.append(
                f'    <div class="my-4 text-center">'
                f'<span class="math-block">'
                f"{math_escaped}</span></div>"
            )
        else:
            text = process_inline(text)
            html_parts.append(f'    <p class="text-gray-300">{text}</p>')

        i += 1

    # Flush remaining
    flush_blockquote()
    flush_list()
    flush_table()
    if in_code_block and code_lines:
        code = html.escape("\n".join(code_lines))
        html_parts.append(f"    <pre><code>{code}</code></pre>")

    return "\n\n".join(html_parts)


def escape_js_string(s: str) -> str:
    """Escape a string for embedding in a JS single-quoted string."""
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
    crawler: str = "mistral",
    converted_date: str = "2026-02-16",
) -> str:
    """Generate a complete .astro page for a paper."""
    title_html = html.escape(title)
    # For the BaseLayout title attr, use a short form
    short_title = title[:60] + "..." if len(title) > 60 else title
    short_title_escaped = html.escape(short_title)
    authors_html = html.escape(authors)

    # Escape for JS single-quoted strings in frontmatter
    title_js = escape_js_string(title_html)
    authors_js = escape_js_string(authors_html)

    # Escape content for embedding in a JS template literal:
    # backticks and ${} must be escaped
    content_for_js = content_html.replace("\\", "\\\\")
    content_for_js = content_for_js.replace("`", "\\`")
    content_for_js = content_for_js.replace("${", "\\${")

    return f"""\
---
import BaseLayout from '../../layouts/BaseLayout.astro';

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
      <p class="mt-4 text-xs text-gray-500">
        All content below belongs to the original authors. This page
        reproduces the paper for educational purposes. Always
        <a
          href={{EPRINT_URL}}
          target="_blank"
          rel="noopener noreferrer"
          class="text-blue-400 hover:text-blue-300"
        >cite the original</a>.
      </p>
      <p class="mt-1 text-xs text-gray-600">
        Converted with: {{CRAWLER}} &middot; {{CONVERTED_DATE}}
      </p>
    </header>

    <Fragment set:html={{CONTENT}} />

  </article>
</BaseLayout>
"""


def process_paper(paper_id_underscore: str) -> str | None:
    """Process a single paper. Returns output filename or None."""
    year, number = paper_id_underscore.split("_", 1)
    eprint_id = f"{year}/{number}"

    if eprint_id in EXISTING_IDS:
        return None

    # Load metadata
    meta_file = METADATA_DIR / f"{paper_id_underscore}.json"
    if not meta_file.exists():
        print(
            f"  SKIP {eprint_id}: no metadata",
            file=sys.stderr,
        )
        return None

    with open(meta_file) as f:
        meta = json.load(f)

    title = meta.get("title", f"Paper {eprint_id}")
    authors_list = meta.get("authors", [])
    authors = ", ".join(a.get("name", "") for a in authors_list)
    if not authors:
        authors = "Unknown authors"

    # Load markdown - try flat structure (mistral) first, then nested (marker)
    flat_md = MARKDOWN_DIR / paper_id_underscore / f"{paper_id_underscore}.md"
    nested_md = (
        MARKDOWN_DIR
        / paper_id_underscore
        / paper_id_underscore
        / f"{paper_id_underscore}.md"
    )

    if flat_md.exists():
        md_file = flat_md
        crawler = "mistral"
    elif nested_md.exists():
        md_file = nested_md
        crawler = "marker"
    else:
        print(
            f"  SKIP {eprint_id}: no markdown",
            file=sys.stderr,
        )
        return None

    md_content = md_file.read_text(encoding="utf-8")

    # Convert markdown to HTML
    content_html = md_to_html(md_content)

    # Generate filename
    slug = title_to_slug(title)
    if not slug:
        slug = paper_id_underscore.replace("_", "-")
    filename = f"{slug}-{year}.astro"

    # Check for filename collisions
    output_path = OUTPUT_DIR / filename
    if output_path.exists():
        # Append eprint number to disambiguate
        filename = f"{slug}-{year}-{number}.astro"
        output_path = OUTPUT_DIR / filename

    # Generate page
    page = generate_astro_page(
        eprint_id=eprint_id,
        title=title,
        authors=authors,
        year=year,
        number=number,
        content_html=content_html,
        crawler=crawler,
        converted_date="2026-02-16",
    )

    output_path.write_text(page, encoding="utf-8")
    return filename


def main() -> None:
    load_existing_ids()
    print(f"Existing papers: {len(EXISTING_IDS)}")

    md_dirs = sorted(MARKDOWN_DIR.iterdir())
    new_count = 0
    skip_count = 0
    error_count = 0

    for md_dir in md_dirs:
        if not md_dir.is_dir():
            continue
        paper_id = md_dir.name
        # Validate format YYYY_NNNN
        if not re.match(r"^\d{4}_\d+$", paper_id):
            continue

        year, number = paper_id.split("_", 1)
        eprint_id = f"{year}/{number}"
        if eprint_id in EXISTING_IDS:
            skip_count += 1
            continue

        try:
            result = process_paper(paper_id)
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

    print(f"\nDone: {new_count} new, {skip_count} skipped, {error_count} errors")


if __name__ == "__main__":
    main()
