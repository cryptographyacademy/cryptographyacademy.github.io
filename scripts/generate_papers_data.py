#!/usr/bin/env python3
"""Generate papers.json and papers-meta.json from .astro files.

Usage:
    python3 scripts/generate_papers_data.py

Reads:
    - web/src/pages/papers/*.astro (first ~20 lines for constants)

Writes:
    - web/src/data/papers.json
    - web/src/data/papers-meta.json
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "web" / "src" / "pages" / "papers"
OUTPUT_DIR = ROOT / "web" / "src" / "data"
DATA_DIR = ROOT / "data" / "markdown" / "eprint"

# Regex patterns for extracting constants from .astro frontmatter
RE_EPRINT = re.compile(r"eprint\.iacr\.org/(\d{4})/(\d+)")
RE_CRAWLER = re.compile(r"const CRAWLER\s*=\s*'([^']+)'")
RE_TITLE = re.compile(r"const TITLE_HTML\s*=\s*'(.+?)';")
RE_AUTHORS = re.compile(r"const AUTHORS_HTML\s*=\s*'(.+?)';")
# Fallback: extract title from <BaseLayout title="...">
RE_LAYOUT_TITLE = re.compile(r'<BaseLayout\s+title="(.+?)"')


def load_eprint_metadata() -> dict[str, dict]:
    """Load eprint metadata from *_meta.json files.

    Returns a dict mapping eprint ID (e.g. "2001/107") to the
    eprint metadata dict (title, authors, category, keywords).
    """
    result: dict[str, dict] = {}
    if not DATA_DIR.exists():
        return result
    for paper_dir in DATA_DIR.iterdir():
        if not paper_dir.is_dir():
            continue
        meta_path = paper_dir / f"{paper_dir.name}_meta.json"
        if not meta_path.exists():
            continue
        with open(meta_path, encoding="utf-8") as f:
            meta = json.load(f)
        eprint = meta.get("eprint")
        if not eprint:
            continue
        year, number = paper_dir.name.split("_", 1)
        eprint_id = f"{year}/{number}"
        result[eprint_id] = eprint
    return result


def unescape_html(s: str) -> str:
    """Unescape basic HTML entities and JS escapes."""
    return (
        s.replace("\\'", "'")
        .replace("&amp;", "&")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
    )


def strip_html(s: str) -> str:
    """Remove HTML tags from a string."""
    return re.sub(r"<[^>]+>", "", s)


def parse_astro_file(path: Path) -> dict | None:
    """Extract metadata from an .astro file.

    Tries frontmatter constants first (TITLE_HTML, AUTHORS_HTML),
    then falls back to BaseLayout title attribute for hand-curated
    files that embed title/authors directly in HTML.
    """
    slug = path.stem
    if slug == "index":
        return None

    text = path.read_text(encoding="utf-8")
    # Use first ~40 lines for frontmatter + template header
    header_lines = text.split("\n")[:40]
    header = "\n".join(header_lines)

    # Extract eprint year/number
    m = RE_EPRINT.search(header)
    if not m:
        print(f"  WARN: no eprint URL in {slug}", file=sys.stderr)
        return None
    year = int(m.group(1))
    number = int(m.group(2))

    # Extract crawler
    m = RE_CRAWLER.search(header)
    crawler = m.group(1) if m else ""

    # Extract title: try TITLE_HTML constant first
    m = RE_TITLE.search(header)
    if m:
        title = unescape_html(m.group(1))
    else:
        # Fallback: extract from <BaseLayout title="...">
        m = RE_LAYOUT_TITLE.search(text)
        if m:
            raw = m.group(1)
            # Remove the eprint suffix like " (2025/2040)"
            raw = re.sub(r"\s*\(\d{4}/\d+\)\s*$", "", raw)
            title = unescape_html(raw) if raw else slug
        else:
            title = slug

    # Extract authors: try AUTHORS_HTML constant first
    m = RE_AUTHORS.search(header)
    authors = unescape_html(m.group(1)) if m else ""

    return {
        "slug": slug,
        "title": title,
        "authors": authors,
        "year": year,
        "number": number,
        "crawler": crawler,
    }


def main() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    eprint_meta = load_eprint_metadata()
    print(f"Loaded eprint metadata for {len(eprint_meta)} papers")

    astro_files = sorted(PAPERS_DIR.glob("*.astro"))
    print(f"Found {len(astro_files)} .astro files in {PAPERS_DIR}")

    papers = []
    for path in astro_files:
        entry = parse_astro_file(path)
        if entry is None:
            continue

        eprint_id = f"{entry['year']}/{entry['number']}"
        eprint = eprint_meta.get(eprint_id)

        if eprint:
            if eprint.get("title") and entry["title"] == entry["slug"]:
                entry["title"] = eprint["title"]
            if eprint.get("authors") and not entry["authors"]:
                names = [a["name"] for a in eprint["authors"]]
                entry["authors"] = ", ".join(names)
            entry["category"] = eprint.get("category", "")
            entry["keywords"] = eprint.get("keywords", [])
        else:
            entry["category"] = ""
            entry["keywords"] = []

        papers.append(entry)

    # Sort by year desc, then number desc
    papers.sort(key=lambda p: (-p["year"], -p["number"]))

    print(f"Generated {len(papers)} paper entries")

    # Compute meta: unique years and categories with counts
    years = sorted({p["year"] for p in papers}, reverse=True)
    cat_counts: dict[str, int] = {}
    for p in papers:
        cat = p["category"] or "Uncategorized"
        cat_counts[cat] = cat_counts.get(cat, 0) + 1
    categories = sorted(cat_counts.items(), key=lambda x: -x[1])

    meta = {
        "years": years,
        "categories": [
            {"name": name, "count": count} for name, count in categories
        ],
        "total": len(papers),
    }

    # Write papers.json
    papers_path = OUTPUT_DIR / "papers.json"
    with open(papers_path, "w", encoding="utf-8") as f:
        json.dump(papers, f, ensure_ascii=False, indent=2)
    size_kb = papers_path.stat().st_size / 1024
    print(f"Wrote {papers_path} ({size_kb:.0f} KB)")

    # Write papers-meta.json
    meta_path = OUTPUT_DIR / "papers-meta.json"
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump(meta, f, ensure_ascii=False, indent=2)
    print(f"Wrote {meta_path}")


if __name__ == "__main__":
    main()
