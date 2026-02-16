#!/usr/bin/env python3
"""Generate papers.json and papers-meta.json from .astro files
and external metadata JSONs.

Usage:
    python3 scripts/generate_papers_data.py

Reads:
    - web/src/pages/papers/*.astro (first ~15 lines for constants)
    - $METADATA_DIR/*.json (category, keywords from eprint metadata)

Writes:
    - web/src/data/papers.json
    - web/src/data/papers-meta.json
"""

import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "web" / "src" / "pages" / "papers"
OUTPUT_DIR = ROOT / "web" / "src" / "data"
METADATA_DIR = Path(
    os.environ.get(
        "METADATA_DIR",
        str(
            Path.home()
            / "codes"
            / "dannywillems"
            / "poseidon-formalization"
            / "data"
            / "metadata"
        ),
    )
)

# Regex patterns for extracting constants from .astro frontmatter
RE_EPRINT = re.compile(r"eprint\.iacr\.org/(\d{4})/(\d+)")
RE_CRAWLER = re.compile(r"const CRAWLER\s*=\s*'([^']+)'")
RE_TITLE = re.compile(r"const TITLE_HTML\s*=\s*'(.+?)';")
RE_AUTHORS = re.compile(r"const AUTHORS_HTML\s*=\s*'(.+?)';")


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
    """Extract metadata from the first lines of an .astro file."""
    slug = path.stem
    if slug == "index":
        return None

    # Read just the frontmatter (first 20 lines is enough)
    lines = []
    with open(path, "r", encoding="utf-8") as f:
        for i, line in enumerate(f):
            if i >= 20:
                break
            lines.append(line)
    header = "".join(lines)

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

    # Extract title
    m = RE_TITLE.search(header)
    title = unescape_html(m.group(1)) if m else slug

    # Extract authors
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


def load_metadata(year: int, number: int) -> dict:
    """Load title, authors, category, keywords from metadata JSON."""
    fname = f"{year}_{number}.json"
    meta_path = METADATA_DIR / fname
    if not meta_path.exists():
        return {}
    try:
        with open(meta_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        result = {}
        if data.get("title"):
            result["title"] = data["title"]
        if data.get("authors"):
            names = [a["name"] for a in data["authors"] if a.get("name")]
            if names:
                result["authors"] = ", ".join(names)
        if data.get("category"):
            result["category"] = data["category"]
        if data.get("keywords"):
            result["keywords"] = data["keywords"]
        return result
    except (json.JSONDecodeError, KeyError):
        return {}


def main() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    astro_files = sorted(PAPERS_DIR.glob("*.astro"))
    print(f"Found {len(astro_files)} .astro files in {PAPERS_DIR}")

    papers = []
    for path in astro_files:
        entry = parse_astro_file(path)
        if entry is None:
            continue

        # Merge external metadata
        meta = load_metadata(entry["year"], entry["number"])

        # Use metadata title/authors as fallback when .astro lacks them
        if entry["title"] == entry["slug"] and meta.get("title"):
            entry["title"] = meta["title"]
        if not entry["authors"] and meta.get("authors"):
            entry["authors"] = meta["authors"]

        entry["category"] = meta.get("category", "")
        entry["keywords"] = meta.get("keywords", [])

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
            {"name": name, "count": count}
            for name, count in categories
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
