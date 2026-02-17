#!/usr/bin/env python3
"""Generate papers-history.json from git log.

For each paper .astro file, extracts the git commit history
and writes a JSON map keyed by slug.

Usage:
    python3 scripts/generate_papers_history.py

Writes:
    - web/src/data/papers-history.json
"""

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "web" / "src" / "pages" / "papers"
OUTPUT_DIR = ROOT / "web" / "src" / "data"


def get_git_history(file_path: Path) -> list[dict]:
    """Get git log for a file as a list of commit entries."""
    rel = file_path.relative_to(ROOT)
    result = subprocess.run(
        [
            "git",
            "log",
            "--format=%H %ai %s",
            "--",
            str(rel),
        ],
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )
    if result.returncode != 0:
        print(
            f"  WARN: git log failed for {rel}: {result.stderr.strip()}",
            file=sys.stderr,
        )
        return []

    entries = []
    for line in result.stdout.strip().splitlines():
        if not line:
            continue
        # Format: <full-hash> <date> <time> <tz> <message>
        parts = line.split(" ", 4)
        if len(parts) < 5:
            continue
        full_hash = parts[0]
        date = parts[1]  # YYYY-MM-DD
        message = parts[4]
        entries.append(
            {
                "hash": full_hash[:7],
                "fullHash": full_hash,
                "date": date,
                "message": message,
            }
        )
    return entries


def main() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    astro_files = sorted(PAPERS_DIR.glob("*.astro"))
    print(f"Found {len(astro_files)} .astro files in {PAPERS_DIR}")

    history: dict[str, list[dict]] = {}
    skipped = 0

    for path in astro_files:
        slug = path.stem
        if slug == "index":
            skipped += 1
            continue

        entries = get_git_history(path)
        if entries:
            history[slug] = entries

    print(f"Generated history for {len(history)} papers (skipped {skipped})")

    out_path = OUTPUT_DIR / "papers-history.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(history, f, ensure_ascii=False, indent=2)
        f.write("\n")

    size_kb = out_path.stat().st_size / 1024
    print(f"Wrote {out_path} ({size_kb:.1f} KB)")


if __name__ == "__main__":
    main()
