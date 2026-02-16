#!/usr/bin/env python3
"""Extract the date each paper page was first added, from git history.

Outputs a mapping of filename -> YYYY-MM-DD for each .astro file
in web/src/pages/papers/, based on the first commit that added it.
"""

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = REPO_ROOT / "web" / "src" / "pages" / "papers"


def get_first_commit_date(filepath: Path) -> str | None:
    """Get the date of the first commit that added a file.

    Returns date as YYYY-MM-DD string, or None if not tracked.
    """
    rel_path = filepath.relative_to(REPO_ROOT)
    result = subprocess.run(
        [
            "git",
            "-C",
            str(REPO_ROOT),
            "log",
            "--diff-filter=A",
            "--format=%ai",
            "--",
            str(rel_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return None
    # The last line is the earliest commit (first addition)
    lines = result.stdout.strip().splitlines()
    earliest = lines[-1]
    # Extract just the date part (YYYY-MM-DD)
    return earliest.split()[0]


def main() -> None:
    if not PAPERS_DIR.exists():
        print(
            f"Papers directory not found: {PAPERS_DIR}",
            file=sys.stderr,
        )
        sys.exit(1)

    papers = sorted(f for f in PAPERS_DIR.glob("*.astro") if f.name != "index.astro")

    print(f"Found {len(papers)} paper pages\n")
    print(f"{'Filename':<60} {'First Added'}")
    print("-" * 75)

    for paper in papers:
        date = get_first_commit_date(paper)
        display_date = date or "(not tracked)"
        print(f"{paper.name:<60} {display_date}")


if __name__ == "__main__":
    main()
