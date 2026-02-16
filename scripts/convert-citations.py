#!/usr/bin/env python3
"""Convert numeric [N] citations to BibTeX-style [AuthorYY] keys in .astro
paper pages.

Usage:
    python3 scripts/convert-citations.py web/src/pages/papers/my-paper.astro
    python3 scripts/convert-citations.py --dry-run web/src/pages/papers/*.astro
    python3 scripts/convert-citations.py \
        --add-crosslinks-only web/src/pages/papers/my-paper.astro

The script:
  1. Parses the references section (id="references")
  2. Extracts author names + year from each <li>
  3. Generates BibTeX-style keys (Surname{YY}, Sur1Sur2{YY}, Sur1+{YY})
  4. Replaces all [N] citations in the body with [Key]
  5. Updates reference labels from numbers to keys
  6. Adds cross-links for papers that exist on the website
"""

import argparse
import html
import os
import re
import sys
import unicodedata

# ──────────────────────────────────────────────────────────────────
# Eprint → slug mapping for cross-links
# ──────────────────────────────────────────────────────────────────
EPRINT_TO_SLUG = {
    "2012/280": "partial-sums-square-attack-aes-2012",
    "2014/187": "fft-key-recovery-integral-2014",
    "2016/660": "skinny-mantis-2016",
    "2017/832": "mixture-differential-aes-2017",
    "2017/1050": "scalable-mpc-zksnark-2017",
    "2017/1148": "improvements-lowmc-2017",
    "2018/182": "truncated-diff-diagonal-aes-2018",
    "2019/397": "feistel-structures-mpc-2019",
    "2019/458": "poseidon-2019",
    "2019/550": "spartan-2019",
    "2019/601": "auroralight-2019",
    "2019/614": "offline-simon-quantum-2019",
    "2019/622": "truncated-diff-aes-2019",
    "2019/652": "exchange-attack-2019",
    "2019/750": "weight-probability-spn-2019",
    "2019/945": "key-independent-aes-6round-2019",
    "2019/951": "collisions-feistel-mimc-2019",
    "2019/953": "plonk-2019",
    "2019/1021": "halo-recursive-proofs-2019",
    "2019/1107": "hades-2019",
    "2020/179": "hades-revisited-2020",
    "2020/188": "out-of-oddity-2020",
    "2020/315": "plookup-2020",
    "2020/500": "subspace-trails-2020",
    "2020/820": "security-rescue-hash-2020",
    "2020/1143": "rescue-prime-2020",
    "2021/1038": "reinforced-concrete-2021",
    "2022/274": "ecgfp5-2022",
    "2022/403": "griffin-2022",
    "2022/462": "plonk-optimization-2022",
    "2022/840": "anemoi-2022",
    "2022/957": "caulk-plus-2022",
    "2022/1447": "flookup-2022",
    "2022/1487": "verifiable-state-zkevm-anemoi-2022",
    "2022/1530": "logup-multivariate-lookups-2022",
    "2022/1577": "rescue-prime-optimized-2022",
    "2023/107": "tip5-2023",
    "2023/323": "poseidon2-2023",
    "2023/342": "turboshake-2023",
    "2023/522": "safe-sponge-api-2023",
    "2024/504": "binius-polylog-proofs-2024",
    "2024/605": "security-analysis-xhash-2024",
    "2024/633": "vision-mark32-2024",
    "2025/937": "attacking-poseidon-graeffe-2025",
    "2025/950": "breaking-poseidon-graeffe-2025",
    "2025/1893": "poseidon-binary-2025",
    "2025/2040": "algebraic-cheaplunch-2025",
}

CROSSLINK_HTML = (
    ' <a href="/papers/{slug}"'
    ' class="text-blue-400 hover:text-blue-300">'
    "[page on this site]</a>"
)


def strip_accents(s):
    """Remove diacritics: e.g. Lueftenegger -> Luftenegger."""
    # First decode HTML entities like &uuml; -> u
    s = html.unescape(s)
    nfkd = unicodedata.normalize("NFKD", s)
    return "".join(c for c in nfkd if not unicodedata.combining(c))


def extract_surname(name):
    """Extract surname from 'Surname, F.' or 'F. Surname' format."""
    name = name.strip().rstrip(".")
    name = strip_accents(name)
    # Remove "van der", "de", "el" etc. prefixes for key generation
    # but keep them for display
    if "," in name:
        # "Surname, FirstName" format
        surname = name.split(",")[0].strip()
    else:
        # "FirstName Surname" or "F. Surname" format
        parts = name.split()
        # Last part is surname (skip initials like "F.")
        surname = parts[-1] if len(parts) >= 2 else parts[0]

    # Clean up
    surname = re.sub(r"[^A-Za-z]", "", surname)
    return surname


def make_bibtex_key(authors, year):
    """Generate BibTeX-style citation key from author list and year.

    Convention:
      1 author:  [SurnameYY]
      2 authors: [Sur1Sur2YY]     (first 3 chars of each surname)
      3 authors: [Sur1Sur2Sur3YY] (first 3 chars of each surname)
      4+ authors: [Sur1+YY]       (first 3 chars of first surname)
    """
    yy = str(year)[-2:]
    surnames = [extract_surname(a) for a in authors if a.strip()]
    surnames = [s for s in surnames if s]  # filter empty

    if not surnames:
        return None

    if len(surnames) == 1:
        return f"{surnames[0]}{yy}"
    elif len(surnames) == 2:
        return f"{surnames[0][:3]}{surnames[1][:3]}{yy}"
    elif len(surnames) == 3:
        return f"{surnames[0][:3]}{surnames[1][:3]}{surnames[2][:3]}{yy}"
    else:
        return f"{surnames[0][:3]}+{yy}"


def parse_reference_entry(li_text):
    """Parse a single <li> reference entry to extract authors, year,
    and eprint ID.

    Returns (authors_list, year, eprint_id_or_None).
    """
    # Strip HTML tags for parsing
    clean = re.sub(r"<[^>]+>", " ", li_text)
    clean = html.unescape(clean)
    clean = re.sub(r"\s+", " ", clean).strip()

    # Extract eprint ID
    eprint_match = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", li_text)
    eprint_id = eprint_match.group(1) if eprint_match else None

    # Extract year - look for (YYYY) or (Mon YYYY) patterns, or
    # standalone 4-digit year
    year = None
    year_patterns = [
        r"\((\d{4})\)",  # (2019)
        r"\([A-Z][a-z]+ (\d{4})\)",  # (Aug 2020)
        r"\b((?:19|20)\d{2})\b",  # standalone year
    ]
    for pat in year_patterns:
        m = re.search(pat, clean)
        if m:
            year = int(m.group(1))
            break

    # Detect non-paper entries (URLs, websites, standards docs)
    # These typically lack the "Author: Title" pattern
    if not re.search(r"[A-Z][a-z]+,\s+[A-Z]\.", clean):
        # No "Surname, I." pattern found - might be a website/URL
        # Try to extract a short name from the beginning
        first_word = clean.split()[0] if clean else ""
        if first_word and re.match(r"^[A-Z]", first_word):
            first_word = re.sub(r"[^A-Za-z]", "", first_word)
            if year:
                return [first_word], year, eprint_id
        # Try to find ANY capitalized word as fallback
        words = clean.split()[:5]
        names = [
            re.sub(r"[^A-Za-z]", "", w)
            for w in words
            if re.match(r"^[A-Z][a-z]+", w)
        ]
        if names and year:
            return [names[0]], year, eprint_id
        return [], year, eprint_id

    # Extract authors - text before ": " (author-title separator)
    # Pattern: "Author1, A., Author2, B.: Title..."
    colon_match = re.match(r"^(.+?):\s", clean)
    if colon_match:
        author_str = colon_match.group(1)
    else:
        author_str = clean.split(".")[0] if "." in clean else ""

    # Parse "Surname, I." pairs using a dedicated regex
    # Handles: "Grassi, L.", "van der Hoeven, J.",
    # "Lueftenegger, R."
    # Pattern: optional prefix (van, de, el, ...) + Surname + ,
    #          + Initials
    author_pattern = re.compile(
        r"(?:(?:van\s+der|van|de\s+la|de|el|di|le|du)\s+)?"
        r"([A-Z][A-Za-z\u00C0-\u017F'-]+)"
        r",\s*"
        r"([A-Z]\.(?:\s*[A-Z]\.)*)",
    )

    authors = []
    for m in author_pattern.finditer(author_str):
        surname = m.group(1)
        authors.append(surname)

    # Handle trailing "and Surname, I." that might not match
    and_match = re.search(
        r"\band\s+"
        r"(?:(?:van\s+der|van|de\s+la|de|el|di|le|du)\s+)?"
        r"([A-Z][A-Za-z\u00C0-\u017F'-]+)"
        r",\s*"
        r"([A-Z]\.(?:\s*[A-Z]\.)*)",
        author_str,
    )
    if and_match and and_match.group(1) not in authors:
        authors.append(and_match.group(1))

    if not authors:
        # Last resort: grab first few capitalized words
        words = clean.split()[:5]
        for w in words:
            w = w.strip(",.")
            if re.match(r"^[A-Z][a-z]+$", w):
                authors.append(w)

    return authors, year, eprint_id


def find_references_section(content):
    """Find the references <section> and return (start, end, tag)
    where tag is 'ol' or 'ul'."""
    ref_match = re.search(r'<section\s+id="references"', content)
    if not ref_match:
        return None, None, None

    section_start = ref_match.start()

    # Try <ol> first, then <ul>
    for tag in ("ol", "ul"):
        list_start = content.find(f"<{tag}", section_start)
        if list_start == -1:
            continue
        # Make sure it's within the references section
        next_section = content.find("<section", section_start + 1)
        if next_section != -1 and list_start > next_section:
            continue
        list_end = content.find(f"</{tag}>", list_start)
        if list_end == -1:
            continue
        return list_start, list_end + len(f"</{tag}>"), tag

    return None, None, None


def extract_li_entries(ol_content):
    """Extract individual <li>...</li> entries from an <ol> block."""
    entries = []
    # Split by <li> tags
    parts = re.split(r"<li[^>]*>", ol_content)
    for part in parts[1:]:  # skip first (before first <li>)
        end = part.find("</li>")
        if end != -1:
            entries.append(part[:end])
        else:
            entries.append(part)
    return entries


def has_crosslink(li_text):
    """Check if a reference entry already has a crosslink."""
    return "page on this site" in li_text


def find_eprint_in_li(li_text):
    """Find eprint ID in a <li> reference entry."""
    m = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", li_text)
    return m.group(1) if m else None


def add_crosslink_to_li(li_text, slug):
    """Add a crosslink before </li>."""
    link = CROSSLINK_HTML.format(slug=slug)
    return li_text + link


def parse_ul_reference_entry(li_text):
    """Parse a <ul> reference entry with [N] prefix.

    Format: "[N] Author1, Author2, ... Title. Venue Year."
    Returns (ref_number, authors_list, year, eprint_id).
    """
    # Strip HTML tags
    clean = re.sub(r"<[^>]+>", " ", li_text)
    clean = html.unescape(clean)
    clean = re.sub(r"\s+", " ", clean).strip()

    # Extract reference number [N]
    num_match = re.match(r"\[(\d+)\]\s*", clean)
    if not num_match:
        return None, [], None, None
    ref_num = int(num_match.group(1))
    rest = clean[num_match.end() :]

    # Extract eprint ID
    eprint_match = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", li_text)
    eprint_id = eprint_match.group(1) if eprint_match else None

    # Extract year
    year = None
    for pat in [r"\b((?:19|20)\d{2})\b"]:
        for m in re.finditer(pat, rest):
            year = int(m.group(1))
            # Take the last year found (usually the publication year)

    # Extract authors - everything before the first period
    # or before an <em> title
    em_match = re.search(r"<em>", li_text)
    if em_match:
        # Authors are between [N] and <em>
        author_section = li_text[li_text.find("]") + 1 : em_match.start()]
        author_section = re.sub(r"<[^>]+>", " ", author_section)
        author_section = html.unescape(author_section).strip()
    else:
        # Take text before first period
        author_section = rest.split(".")[0]

    # Split by comma and clean
    parts = [p.strip().rstrip(".") for p in re.split(r",\s*", author_section)]
    authors = []
    for p in parts:
        p = re.sub(r"^and\s+", "", p).strip()
        # Skip empty, initials-only, or non-name parts
        if p and re.match(r"^[A-Z][a-z]", p):
            # Extract just the surname (first word)
            surname = p.split()[0].rstrip(",.")
            surname = re.sub(r"[^A-Za-z]", "", surname)
            if surname:
                authors.append(surname)

    return ref_num, authors, year, eprint_id


def convert_file(filepath, dry_run=False, crosslinks_only=False):
    """Convert citations in a single .astro file.

    Returns (success, message).
    """
    with open(filepath, encoding="utf-8") as f:
        content = f.read()

    original = content
    slug = os.path.basename(filepath).replace(".astro", "")

    # Find references section
    list_start, list_end, list_tag = find_references_section(content)
    if list_start is None:
        return False, f"No references section found in {filepath}"

    list_block = content[list_start:list_end]
    entries = extract_li_entries(list_block)

    if not entries:
        return False, (f"No <li> entries found in references of {filepath}")

    # Detect if this is a <ul> with [N] prefixes
    is_ul_numbered = list_tag == "ul" and re.search(
        r"^\s*\[\d+\]", re.sub(r"<[^>]+>", "", entries[0])
    )

    # Parse each reference
    ref_map = {}  # number -> bibtex_key
    eprint_map = {}  # number -> eprint_id
    crosslink_map = {}  # number -> slug (for papers on site)

    for i, entry in enumerate(entries):
        if is_ul_numbered:
            ref_num, authors, year, eprint_id = parse_ul_reference_entry(entry)
            if ref_num is None:
                continue
            num = ref_num
        else:
            num = i + 1
            authors, year, eprint_id = parse_reference_entry(entry)

        if eprint_id:
            eprint_map[num] = eprint_id
            if eprint_id in EPRINT_TO_SLUG:
                target_slug = EPRINT_TO_SLUG[eprint_id]
                if target_slug != slug:  # don't self-link
                    crosslink_map[num] = target_slug

        if not crosslinks_only and authors and year:
            key = make_bibtex_key(authors, year)
            if key:
                # Handle duplicate keys by appending a/b/c
                base_key = key
                suffix_idx = 0
                while key in ref_map.values():
                    key = base_key + chr(ord("a") + suffix_idx)
                    suffix_idx += 1
                ref_map[num] = key

    if not crosslinks_only:
        print(f"\n  {filepath}:")
        print(
            f"  Found {len(entries)} references, generated {len(ref_map)} keys"
        )
        for num, key in sorted(ref_map.items()):
            eprint = eprint_map.get(num, "")
            xlink = (
                f" -> /papers/{crosslink_map[num]}"
                if num in crosslink_map
                else ""
            )
            print(
                f"    [{num}] -> [{key}]"
                f"{'  (eprint ' + eprint + ')' if eprint else ''}"
                f"{xlink}"
            )

    # ── Phase 1: Replace numeric citations in body ──

    if not crosslinks_only:
        # Replace in content BEFORE the references section
        body = content[:list_start]

        # Replace multi-citations FIRST [N, M, ...] -> [Key1, Key2]
        def replace_multi_citation(match):
            nums_str = match.group(1)
            nums = [n.strip() for n in nums_str.split(",")]
            keys = []
            for n in nums:
                try:
                    num_int = int(n)
                    if num_int in ref_map:
                        keys.append(ref_map[num_int])
                    else:
                        keys.append(n)
                except ValueError:
                    keys.append(n)
            return "[" + ", ".join(keys) + "]"

        body = re.sub(
            r"\[(\d+(?:\s*,\s*\d+)+)\]",
            replace_multi_citation,
            body,
        )

        # Then replace single [N] with [Key] (highest first to
        # avoid [1] matching part of [11])
        for num, key in sorted(ref_map.items(), reverse=True):
            body = re.sub(
                rf"(?<!=)(?<!\")(?<!id=\")\[{num}\]",
                f"[{key}]",
                body,
            )

        content = body + content[list_start:]

        # Also replace [N] prefixes in the reference entries
        # themselves (for <ul> format)
        if is_ul_numbered:
            list_start2, list_end2, _ = find_references_section(content)
            if list_start2 is not None:
                ref_block = content[list_start2:list_end2]
                for num, key in sorted(ref_map.items(), reverse=True):
                    ref_block = ref_block.replace(f"[{num}]", f"[{key}]")
                content = (
                    content[:list_start2] + ref_block + content[list_end2:]
                )

    # ── Phase 2: Add crosslinks to references ──

    list_start, list_end, _ = find_references_section(content)
    if list_start is not None:
        list_block = content[list_start:list_end]

        for num, target_slug in crosslink_map.items():
            li_positions = list(re.finditer(r"<li[^>]*>", list_block))
            if num - 1 < len(li_positions):
                li_start = li_positions[num - 1].start()
                li_end = list_block.find("</li>", li_start)
                if li_end != -1:
                    li_content = list_block[li_start:li_end]
                    if not has_crosslink(li_content):
                        link = CROSSLINK_HTML.format(slug=target_slug)
                        list_block = (
                            list_block[:li_end] + link + list_block[li_end:]
                        )

        content = content[:list_start] + list_block + content[list_end:]

    if content == original:
        return True, f"No changes needed for {filepath}"

    if dry_run:
        return True, f"Would modify {filepath}"

    with open(filepath, "w", encoding="utf-8") as f:
        f.write(content)

    return True, f"Converted {filepath}"


def main():
    parser = argparse.ArgumentParser(
        description="Convert numeric citations to BibTeX-style keys"
    )
    parser.add_argument("files", nargs="+", help="Astro paper files to convert")
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be done without modifying files",
    )
    parser.add_argument(
        "--add-crosslinks-only",
        action="store_true",
        help="Only add cross-links, don't convert citation keys",
    )
    parser.add_argument(
        "--update-slug-map",
        metavar="DIR",
        help="Scan a papers directory to update the eprint->slug map",
    )

    args = parser.parse_args()

    # Optionally update the slug map from the papers directory
    if args.update_slug_map:
        scan_dir = args.update_slug_map
        print(f"Scanning {scan_dir} for eprint->slug mapping...")
        for fname in sorted(os.listdir(scan_dir)):
            if not fname.endswith(".astro") or fname == "index.astro":
                continue
            fpath = os.path.join(scan_dir, fname)
            with open(fpath) as f:
                text = f.read()
            m = re.search(r"eprint\.iacr\.org/(\d{4}/\d+)", text)
            if m:
                eid = m.group(1)
                s = fname.replace(".astro", "")
                if eid not in EPRINT_TO_SLUG:
                    print(f"  NEW: {eid} -> {s}")
                EPRINT_TO_SLUG[eid] = s

    for filepath in args.files:
        if not filepath.endswith(".astro"):
            print(f"Skipping non-astro file: {filepath}")
            continue
        if filepath.endswith("index.astro"):
            continue

        success, msg = convert_file(
            filepath,
            dry_run=args.dry_run,
            crosslinks_only=args.add_crosslinks_only,
        )
        print(msg)
        if not success:
            print(f"  WARNING: {msg}", file=sys.stderr)


if __name__ == "__main__":
    main()
