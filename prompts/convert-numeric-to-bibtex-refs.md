# Convert Numeric Citations to BibTeX-Style Keys

## Goal

For paper pages that still use numeric citation keys (`[1]`, `[2]`,
etc.), convert them to BibTeX-style author-year keys (e.g.,
`[GKR+21]`). Keep the original numeric key as a comment or
data attribute so the mapping is preserved.

## Context

- Paper pages live in `web/src/pages/papers/<slug>.astro`
- The original 47 marker-converted pages already had their numeric
  citations converted to BibTeX keys (see `scripts/convert-citations.py`)
- The 471 new mistral-converted pages still use numeric keys
- Metadata JSON files in the poseidon-formalization repo at
  `/Users/soc/codes/dannywillems/poseidon-formalization/data/metadata/`
  contain BibTeX entries that can be used for key generation

## Requirements

1. **Identify papers with numeric citations** by scanning for
   patterns like `[1]`, `[2]`, `[12]` in reference sections.

2. **For each numeric reference**, extract the author surnames and
   year to generate a BibTeX-style key:
   - Single author: `[Gra23]` (first 3 letters of surname + 2-digit year)
   - Two authors: `[GK21]` (initials + year)
   - Three+ authors: `[GKR+21]` (initials of first 3 + "+" + year)

3. **Replace all occurrences** of the numeric key `[N]` with the
   generated BibTeX key `[Key]` throughout the page (both inline
   citations and the reference list).

4. **Preserve the original mapping** by adding a data attribute:
   ```html
   <span data-original-ref="1">[GKR+21]</span>
   ```

5. **Handle edge cases**:
   - References without author info: keep numeric key
   - Duplicate generated keys: append `a`, `b`, `c` suffix
   - References that are already BibTeX-style: skip

6. **Write as a Python script** in `scripts/`. Requirements:
   - Idempotent (skip pages already converted)
   - Report conversion stats per file
   - Pass `ruff check` and `ruff format`

## Priority

This is a secondary task. Run it AFTER cross-linking bibliography
references, since numeric keys make cross-linking harder.

## Verification

- `npx astro build --root web/` succeeds
- Spot-check 5 converted pages
- Verify no numeric citations remain in converted files
- Verify `data-original-ref` attributes are present
