# Cross-Link Bibliography References to On-Site Papers

## Goal

For every paper page in `web/src/pages/papers/*.astro`, scan the
references/bibliography section and check whether any cited paper
also has its own page on the website. When a match is found, add a
link to the on-site page next to the original citation.

## Context

- Paper pages live in `web/src/pages/papers/<slug>.astro`
- Each page has `const EPRINT_URL = 'https://eprint.iacr.org/YYYY/NNNN'`
  in its frontmatter
- References typically cite eprint papers by their ID (e.g.,
  `[GKR+21]` pointing to `eprint.iacr.org/2021/1038`)
- Some references use numeric keys `[1], [2], ...` while others
  already use BibTeX-style keys `[GKR+21]`

## Requirements

1. **Build a mapping** of all eprint IDs to their on-site page slugs
   by scanning every `.astro` file for `EPRINT_URL`.

2. **Scan each paper's references section** for eprint URLs
   (`eprint.iacr.org/YYYY/NNNN` or `ia.cr/YYYY/NNNN`).

3. **For each match**, add a small link to the on-site page next to
   the existing reference. Example:

   Before:
   ```html
   <li>[GKR+21] Grassi et al. <em>Poseidon...</em>
     <a href="https://eprint.iacr.org/2019/458">eprint</a></li>
   ```

   After:
   ```html
   <li>[GKR+21] Grassi et al. <em>Poseidon...</em>
     <a href="https://eprint.iacr.org/2019/458">eprint</a>
     <a href="/papers/poseidon-2019"
        class="text-green-400 hover:text-green-300 text-xs ml-1"
        title="Available on this site">[on-site]</a></li>
   ```

4. **Write this as a Python script** in `scripts/` that can be re-run
   whenever new papers are added. The script should:
   - Be idempotent (running it twice produces the same result)
   - Report how many cross-links were added per file
   - Pass `ruff check` and `ruff format`

5. **Do not modify** the original reference text or URL. Only append
   the on-site link.

## Verification

- `npx astro build --root web/` succeeds
- Spot-check 3 papers that cite other on-site papers
- Count total cross-links added
