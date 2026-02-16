# Cryptography Academy — Web

The Astro static site powering
[cryptography.academy](https://cryptography.academy).

## Stack

- **Astro 5** — Static site generator (zero JS by default)
- **Tailwind CSS 4** — Utility-first styling via Vite plugin
- **React 19** — Interactive islands (Lean editor, social icons)
- **KaTeX** — Client-side LaTeX math rendering

## Project Structure

```
web/
├── public/               # Static assets (favicon, logo, CNAME)
├── src/
│   ├── components/       # React components
│   │   ├── LeanEditor.tsx
│   │   └── SocialIcons.tsx
│   ├── content/          # Astro content collections
│   │   ├── foundations/
│   │   ├── papers/
│   │   ├── primitives/
│   │   └── proofs/
│   ├── layouts/
│   │   └── BaseLayout.astro
│   ├── pages/
│   │   ├── about.astro
│   │   ├── index.astro
│   │   ├── foundations/
│   │   ├── papers/       # 518 paper pages + index
│   │   ├── primitives/
│   │   └── proofs/
│   └── styles/
│       └── global.css
├── astro.config.mjs
└── package.json
```

## Paper Pages

Each paper in `src/pages/papers/` is a standalone `.astro` file
containing the full HTML content of a cryptographic paper from
the IACR ePrint Archive.

**Two formats exist:**

1. **Hand-curated pages** (47 pages) — Converted with the
   `marker` tool, often enriched with Lean 4 code blocks and
   interactive editors.
2. **Auto-generated pages** (471 pages) — Converted from
   markdown using `scripts/convert_papers.py`. Content is
   stored in a JS template literal and injected via
   `<Fragment set:html={CONTENT} />` to avoid JSX parsing
   issues with math notation.

Each page declares:

```javascript
const EPRINT_URL = 'https://eprint.iacr.org/YYYY/NNNN';
const CRAWLER = 'marker' | 'mistral';
const CONVERTED_DATE = 'YYYY-MM-DD';
```

The papers index (`papers/index.astro`) dynamically discovers
all paper pages at build time using `import.meta.glob`.

## Math Rendering

KaTeX renders math client-side. Content uses two CSS classes:

- `.math` — Inline math (`$...$` in source)
- `.math-block` — Display math (`$$...$$` in source)

The `BaseLayout.astro` loads KaTeX and runs rendering on
`DOMContentLoaded`.

## Development

All commands should be run from the repository root using Make:

```bash
# Install dependencies
make setup

# Start dev server (localhost:4321)
make serve

# Production build
make build-web

# Verbose build (for debugging)
make build-web-verbose
```

Or from the `web/` directory with npm:

```bash
npm install
npm run dev          # Dev server
npm run build        # Production build
npm run preview      # Preview built site
npm run format       # Format with Prettier
npm run check-format # Check formatting
```

## Build Configuration

- `build.concurrency: 2` — Parallel page rendering (524 pages
  build in ~35 seconds)
- Site URL: `https://cryptography.academy`
- Output: static HTML in `dist/`

## Adding Papers

To add new papers from the poseidon-formalization data:

```bash
python3 scripts/convert_papers.py
```

The script reads metadata JSON and markdown from
`/data/metadata/` and `/data/markdown/`, converts to HTML, and
generates `.astro` files. It skips papers that already have
pages on the site.
