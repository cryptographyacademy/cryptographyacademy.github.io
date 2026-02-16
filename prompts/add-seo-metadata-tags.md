# Add SEO and Crawler Metadata Tags to Paper Pages

## Goal

Add hidden structured metadata to every paper page so that external
crawlers, search engines, and AI bots can discover and process paper
information without affecting the visual presentation for humans.

## Context

- Paper pages live in `web/src/pages/papers/<slug>.astro`
- Each page has `EPRINT_URL` in its frontmatter
- Metadata JSON files are available at
  `/Users/soc/codes/dannywillems/poseidon-formalization/data/metadata/`
  with full paper details (title, authors, abstract, keywords,
  category, publication info, license, versions, BibTeX)
- The layout is `web/src/layouts/BaseLayout.astro` which has a
  `<head>` section

## Requirements

### 1. Dublin Core Meta Tags (in `<head>`)

Add to each paper page's frontmatter section, passed to BaseLayout:

```html
<meta name="dc.title" content="{title}" />
<meta name="dc.creator" content="{authors}" />
<meta name="dc.date" content="{year}" />
<meta name="dc.identifier" content="https://eprint.iacr.org/{id}" />
<meta name="dc.type" content="Text" />
<meta name="dc.format" content="text/html" />
<meta name="dc.source" content="IACR ePrint Archive" />
<meta name="dc.subject" content="{keywords}" />
<meta name="dc.rights" content="{license}" />
```

### 2. Schema.org JSON-LD (in `<head>`)

Add a `<script type="application/ld+json">` block:

```json
{
  "@context": "https://schema.org",
  "@type": "ScholarlyArticle",
  "name": "{title}",
  "author": [
    { "@type": "Person", "name": "{author1}" },
    { "@type": "Person", "name": "{author2}" }
  ],
  "datePublished": "{year}",
  "url": "https://eprint.iacr.org/{id}",
  "identifier": "eprint:{id}",
  "keywords": ["{kw1}", "{kw2}"],
  "abstract": "{abstract}",
  "publisher": {
    "@type": "Organization",
    "name": "IACR"
  },
  "isPartOf": {
    "@type": "WebSite",
    "name": "Cryptography Academy",
    "url": "https://cryptography.academy"
  }
}
```

### 3. Hidden Metadata in Article Body

Add a visually hidden `<div>` at the top of the article with
machine-readable attributes:

```html
<div class="sr-only" aria-hidden="true"
     data-paper-id="{eprint_id}"
     data-paper-url="{eprint_url}"
     data-paper-title="{title}"
     data-paper-authors="{authors}"
     data-paper-year="{year}"
     data-paper-keywords="{keywords}"
     data-paper-category="{category}"
     data-paper-license="{license}"
     data-crawler="{crawler}"
     data-converted-date="{converted_date}">
</div>
```

Use `class="sr-only"` (screen-reader only, invisible to sighted
users) with `aria-hidden="true"` to hide from assistive tech too.
This makes the metadata purely for bots/crawlers.

### 4. OpenGraph Tags

```html
<meta property="og:type" content="article" />
<meta property="og:title" content="{title}" />
<meta property="og:description" content="{abstract_truncated}" />
<meta property="og:url" content="https://cryptography.academy/papers/{slug}" />
<meta property="article:published_time" content="{year}" />
<meta property="article:author" content="{authors}" />
<meta property="article:tag" content="{keyword}" />
```

## Implementation

1. **Modify `BaseLayout.astro`** to accept optional metadata props
   (paperMeta object) and render the `<meta>` tags, JSON-LD, and
   OpenGraph tags when present.

2. **Write a Python script** in `scripts/` that:
   - Reads metadata JSON for each paper
   - Adds the metadata props to each `.astro` file's frontmatter
   - Adds the hidden `<div>` to the article body
   - Is idempotent
   - Passes `ruff check` and `ruff format`

3. **Add `sr-only` utility** to `global.css` if not already present:
   ```css
   .sr-only {
     position: absolute;
     width: 1px;
     height: 1px;
     padding: 0;
     margin: -1px;
     overflow: hidden;
     clip: rect(0, 0, 0, 0);
     white-space: nowrap;
     border-width: 0;
   }
   ```

## Verification

- `npx astro build --root web/` succeeds
- View page source of 3 papers and confirm metadata is present
- Validate JSON-LD with https://validator.schema.org/
- Confirm metadata is invisible in the browser
