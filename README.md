# Cryptography Academy

An educational platform for learning cryptography with formal foundations in Lean 4.

## Vision

A living textbook where:
- Every definition is precise (Lean 4 code)
- Every theorem references its source paper
- Proofs can be incrementally formalized over time
- Interactive visualizations build geometric intuition
- The formalization status of each result is transparent

## Project Structure

```
.
├── lean/              # Lean 4 formalizations
│   └── CryptoAcademy/
│       ├── Meta/      # Infrastructure (papers, status tracking)
│       ├── Foundations/ # Mathematical prerequisites
│       ├── Primitives/  # Cryptographic building blocks
│       └── Proofs/      # Zero-knowledge and arguments
├── web/               # Astro website
└── Branding/          # Logos and assets
```

## Quick Start

```bash
# Install dependencies
make setup

# Build everything
make build

# Start development server
make serve
```

## Development

See the setup page on the website for detailed environment setup.

### Prerequisites

- [elan](https://github.com/leanprover/elan) - Lean version manager
- Node.js 20+
- npm or pnpm

### Commands

| Command | Description |
|---------|-------------|
| `make help` | Show all available commands |
| `make build` | Build Lean proofs and website |
| `make serve` | Start development server |
| `make test` | Run all tests |
| `make lint` | Run linters |
| `make format` | Format code |

## Contributing

Contributions welcome! Please see our contributing guidelines.

## Developed by

**BaDaaS** — A research laboratory in mathematics based in Belgium.

## Tech Stack

### Formal Proofs

- **Lean 4** (Latest) — Dependently-typed programming language for writing
  machine-checkable proofs. Chosen for modern syntax, fast compilation, and
  strong metaprogramming capabilities.
- **Mathlib4** (v4.26.0) — Comprehensive mathematical library providing
  foundational algebraic structures, number theory, and analysis needed for
  cryptographic definitions.

### Web Framework

- **Astro** (5.x) — Static site generator with islands architecture. Chosen
  for zero-JS-by-default approach, excellent performance, and first-class MDX
  support. Perfect for content-heavy educational sites.
- **React** (18.x) — UI library for interactive components (visualizations,
  code editors). Used only where interactivity is needed, keeping most pages
  as static HTML.
- **MDX** (3.x) — Markdown with JSX components. Enables rich educational
  content mixing prose, math notation, and interactive React components.

### Styling

- **Tailwind CSS** (4.x) — Utility-first CSS framework. Chosen for rapid
  prototyping, consistent design system, and excellent dark mode support
  without writing custom CSS.

### Icons

- **lucide-react** — Clean, consistent UI icons (navigation, buttons,
  indicators). MIT licensed with 1000+ icons.
- **@icons-pack/react-simple-icons** — Brand icons for social links (GitHub,
  X/Twitter). Official Simple Icons as React components.

### Development Infrastructure

- **Node.js** (24+) — JavaScript runtime for build tooling and development
  server.
- **elan** — Lean version manager ensuring consistent Lean toolchain across
  environments.
- **Lake** — Lean's official build system and package manager.
- **Make** — Standard build automation. Provides consistent interface
  (`make build`, `make serve`, `make test`) across Lean and web projects.

### CI/CD

- **GitHub Actions** — Continuous integration (linting, building, testing)
  and deployment to GitHub Pages.
- **Dependabot** — Automated dependency updates with weekly checks for npm
  packages and GitHub Actions.

### Future Integrations

- **lean4web** — Browser-based Lean editor for interactive proof exploration
  without local installation.
- **Postiz** — Social media automation for content distribution (planned).

## License

MIT
