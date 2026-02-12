# Vision

cryptography.academy is an open knowledge base for cryptographic
research literature.

We automatically process papers from the cryptographic research
corpus, extract every definition, theorem, lemma, and formula, and
cross-reference them across the entire body of literature. When
Paper A cites a definition from Paper B, we link them. When two
papers define the same concept differently, we surface it. When a
proof relies on a property established elsewhere, we trace it back
to its source.

Think of it as a compiler for cryptographic literature: just as a
compiler checks that every reference in your code resolves
correctly, cryptography.academy verifies that every reference in
the research resolves, is consistent, and is traceable to its
origin.

The long-term goal is formal verification. Definitions and theorems
extracted from papers are progressively formalized in Lean 4,
building a machine-checked foundation for cryptographic knowledge
-- starting with zero-knowledge-proof-optimized primitives like
Poseidon and the algebraic structures they depend on.

No other tool operates at this level of granularity. Citation
graphs link papers to papers. We link definitions to definitions,
formulas to formulas, and proofs to the precise results they depend
on -- across the entire cryptographic literature.

## Principles

- **Free forever.** No paywalls, no subscriptions, no payments. We
  will never charge for access to knowledge.
- **Open source.** The entire source code is publicly available on
  GitHub.
- **No profit motive.** This project exists to make knowledge
  accessible, not to generate revenue. Knowledge will never be
  sold.
- **Good faith.** We act in good faith, respect intellectual
  property, and welcome feedback from authors and the community.
- **Verifiable.** All formalizations are machine-checked in Lean 4.
  Trust is built through proof, not authority.
