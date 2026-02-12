/-
  CryptoAcademy — Formal Cryptography Education

  A living textbook where:
  - Every definition is precise (Lean 4 code)
  - Every theorem references its source paper
  - Proofs can be incrementally formalized over time
  - The formalization status of each result is transparent
-/

-- Infrastructure
import CryptoAcademy.Meta.Paper
import CryptoAcademy.Meta.Notation

-- Tutorials (code examples from the Learn section)
import CryptoAcademy.Tutorials

-- Primitives
import CryptoAcademy.Primitives.Security
import CryptoAcademy.Primitives.Hash.Sponge
import CryptoAcademy.Primitives.Hash.Poseidon.SBox
import CryptoAcademy.Primitives.Hash.Poseidon.MDS
import CryptoAcademy.Primitives.Hash.Poseidon.HADES
import CryptoAcademy.Primitives.Hash.Poseidon.Basic
import CryptoAcademy.Primitives.Hash.Poseidon.Security
import CryptoAcademy.Primitives.Hash.Poseidon.Instances
import CryptoAcademy.Primitives.Hash.Poseidon.Grain

-- Paper analyses
import CryptoAcademy.Papers.Poseidon2019
