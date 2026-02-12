import Mathlib.Data.ZMod.Basic

/-!
# Grain LFSR Parameter Generation

Deterministic generation of Poseidon round constants and MDS matrices
using the Grain LFSR in self-shrinking mode. This provides the
NUMS (Nothing-Up-My-Sleeve) property.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Poseidon.Grain.GrainConfig` :
    Seed parameters for the Grain LFSR
- `CryptoAcademy.Primitives.Hash.Poseidon.Grain.grainInit` :
    Initialize the 80-bit LFSR state
- `CryptoAcademy.Primitives.Hash.Poseidon.Grain.grainNext` :
    Update the LFSR state
- `CryptoAcademy.Primitives.Hash.Poseidon.Grain.generateConstants` :
    Generate round constants from the LFSR

## References

- Section E (Appendix) in [GKRRS19]
  https://eprint.iacr.org/2019/458
-/

namespace CryptoAcademy.Primitives.Hash.Poseidon.Grain

/-- Configuration (seed) for the Grain LFSR.

  The 80-bit initial state encodes the Poseidon instance parameters:
  - bits 0–1: field type
  - bits 2–5: S-box type
  - bits 6–17: field size parameter `n`
  - bits 18–29: state width `t`
  - bits 30–39: full rounds `R_F`
  - bits 40–49: partial rounds `R_P`
  - bits 50–79: set to 1

  From: Appendix E in [GKRRS19] (eprint 2019/458).
  JSON ref: algo_3 -/
structure GrainConfig where
  /-- Field type (2 bits) -/
  fieldType : Fin 4
  /-- S-box type (4 bits) -/
  sboxType : Fin 16
  /-- Field size parameter `n ≈ log₂(p)` -/
  n : ℕ
  /-- State width -/
  t : ℕ
  /-- Number of full rounds -/
  R_F : ℕ
  /-- Number of partial rounds -/
  R_P : ℕ

/-- 80-bit LFSR state. -/
def LFSRState := Fin 80 → Bool

/-- Initialize the Grain LFSR from a configuration.

  From: Appendix E, Step 1 in [GKRRS19] (eprint 2019/458).
  JSON ref: algo_3 -/
def grainInit (_cfg : GrainConfig) : LFSRState :=
  sorry
  -- TODO: Encode cfg into 80-bit state as specified.

/-- Update rule for the Grain LFSR.

  `b_{i+80} = b_{i+62} ⊕ b_{i+51} ⊕ b_{i+38} ⊕ b_{i+23}
              ⊕ b_{i+13} ⊕ b_i`

  From: Appendix E, Step 2 in [GKRRS19] (eprint 2019/458).
  JSON ref: algo_3 -/
def grainNext (_state : LFSRState) : LFSRState :=
  sorry
  -- TODO: Implement the LFSR feedback polynomial.

/-- Generate round constants from the Grain LFSR.

  After discarding the first 160 bits, uses self-shrinking mode:
  evaluate bits in pairs — if the first bit is 1, output the
  second; otherwise discard both. Reject samples ≥ p.

  From: Appendix E, Steps 3–5 in [GKRRS19] (eprint 2019/458).
  JSON ref: algo_3, const_1 -/
def generateConstants
    (p : ℕ) [Fact (Nat.Prime p)]
    (cfg : GrainConfig) (numConstants : ℕ) :
    List (ZMod p) :=
  sorry
  -- TODO: Implement self-shrinking generation with rejection
  -- sampling for values ≥ p.

end CryptoAcademy.Primitives.Hash.Poseidon.Grain
