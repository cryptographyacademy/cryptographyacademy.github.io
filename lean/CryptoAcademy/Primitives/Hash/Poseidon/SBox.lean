import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Poseidon S-Box (Power Map)

The S-box for the Poseidon hash function is defined as the power map
`x ↦ x^α` over `𝔽_p`, where `α` is the smallest positive integer
`≥ 3` such that `gcd(α, p − 1) = 1`.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Poseidon.SBox.sbox` :
    The S-box function `x ↦ x^α`
- `CryptoAcademy.Primitives.Hash.Poseidon.SBox.validExponent` :
    Predicate for a valid S-box exponent
- `CryptoAcademy.Primitives.Hash.Poseidon.SBox.sbox_bijective` :
    The S-box is a permutation when `gcd(α, p−1) = 1`

## Main theorems

- `CryptoAcademy.Primitives.Hash.Poseidon.SBox.dpMax_cube` :
    Differential probability of `x³` is bounded by `2/p`
- `CryptoAcademy.Primitives.Hash.Poseidon.SBox.dpMax_fifth` :
    Differential probability of `x⁵` is bounded by `4/p`

## References

- Section 2.3 in [GKRRS19] https://eprint.iacr.org/2019/458
- Section C.1.1 in [GKRRS19] for differential bounds
-/

namespace CryptoAcademy.Primitives.Hash.Poseidon.SBox

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- A valid S-box exponent: `α ≥ 3` and `gcd(α, p − 1) = 1`.

  The coprimality condition ensures the power map is a permutation
  (i.e., invertible) over `𝔽_p`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: notation_11, def_5 -/
def validExponent (α : ℕ) : Prop :=
  α ≥ 3 ∧ Nat.Coprime α (p - 1)

/-- The S-box function: `x ↦ x^α` over `𝔽_p`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_5
  Dependencies: `validExponent` -/
def sbox (α : ℕ) (x : ZMod p) : ZMod p :=
  x ^ α

/-- The S-box is a bijection (permutation) when `gcd(α, p − 1) = 1`.

  This is because `x ↦ x^α` is invertible in `𝔽_p^*` when `α` is
  coprime to the group order `p − 1`. The inverse is `x ↦ x^β`
  where `β ≡ α⁻¹ (mod p − 1)`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_5
  Dependencies: `sbox`, `validExponent` -/
theorem sbox_bijective
    (α : ℕ) (hα : Nat.Coprime α (p - 1)) :
    Function.Bijective (sbox p α) := by
  sorry

/-- Common choice: `α = 5` is valid for BLS12-381, BN254, Ed25519
  scalar fields where `p ≡ 1 (mod 3)` but `p ≢ 1 (mod 5)`.

  From: Section 2.3 in [GKRRS19].
  JSON ref: def_5 -/
theorem alpha5_valid
    (hp5 : Nat.Coprime 5 (p - 1)) :
    validExponent p 5 := by
  exact ⟨by omega, hp5⟩

/-! ## Differential probability bounds -/

/-- The maximum differential probability of the cube S-box `x³`
  (which is Almost Perfect Nonlinear) is bounded by `2/p`.

  From: Section C.1.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_6
  Dependencies: `sbox` -/
theorem dpMax_cube
    (hp3 : (3 : ℕ) ≠ 0) :
    -- For all nonzero input difference a and output difference b,
    -- |{x ∈ 𝔽_p : (x+a)³ − x³ = b}| ≤ 2
    ∀ (a : ZMod p), a ≠ 0 →
    ∀ (b : ZMod p),
    True := by  -- TODO: formalize cardinality bound
  sorry

/-- The maximum differential probability of the `x⁵` S-box is
  bounded by `4/p`.

  From: Section C.1.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_6
  Dependencies: `sbox` -/
theorem dpMax_fifth :
    -- For all nonzero input difference a and output difference b,
    -- |{x ∈ 𝔽_p : (x+a)⁵ − x⁵ = b}| ≤ 4
    ∀ (a : ZMod p), a ≠ 0 →
    ∀ (b : ZMod p),
    True := by  -- TODO: formalize cardinality bound
  sorry

end CryptoAcademy.Primitives.Hash.Poseidon.SBox
