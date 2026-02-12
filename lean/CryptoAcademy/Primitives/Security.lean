import Mathlib.Data.ZMod.Basic

/-!
# Cryptographic Security Definitions

General security definitions for hash functions and permutations.
These are reusable across all hash function papers (Poseidon, Rescue,
Anemoi, Griffin, etc.).

## Main definitions

- `CryptoAcademy.Primitives.Security.CollisionResistant` :
    T-security against collisions
- `CryptoAcademy.Primitives.Security.PreimageResistant` :
    T-security against preimages
- `CryptoAcademy.Primitives.Security.SecondPreimageResistant` :
    T-security against second preimages
- `CryptoAcademy.Primitives.Security.CICOSecure` :
    T-security against the CICO problem
- `CryptoAcademy.Primitives.Security.ZeroSumPartition` :
    Zero-sum partition for a permutation

## References

- Definitions 5.1–5.5 in [GKRRS19]
  https://eprint.iacr.org/2019/458
-/

namespace CryptoAcademy.Primitives.Security

/-! ## Hash function security -/

/-- T-security against collisions.

  A function `F` is `T`-secure against collisions if there is no
  algorithm with expected complexity smaller than `T` that finds
  `x₁ ≠ x₂` such that `F x₁ = F x₂`.

  From: Definition 5.1 in [GKRRS19] (eprint 2019/458), Section 5.1.
  Dependencies: none -/
def CollisionResistant
    {α β : Type*} (F : α → β) (T : ℕ) : Prop :=
  ∀ (x₁ x₂ : α), F x₁ = F x₂ → x₁ = x₂ ∨ T = 0
  -- NOTE: This is a simplified formalization. A full treatment
  -- requires a computational model with oracle access and
  -- complexity bounds. The statement above captures the
  -- information-theoretic core: no collision exists, or the
  -- bound is trivial.

/-- T-security against preimages.

  A function `F` is `T`-secure against preimages if there is no
  algorithm with expected complexity smaller than `T` that, given
  `y`, finds `x` such that `F x = y`.

  From: Definition 5.2 in [GKRRS19] (eprint 2019/458), Section 5.1.
  Dependencies: none -/
def PreimageResistant
    {α β : Type*} (F : α → β) (T : ℕ) : Prop :=
  ∀ (y : β), (∃ (x : α), F x = y) →
    T > 0
  -- NOTE: Simplified. Full definition needs computational model.

/-- T-security against second preimages.

  A function `F` is `T`-secure against second preimages if there
  is no algorithm with expected complexity smaller than `T` that,
  given `x₁`, finds `x₂` such that `F x₁ = F x₂`.

  From: Definition 5.3 in [GKRRS19] (eprint 2019/458), Section 5.1.
  Dependencies: none -/
def SecondPreimageResistant
    {α β : Type*} (F : α → β) (T : ℕ) : Prop :=
  ∀ (x₁ x₂ : α), x₁ ≠ x₂ → F x₁ = F x₂ → T = 0
  -- NOTE: Simplified. Full definition needs computational model.

/-! ## Permutation security -/

/-- T-security against the CICO (Constrained-Input Constrained-Output)
  `(m₁, m₂)`-problem.

  An invertible function `P` is `T`-secure against the CICO
  `(m₁, m₂)`-problem if there is no algorithm with expected
  complexity smaller than `T` that, given `m₁`-bit `I₁` and
  `m₂`-bit `O₁`, finds `I₂, O₂` such that `P(I₁ ‖ I₂) = O₁ ‖ O₂`.

  We model this over `Fin t → F` where the first `r` positions
  are the rate (constrained) and the remaining `c` positions are
  the capacity (free).

  From: Definition 5.4 in [GKRRS19] (eprint 2019/458), Section 5.1.
  Dependencies: none -/
structure CICOProblem
    (F : Type*) (t r c : ℕ) (htrc : t = r + c)
    (P : (Fin t → F) → (Fin t → F)) where
  /-- Known input portion (rate part of input) -/
  inputRate : Fin r → F
  /-- Known output portion (rate part of output) -/
  outputRate : Fin r → F
  /-- Solution: capacity part of input -/
  inputCapacity : Fin c → F
  /-- Solution: capacity part of output -/
  outputCapacity : Fin c → F

/-- A permutation is CICO-secure if no solution to the CICO problem
  can be found faster than `T`. -/
def CICOSecure
    (F : Type*) (t r c : ℕ) (htrc : t = r + c)
    (P : (Fin t → F) → (Fin t → F)) (T : ℕ) : Prop :=
  ∀ (_prob : CICOProblem F t r c htrc P), T > 0
  -- NOTE: Simplified. Full definition needs computational model
  -- and a check that P applied to the combined input equals the
  -- combined output.

/-! ## Distinguishers -/

/-- A zero-sum partition for a permutation `P` over `Fⁿ`.

  A collection of `K` disjoint sets `{X₁, …, X_K}` such that
  for all `i`: `∑_{x ∈ Xᵢ} x = ∑_{x ∈ Xᵢ} P(x) = 0`.

  From: Definition 5.5 in [GKRRS19] (eprint 2019/458),
  Section 5.5.2.
  Dependencies: none -/
structure ZeroSumPartition
    {F : Type*} [AddCommMonoid F]
    {t : ℕ}
    (P : (Fin t → F) → (Fin t → F))
    (K : ℕ) where
  /-- The partition as a function from partition index to set -/
  sets : Fin K → Finset (Fin t → F)
  /-- Sets are pairwise disjoint -/
  disjoint : ∀ (i j : Fin K), i ≠ j →
    Disjoint (sets i) (sets j)
  /-- Zero-sum on inputs: ∑_{x ∈ Xᵢ} x = 0 componentwise -/
  zeroSumInput : ∀ (i : Fin K) (k : Fin t),
    (sets i).sum (fun x => x k) = 0
  /-- Zero-sum on outputs: ∑_{x ∈ Xᵢ} P(x) = 0 componentwise -/
  zeroSumOutput : ∀ (i : Fin K) (k : Fin t),
    (sets i).sum (fun x => P x k) = 0

end CryptoAcademy.Primitives.Security
