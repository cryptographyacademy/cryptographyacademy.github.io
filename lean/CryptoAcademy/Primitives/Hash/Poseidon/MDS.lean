import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Poseidon MDS Matrix (Linear Layer)

The linear layer of Poseidon uses multiplication by a Maximum Distance
Separable (MDS) matrix. MDS matrices ensure full diffusion: every
output element depends on every input element.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Poseidon.MDS.isMDS` :
    Predicate for a matrix being MDS
- `CryptoAcademy.Primitives.Hash.Poseidon.MDS.cauchyMatrix` :
    Cauchy matrix construction
- `CryptoAcademy.Primitives.Hash.Poseidon.MDS.InactiveSBoxSubspace` :
    Subspace where no S-box is active in partial rounds
- `CryptoAcademy.Primitives.Hash.Poseidon.MDS.mixLayer` :
    The MixLayer operation (state × MDS matrix)

## References

- Section 2.3 in [GKRRS19] https://eprint.iacr.org/2019/458
- [GRS21] for matrix security verification algorithms
-/

namespace CryptoAcademy.Primitives.Hash.Poseidon.MDS

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (t : ℕ)

/-- A `t × t` matrix over `𝔽_p` is MDS if every square submatrix
  is nonsingular (has nonzero determinant).

  An MDS matrix exists when `2t + 1 ≤ p`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_6
  Dependencies: none -/
def isMDS (M : Matrix (Fin t) (Fin t) (ZMod p)) : Prop :=
  sorry
  -- TODO: Formalize as: for every subset S ⊆ Fin t and every
  -- subset T ⊆ Fin t with |S| = |T|, the submatrix M[S,T] has
  -- nonzero determinant. Requires Mathlib's minor/submatrix API.

/-- Cauchy matrix construction.

  Given pairwise distinct sequences `{xᵢ}` and `{yⱼ}` with
  `xᵢ + yⱼ ≠ 0`, the Cauchy matrix is defined as:
  `M_{i,j} = 1 / (xᵢ + yⱼ)`

  Cauchy matrices are always MDS.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_6
  Dependencies: none -/
def cauchyMatrix
    (x y : Fin t → ZMod p)
    (hxy : ∀ (i : Fin t) (j : Fin t), x i + y j ≠ 0) :
    Matrix (Fin t) (Fin t) (ZMod p) :=
  Matrix.of (fun i j => (x i + y j)⁻¹)

/-- Cauchy matrices are MDS.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_6
  Dependencies: `cauchyMatrix`, `isMDS` -/
theorem cauchyMatrix_isMDS
    (x y : Fin t → ZMod p)
    (hxy : ∀ (i : Fin t) (j : Fin t), x i + y j ≠ 0)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    isMDS p t (cauchyMatrix p t x y hxy) := by
  sorry

/-- Existence of MDS matrices when `2t + 1 ≤ p`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_6 -/
theorem mds_exists (h : 2 * t + 1 ≤ p) :
    ∃ (M : Matrix (Fin t) (Fin t) (ZMod p)), isMDS p t M := by
  sorry

/-- The MixLayer operation: multiply state by the MDS matrix.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: notation_18
  Dependencies: none -/
def mixLayer
    (M : Matrix (Fin t) (Fin t) (ZMod p))
    (state : Fin t → ZMod p) : Fin t → ZMod p :=
  M.mulVec state

/-! ## Inactive S-box subspace -/

/-- The subspace `S^(i)` of vectors for which no S-box is active
  in the first `i` consecutive partial rounds.

  `S^(i) := { v ∈ 𝔽^t | [M^j · v]₀ = 0 for all j < i }`

  where `[x]₀` denotes the first component of `x`.

  Properties: `S^(0) = 𝔽^t` and `dim(S^(i)) ≥ t − i`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_7, notation_14
  Dependencies: `MDS matrix` -/
def InactiveSBoxSubspace
    (M : Matrix (Fin t) (Fin t) (ZMod p))
    (i : ℕ) : Set (Fin t → ZMod p) :=
  { v | ∀ (j : ℕ), j < i →
    (M ^ j).mulVec v ⟨0, sorry⟩ = 0 }
  -- TODO: Requires t > 0 proof for ⟨0, _⟩.

/-- The dimension of `S^(i)` is at least `t − i`.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_7 -/
theorem inactiveSBoxSubspace_dim
    (M : Matrix (Fin t) (Fin t) (ZMod p))
    (i : ℕ) (hi : i ≤ t) :
    True := by  -- TODO: dim(S^(i)) ≥ t − i
  sorry
  -- TODO: Requires Mathlib's Submodule.finrank API and
  -- showing that InactiveSBoxSubspace is a submodule with
  -- the claimed dimension bound.

/-- No invariant or iterative subspace trail with inactive S-boxes
  can cover more than `t − 1` partial rounds.

  From: Section 5.5.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_7
  Dependencies: `InactiveSBoxSubspace` -/
theorem maxInactiveRounds
    (M : Matrix (Fin t) (Fin t) (ZMod p))
    (hMDS : isMDS p t M) (ht : t > 0) :
    InactiveSBoxSubspace p t M t = {0} := by
  sorry

end CryptoAcademy.Primitives.Hash.Poseidon.MDS
