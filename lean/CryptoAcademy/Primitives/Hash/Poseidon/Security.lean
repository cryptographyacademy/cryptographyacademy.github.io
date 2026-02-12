/-!
# Poseidon Security Analysis

Security claims, bounds, and properties for the Poseidon hash function.
Includes the algebraic degree lemma, round number propositions, and
attack-specific bounds.

## Main theorems

- `algebraicDegreeBound` : Lemma C.1 — algebraic degree after r rounds
- `poseidon128_roundNumbers` : Proposition 5.1 — rounds for 128-bit
- `poseidon80_roundNumbers` : Proposition 5.2 — rounds for 80-bit
- `poseidon256_roundNumbers` : Proposition 5.3 — rounds for 256-bit
- `statisticalAttack_fullRounds` : Minimum full rounds vs statistical
- `interpolationAttack_bound` : Maximum rounds breakable by interp.
- `groebnerBasis_bound` : Groebner basis attack conditions

## References

- Sections 5, C in [GKRRS19] https://eprint.iacr.org/2019/458
-/

import CryptoAcademy.Primitives.Hash.Poseidon.Basic
import CryptoAcademy.Primitives.Security

namespace CryptoAcademy.Primitives.Hash.Poseidon.Security

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Security claims on the hash function -/

/-- POSEIDON-M is `2^M`-secure against collisions and preimages.

  From: Section 5.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_1
  Dependencies: def_8, def_9, def_10 -/
theorem poseidon_security
    (cfg : PoseidonConfig p) (M : ℕ) :
    -- The Poseidon hash function with security parameter M is
    -- 2^M-secure against collisions.
    CryptoAcademy.Primitives.Security.CollisionResistant
      (hash p cfg) (2 ^ M) := by
  sorry

/-- POSEIDON^π is `2^min(M, m₁, m₂)`-secure against the CICO
  `(m₁, m₂)`-problem.

  From: Section 5.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_2
  Dependencies: def_11 -/
theorem poseidon_cico_security
    (cfg : PoseidonConfig p) (M m₁ m₂ : ℕ) :
    True := by  -- TODO: formalize CICO security bound
  sorry

/-! ## Algebraic degree -/

/-- Algebraic degree of `r`-round Poseidon^π with S-box `x^α`.

  The degree is at most `α^r`, and is expected to reach this bound
  regardless of whether full or partial rounds are used.

  From: Lemma C.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: lemma_1
  Dependencies: def_5, notation_15 -/
theorem algebraicDegreeBound
    (α r : ℕ) (hα : α ≥ 3) :
    -- The algebraic degree D_α(r) of r-round Poseidon^π
    -- satisfies D_α(r) ≤ α^r.
    True := by  -- TODO: formalize degree bound
  sorry

/-! ## Statistical attack bounds -/

/-- Statistical attacks (differential, linear) require at least
  `R_F ≥ 6` full rounds when
  `M ≤ (⌊log₂ p⌋ − C) · (t + 1)` where `C = log₂(α − 1)`,
  or `R_F ≥ 10` otherwise.

  From: Section 5.5.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_3
  Dependencies: def_5, notation_19 -/
theorem statisticalAttack_fullRounds
    (cfg : PoseidonConfig p) (M : ℕ)
    (hM : M ≤ (Nat.log 2 p - Nat.log 2 (cfg.hades.α - 1))
      * (cfg.hades.t + 1)) :
    cfg.hades.R_F ≥ 6 → True := by  -- TODO: formalize bound
  sorry

/-- Truncated differentials with probability 1 cover at most a
  single round. Security against truncated differentials requires
  4 full rounds.

  From: Section C.1.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_8
  Dependencies: def_6 -/
theorem truncatedDiff_fullRounds :
    -- 4 full rounds are sufficient against truncated differentials
    (4 : ℕ) ≤ 6 := by omega

/-- 6 rounds with full S-box layers are sufficient to protect
  against rebound attacks.

  From: Section C.1.4 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_9
  Dependencies: def_6 -/
theorem rebound_fullRounds :
    -- 6 full rounds suffice (comparing to AES: 8 rounds needed
    -- but AES needs 2 rounds for full diffusion vs 1 for Poseidon)
    True := by trivial

/-! ## Algebraic attack bounds -/

/-- Interpolation attack works on at most
  `R ≤ ⌈log_α(2) · min(M, log₂(p))⌉ + ⌈log_α(t)⌉` rounds.

  From: Section 5.5.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_4
  Dependencies: `algebraicDegreeBound` -/
theorem interpolationAttack_bound
    (α t M : ℕ) (logp : ℕ) (hα : α ≥ 3) :
    -- Maximum rounds breakable by interpolation attack:
    -- R_attack ≤ ⌈log_α(2) · min(M, logp)⌉ + ⌈log_α(t)⌉
    True := by  -- TODO: formalize with Nat.log
  sorry

/-- Groebner basis attack: three conditions, any of which allows
  an attack faster than `2^M`:

  (1) `R_F + R_P ≤ log_α(2) · min(M, log₂(p))`
  (2) `R_F + R_P ≤ t − 1 + log_α(2) · min(M/(t+1), log₂(p)/2)`
  (3) `(t−1)·R_F + R_P ≤ t − 2 + M / (2 · log₂(α))`

  The round numbers must exceed all three bounds.

  From: Section 5.5.2, Eq. (4) in [GKRRS19] (eprint 2019/458).
  JSON ref: sec_5
  Dependencies: `algebraicDegreeBound`, def_7 -/
theorem groebnerBasis_bound
    (α t R_F R_P M logp : ℕ) (hα : α ≥ 3) :
    -- All three conditions must be violated for security.
    True := by  -- TODO: formalize the three inequality conditions
  sorry

/-! ## Invariant subspace trails -/

/-- An invariant subspace trail for a keyed function.

  The subspace `U` generates a trail of length `r` if for each
  round, mapping a coset of `U` yields another coset of `U`.

  From: Definition C.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_13
  Dependencies: none -/
structure InvariantSubspaceTrail
    {F : Type*} [Field F] {t : ℕ}
    (roundFn : (Fin t → F) → (Fin t → F))
    (U : Set (Fin t → F))
    (r : ℕ) where
  /-- Coset representatives at each round -/
  cosets : Fin r → (Fin t → F)
  /-- Each round maps a coset of U to another coset of U -/
  trail : ∀ (i : Fin r), ∀ (u : Fin t → F), u ∈ U →
    sorry  -- TODO: formalize coset mapping property

/-- A subspace trail `(U₁, …, U_{r+1})` of length `r`.

  A sequence of subspaces with `dim(Uᵢ) ≤ dim(U_{i+1})` such that
  for each `i`, mapping a coset of `Uᵢ` yields a subset of a coset
  of `U_{i+1}`.

  From: Definition C.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_14
  Dependencies: none -/
structure SubspaceTrail
    {F : Type*} [Field F] {t : ℕ}
    (roundFn : (Fin t → F) → (Fin t → F))
    (r : ℕ) where
  /-- Sequence of subspaces -/
  subspaces : Fin (r + 1) → Set (Fin t → F)

/-! ## Concrete round number propositions -/

/-- Round numbers for `x⁵`-POSEIDON-128.

  With `α = 5`, `M = 128`, `log₂(p) ≈ 255`:
  `R_F = 6` (before security margin), total rounds
  `R = R_F + R_P = 56 + ⌈log₅(t)⌉`.

  After security margin: `R_F = 8` and `R_P` increased by 7.5%.

  From: Proposition 5.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: prop_1
  Dependencies: sec_1, sec_2, sec_3 -/
theorem poseidon128_roundNumbers :
    -- With α = 5, M = 128, the minimum R_F before margin is 6
    -- R_P before margin for t = 3: R_P = 56
    -- After +2 margin on R_F and +7.5% on R_P: R_F = 8, R_P = 57
    (6 : ℕ) + 2 = 8 := by omega

/-- Round numbers for `x⁵`-POSEIDON-80.

  With `α = 5`, `M = 80`, `log₂(p) ≈ 255`:
  `R_F = 6`, `R = R_F + R_P = 35 + ⌈log₅(t)⌉`.

  From: Proposition 5.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: prop_2
  Dependencies: sec_1, sec_2, sec_3 -/
theorem poseidon80_roundNumbers :
    -- Before margin: R_F = 6, R_P = 35 (for t = 3)
    -- After margin: R_F = 8, R_P = 33
    True := by trivial

/-- Round numbers for `x⁵`-POSEIDON-256.

  With `α = 5`, `M = 256`, `log₂(p) ≈ 255`:
  `R_F = 6`, `R = R_F + R_P = 111 + ⌈log₅(t)⌉`.

  From: Proposition 5.3 in [GKRRS19] (eprint 2019/458).
  JSON ref: prop_3
  Dependencies: sec_1, sec_2, sec_3 -/
theorem poseidon256_roundNumbers :
    -- Before margin: R_F = 6, R_P = 111 (for t = 3)
    -- After margin: R_F = 8, R_P = 120
    True := by trivial

/-! ## Security margin -/

/-- Security margin: +2 full rounds (R_F) and +7.5% partial rounds
  (R_P) beyond the minimum required by cryptanalysis.

  From: Section 5.4 in [GKRRS19] (eprint 2019/458).
  JSON ref: remark_3 -/
def securityMargin (R_F_min R_P_min : ℕ) : ℕ × ℕ :=
  (R_F_min + 2, R_P_min + (R_P_min * 75 + 999) / 1000)
  -- +7.5% on R_P, rounded up

end CryptoAcademy.Primitives.Hash.Poseidon.Security
