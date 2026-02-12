/-!
# HADES Design Strategy

The HADES design strategy alternates between full S-box rounds (where
all state elements go through the S-box) and partial S-box rounds
(where only one element does). This provides security equivalent to
full rounds at a fraction of the cost in arithmetic circuits.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.HADESConfig` :
    Configuration: `R_f` full rounds + `R_P` partial rounds
- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.addRoundConstants` :
    AddRoundConstants (ARC) operation
- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.fullSBoxLayer` :
    Full S-box layer (all `t` elements)
- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.partialSBoxLayer` :
    Partial S-box layer (only first element)
- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.fullRound` :
    One full round: ARC → S-box → MixLayer
- `CryptoAcademy.Primitives.Hash.Poseidon.HADES.partialRound` :
    One partial round: ARC → partial S-box → MixLayer

## References

- Section 2.2 in [GKRRS19] https://eprint.iacr.org/2019/458
- [GLRS19] "HADES: Design Strategy for Crypto Primitives"
  https://eprint.iacr.org/2019/1107
-/

import CryptoAcademy.Primitives.Hash.Poseidon.SBox
import CryptoAcademy.Primitives.Hash.Poseidon.MDS

namespace CryptoAcademy.Primitives.Hash.Poseidon.HADES

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Configuration for the HADES design strategy.

  The permutation has three phases:
  1. `R_f` full rounds at the beginning
  2. `R_P` partial rounds in the middle
  3. `R_f` full rounds at the end

  Total full rounds: `R_F = 2 * R_f`.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_3 -/
structure HADESConfig where
  /-- State width (number of field elements) -/
  t : ℕ
  /-- S-box exponent -/
  α : ℕ
  /-- Number of full rounds per side (beginning and end) -/
  R_f : ℕ
  /-- Number of partial rounds (middle) -/
  R_P : ℕ
  /-- Total number of full rounds -/
  R_F : ℕ := 2 * R_f
  /-- Total number of rounds -/
  R : ℕ := 2 * R_f + R_P
  /-- S-box exponent is valid -/
  hα : SBox.validExponent p α
  /-- State width is positive -/
  ht : t > 0

/-- Round constants for all rounds.

  From: Section 2.2, 4.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: notation_16, const_1 -/
structure RoundConstants (cfg : HADESConfig p) where
  /-- Constants for each round and each state position -/
  constants : Fin cfg.R → Fin cfg.t → ZMod p

/-- AddRoundConstants (ARC): add round-specific constants to each
  state element.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: notation_16, def_4
  Dependencies: `HADESConfig` -/
def addRoundConstants
    (cfg : HADESConfig p) (rc : RoundConstants p cfg)
    (round : Fin cfg.R) (state : Fin cfg.t → ZMod p) :
    Fin cfg.t → ZMod p :=
  fun i => state i + rc.constants round i

/-- Full S-box layer: apply `x ↦ x^α` to every state element.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_4, notation_17
  Dependencies: `SBox.sbox` -/
def fullSBoxLayer
    (cfg : HADESConfig p)
    (state : Fin cfg.t → ZMod p) :
    Fin cfg.t → ZMod p :=
  fun i => SBox.sbox p cfg.α (state i)

/-- Partial S-box layer: apply `x ↦ x^α` only to the first state
  element; the rest are identity.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_4, notation_17
  Dependencies: `SBox.sbox` -/
def partialSBoxLayer
    (cfg : HADESConfig p)
    (state : Fin cfg.t → ZMod p) :
    Fin cfg.t → ZMod p :=
  fun i =>
    if i = ⟨0, cfg.ht⟩
    then SBox.sbox p cfg.α (state i)
    else state i

/-- One full round: ARC → full S-box → MixLayer.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_4
  Dependencies: `addRoundConstants`, `fullSBoxLayer`,
  `MDS.mixLayer` -/
def fullRound
    (cfg : HADESConfig p) (rc : RoundConstants p cfg)
    (M : Matrix (Fin cfg.t) (Fin cfg.t) (ZMod p))
    (round : Fin cfg.R) (state : Fin cfg.t → ZMod p) :
    Fin cfg.t → ZMod p :=
  MDS.mixLayer p cfg.t M
    (fullSBoxLayer p cfg
      (addRoundConstants p cfg rc round state))

/-- One partial round: ARC → partial S-box → MixLayer.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_4
  Dependencies: `addRoundConstants`, `partialSBoxLayer`,
  `MDS.mixLayer` -/
def partialRound
    (cfg : HADESConfig p) (rc : RoundConstants p cfg)
    (M : Matrix (Fin cfg.t) (Fin cfg.t) (ZMod p))
    (round : Fin cfg.R) (state : Fin cfg.t → ZMod p) :
    Fin cfg.t → ZMod p :=
  MDS.mixLayer p cfg.t M
    (partialSBoxLayer p cfg
      (addRoundConstants p cfg rc round state))

end CryptoAcademy.Primitives.Hash.Poseidon.HADES
