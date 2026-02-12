import Mathlib.Algebra.Field.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Basic

/-!
# Sponge Construction

Generic sponge construction for hash functions over finite fields.
This is reusable by any sponge-based hash function: Poseidon, Rescue,
Anemoi, Griffin, etc.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Sponge.SpongeConfig` :
    Configuration for a sponge (rate, capacity, permutation)
- `CryptoAcademy.Primitives.Hash.Sponge.SpongeState` :
    State of the sponge during hashing
- `CryptoAcademy.Primitives.Hash.Sponge.absorb` :
    Absorb a message block into the sponge state
- `CryptoAcademy.Primitives.Hash.Sponge.squeeze` :
    Extract output from the sponge state
- `CryptoAcademy.Primitives.Hash.Sponge.hash` :
    Full sponge hash function

## References

- Section 2.1 in [GKRRS19] https://eprint.iacr.org/2019/458
- Bertoni, Daemen, Peeters, Van Assche.
  "Sponge functions", ECRYPT Hash Workshop 2007.
-/

namespace CryptoAcademy.Primitives.Hash.Sponge

variable {F : Type*} [Field F]

/-- Configuration for a sponge construction.

  A sponge is parametrized by a rate `r`, a capacity `c`, and an
  internal permutation over `F^t` where `t = r + c`.

  From: Section 2.1 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_2 -/
structure SpongeConfig (F : Type*) [Field F] where
  /-- Rate: number of field elements absorbed per permutation -/
  r : ℕ
  /-- Capacity: determines security level -/
  c : ℕ
  /-- State width: `t = r + c` -/
  t : ℕ
  /-- Constraint: state width equals rate plus capacity -/
  ht : t = r + c
  /-- Rate is positive -/
  hr : r > 0
  /-- Capacity is positive -/
  hc : c > 0
  /-- The internal permutation over `F^t` -/
  perm : (Fin t → F) → (Fin t → F)

/-- State of the sponge during hashing.

  The state is a vector of `t` field elements, split conceptually
  into a rate part (first `r` elements) and a capacity part
  (remaining `c` elements). -/
structure SpongeState
    (F : Type*) [Field F] (cfg : SpongeConfig F) where
  /-- Current state vector -/
  state : Fin cfg.t → F

/-- Initial sponge state: all zeros.

  From: Section 2.1 in [GKRRS19]: "The initial state I contains
  all zeros, i.e., I = 0^r ‖ 0^c." -/
def SpongeState.init (cfg : SpongeConfig F) : SpongeState F cfg :=
  ⟨fun _ => 0⟩

/-- Absorb a single message block into the sponge state.

  XORs (adds in F) the message block into the rate portion of the
  state, then applies the permutation.

  From: Section 2.1 in [GKRRS19], Algorithm 1 (algo_1), Step 4.
  Dependencies: `SpongeConfig`, `SpongeState` -/
def absorb
    (cfg : SpongeConfig F) (st : SpongeState F cfg)
    (block : Fin cfg.r → F) : SpongeState F cfg :=
  sorry
  -- TODO: Add block to rate part of state, then apply cfg.perm.
  -- Requires casting between Fin cfg.r and Fin cfg.t using cfg.ht.

/-- Squeeze output elements from the sponge state.

  Reads `o` field elements from the rate portion. If `o > r`,
  applies the permutation again and reads more.

  From: Section 2.1 in [GKRRS19], Algorithm 1 (algo_1), Step 5.
  Dependencies: `SpongeConfig`, `SpongeState` -/
def squeeze
    (cfg : SpongeConfig F) (st : SpongeState F cfg)
    (o : ℕ) : List F :=
  sorry
  -- TODO: Extract o elements from rate part, iterating
  -- the permutation if o > cfg.r.

/-- Full sponge hash function.

  Given a message as a list of field elements and an output length,
  pads the message, absorbs all blocks, and squeezes the output.

  From: Section 2.1 in [GKRRS19], Algorithm 1 (algo_1).
  Dependencies: `SpongeConfig`, `absorb`, `squeeze`
  JSON ref: algo_1 -/
def hash
    (cfg : SpongeConfig F) (msg : List F)
    (o : ℕ := 1) : List F :=
  sorry
  -- TODO: Pad message, split into r-sized chunks, absorb
  -- each chunk, then squeeze o output elements.

end CryptoAcademy.Primitives.Hash.Sponge
