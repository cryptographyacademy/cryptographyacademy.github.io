import CryptoAcademy.Primitives.Hash.Sponge
import CryptoAcademy.Primitives.Hash.Poseidon.HADES

/-!
# Poseidon Hash Function

Poseidon is a hash function designed for zero-knowledge proof systems.
It maps strings over `𝔽_p` to fixed-length strings over `𝔽_p` by
instantiating a sponge construction with the HADES-based Poseidon^π
permutation.

## Main definitions

- `CryptoAcademy.Primitives.Hash.Poseidon.PoseidonConfig` :
    Full configuration for a Poseidon instance
- `CryptoAcademy.Primitives.Hash.Poseidon.permutation` :
    The Poseidon^π permutation (R_f full + R_P partial + R_f full)
- `CryptoAcademy.Primitives.Hash.Poseidon.hash` :
    The Poseidon hash function (sponge + Poseidon^π)
- `CryptoAcademy.Primitives.Hash.Poseidon.DomainSeparation` :
    Domain separation constants for different use cases

## References

- Grassi, Khovratovich, Rechberger, Roy, Schofnegger.
  "POSEIDON: A New Hash Function for Zero-Knowledge Proof Systems
  (Updated Version)", eprint 2019/458, 2019.
  URL: https://eprint.iacr.org/2019/458
-/

namespace CryptoAcademy.Primitives.Hash.Poseidon

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Full configuration for a Poseidon instance.

  Bundles the HADES configuration with MDS matrix, round constants,
  sponge parameters, and all necessary validity conditions.

  From: Sections 2–4 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_1
  Dependencies: `HADES.HADESConfig`, `HADES.RoundConstants`,
  `MDS.isMDS`, `Sponge.SpongeConfig` -/
structure PoseidonConfig where
  /-- HADES round configuration -/
  hades : HADES.HADESConfig p
  /-- MDS matrix for the linear layer -/
  M : Matrix (Fin hades.t) (Fin hades.t) (ZMod p)
  /-- Round constants -/
  rc : HADES.RoundConstants p hades
  /-- The MDS matrix is valid -/
  hMDS : MDS.isMDS p hades.t M
  /-- Sponge rate -/
  r : ℕ
  /-- Sponge capacity -/
  c : ℕ
  /-- State width equals rate + capacity -/
  htrc : hades.t = r + c
  /-- Rate is positive -/
  hr : r > 0
  /-- Capacity is positive -/
  hc : c > 0
  /-- Output length in field elements (usually 1) -/
  o : ℕ := 1

/-- The Poseidon^π permutation.

  Applies `R_f` full rounds, then `R_P` partial rounds, then `R_f`
  full rounds, following the HADES design strategy.

  From: Section 2.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_4, algo_2
  Dependencies: `PoseidonConfig`, `HADES.fullRound`,
  `HADES.partialRound` -/
def permutation
    (cfg : PoseidonConfig p)
    (state : Fin cfg.hades.t → ZMod p) :
    Fin cfg.hades.t → ZMod p :=
  sorry
  -- TODO: Compose R_f full rounds, then R_P partial rounds,
  -- then R_f full rounds, each using the appropriate round
  -- constants. Implementation requires iterating over Fin
  -- ranges and careful index management.

/-- The Poseidon^π permutation is a bijection.

  This follows from the S-box being a permutation
  (`gcd(α, p−1) = 1`) and the MDS matrix being invertible.

  From: Section 2.3 in [GKRRS19] (eprint 2019/458).
  Dependencies: `permutation`, `SBox.sbox_bijective` -/
theorem permutation_bijective
    (cfg : PoseidonConfig p) :
    Function.Bijective (permutation p cfg) := by
  sorry

/-- The Poseidon hash function.

  Instantiates a sponge construction with the Poseidon^π
  permutation. Maps `𝔽_p^* → 𝔽_p^o` where `o` is the output
  length (usually 1).

  `Poseidon : 𝔽_p^* → 𝔽_p^o`

  From: Section 2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_1, algo_1
  Dependencies: `PoseidonConfig`, `permutation`,
  `Sponge.hash` -/
def hash
    (cfg : PoseidonConfig p)
    (msg : List (ZMod p)) : List (ZMod p) :=
  sorry
  -- TODO: Construct a SpongeConfig from PoseidonConfig
  -- (using `permutation` as the sponge permutation),
  -- then call Sponge.hash.

/-! ## Domain Separation -/

/-- Domain separation constants for different Poseidon use cases.

  The capacity element encodes the use case to prevent cross-domain
  attacks.

  From: Section 4.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_15
  Dependencies: `PoseidonConfig` -/
inductive DomainTag where
  /-- Merkle tree hashing (all leaves present) -/
  | merkleTree (arity : ℕ)
  /-- Variable-input-length hashing -/
  | variableLength (outputLen : ℕ)
  /-- Constant-input-length hashing -/
  | constantLength (inputLen outputLen : ℕ)
  /-- Encryption -/
  | encryption

/-- Compute the capacity value for a given domain tag.

  - Merkle tree: `2^arity − 1`
  - Variable-length: `2^64 + (o − 1)`
  - Constant-length: `length * 2^64 + (o − 1)`
  - Encryption: `2^32`

  From: Section 4.2 in [GKRRS19] (eprint 2019/458).
  JSON ref: def_15 -/
def domainTagValue : DomainTag → ℕ
  | .merkleTree arity => 2 ^ arity - 1
  | .variableLength o => 2 ^ 64 + (o - 1)
  | .constantLength len o => len * 2 ^ 64 + (o - 1)
  | .encryption => 2 ^ 32

end CryptoAcademy.Primitives.Hash.Poseidon
