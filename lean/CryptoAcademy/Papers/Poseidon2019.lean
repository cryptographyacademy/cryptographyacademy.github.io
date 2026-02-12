-- Re-export all Poseidon modules
import CryptoAcademy.Primitives.Security
import CryptoAcademy.Primitives.Hash.Sponge
import CryptoAcademy.Primitives.Hash.Poseidon.SBox
import CryptoAcademy.Primitives.Hash.Poseidon.MDS
import CryptoAcademy.Primitives.Hash.Poseidon.HADES
import CryptoAcademy.Primitives.Hash.Poseidon.Basic
import CryptoAcademy.Primitives.Hash.Poseidon.Security
import CryptoAcademy.Primitives.Hash.Poseidon.Instances
import CryptoAcademy.Primitives.Hash.Poseidon.Grain
import CryptoAcademy.Meta.Paper

/-!
# Paper: POSEIDON (eprint 2019/458)

Formalization of definitions and theorems from:
  Grassi, Khovratovich, Rechberger, Roy, Schofnegger.
  "POSEIDON: A New Hash Function for Zero-Knowledge Proof Systems
  (Updated Version)", eprint 2019/458, 2019.
  URL: https://eprint.iacr.org/2019/458

This file re-exports all Poseidon-related definitions and theorems,
providing a single import point for the web page and for other papers
that reference [GKRRS19].

## How to use in another paper

```
import CryptoAcademy.Papers.Poseidon2019
-- Now you can reference:
--   Poseidon.SBox.sbox           (def_5)
--   Poseidon.HADES.HADESConfig   (def_3)
--   Poseidon.Security.poseidon128_roundNumbers  (prop_1)
--   etc.
```

## JSON → Lean mapping

| JSON ID   | Lean name                                   | Type       |
|-----------|---------------------------------------------|------------|
| def_1     | `Poseidon.PoseidonConfig`                   | structure  |
| def_2     | `Sponge.SpongeConfig`                       | structure  |
| def_3     | `Poseidon.HADES.HADESConfig`                | structure  |
| def_4     | `Poseidon.HADES.fullRound` / `partialRound` | def        |
| def_5     | `Poseidon.SBox.sbox`                        | def        |
| def_6     | `Poseidon.MDS.cauchyMatrix`                 | def        |
| def_7     | `Poseidon.MDS.InactiveSBoxSubspace`         | def        |
| def_8     | `Security.CollisionResistant`               | def        |
| def_9     | `Security.PreimageResistant`                | def        |
| def_10    | `Security.SecondPreimageResistant`          | def        |
| def_11    | `Security.CICOSecure`                       | def        |
| def_12    | `Security.ZeroSumPartition`                 | structure  |
| def_13    | `Poseidon.Security.InvariantSubspaceTrail`  | structure  |
| def_14    | `Poseidon.Security.SubspaceTrail`           | structure  |
| def_15    | `Poseidon.DomainTag` / `domainTagValue`     | inductive  |
| lemma_1   | `Poseidon.Security.algebraicDegreeBound`    | theorem    |
| prop_1    | `Poseidon.Security.poseidon128_roundNumbers`| theorem    |
| prop_2    | `Poseidon.Security.poseidon80_roundNumbers` | theorem    |
| prop_3    | `Poseidon.Security.poseidon256_roundNumbers`| theorem    |
| algo_1    | `Sponge.hash`                               | def        |
| algo_2    | `Poseidon.permutation`                      | def        |
| algo_3    | `Poseidon.Grain.generateConstants`          | def        |
| sec_1     | `Poseidon.Security.poseidon_security`       | theorem    |
| sec_2     | `Poseidon.Security.poseidon_cico_security`  | theorem    |
| sec_3     | `Poseidon.Security.statisticalAttack_*`     | theorem    |
| sec_4     | `Poseidon.Security.interpolationAttack_*`   | theorem    |
| sec_5     | `Poseidon.Security.groebnerBasis_bound`     | theorem    |
| sec_6     | `Poseidon.SBox.dpMax_cube/fifth`            | theorem    |
| sec_7     | `Poseidon.MDS.maxInactiveRounds`            | theorem    |
| table_2   | `Poseidon.Instances.poseidon128_t3` etc.    | def        |
-/

namespace CryptoAcademy.Papers

/-- Reference to the Poseidon paper [GKRRS19]. -/
def poseidon := CryptoAcademy.Meta.Poseidon2019

end CryptoAcademy.Papers
