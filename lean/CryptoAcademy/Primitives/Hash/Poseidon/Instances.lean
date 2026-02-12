/-!
# Poseidon Concrete Instances

Concrete parameter sets for Poseidon instances used in practice.
These correspond to Table 2 in [GKRRS19] (with security margin).

## Main definitions

- `poseidon128_t3` : POSEIDON-128, t = 3 (Merkle 2:1)
- `poseidon128_t5` : POSEIDON-128, t = 5 (Merkle 4:1)
- `poseidon80_t3` : POSEIDON-80, t = 3 (Merkle 2:1)
- `poseidon80_t5` : POSEIDON-80, t = 5 (Merkle 4:1)
- `poseidon256_t6` : POSEIDON-256, t = 6
- `poseidon256_t10` : POSEIDON-256, t = 10

## References

- Table 2 (Section 4.1) in [GKRRS19]
  https://eprint.iacr.org/2019/458
-/

import CryptoAcademy.Primitives.Hash.Poseidon.HADES

namespace CryptoAcademy.Primitives.Hash.Poseidon.Instances

/-- Parameter record for a concrete Poseidon instance.

  Stores the instance name, security level, and HADES parameters
  without requiring a specific prime (these work over BLS12-381,
  BN254, and Ed25519 scalar fields).

  From: Table 2 in [GKRRS19] (eprint 2019/458).
  JSON ref: table_2 -/
structure InstanceParams where
  /-- Instance name -/
  name : String
  /-- Security level in bits -/
  securityLevel : ℕ
  /-- S-box exponent -/
  α : ℕ
  /-- State width -/
  t : ℕ
  /-- Total number of full rounds -/
  R_F : ℕ
  /-- Number of partial rounds -/
  R_P : ℕ
  deriving Repr

/-! ## x⁵-POSEIDON instances over BLS12-381 / BN254 / Ed25519

  All instances use S-box `f(x) = x⁵` and include the security
  margin from Section 5.4: `+2` on `R_F`, `+7.5%` on `R_P`.

  From: Table 2 in [GKRRS19] (eprint 2019/458).
  JSON ref: table_2 -/

/-- POSEIDON^π-128, t = 3 (Merkle tree arity 2:1) -/
def poseidon128_t3 : InstanceParams :=
  { name := "POSEIDON^π-128"
    securityLevel := 128
    α := 5
    t := 3
    R_F := 8
    R_P := 57 }

/-- POSEIDON^π-128, t = 5 (Merkle tree arity 4:1) -/
def poseidon128_t5 : InstanceParams :=
  { name := "POSEIDON^π-128"
    securityLevel := 128
    α := 5
    t := 5
    R_F := 8
    R_P := 60 }

/-- POSEIDON^π-80, t = 3 (Merkle tree arity 2:1) -/
def poseidon80_t3 : InstanceParams :=
  { name := "POSEIDON^π-80"
    securityLevel := 80
    α := 5
    t := 3
    R_F := 8
    R_P := 33 }

/-- POSEIDON^π-80, t = 5 (Merkle tree arity 4:1) -/
def poseidon80_t5 : InstanceParams :=
  { name := "POSEIDON^π-80"
    securityLevel := 80
    α := 5
    t := 5
    R_F := 8
    R_P := 35 }

/-- POSEIDON^π-256, t = 6 -/
def poseidon256_t6 : InstanceParams :=
  { name := "POSEIDON^π-256"
    securityLevel := 256
    α := 5
    t := 6
    R_F := 8
    R_P := 120 }

/-- POSEIDON^π-256, t = 10 -/
def poseidon256_t10 : InstanceParams :=
  { name := "POSEIDON^π-256"
    securityLevel := 256
    α := 5
    t := 10
    R_F := 8
    R_P := 120 }

/-! ## Consistency checks -/

/-- All instances use at least 8 full rounds (6 minimum + 2 margin).
  JSON ref: remark_3 -/
example : poseidon128_t3.R_F = 8 := rfl
example : poseidon128_t5.R_F = 8 := rfl
example : poseidon80_t3.R_F = 8 := rfl
example : poseidon256_t6.R_F = 8 := rfl

/-- All instances use α = 5. -/
example : poseidon128_t3.α = 5 := rfl
example : poseidon80_t3.α = 5 := rfl
example : poseidon256_t6.α = 5 := rfl

end CryptoAcademy.Primitives.Hash.Poseidon.Instances
