/-
  CryptoAcademy Tutorial: Using Mathlib

  This file contains all code examples from the "Using Mathlib" tutorial.
  Source: web/src/pages/learn/mathlib-basics.astro
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-! ## Algebraic Structures -/

section GroupExamples
variable {G : Type*} [Group G]

-- G is a group means we have:
-- * : G → G → G      (multiplication)
-- 1 : G              (identity)
-- ⁻¹ : G → G         (inverse)

-- These theorems are available:
#check @mul_assoc G _        -- (a * b) * c = a * (b * c)
#check @one_mul G _          -- 1 * a = a
#check @mul_inv_cancel G _   -- a⁻¹ * a = 1

end GroupExamples

section CommGroupExamples
variable {G : Type*} [CommGroup G]

#check @mul_comm G _   -- a * b = b * a

end CommGroupExamples

section FieldExamples
variable {F : Type*} [Field F]

-- We get both additive and multiplicative structure:
#check @add_comm F _        -- a + b = b + a
#check @mul_add F _         -- a * (b + c) = a*b + a*c
#check @mul_inv_cancel₀ F _ -- a ≠ 0 → a * a⁻¹ = 1

end FieldExamples

/-! ## ZMod n -/

-- ZMod 7 is a field (7 is prime)
example : Field (ZMod 7) := inferInstance

-- Arithmetic works as expected
example : (3 : ZMod 7) + 5 = 1 := rfl  -- 3 + 5 = 8 ≡ 1 (mod 7)

/-! ## Type Classes in Action -/

-- A theorem that works for ANY group
theorem my_inv_inv {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a := by
  exact inv_inv a

-- Apply to any specific group
example : (3 : ZMod 7)⁻¹⁻¹ = 3 := my_inv_inv 3

/-! ## Finding Theorems -/

-- exact? suggests lemmas that close the goal
example {G : Type*} [Group G] (a b : G) : a * b * b⁻¹ = a := by
  exact mul_inv_cancel_right a b

/-! ## Cryptographic Example -/

-- A Schnorr-like discrete log setting
structure DLSetting where
  G : Type*
  [grp : CommGroup G]
  g : G
  q : ℕ
  g_order : g ^ q = 1

attribute [instance] DLSetting.grp

-- With this structure, we inherit all group lemmas:
example (s : DLSetting) : s.g * s.g⁻¹ = 1 := by
  exact mul_inv_cancel s.g
