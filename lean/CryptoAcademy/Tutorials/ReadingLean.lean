/-
  CryptoAcademy Tutorial: Reading Lean Code

  This file contains all code examples from the "Reading Lean Code" tutorial.
  Source: web/src/pages/learn/reading-lean.astro
-/

/-! ## The Basics -/

/-- A natural number is even if it equals 2 times some other natural number. -/
def isEven (n : Nat) : Prop :=
  ∃ k, n = 2 * k

/-! ## Definitions vs Theorems -/

/-- A group structure with multiplication, identity, and inverse operations. -/
structure Group' (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_inv : ∀ a, mul (inv a) a = one

/-- The sum of two even numbers is even. -/
theorem even_plus_even (m n : Nat)
    (hm : isEven m) (hn : isEven n) : isEven (m + n) := by
  obtain ⟨k₁, hk₁⟩ := hm
  obtain ⟨k₂, hk₂⟩ := hn
  use k₁ + k₂
  omega

/-! ## Reading a Real Example -/

/-- A simple commitment scheme with commit and open operations. -/
structure CommitmentScheme (M R C : Type) where
  /-- Commit takes a message and randomness, returns a commitment -/
  commit : M → R → C
  /-- Opening reveals the message -/
  open : C → R → M
  /-- Correctness: opening a commitment reveals the original message -/
  correctness : ∀ (m : M) (r : R), open (commit m r) r = m

/-! ## Interactive Example -/

-- Check what type isEven 4 has
#check isEven 4

-- You can evaluate expressions too
#eval 2 + 2
