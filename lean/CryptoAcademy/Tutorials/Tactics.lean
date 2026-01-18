/-
  CryptoAcademy Tutorial: Proofs and Tactics

  This file contains all code examples from the "Proofs and Tactics" tutorial.
  Source: web/src/pages/learn/proofs-and-tactics.astro
-/

/-! ## Proofs Are Programs -/

-- The proposition "2 + 2 = 4" is a type
#check (2 + 2 = 4)  -- : Prop

-- A proof is a term of that type
example : 2 + 2 = 4 := rfl  -- rfl proves equality by computation

/-! ## Tactic Mode -/

theorem add_comm_example (a b : Nat) : a + b = b + a := by
  -- Goal: a + b = b + a
  apply Nat.add_comm
  -- No more goals!

/-! ## Essential Tactics -/

-- intro: introduces hypotheses
example : ∀ n : Nat, n = n := by
  intro n      -- introduces n, goal becomes: n = n
  rfl

-- apply: uses a theorem or hypothesis
example (h : ∀ n, n + 0 = n) : 5 + 0 = 5 := by
  apply h     -- uses h with n = 5

-- exact: provides exactly the term needed
example (h : 2 + 2 = 4) : 2 + 2 = 4 := by
  exact h     -- h is exactly what we need

-- rw (rewrite): substitutes equals for equals
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]      -- goal becomes: b + 1 = b + 1
  rfl

-- simp: simplifies using a database of lemmas
example : (1 + 2) * 3 = 9 := by
  native_decide  -- computes and verifies

-- constructor / cases
-- Proving an And
example : 1 = 1 ∧ 2 = 2 := by
  constructor    -- splits into two goals
  · rfl          -- proves 1 = 1
  · rfl          -- proves 2 = 2

-- Using an And hypothesis
example (h : 1 = 1 ∧ 2 = 2) : 1 = 1 := by
  obtain ⟨left, _⟩ := h
  exact left

/-! ## The sorry Escape Hatch -/

-- sorry is a placeholder that "proves" anything (UNSAFE!)
-- The following theorem is FALSE but compiles with sorry
theorem incomplete : 1 = 2 := by
  sorry  -- This "proves" the false statement!

-- Lean will warn about theorems using sorry
#check incomplete  -- Warning: declaration uses 'sorry'
