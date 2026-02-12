import Mathlib.Tactic

/-
  CryptoAcademy/Meta/Notation.lean

  Custom notation for cryptographic constructions.
-/

namespace CryptoAcademy.Meta

/-! ## Security parameter notation -/

/-- Security parameter (typically λ or κ) -/
abbrev SecurityParam := Nat

/-- Notation for security parameter -/
scoped notation "λ" => SecurityParam

/-! ## Negligible function notation -/

-- Negligible functions will be defined in Complexity/Negligible.lean
-- This file provides notation hooks

/-! ## Cryptographic game notation -/

-- Game-based security definitions will use these notations

end CryptoAcademy.Meta
