/-
  CryptoAcademy Tutorial: Types and Terms

  This file contains all code examples from the "Types and Terms" tutorial.
  Source: web/src/pages/learn/types-and-terms.astro
-/

/-! ## Everything Has a Type -/

-- Numbers have types
#check (42 : Nat)         -- 42 is a natural number
#check (-5 : Int)         -- -5 is an integer
#check (3.14 : Float)     -- 3.14 is a floating-point number

-- Functions have types
#check (Nat.add : Nat → Nat → Nat)   -- takes two Nats, returns a Nat

-- Propositions have types too
#check (2 + 2 = 4 : Prop)   -- this is a proposition

/-! ## Function Types -/

-- A function from Nat to Nat
def double : Nat → Nat :=
  fun n => n * 2

-- A function taking two arguments
def add : Nat → Nat → Nat :=
  fun a b => a + b

-- Equivalent to:
def add' (a b : Nat) : Nat := a + b

-- Verify they compute the same thing
example : add 3 4 = add' 3 4 := rfl

/-! ## Dependent Types -/

-- A vector of exactly n elements
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0                        -- empty vector has length 0
  | cons : α → Vec α n → Vec α (n + 1)   -- adding element increases length

-- The type Vec α n depends on the value n!
-- Vec Nat 3 is different from Vec Nat 5
#check (Vec Nat 3)
#check (Vec Nat 5)

-- Example vectors
def emptyVec : Vec Nat 0 := Vec.nil
def oneElem : Vec Nat 1 := Vec.cons 42 Vec.nil
def twoElems : Vec Nat 2 := Vec.cons 1 (Vec.cons 2 Vec.nil)

/-! ## Structures -/

structure Point where
  x : Float
  y : Float

-- Create a point
def origin : Point := { x := 0.0, y := 0.0 }

-- Or using constructor syntax
def origin' : Point := Point.mk 0.0 0.0

-- Access fields
#check origin.x  -- Float

-- Both definitions are equivalent
example : origin = origin' := rfl

/-! ## Inductive Types -/

-- Natural numbers: either zero or successor of another Nat
-- (This is how Nat is actually defined in Lean's core)
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- A list is either empty or an element followed by a list
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

-- Boolean: true or false
inductive MyBool where
  | false : MyBool
  | true  : MyBool

-- Examples
def myZero : MyNat := MyNat.zero
def myTwo : MyNat := MyNat.succ (MyNat.succ MyNat.zero)
def myList : MyList Nat := MyList.cons 1 (MyList.cons 2 MyList.nil)
