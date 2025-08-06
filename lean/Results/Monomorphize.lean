import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Canonical
import Lean

def zulip : ∃ n : Nat, n * n = 4 := by
  canonical

-- standard monomorphization
example (R : Type*) [CommRing R] (x : R) : x + 2 = 2 + x := by
  canonical [add_comm]

-- monomorphized simp lemma
example (R : Type*) [Monoid R] (a b c : R) : a * b * c = a * (b * c) := by
  canonical [mul_assoc]

-- using HAdd by default
example (a b : Nat) : a + b = b + a := by
  canonical

-- -- Premise selection
-- set_premise_selector Lean.PremiseSelection.random
-- example : Nat := by
--   canonical +debug +premises

-- Instance coupling
example [Finite ℕ] : False := by
  canonical [not_finite]

-- Instances parameterized by values
example (n : Nat) (x y : Fin n) : x + y = x + y := by
  monomorphize
  sorry

example (l : List X) : l ++ l = l ++ l := by
  monomorphize
  sorry

example : (4 : Real) = 4 := by
  monomorphize
  sorry

-- No use of the function symbol.
example [Inhabited X] : X := by canonical [default]

-- Synthesis during reconstruction
axiom HashSet (α : Type) : Type
axiom HashSet.empty [BEq α] [Hashable α] : HashSet α
noncomputable example : HashSet Nat := by canonical [HashSet.empty]

-- Creating instances
example : Inhabited Nat := by canonical
