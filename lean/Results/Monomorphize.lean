import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Canonical
import Lean

def zulip : ∃ n : Nat, n * n = 4 := by
  canonical


-- -- Premise selection
-- set_premise_selector Lean.PremiseSelection.random
-- example : Nat := by
--   canonical +debug +premises

-- Monomorphized premise
example (R : Type*) [CommRing R] (x : R) : x + 2 = 2 + x := by
  canonical [add_comm]
  -- exact add_comm x ↑2

-- Monomorphized simp lemma
example (R : Type*) [Monoid R] (a b c : R) : a * b * c = a * (b * c) := by
  canonical [mul_assoc]
  -- simp only [mul_assoc] <;> exact Eq.refl (a * (b * c))

-- Monomorphized operation (notice `+`!)
example (a b : Nat) : a + b = b + a := by
  canonical
  -- exact
  --   Nat.rec (motive := fun t ↦ t + b = b + t)
  --     (by simp only [Nat.zero_add, Nat.add_zero] <;> exact Eq.refl b)
  --     (fun n n_ih ↦ by simp only [Nat.add_succ, Nat.succ.injEq, Nat.succ_add] <;> exact n_ih) a

-- synthInstance
example [Finite ℕ] : False := by
  canonical [not_finite]
  -- exact not_finite ℕ

-- Instance in local context
example [Inhabited X] : X := by
  canonical [default]
  -- exact default

-- Synthesis during reconstruction
axiom HashSet (α : Type) : Type
axiom HashSet.empty [BEq α] [Hashable α] : HashSet α
noncomputable example : HashSet Nat := by
  canonical [HashSet.empty]
  -- exact HashSet.empty

-- Creating instances
example : Inhabited Nat := by
  canonical [Inhabited]
  -- exact { default := Nat.zero }
