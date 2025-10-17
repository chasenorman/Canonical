import Canonical
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
open Mathlib.Tactic.CC
open Function

example : (A ∧ ¬A) → B :=
  by canonical


theorem Cantor (f : X → Set X) : ¬Surjective f :=
  by canonical +debug [false_of_a_eq_not_a, congrFun]


-- inductive Vec (A : Type) : Nat → Type u where
-- | vnil  : Vec A 0
-- | vcons : A → {n : Nat} → Vec A n → Vec A (n+1)

-- noncomputable def append : Vec α n → Vec α m → Vec α (m + n) :=
--   by canonical


theorem Eq.trans' {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  by canonical


-- theorem List.recGen (motive : List α → List α → Prop) : (∀ (y : List α), motive [] y) →
--   (∀ (head : α) (tail : List α), (∀ (y : List α), motive tail y) → ∀ (y : List α), motive (head :: tail) y) →
--     ∀ (t y : List α), motive t y :=
--   List.rec (motive := fun x => ∀ y, motive x y)

-- -- Requires synth
-- theorem reverse_reverse (as : List α) : as.reverse.reverse = as :=
--   by canonical [List.recGen]

-- set_option trace.Meta.isDefEq true
-- set_option pp.all true
theorem sSup_inter_le' {α : Type} [CompleteLattice α] {s t : Set α}
  : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  by canonical [sSup_le, le_sSup, le_inf, And]


-- class Group' (α : Type u) extends Semigroup α, Inv α where
--   one : α
--   one_mul : ∀ a : α, one * a = a
--   inv_mul_cancel : ∀ a : α, a⁻¹ * a = one

-- example [m : Group' R] : MulHom R R :=
--   by canonical (count := 10)

example (a b : Nat) : a + b = b + a := by
  canonical
