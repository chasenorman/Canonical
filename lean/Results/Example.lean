import Canonical
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
open Mathlib.Tactic.CC
open Function

example : (A ∧ ¬A) → B :=
  by canonical


theorem Cantor (f : X → Set X) : ¬Surjective f :=
  by canonical [false_of_a_eq_not_a, congrFun]


inductive Vec (A : Type) : Nat → Type u where
| vnil  : Vec A 0
| vcons : A → {n : Nat} → Vec A n → Vec A (n+1)

noncomputable def append : Vec α n → Vec α m → Vec α (m + n) :=
  by canonical


theorem Eq.trans' {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  by canonical


-- theorem List.recGen (motive : List α → List α → Prop) : (∀ (y : List α), motive [] y) →
--   (∀ (head : α) (tail : List α), (∀ (y : List α), motive tail y) → ∀ (y : List α), motive (head :: tail) y) →
--     ∀ (t y : List α), motive t y :=
--   List.rec (motive := fun x => ∀ y, motive x y)

-- -- Requires synth
-- theorem reverse_reverse (as : List α) : as.reverse.reverse = as :=
--   by canonical [List.recGen]


-- theorem sSup_inter_le' [CompleteLattice α] {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
--   by canonical 30


-- class Group' (α : Type u) extends Semigroup α, Inv α where
--   one : α
--   one_mul : ∀ a : α, one * a = a
--   inv_mul_cancel : ∀ a : α, a⁻¹ * a = one

-- example [m : Group' R] : MulHom R R :=
--   by canonical (count := 10)

-- example (a b : Nat) : a + b = b + a :=
--   by exact
--     Nat.rec (motive := fun t ↦ t + b = b + t)
--       (by
--         simp only [Nat.zero_add, Nat.add_zero] <;> simpa only [Nat.succ.injEq] using Eq.refl b.succ)
--       (fun n n_ih ↦ by simp only [Nat.add_succ, Nat.succ.injEq, Nat.succ_add] <;> exact n_ih) a
