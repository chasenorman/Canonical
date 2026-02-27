import Canonical
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
open Function

inductive Nat'
| zero : Nat'
| succ : Nat' → Nat'

def add (n : Nat') : Nat' → Nat'
| Nat'.zero => n
| Nat'.succ m => Nat'.succ (add n m)

set_option pp.explicit true in
example (a b : Nat') : add a b = add b a := by
  canonical 30


variable {α : Type} {n m : Nat}

inductive Vec (A : Type) : Nat → Type where
| nil  : Vec A 0
| cons : A → {n : Nat} → Vec A n → Vec A (n + 1)

noncomputable def append (v1 : Vec α n) (v2 : Vec α m) : Vec α (m + n) :=
  by canonical


theorem sSup_inter_le' {α : Type} [CompleteLattice α] {s t : Set α}
  : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  by canonical [sSup_le, le_sSup, le_inf, And]


def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-- Continuous functions are sequentially continuous -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  canonical

instance {G : Type} [Group G] : MulHom G G := by
  canonical (count := 2) [MulHom, one_mul]

theorem false_of_a_eq_not_a {a : Prop} (h : a = Not a) : False :=
  have : Not a := fun ha ↦ absurd ha (Eq.mp h ha)
  absurd (Eq.mpr h this) this

theorem Cantor {X : Type} (f : X → Set X) : ¬Surjective f :=
  by canonical [false_of_a_eq_not_a, congrFun]
