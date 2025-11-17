import Canonical
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
open Mathlib.Tactic.CC
open Function

inductive Nat'
| zero : Nat'
| succ : Nat' → Nat'

def add (n : Nat') : Nat' → Nat'
| Nat'.zero => n
| Nat'.succ m => Nat'.succ (add n m)

set_option pp.explicit true in
example (a b : Nat') : add a b = add b a := by
  exact
    @Nat'.rec (fun t ↦ @Eq Nat' (add t b) (add b t))
      (@Nat'.rec (fun t ↦ @Eq Nat' (add Nat'.zero t) t) (@Eq.refl Nat' Nat'.zero)
        (fun a a_ih ↦ by simp only [add.eq_2, Nat'.succ.injEq] <;> exact a_ih) b)
      (fun a a_ih ↦
        @Eq.rec Nat' (add a b).succ (fun a_1 t ↦ @Eq Nat' (add a.succ b) a_1)
          (@Nat'.rec (fun t ↦ @Eq Nat' (add a.succ t) (add a t).succ)
            (by simp only [add.eq_1, Nat'.succ.injEq] <;> exact @Eq.refl Nat' a)
            (fun a_1 a_ih ↦ by simp only [add.eq_2, Nat'.succ.injEq] <;> exact a_ih) b)
          (add b a).succ (by simp only [Nat'.succ.injEq] <;> exact a_ih))
      a


variable {α : Type} {n m : Nat}

inductive Vec (A : Type) : Nat → Type where
| nil  : Vec A 0
| cons : A → {n : Nat} → Vec A n → Vec A (n + 1)

noncomputable def append (v1 : Vec α n) (v2 : Vec α m) : Vec α (m + n) :=
  by exact
    Vec.rec (motive := fun a t ↦ Vec α (m + a)) v2
      (fun a {n} a_1 a_ih ↦ by
        simpa only [Nat.add_succ, Nat.add_assoc, Nat.add_zero] using Vec.cons a a_ih)
      v1


theorem sSup_inter_le' {α : Type} [CompleteLattice α] {s t : Set α}
  : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  by exact sSup_le fun b a ↦ le_inf (le_sSup a.left) (le_sSup a.right)


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


theorem Cantor {X : Type} (f : X → Set X) : ¬Surjective f :=
  by exact fun a ↦
    False.rec (fun t ↦ False)
      (false_of_a_eq_not_a
        (congrFun (Exists.choose_spec (a fun a ↦ f a a → False)) (a fun a ↦ f a a → False).choose))
