import Canonical
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs

inductive Nat'
| zero : Nat'
| succ : Nat' → Nat'

def add (n : Nat') : Nat' → Nat'
| Nat'.zero => n
| Nat'.succ m => Nat'.succ (add n m)

example (a b : Nat') : add a b = add b a := by
  canonical 30 +debug


variables {α : Type} {n m : Nat}

inductive Vec (A : Type) : Nat → Type where
| vnil  : Vec A 0
| vcons : A → {n : Nat} → Vec A n → Vec A (n+1)

#check Vec.vnil
-- Vec.vcons A.1563 a.1564 n.1565 a.1566
noncomputable def append : Vec α n → Vec α m → Vec α (m + n) :=
  by canonical +debug



def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  canonical


-- fix monomorphize to register supertypes
instance {G : Type} [Group G] : MulHom G G := by
  canonical (count := 2) [MulHom, one_mul]
