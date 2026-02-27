import Canonical
import Mathlib.Data.Real.Basic

-- You can use `destruct` to skolemize existentials:
example (p : ∃ x : Nat, x = x + 1) : False := by
  destruct

-- `destruct` can unpack nested structures:
variable (A B C : Prop)
example (p : (A ↔ B) ∧ C) : False := by
  destruct

/-
destruct can even unpack structure types that are behind universal
quantifiers, implications, and function types. Observe how each field
has `A` as an antecedent, and only the `right` field has `B`:
-/
example (p : A → (B ∧ (B → C))) : False := by
  destruct

/-
But wait, there's more. You can even unpack
structures in the antecedents of premises:
-/
example (p : (Nat × Nat) → (Nat × Nat)) : Nat := by
  destruct

-- If the goal is a structure type, multiple goals can be created:
example : ∃ n : Nat, n = n := by
  destruct

-- There is a default list of structures that unfold, but you can specify your own:
example (map : Std.HashMap String Nat) : Nat := by
  destruct [Std.HashMap, Std.DHashMap, Std.DHashMap.Raw]

/-
Unit is treated like a structure, and is eliminated. Also notice the
treatment of dependence on variables that were previously structure types:
-/
example (p : (Unit × Unit ×' ∃ x : (Nat × Nat), x.1 = x.2) → (A → B)) : B := by
  destruct


def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  canonical
