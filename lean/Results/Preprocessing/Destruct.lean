import Canonical
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic


example (p : Nat × Nat × Nat) : Unit := by
  destruct

example (p : Bool → Nat × (Bool → Nat)) : Unit := by
  -- canonical +debug
  destruct

example (p : A → B ∧ (C → B)) : Unit := by
  -- canonical +debug
  destruct

example (p : ∃ n : Nat, n > 0) : Unit := by
  destruct

example (p : ∃ x : Nat, ∀ y : Nat, ∃ z : Nat, x * y = z) : Unit := by
  destruct

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  by_contra h
  destruct
  exact
    h_0 (fun x x_1 ↦ hu_0 (hf_0 x x_1) (hf_1 x x_1)) fun x x_1 n a ↦
      hf_2 x x_1 (u n) (hu_1 (hf_0 x x_1) (hf_1 x x_1) n a)
  -- destruct
  -- intros ε hε
  -- canonical +debug
  -- use hu_0 (hf_0 ε hε) (hf_1 ε hε)
  -- exact fun n a ↦ hf_2 ε hε (u n) (hu_1 (hf_0 ε hε) (hf_1 ε hε) n a)

example : ∃ n : Nat, n = n := by
  destruct
