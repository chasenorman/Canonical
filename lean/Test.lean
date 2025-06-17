import Canonical
import Lean

inductive MyNat
| zero : MyNat
| succ : MyNat → MyNat

open MyNat

def add : MyNat → MyNat → MyNat
| a, zero => a
| a, succ b => succ (add a b)

@[simp] theorem zero_add (a : MyNat) : add zero a = a := by
  exact
    rec (motive := fun t ↦ add zero t = t) (by simp [add.eq_1] <;> exact Eq.refl zero)
      (fun a a_ih ↦ by simp [add.eq_2] <;> exact a_ih) a

@[simp] theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b) := by
  exact
    rec (motive := fun t ↦ add a.succ t = (add a t).succ) (by simp [add.eq_1] <;> exact Eq.refl a)
      (fun a_1 a_ih ↦ by simp [add.eq_2] <;> exact a_ih) b

theorem add_comm (a b : MyNat) : add a b = add b a := by
  exact
    rec (motive := fun t ↦ add t b = add b t) (by simp [add.eq_1] <;> exact Eq.refl b)
      (fun a a_ih ↦ by simp [add.eq_2] <;> exact a_ih) a

@[simp] theorem add_assoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  exact
    rec (motive := fun t ↦ add (add a b) t = add a (add b t))
      (by simp [add.eq_1] <;> exact Eq.refl (add a b))
      (fun a_1 a_ih ↦ by simp [add.eq_2] <;> exact a_ih) c
