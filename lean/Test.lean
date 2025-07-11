import Canonical
import Lean

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

open MyNat

def add : MyNat → MyNat → MyNat
| a, zero => a
| a, succ b => succ (add a b)

@[simp] theorem zero_add (a : MyNat) : add zero a = a := by
  exact
    rec (motive := fun t ↦ add zero t = t) (Eq.refl zero)
      (fun a a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) a

@[simp] theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b) := by
  exact
    rec (motive := fun t ↦ add a.succ t = (add a t).succ)
      (by simp only [MyNat.succ.injEq, add.eq_1] <;> exact Eq.refl a)
      (fun a_1 a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) b

theorem add_comm (a b : MyNat) : add a b = add b a := by
  exact
    rec (motive := fun t ↦ add t b = add b t)
      (by simp only [add.eq_1, zero_add] <;> exact Eq.refl b)
      (fun a a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2, succ_add] <;> exact a_ih) a

@[simp] theorem add_assoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  exact
    rec (motive := fun t ↦ add (add a b) t = add a (add b t)) (Eq.refl (add a b))
      (fun a_1 a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) c

theorem add_comm' (a b : Nat) : a + b = b + a := by
  exact
    Nat.rec (motive := fun t ↦ t.add b = b.add t)
      (by simp only [Nat.zero_add, Nat.add_eq, Nat.add_zero] <;> exact Eq.refl b)
      (fun n n_ih ↦ by
        simp only [Nat.add_succ, Nat.add_eq, Nat.succ_add] <;>
          exact Eq.rec (motive := fun a t ↦ (n.add b).succ = a.succ) (Eq.refl (n.add b).succ) n_ih)
      a


example : true ≠ false := by exact fun a ↦ by exact by simpa only [reduceCtorEq] using a
