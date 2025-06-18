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
    rec (motive := fun t ↦ add zero t = t) (by simp [add.eq_1])
      (fun a a_ih ↦ by simpa [MyNat.succ.injEq, add.eq_2] using a_ih) a

@[simp] theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b) := by
  exact
    rec (motive := fun t ↦ add a.succ t = (add a t).succ) (by simp [MyNat.succ.injEq, add.eq_1])
      (fun a_1 a_ih ↦ by simpa [MyNat.succ.injEq, add.eq_2] using a_ih) b

theorem add_comm (a b : MyNat) : add a b = add b a := by
  exact
    rec (motive := fun t ↦ add t b = add b t) (by simp [add.eq_1, zero_add] <;> exact Eq.refl b)
      (fun a a_ih ↦ by simp [MyNat.succ.injEq, add.eq_2, succ_add] <;> exact a_ih) a

@[simp] theorem add_assoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  exact
    rec (motive := fun t ↦ add (add a b) t = add a (add b t)) (by simp [add.eq_1])
      (fun a_1 a_ih ↦ by simpa [MyNat.succ.injEq, add.eq_2] using a_ih) c

theorem add_comm' (a b : Nat) : a + b = b + a := by
  exact
    Nat.rec (motive := fun t ↦ t.add b = b.add t)
      (by
        simp [Nat.zero_add] <;>
          exact
              Nat.rec (motive := fun t ↦ t = t) (Eq.refl Nat.zero) (fun n n_ih ↦ Eq.refl n.succ) b)
      (fun n n_ih ↦ by
        simp [Nat.succ_add] <;>
          exact Eq.rec (motive := fun a t ↦ (n.add b).succ = a.succ) (Eq.refl (n.add b).succ) n_ih)
      a
