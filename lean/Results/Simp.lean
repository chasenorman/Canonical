import Canonical

inductive MyNat
| zero : MyNat
| succ : MyNat → MyNat

def add : MyNat → MyNat → MyNat
| b, MyNat.zero => b
| b, MyNat.succ a => MyNat.succ (add b a)

@[simp] theorem zero_add (a : MyNat) : add MyNat.zero a = a :=
  by exact
    MyNat.rec (motive := fun t ↦ add MyNat.zero t = t) (Eq.refl MyNat.zero)
      (fun a a_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact a_ih) a

@[simp] theorem succ_add (a b : MyNat) : add (MyNat.succ a) b = MyNat.succ (add a b) :=
  by exact
    MyNat.rec (motive := fun t ↦ add (MyNat.succ a) t = MyNat.succ (add a t))
      (by simp only [zero_add, add.eq_1]) (fun c c_ih ↦ by simp only [MyNat.succ.injEq, add.eq_2] <;> exact c_ih) b

-- example (a b : MyNat) : add a b = add b a := by
--   canonical +refine
