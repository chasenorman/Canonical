import Canonical
import Lean
import Mathlib

open Lean Meta


example  (a b : Nat) : a + b = b + a := by
  exact
    Nat.rec (motive := fun t ↦ t + b = b + t)
      (by
        simp only [Nat.add_zero, Nat.zero_add]
        -- exact Eq.refl b
        )
      (fun n n_ih ↦
        by simpa only [Nat.add_succ, Nat.succ_add] using Eq.rec (motive := fun a t ↦ (n + b).succ = a.succ) (by rfl) n_ih) a

-- @[PrettyPrinter.Delaborator.delabForall]
#check PrettyPrinter.Delaborator.delabPProdMk


-- set_option pp.explicit true
#check add_comm

example : 0 + n = n := by canonical
