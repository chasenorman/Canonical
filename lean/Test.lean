import Canonical

noncomputable def add (x : Nat) : Nat := Nat.rec Nat.zero (fun _ _ => Nat.zero) x

example (n : Nat) : add n = add n := by canonical +debug
