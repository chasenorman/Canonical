import Canonical

example {a b c : Nat} : (a + b) + c = a + (b + c) := by canonical +refine
