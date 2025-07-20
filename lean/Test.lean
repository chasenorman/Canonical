import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Canonical
import Lean

def test : ∃ n : Nat, n * n = 4 := by
  canonical

def test2 : 0 ≠ 1 := by canonical

-- example (x : ℝ) : x + 2 = 2 + x := by
--   canonical [add_comm]

-- example (R : Type*) [CommRing R] (x : R) : x + 2 = 2 + x := by
--   canonical [add_comm]

-- example (a b : Nat) : a + b = b + a := by
--   canonical [add_comm]

-- -- fails
-- example (R : Type*) [CommRing R] (x : R) (m n : Nat) : x^(m + n) = x^m * x^n := by
--   canonical [pow_add]

-- -- fails
-- example (n : Nat) (x : ZMod n) : x + 2 = 2 + x := by
--   canonical [add_comm]

-- -- fails
-- example (R : Type*) [CommRing R] (x y z : R) : x + y + z = x + z + y := by
--   canonical [add_right_comm]
