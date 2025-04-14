import Canonical

-- TUTORIAL WORLD

example (x q : Nat) : (37 * x) + q = (37 * x) + q := by canonical

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by canonical

example : 2 = Nat.succ (Nat.succ 0) := by canonical

example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by canonical

example (n : Nat) : Nat.succ n = n + 1 := by canonical

example : 2 + 2 = 4 := by canonical

-- ADDITION WORLD

theorem zero_add (n : Nat) : 0 + n = n := by canonical

theorem succ_add (a b : Nat) : a.succ + b = (a + b).succ := by canonical

theorem add_comm (a b : Nat) : a + b = b + a := by canonical [zero_add, succ_add]

theorem add_assoc (a b c : Nat) : a + b + c = a + (b + c) := by canonical

theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := by canonical [add_comm, add_assoc]

-- IMPLICATION WORLD

example (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by canonical

example (x y : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 := by canonical [zero_add]

example (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by canonical

example (x : Nat) (h : x + 1 = 4) : x = 3 := by canonical [Nat.succ.inj]

example (x : Nat) : x = 37 → x = 37 := by canonical

example (x y : Nat) : x + 1 = y + 1 → x = y := by canonical [Nat.succ.inj]

example (x y : Nat) (h1 : x = y) (h2 : x ≠ y) : False := by canonical

example : 0 ≠ 1 := by canonical [Nat.zero_ne_add_one]

example : 1 ≠ 0 := by canonical [Nat.zero_ne_add_one]

example : 2 + 2 ≠ 5 := by canonical [Nat.succ.inj, Nat.zero_ne_add_one]

-- MULTIPLICATION WORLD

theorem mul_one (m : Nat) : m * 1 = m := by canonical [zero_add]

theorem zero_mul (m : Nat) : 0 * m = 0 := by canonical

theorem succ_mul (a b : Nat) : a.succ * b = a * b + b := by canonical [add_right_comm]

theorem mul_comm (a b : Nat) : a * b = b * a := by canonical [zero_mul, succ_mul]

theorem one_mul (m : Nat) : 1 * m = m := by canonical [mul_comm, mul_one]

theorem two_mul (m : Nat) : 2 * m = m + m := by canonical [succ_mul, one_mul]

theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by canonical [add_assoc]

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by canonical [mul_add, mul_comm]

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by canonical [mul_add]

-- ALGORITHM WORLD

theorem add_left_comm (a b c : Nat) : a + (b + c) = b + (a + c) := by canonical [add_comm, add_assoc]

example (a b c d : Nat) : (a + b) + (c + d) = ((a + c) + d) + b := by canonical [add_assoc, add_left_comm, add_comm]

example (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry

axiom pred : Nat → Nat
axiom pred_succ (n : Nat) : pred n.succ = n

example (a b : Nat) (h : a.succ = b.succ) : a = b := by canonical [pred_succ]

axiom is_zero : Nat → Prop
axiom is_zero_zero : is_zero 0 = True
axiom is_zero_succ (n : Nat) : is_zero n.succ = False

theorem succ_ne_zero (a : Nat) : a.succ ≠ 0 := by canonical [is_zero_zero, is_zero_succ]

example (m n : Nat) (h : m ≠ n) : m.succ ≠ n.succ := by canonical [Nat.succ.inj]

example : 20 + 20 = 40 := by canonical

-- ADVANCED ADDITION WORLD

structure If (a b : Prop) : Prop where
  h : a → b

theorem add_right_cancel (a b n : Nat) : a + n = b + n → a = b := by canonical [If, Nat.succ.inj]

theorem add_left_cancel (a b n : Nat) : n + a = n + b → a = b := by canonical [add_right_cancel, add_comm]

theorem add_left_eq_self (x y : Nat) : x + y = y → x = 0 := by canonical [zero_add, add_right_cancel]

theorem add_right_eq_self (x y : Nat) : x + y = x → y = 0 := by canonical [add_left_eq_self, add_comm]

theorem add_right_eq_zero (a b : Nat) : a + b = 0 → a = 0 := by canonical [If, succ_ne_zero]

theorem add_left_eq_zero (a b : Nat) : a + b = 0 → b = 0 := by canonical [add_right_eq_zero, add_comm]

-- POWER WORLD

example : 0^0 = 1 := by canonical

example (n : Nat) : 0^n.succ = 0 := by canonical

theorem pow_one (a : Nat) : a^1 = a := by canonical [one_mul]

theorem one_pow (n : Nat) : 1^n = 1 := sorry

theorem pow_two (a : Nat) : a^2 = a * a := by canonical [pow_one]

theorem pow_add (a m n : Nat) : a^(m + n) = a^m * a^n := by canonical [mul_one, mul_assoc]

theorem mul_pow (a b n : Nat) : (a * b)^n = a^n * b^n := sorry

theorem pow_pow (a m n : Nat) : (a^m)^n = a^(m * n) := by canonical [pow_add]

theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := sorry

axiom xyzzyAxiom (α : Sort) (synthetic := false) : α
theorem flt (a b c n : Nat) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by canonical [xyzzyAxiom]

-- LEQ WORLD

example (x : Nat) : x ≤ x := by canonical

theorem zero_le (x : Nat) : 0 ≤ x := by canonical

example (x : Nat) : x ≤ x.succ := by canonical

theorem le_trans (x y z : Nat) : x ≤ y → y ≤ z → x ≤ z := by canonical

theorem le_zero (x : Nat) : x ≤ 0 → x = 0 := by canonical [succ_ne_zero, If]

theorem le_antisymm (x y : Nat) : x ≤ y → y ≤ x → x = y := sorry

example (x y : Nat) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by canonical

theorem le_total (x y : Nat) : x ≤ y ∨ y ≤ x := sorry

theorem succ_le_succ (x y : Nat) : x.succ ≤ y.succ → x ≤ y := by canonical [Nat.le.dest, Nat.le.intro, Nat.succ.inj, Nat.succ_add]

theorem le_one (x : Nat) : (x ≤ 1) → (x = 0 ∨ x = 1) := sorry

theorem le_two (x : Nat) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := sorry

-- ADVANCED MULTIPLICATION WORLD

theorem mul_le_mul_right (a b t : Nat) (h : a ≤ b) : a * t ≤ b * t := by canonical [Nat.le.dest, Nat.le.intro, add_mul]

theorem mul_left_ne_zero (a b : Nat) (h : a * b ≠ 0) : b ≠ 0 := by canonical

theorem eq_succ_of_ne_zero (a : Nat) (ha : a ≠ 0) : ∃ n, a = Nat.succ n := by canonical [If]

theorem one_le_of_ne_zero (a : Nat) (ha : a ≠ 0) : 1 ≤ a := by canonical [eq_succ_of_ne_zero, add_comm]

theorem le_mul_right (a b : Nat) (h : a * b ≠ 0) : a ≤ (a * b) := sorry

theorem mul_right_eq_one (x y : Nat) (h : x * y = 1) : x = 1 := sorry

theorem mul_ne_zero (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := sorry

theorem mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 := by canonical [mul_ne_zero, Classical.byContradiction]

theorem mul_left_cancel (a b c : Nat) (ha : a ≠ 0) (h : a * b = a * c) : b = c := sorry

theorem mul_right_eq_self (a b : Nat) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by canonical [Nat.add, mul_one, mul_left_cancel]
