import Canonical

-- TUTORIAL WORLD

example (x q : Nat) : (37 * x) + q = (37 * x) + q := by exact Eq.refl ((Nat.mul 37 x).add q)

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
  by
    simp only [Nat.zero_add, Nat.zero_mul, Nat.add_eq, Nat.add_assoc, Nat.succ_mul, Nat.mul_eq] <;>
      exact
          Eq.rec (motive := fun a t ↦ a) (Eq.refl (x.add (Nat.add 7 (x.add 7))))
            (by
              simpa only [Nat.add_eq, Nat.add_assoc] using
                Eq.rec (motive := fun a t ↦
                  (a.add a = x.add (Nat.add 7 a)) = (y.add y = x.add (Nat.add 7 a)))
                  (Eq.refl (y.add y = x.add (Nat.add 7 y))) h)

example : 2 = Nat.succ (Nat.succ 0) := by exact Eq.refl Nat.zero.succ.succ

example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  simp only [Nat.add_eq, Nat.add_assoc, Nat.add_zero] <;> exact Eq.refl (a.add (b.add c))

example (n : Nat) : Nat.succ n = n + 1 := by
  exact Eq.refl n.succ

example : 2 + 2 = 4 := by exact Eq.refl Nat.zero.succ.succ.succ.succ

-- ADDITION WORLD

theorem zero_add (n : Nat) : 0 + n = n :=
  by exact by simp only [Nat.zero_add, Nat.add_eq] <;> exact Eq.refl n

theorem succ_add (a b : Nat) : a.succ + b = (a + b).succ :=
  by exact by simp only [Nat.add_eq, Nat.succ_add] <;> exact Eq.refl (a.add b).succ

theorem add_comm (a b : Nat) : a + b = b + a :=
  by exact
    Nat.rec (motive := fun t ↦ t.add b = b.add t)
      (by
        simp only [Nat.zero_add, Nat.add_eq, Nat.add_zero] <;>
          exact Nat.rec (motive := fun t ↦ b = b) (Eq.refl b) (fun n n_ih ↦ n_ih) a)
      (fun n n_ih ↦ by
        simp only [Nat.add_succ, Nat.add_eq, Nat.succ_add] <;>
          exact Eq.rec (motive := fun a t ↦ (n.add b).succ = a.succ) (Eq.refl (n.add b).succ) n_ih)
      a

theorem add_assoc (a b c : Nat) : a + b + c = a + (b + c) :=
  by exact by simp only [Nat.add_eq, Nat.add_assoc] <;> exact Eq.refl (a.add (b.add c))

theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b :=
  by
    simp only [Nat.add_eq, Nat.add_assoc] <;>
      exact
          Nat.rec (motive := fun t ↦ a.add (b.add t) = a.add (t.add b))
            (by simp only [Nat.zero_add, Nat.add_eq, Nat.add_zero] <;> exact Eq.refl (a.add b))
            (fun n n_ih ↦ by
              simp only [Nat.add_succ, Nat.add_eq, Nat.succ_add] <;>
                exact
                    Eq.rec (motive := fun a_1 t ↦ (a.add (b.add n)).succ = a_1.succ)
                      (Eq.refl (a.add (b.add n)).succ) n_ih)
            c

-- IMPLICATION WORLD

example (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by exact h1

example (x y : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 :=
  by exact by simpa only [Nat.zero_add, Nat.add_succ, Nat.add_eq, Nat.add_zero] using h

example (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by exact h2 h1

example (x : Nat) (h : x + 1 = 4) : x = 3 := by exact Nat.succ.inj h

example (x : Nat) : x = 37 → x = 37 := by exact fun a ↦ a

example (x y : Nat) : x + 1 = y + 1 → x = y := by exact fun a ↦ Nat.succ.inj a

example (x y : Nat) (h1 : x = y) (h2 : x ≠ y) : False :=
  by exact
    Nat.rec (motive := fun t ↦ False) (h2 h1) (fun n n_ih ↦ False.rec (fun t ↦ False) n_ih) x

example : 0 ≠ 1 :=
  by exact fun a ↦ by simpa only [reduceCtorEq] using a

example : 1 ≠ 0 :=
  by exact fun a ↦ by simpa only [reduceCtorEq] using a

example : 2 + 2 ≠ 5 :=
  by exact fun a ↦
    False.rec (fun t ↦ False)
      (Nat.zero_ne_add_one Nat.zero
        (by
          simp only [Nat.zero_add, Nat.add_eq] <;>
            exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj a)))))

-- MULTIPLICATION WORLD

theorem mul_one (m : Nat) : m * 1 = m := by
exact by
  simp only [Nat.zero_add, Nat.mul_succ, Nat.add_eq, Nat.mul_zero, Nat.mul_eq] <;> exact Eq.refl m

theorem zero_mul (m : Nat) : 0 * m = 0 :=
  by exact by simp only [Nat.zero_mul, Nat.mul_eq] <;> exact Eq.refl Nat.zero

theorem succ_mul (a b : Nat) : a.succ * b = a * b + b :=
  by exact by simp only [Nat.succ_mul, Nat.mul_eq] <;> exact Eq.refl ((a.mul b).add b)

theorem mul_comm (a b : Nat) : a * b = b * a :=
  by exact
    Nat.rec (motive := fun t ↦ a.mul t = t.mul a)
      (by simp only [Nat.zero_mul, Nat.mul_zero, Nat.mul_eq] <;> exact Eq.refl Nat.zero)
      (fun n n_ih ↦ by
        simp only [Nat.mul_succ, Nat.succ_mul, Nat.mul_eq] <;>
          exact
              Eq.rec (motive := fun a_1 t ↦ (a.mul n).add a = a_1.add a) (Eq.refl ((a.mul n).add a))
                n_ih)
      b

theorem one_mul (m : Nat) : 1 * m = m :=
  by exact by simp only [Nat.zero_add, Nat.zero_mul, Nat.add_eq, Nat.succ_mul, Nat.mul_eq] <;> exact Eq.refl m

theorem two_mul (m : Nat) : 2 * m = m + m :=
  by simp only [Nat.zero_add, Nat.zero_mul, Nat.add_eq, Nat.succ_mul, Nat.mul_eq] <;>
      exact Eq.refl (m.add m)

theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c :=
  by exact by simp only [Nat.mul_add, Nat.mul_eq] <;> exact Eq.refl ((a.mul b).add (a.mul c))

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c :=
  by exact by simp only [Nat.add_mul, Nat.mul_eq] <;> exact Eq.refl ((a.mul c).add (b.mul c))

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) :=
  by exact by simp only [Nat.mul_assoc, Nat.mul_eq] <;> exact Eq.refl (a.mul (b.mul c))

-- ALGORITHM WORLD

theorem add_left_comm (a b c : Nat) : a + (b + c) = b + (a + c) :=
  by exact
    Nat.rec (motive := fun t ↦ t.add (b.add c) = b.add (t.add c))
      (by simp only [Nat.zero_add, Nat.add_eq] <;> exact Eq.refl (b.add c))
      (fun n n_ih ↦ by
        simp only [Nat.add_succ, Nat.add_eq, Nat.succ_add] <;>
          exact
              Eq.rec (motive := fun a t ↦ (n.add (b.add c)).succ = a.succ)
                (Eq.refl (n.add (b.add c)).succ) n_ih)
      a

example (a b c d : Nat) : (a + b) + (c + d) = ((a + c) + d) + b :=
  by simp only [Nat.add_eq, Nat.add_assoc] <;>
      exact
          Nat.rec (motive := fun t ↦ a.add (t.add (c.add d)) = a.add (c.add (d.add t)))
            (by
              simp only [Nat.zero_add, Nat.add_eq, Nat.add_zero] <;>
                exact Eq.refl (a.add (c.add d)))
            (fun n n_ih ↦ by
              simp only [Nat.add_succ, Nat.add_eq, Nat.succ_add] <;>
                exact
                    Eq.rec (motive := fun a_1 t ↦ (a.add (n.add (c.add d))).succ = a_1.succ)
                      (Eq.refl (a.add (n.add (c.add d))).succ) n_ih)
            b

example (a b c d e f g h : Nat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry

axiom pred : Nat → Nat
axiom pred_succ (n : Nat) : pred n.succ = n

example (a b : Nat) (h : a.succ = b.succ) : a = b :=
  by exact
    Eq.rec (motive := fun a t ↦ a = b) (pred_succ b)
      (Eq.rec (motive := fun a_1 t ↦ pred a_1 = a) (pred_succ a) h)

axiom is_zero : Nat → Prop
axiom is_zero_zero : is_zero 0 = True
axiom is_zero_succ (n : Nat) : is_zero n.succ = False

theorem succ_ne_zero (a : Nat) : a.succ ≠ 0 :=
  by exact fun a_1 ↦
    Eq.rec (motive := fun a t ↦ a) True.intro
      (Eq.rec (motive := fun a t ↦ a = False)
        (Eq.rec (motive := fun a_2 t ↦ is_zero a_2 = False) (is_zero_succ a) a_1) is_zero_zero)

example (m n : Nat) (h : m ≠ n) : m.succ ≠ n.succ := by exact fun a ↦ h (Nat.succ.inj a)

example : 20 + 20 = 40 := by exact Eq.refl 40

-- ADVANCED ADDITION WORLD

structure If (a b : Prop) : Prop where
  h : a → b


-- TODO
theorem add_right_cancel (a b n : Nat) : a + n = b + n → a = b :=
  by canonical +debug [If, Nat.succ.inj]

theorem add_left_cancel (a b n : Nat) : n + a = n + b → a = b :=
  by exact fun a_1 ↦
    add_right_cancel a b n
      (Eq.rec (motive := fun a_2 t ↦ a.add n = a_2)
        (Eq.rec (motive := fun a_2 t ↦ a_2 = n.add b) a_1 (add_comm n a)) (add_comm n b))

theorem add_left_eq_self (x y : Nat) : x + y = y → x = 0 :=
  by exact fun a ↦
    add_right_cancel x Nat.zero y (by simp only [Nat.zero_add, Nat.add_eq] <;> exact a)

theorem add_right_eq_self (x y : Nat) : x + y = x → y = 0 :=
  by exact fun a ↦
    add_left_eq_self y x (Eq.rec (motive := fun a t ↦ a = x) a (add_comm x y))

theorem add_right_eq_zero (a b : Nat) : a + b = 0 → a = 0 :=
  by exact fun a_1 ↦
    (Nat.rec (motive := fun t ↦ If (a.add t = Nat.zero) (a = Nat.zero)) { h := fun a ↦ a }
          (fun n n_ih ↦
            { h := fun a_2 ↦ False.rec (fun t ↦ a = Nat.zero) (succ_ne_zero (a.add n) a_2) })
          b).h
      a_1

theorem add_left_eq_zero (a b : Nat) : a + b = 0 → b = 0 :=
  by exact fun a_1 ↦
    add_right_eq_zero b a (Eq.rec (motive := fun a_2 t ↦ b.add a = a_2) (add_comm b a) a_1)

-- POWER WORLD

example : 0^0 = 1 := by exact Eq.refl Nat.zero.succ

example (n : Nat) : 0^n.succ = 0 := by exact Eq.refl Nat.zero

theorem pow_one (a : Nat) : a^1 = a := by
  exact by
    simp only [Nat.zero_add, Nat.pow_zero, Nat.zero_mul, Nat.add_eq, Nat.pow_succ, Nat.succ_mul,
        Nat.pow_eq, Nat.mul_eq] <;>
      exact Eq.refl a

theorem one_pow (n : Nat) : 1^n = 1 :=
  by exact
    Nat.rec (motive := fun t ↦ Nat.zero.succ.pow t = Nat.zero.succ) (Eq.refl Nat.zero.succ)
      (fun n n_ih ↦ by
        simp only [Nat.zero_add, Nat.mul_succ, Nat.add_eq, Nat.mul_zero, Nat.pow_succ, Nat.pow_eq,
            Nat.mul_eq] <;>
          exact n_ih)
      n

theorem pow_two (a : Nat) : a^2 = a * a :=
  by simp only [Nat.zero_add, Nat.pow_zero, Nat.zero_mul, Nat.add_eq, Nat.pow_succ, Nat.succ_mul,
        Nat.pow_eq, Nat.mul_eq] <;>
      exact Eq.refl (a.mul a)

theorem pow_add (a m n : Nat) : a^(m + n) = a^m * a^n :=
  by exact by simp only [Nat.pow_add, Nat.pow_eq] <;> exact Eq.refl ((a.pow m).mul (a.pow n))

theorem mul_pow (a b n : Nat) : (a * b)^n = a^n * b^n := by
  simp only [Nat.mul_pow, Nat.pow_eq] <;> exact Eq.refl ((a.pow n).mul (b.pow n))

theorem pow_pow (a m n : Nat) : (a^m)^n = a^(m * n) :=
  by exact
    Nat.rec (motive := fun t ↦ (a.pow m).pow t = a.pow (m.mul t)) (Eq.refl Nat.zero.succ)
      (fun n n_ih ↦ by
        simp only [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, Nat.pow_eq, Nat.mul_eq] <;>
          exact
              Eq.rec (motive := fun a_1 t ↦ ((a.pow m).pow n).mul (a.pow m) = a_1.mul (a.pow m))
                (Eq.refl (((a.pow m).pow n).mul (a.pow m))) n_ih)
      n

theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := sorry

axiom xyzzyAxiom (α : Sort) (synthetic := false) : α
theorem flt (a b c n : Nat) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) :=
  by exact fun a ↦ xyzzyAxiom False true

-- LEQ WORLD

example (x : Nat) : x ≤ x := by exact Nat.le.refl

theorem zero_le (x : Nat) : 0 ≤ x :=
  by exact
    Nat.rec (motive := fun t ↦ Nat.zero.le t)
      (by simp only [Nat.le_eq, Nat.le_zero_eq] <;> exact Eq.refl Nat.zero) (fun n n_ih ↦ Nat.le.step n_ih) x

example (x : Nat) : x ≤ x.succ :=
  by exact Nat.rec (motive := fun t ↦ t.le t.succ) (Nat.le.step Nat.le.refl)
      (fun n n_ih ↦ Nat.le.step Nat.le.refl) x

theorem le_trans (x y z : Nat) : x ≤ y → y ≤ z → x ≤ z :=
  by exact fun a a_1 ↦
    Nat.le.rec (motive := fun a t ↦ x.le a) a (fun {m} a a_ih ↦ Nat.le.step a_ih) a_1

theorem le_zero (x : Nat) : x ≤ 0 → x = 0 :=
  by exact fun a ↦
    (Nat.le.rec (motive := fun a t ↦ If (a = Nat.zero) (x = a)) { h := fun a ↦ Eq.refl x }
          (fun {m} a a_ih ↦ { h := fun a ↦ False.rec (fun t ↦ x = m.succ) (succ_ne_zero m a) }) a).h
      (Eq.refl Nat.zero)

theorem le_antisymm (x y : Nat) : x ≤ y → y ≤ x → x = y := sorry

example (x y : Nat) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 :=
  by exact Or.rec (motive := fun t ↦ y = 42 ∨ x = 37) (fun h ↦ Or.inr h) (fun h ↦ Or.inl h) h

theorem le_total (x y : Nat) : x ≤ y ∨ y ≤ x := sorry

theorem succ_le_succ (x y : Nat) : x.succ ≤ y.succ → x ≤ y :=
  by exact fun a ↦
    Exists.rec (motive := fun t ↦ x.le y)
      (fun w h ↦
        Nat.le.intro (Nat.succ.inj (Eq.rec (motive := fun a t ↦ a = y.succ) h (Nat.succ_add x w))))
      (Nat.le.dest a)

theorem le_one (x : Nat) : (x ≤ 1) → (x = 0 ∨ x = 1) := sorry

theorem le_two (x : Nat) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := sorry

-- ADVANCED MULTIPLICATION WORLD

theorem mul_le_mul_right (a b t : Nat) (h : a ≤ b) : a * t ≤ b * t :=
  by exact
    Exists.rec (motive := fun t_1 ↦ (a.mul t).le (b.mul t))
      (fun w h ↦
        Eq.rec (motive := fun a_1 t_1 ↦ (a.mul t).le (a_1.mul t))
          (Nat.le.intro
            (Eq.rec (motive := fun a_1 t_1 ↦ a_1 = (a.add w).mul t) (Eq.refl ((a.add w).mul t))
              (add_mul a w t)))
          h)
      (Nat.le.dest h)

theorem mul_left_ne_zero (a b : Nat) (h : a * b ≠ 0) : b ≠ 0 :=
  by exact fun a_1 ↦ h (Eq.rec (motive := fun a t ↦ a) (Eq.refl Nat.zero)
    (Eq.rec (motive := fun a_2 t ↦ (a.mul a_2 = a_2) = (a.mul b = a_2)) (Eq.refl (a.mul b = b)) a_1))

theorem eq_succ_of_ne_zero (a : Nat) (ha : a ≠ 0) : ∃ n, a = Nat.succ n :=
  by exact
    (Nat.rec (motive := fun t ↦ If (a = t) (∃ a, t = a.succ))
          { h := fun a ↦ False.rec (fun t ↦ ∃ a, Nat.zero = Nat.succ a) (ha a) }
          (fun n n_ih ↦ { h := fun a ↦ Exists.intro n (Eq.refl n.succ) }) a).h
      (Eq.refl a)

theorem one_le_of_ne_zero (a : Nat) (ha : a ≠ 0) : 1 ≤ a :=
  by exact Exists.rec (motive := fun t ↦ Nat.zero.succ.le a)
      (fun w h ↦ Eq.rec (motive := fun a t ↦ Nat.zero.succ.le a)
        (Nat.rec (motive := fun t ↦ Nat.zero.succ.le t.succ) Nat.le.refl
          (fun n n_ih ↦ Nat.le.step n_ih) w)
        (Eq.rec (motive := fun a_1 t ↦ a_1 = a) (Eq.refl a) h))
      (eq_succ_of_ne_zero a fun a ↦ ha a)

theorem le_mul_right (a b : Nat) (h : a * b ≠ 0) : a ≤ (a * b) := sorry

theorem mul_right_eq_one (x y : Nat) (h : x * y = 1) : x = 1 := sorry

theorem mul_ne_zero (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := sorry

theorem mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 :=
  by exact Classical.byContradiction fun a_1 ↦
    mul_ne_zero a b (fun a_2 ↦ a_1 (Or.inl a_2)) (fun a_2 ↦ a_1 (Or.inr a_2)) h

theorem mul_left_cancel (a b c : Nat) (ha : a ≠ 0) (h : a * b = a * c) : b = c := sorry

theorem mul_right_eq_self (a b : Nat) (ha : a ≠ 0) (h : a * b = a) : b = 1 :=
  by exact Eq.rec (motive := fun a t ↦ a = Nat.zero.succ) (Eq.refl Nat.zero.succ)
      (mul_left_cancel a Nat.zero.succ b (fun a ↦ ha a)
        (Eq.rec (motive := fun a_1 t ↦ Nat.zero.add a_1 = a.mul b) (mul_one (a.mul b)) h))
