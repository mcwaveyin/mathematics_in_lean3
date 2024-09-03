import data.real.basic

section
variables {x y : ℝ}

theorem 05_Disjunction_1 (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

theorem 05_Disjunction_2 (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

theorem 05_Disjunction_3 (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

theorem 05_Disjunction_4 (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

theorem 05_Disjunction_5 : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
sorry

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
sorry

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
sorry

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
sorry

end my_abs
end

theorem 05_Disjunction_6 {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

theorem 05_Disjunction_7 {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

theorem 05_Disjunction_8 {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
sorry

theorem 05_Disjunction_9 {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

theorem 05_Disjunction_10 {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

theorem 05_Disjunction_11 (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

theorem 05_Disjunction_12 (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

end

theorem 05_Disjunction_13 (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

theorem 05_Disjunction_14 (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

theorem 05_Disjunction_15 (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
sorry

end