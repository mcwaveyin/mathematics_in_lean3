import data.real.basic

section
variables a b c d : ℝ

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

theorem 04_More_on_Order_and_Divisibility_1 : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

theorem 04_More_on_Order_and_Divisibility_2 : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

theorem 04_More_on_Order_and_Divisibility_3 : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

theorem 04_More_on_Order_and_Divisibility_4 : max a b = max b a :=
sorry

theorem 04_More_on_Order_and_Divisibility_5 : min (min a b) c = min a (min b c) :=
sorry

lemma aux : min a b + c ≤ min (a + c) (b + c) :=
sorry

theorem 04_More_on_Order_and_Divisibility_6 : min a b + c = min (a + c) (b + c) :=
sorry

#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

theorem 04_More_on_Order_and_Divisibility_7 : abs a - abs b ≤ abs (a - b) :=
sorry

end

section
variables w x y z : ℕ

theorem 04_More_on_Order_and_Divisibility_8 (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

theorem 04_More_on_Order_and_Divisibility_9 : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

theorem 04_More_on_Order_and_Divisibility_10 : x ∣ x^2 :=
by apply dvd_mul_right

theorem 04_More_on_Order_and_Divisibility_11 (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
sorry

end

section
variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)

theorem 04_More_on_Order_and_Divisibility_12 : gcd m n = gcd n m :=
sorry

end
