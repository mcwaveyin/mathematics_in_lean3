import data.real.basic

/- An example. -/

import data.real.basic
theorem 01_Calculating_1 (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c
end

/- Try these.-/

theorem 01_Calculating_2 (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  sorry
end

theorem 01_Calculating_3 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry
end

/- An example. -/

theorem 01_Calculating_4 (a b c : ℝ) : a * b * c = b * c * a :=
begin
  rw mul_assoc,
  rw mul_comm
end

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/

theorem 01_Calculating_5 (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  sorry
end

theorem 01_Calculating_6 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry
end

/- Using facts from the local context. -/

theorem 01_Calculating_7 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc
end

/- Try these. For the second one, use the theorem `sub_self`. -/

theorem 01_Calculating_8 (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  sorry
end

theorem 01_Calculating_9 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  sorry
end

/- Examples. -/

theorem 01_Calculating_10 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

section

variables a b c d e f g : ℝ

theorem 01_Calculating_11 (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
by rw [h', ←mul_assoc, h, mul_assoc]

end

section
variables a b c : ℝ

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check @mul_comm

end

section
variables a b : ℝ

theorem 01_Calculating_12 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul]
end

theorem 01_Calculating_13 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]


theorem 01_Calculating_14 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      sorry
    end
  ... = a * a + (b * a + a * b) + b * b : by sorry
  ... = a * a + 2 * (a * b) + b * b     : by sorry
end

/- Try these. For the second, use the theorems listed underneath. -/

section
variables a b c d : ℝ

theorem 01_Calculating_15 : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
sorry

theorem 01_Calculating_16 (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin
  sorry
end

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

/- Examples. -/

section
variables a b c d : ℝ

theorem 01_Calculating_17 (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a * d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp
end

theorem 01_Calculating_18 : (c * b) * a = b * (a * c) :=
by ring

theorem 01_Calculating_19 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

theorem 01_Calculating_20 : (a + b) * (a - b) = a^2 - b^2 :=
by ring

theorem 01_Calculating_21 (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end

end

theorem 01_Calculating_22 (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c :=
begin
  nth_rewrite 1 h,
  rw add_mul
end

