import analysis.special_functions.log.basic

variables a b c d e : ℝ
open real

theorem solutions_03_Using_Theorems_and_Lemmas_1 (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
begin
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁,
  exact lt_of_le_of_lt h₂ h₃
end

theorem solutions_03_Using_Theorems_and_Lemmas_2 (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add_left,
  rw exp_le_exp,
  apply add_le_add_left h₀
end

-- an alternative using `linarith`.
theorem solutions_03_Using_Theorems_and_Lemmas_3 (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  have : exp (a + d) ≤ exp (a + e),
  { rw exp_le_exp, linarith },
  linarith [this]
end

theorem solutions_03_Using_Theorems_and_Lemmas_4 (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { linarith [exp_pos a]},
  have h₁ : 0 < 1 + exp b,
  { linarith [exp_pos b] },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add_left (exp_le_exp.mpr h),
end

-- SOLUTION.
theorem solutions_03_Using_Theorems_and_Lemmas_5 (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  apply sub_le_sub_left,
  exact exp_le_exp.mpr h
end

-- alternatively:
theorem solutions_03_Using_Theorems_and_Lemmas_6 (h : a ≤ b) : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

theorem fact1 : a*b*2 ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith
end

theorem fact2 : -(a*b)*2 ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 + 2*a*b + b^2,
  calc
    a^2 + 2*a*b + b^2 = (a + b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith
end

theorem solutions_03_Using_Theorems_and_Lemmas_7 : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  have h : (0 : ℝ) < 2,
  { norm_num },
  apply abs_le'.mpr,
  split,
  { rw le_div_iff h,
    apply fact1 },
  rw le_div_iff h,
  apply fact2,
end
