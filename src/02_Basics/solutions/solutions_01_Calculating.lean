import data.real.basic

theorem solutions_01_Calculating_1 (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc b c a,
  rw mul_comm c a
end

theorem solutions_01_Calculating_2 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc a b c,
  rw mul_comm a b,
  rw mul_assoc b a c
end

theorem solutions_01_Calculating_3 (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc
end

theorem solutions_01_Calculating_4 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc,
  rw mul_comm a,
  rw mul_assoc
end

theorem solutions_01_Calculating_5 (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a,
  rw h,
  rw ←mul_assoc
end

theorem solutions_01_Calculating_6 (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw hyp',
  rw mul_comm,
  rw sub_self
end

