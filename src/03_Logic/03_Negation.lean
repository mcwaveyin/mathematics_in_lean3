import data.real.basic

section
variables a b : ℝ

theorem 03_Negation_1 (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

theorem 03_Negation_2 (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

theorem 03_Negation_3 (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
sorry

theorem 03_Negation_4 : ¬ fn_has_ub (λ x, x) :=
sorry

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

theorem 03_Negation_5 (h : monotone f) (h' : f a < f b) : a < b :=
sorry

theorem 03_Negation_6 (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
sorry

theorem 03_Negation_7 :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  { sorry },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  sorry
end

theorem 03_Negation_8 (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
sorry

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

theorem 03_Negation_9 (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
sorry

theorem 03_Negation_10 (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
sorry

theorem 03_Negation_11 (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
sorry

theorem 03_Negation_12 (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
sorry

open_locale classical

theorem 03_Negation_13 (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

theorem 03_Negation_14 (h : ¬ ¬ Q) : Q :=
sorry

theorem 03_Negation_15 (h : Q) : ¬ ¬ Q :=
sorry

end

open_locale classical
section
variable (f : ℝ → ℝ)

theorem 03_Negation_16 (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
sorry

theorem 03_Negation_17 (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

theorem 03_Negation_18 (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

theorem 03_Negation_19 (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
sorry

theorem 03_Negation_20 (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

theorem 03_Negation_21 (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

theorem 03_Negation_22 (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

theorem 03_Negation_23 (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

theorem 03_Negation_24 (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end

end

