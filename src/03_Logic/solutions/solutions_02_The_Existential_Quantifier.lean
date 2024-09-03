import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

section
variables {f g : ℝ → ℝ}

theorem solutions_02_The_Existential_Quantifier_1 (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  intro x,
  exact add_le_add (lbfa x) (lbgb x)
end

theorem solutions_02_The_Existential_Quantifier_2 {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a lbfa,
  use c * a,
  intro x,
  exact mul_le_mul_of_nonneg_left (lbfa x) h
end

end

section
variables {a b c : ℕ}

theorem solutions_02_The_Existential_Quantifier_3 (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divbc with ⟨e, rfl⟩,
  use (d * e), ring
end

theorem solutions_02_The_Existential_Quantifier_4 (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use (d + e), ring
end

end

section
open function

theorem solutions_02_The_Existential_Quantifier_5 {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  dsimp, rw [mul_div_cancel' _ h]
end

theorem solutions_02_The_Existential_Quantifier_6 {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  field_simp [h], ring
end

end

section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

theorem solutions_02_The_Existential_Quantifier_7 (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro z,
  rcases surjg z with ⟨y, rfl⟩,
  rcases surjf y with ⟨x, rfl⟩,
  use [x, rfl]
end

end
