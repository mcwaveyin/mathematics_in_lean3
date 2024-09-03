import data.real.basic
import data.nat.prime_norm_num

theorem 04_Conjunction_and_Bi-implication_1 {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h
end

theorem 04_Conjunction_and_Bi-implication_2 {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

theorem 04_Conjunction_and_Bi-implication_3 {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end

theorem 04_Conjunction_and_Bi-implication_4 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁
end

theorem 04_Conjunction_and_Bi-implication_5 {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h')
end

theorem 04_Conjunction_and_Bi-implication_6 {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

theorem 04_Conjunction_and_Bi-implication_7 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h'
end

theorem 04_Conjunction_and_Bi-implication_8 {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

theorem 04_Conjunction_and_Bi-implication_9 {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
sorry

theorem 04_Conjunction_and_Bi-implication_10 : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨5/2, by norm_num, by norm_num⟩

theorem 04_Conjunction_and_Bi-implication_11 (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty
end

theorem 04_Conjunction_and_Bi-implication_12 (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty

theorem 04_Conjunction_and_Bi-implication_13 : ∃ x : ℝ, 2 < x ∧ x < 4 :=
begin
  use 5 / 2,
  split; norm_num
end

theorem 04_Conjunction_and_Bi-implication_14 : ∃ m n : ℕ,
  4 < m ∧ m < n ∧ n < 10 ∧ nat.prime m ∧ nat.prime n :=
begin
  use [5, 7],
  norm_num
end

theorem 04_Conjunction_and_Bi-implication_15 {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩,
  use [h₀, λ h', h₁ (le_antisymm h₀ h')]
end

theorem 04_Conjunction_and_Bi-implication_16 {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h
end

theorem 04_Conjunction_and_Bi-implication_17 {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩

theorem 04_Conjunction_and_Bi-implication_18 {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
sorry

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { sorry },
  exact pow_eq_zero h'
end

theorem 04_Conjunction_and_Bi-implication_19 (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
sorry

section

theorem 04_Conjunction_and_Bi-implication_20 (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

theorem 04_Conjunction_and_Bi-implication_21 : 3 ∣ nat.gcd 6 15 :=
begin
  rw nat.dvd_gcd_iff,
  split; norm_num
end

end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

theorem 04_Conjunction_and_Bi-implication_22 : ¬ monotone (λ x : ℝ, -x) :=
sorry

section
variables {α : Type*} [partial_order α]
variables a b : α

theorem 04_Conjunction_and_Bi-implication_23 : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  sorry
end

end

section
variables {α : Type*} [preorder α]
variables a b c : α

theorem 04_Conjunction_and_Bi-implication_24 : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  sorry
end

theorem 04_Conjunction_and_Bi-implication_25 : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  sorry
end

end
