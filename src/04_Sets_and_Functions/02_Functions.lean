import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

theorem 02_Functions_1 : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

theorem 02_Functions_2 : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

theorem 02_Functions_3 : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

theorem 02_Functions_4 : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
sorry

theorem 02_Functions_5 (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
sorry

theorem 02_Functions_6 : f '' (f⁻¹' u) ⊆ u :=
sorry

theorem 02_Functions_7 (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
sorry

theorem 02_Functions_8 (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

theorem 02_Functions_9 (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

theorem 02_Functions_10 : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

theorem 02_Functions_11 : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

theorem 02_Functions_12 (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

theorem 02_Functions_13 : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

theorem 02_Functions_14 : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

theorem 02_Functions_15 : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

theorem 02_Functions_16 : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

theorem 02_Functions_17 : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

theorem 02_Functions_18 : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

variables {I : Type*} (A : I → set α) (B : I → set β)

theorem 02_Functions_19 : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

theorem 02_Functions_20 : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

theorem 02_Functions_21 (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

theorem 02_Functions_22 : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

theorem 02_Functions_23 : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

theorem 02_Functions_24 : inj_on f s ↔
  ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
iff.refl _

end

section
open set real

theorem 02_Functions_25 : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro e,   -- log x = log y
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y           : by rw exp_log ypos
end

theorem 02_Functions_26 : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  intro ypos,
  use log y,
  rw exp_log ypos
end

theorem 02_Functions_27 : inj_on sqrt { x | x ≥ 0 } :=
sorry

theorem 02_Functions_28 : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
sorry

theorem 02_Functions_29 : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
sorry

theorem 02_Functions_30 : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
sorry

end

section
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

theorem 02_Functions_31 : P (classical.some h) := classical.some_spec h

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

theorem 02_Functions_32 : injective f ↔ left_inverse (inverse f) f  :=
sorry

theorem 02_Functions_33 : surjective f ↔ right_inverse (inverse f) f :=
sorry

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    sorry,
  have h₃ : j ∉ S,
    sorry,
  contradiction
end

end
