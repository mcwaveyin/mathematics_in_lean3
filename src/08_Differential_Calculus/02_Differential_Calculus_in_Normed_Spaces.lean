import analysis.normed_space.banach_steinhaus
import analysis.normed_space.finite_dimension

import analysis.calculus.inverse

open set filter
open_locale topology filter

noncomputable theory

section
variables {E : Type*} [normed_add_comm_group E]

theorem 02_Differential_Calculus_in_Normed_Spaces_1 (x : E) : 0 ≤ ‖x‖ :=
norm_nonneg x

theorem 02_Differential_Calculus_in_Normed_Spaces_2 {x : E} : ‖x‖ = 0 ↔ x = 0 :=
norm_eq_zero

theorem 02_Differential_Calculus_in_Normed_Spaces_3 (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
norm_add_le x y

theorem 02_Differential_Calculus_in_Normed_Spaces_4 : metric_space E := by apply_instance

theorem 02_Differential_Calculus_in_Normed_Spaces_5 {X : Type*} [topological_space X] {f : X → E} (hf : continuous f) :
  continuous (λ x, ‖f x‖) :=
hf.norm

variables [normed_space ℝ E]

theorem 02_Differential_Calculus_in_Normed_Spaces_6 (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
norm_smul a x

theorem 02_Differential_Calculus_in_Normed_Spaces_7 [finite_dimensional ℝ E] : complete_space E :=
by apply_instance

theorem 02_Differential_Calculus_in_Normed_Spaces_8 (𝕜 : Type*) [nontrivially_normed_field 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
norm_mul x y

theorem 02_Differential_Calculus_in_Normed_Spaces_9 (𝕜 : Type*) [nontrivially_normed_field 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
normed_field.exists_one_lt_norm 𝕜

theorem 02_Differential_Calculus_in_Normed_Spaces_10 (𝕜 : Type*) [nontrivially_normed_field 𝕜] (E : Type*) [normed_add_comm_group E]
  [normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E] : complete_space E :=
finite_dimensional.complete 𝕜 E

end

section
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
          {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

theorem 02_Differential_Calculus_in_Normed_Spaces_11 : E →L[𝕜] E := continuous_linear_map.id 𝕜 E

theorem 02_Differential_Calculus_in_Normed_Spaces_12 (f : E →L[𝕜] F) : E → F :=
f

theorem 02_Differential_Calculus_in_Normed_Spaces_13 (f : E →L[𝕜] F) : continuous f :=
f.cont

theorem 02_Differential_Calculus_in_Normed_Spaces_14 (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
f.map_add x y

theorem 02_Differential_Calculus_in_Normed_Spaces_15 (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
f.map_smul a x

variables (f : E →L[𝕜] F)

theorem 02_Differential_Calculus_in_Normed_Spaces_16 (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
f.le_op_norm x

theorem 02_Differential_Calculus_in_Normed_Spaces_17 {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
  ‖f‖ ≤ M :=
f.op_norm_le_bound hMp hM

end

section
variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

open metric

theorem 02_Differential_Calculus_in_Normed_Spaces_18 {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
  (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
  ∃ C', ∀ i, ‖g i‖ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n` -/
  let e : ℕ → set E := λ n, ⋂ i : ι, { x : E | ‖g i x‖ ≤ n },
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n),
  sorry,
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  sorry,
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
     `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry,
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry,
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ‖g i z‖ ≤ m,
  sorry,
  have εk_pos : 0 < ε / ‖k‖ := sorry,
  refine ⟨(m + m : ℕ) / (ε / ‖k‖),
           λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  sorry,
  sorry
end

end

open asymptotics
open_locale asymptotics

theorem 02_Differential_Calculus_in_Normed_Spaces_19 {α : Type*} {E : Type*}
  [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  is_O_with c l f g ↔ ∀ᶠ x in l, ‖ f x ‖ ≤ c * ‖ g x ‖ :=
is_O_with_iff

theorem 02_Differential_Calculus_in_Normed_Spaces_20 {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  f =O[l] g ↔ ∃ C, is_O_with C l f g :=
is_O_iff_is_O_with

theorem 02_Differential_Calculus_in_Normed_Spaces_21 {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  f =o[l] g ↔ ∀ C > 0, is_O_with C l f g :=
is_o_iff_forall_is_O_with

theorem 02_Differential_Calculus_in_Normed_Spaces_22 {α : Type*} {E : Type*} [normed_add_comm_group E]
    (c : ℝ) (l : filter α) (f g : α → E) :
  f ~[l] g ↔ (f - g) =o[l] g :=
iff.rfl

section
variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

theorem 02_Differential_Calculus_in_Normed_Spaces_23 (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
  has_fderiv_at f f' x₀ ↔ (λ x, f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] (λ x, x - x₀) :=
iff.rfl

theorem 02_Differential_Calculus_in_Normed_Spaces_24 (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : has_fderiv_at f f' x₀) :
  fderiv 𝕜 f x₀ = f' :=
hff'.fderiv

theorem 02_Differential_Calculus_in_Normed_Spaces_25 (n : ℕ) (f : E → F) : E → (E [×n]→L[𝕜] F) :=
iterated_fderiv 𝕜 n f

theorem 02_Differential_Calculus_in_Normed_Spaces_26 (n : with_top ℕ) {f : E → F} :
  cont_diff 𝕜 n f ↔
    (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
cont_diff_iff_continuous_differentiable

theorem 02_Differential_Calculus_in_Normed_Spaces_27 {𝕂 : Type*} [is_R_or_C 𝕂] {E : Type*} [normed_add_comm_group E] [normed_space 𝕂 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕂 F]
  {f : E → F} {x : E} {n : with_top ℕ}
  (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
hf.has_strict_fderiv_at hn

section local_inverse
variables [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem 02_Differential_Calculus_in_Normed_Spaces_28 (hf : has_strict_fderiv_at f ↑f' a) : F → E :=
has_strict_fderiv_at.local_inverse f f' a hf

theorem 02_Differential_Calculus_in_Normed_Spaces_29  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 a, hf.local_inverse f f' a (f x) = x :=
hf.eventually_left_inverse

theorem 02_Differential_Calculus_in_Normed_Spaces_30  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 (f a), f (hf.local_inverse f f' a x) = x :=
hf.eventually_right_inverse

theorem 02_Differential_Calculus_in_Normed_Spaces_31 [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : has_strict_fderiv_at f ↑f' a) :
  has_strict_fderiv_at (has_strict_fderiv_at.local_inverse f f' a hf)
    (f'.symm : F →L[𝕜] E) (f a) :=
has_strict_fderiv_at.to_local_inverse hf

end local_inverse

#check has_fderiv_within_at
#check has_fderiv_at_filter

end