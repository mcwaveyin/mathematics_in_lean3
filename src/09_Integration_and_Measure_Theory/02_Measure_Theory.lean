import analysis.normed_space.finite_dimension
import analysis.convolution
import measure_theory.function.jacobian
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue

open set filter
open_locale topological_space filter ennreal
noncomputable theory

variables {α : Type*} [measurable_space α]

theorem 02_Measure_Theory_1 : measurable_set (∅ : set α) := measurable_set.empty

theorem 02_Measure_Theory_2 : measurable_set (univ : set α) := measurable_set.univ

theorem 02_Measure_Theory_3 {s : set α} (hs : measurable_set s) : measurable_set sᶜ :=
hs.compl

theorem 02_Measure_Theory_4 : encodable ℕ :=
by apply_instance

theorem 02_Measure_Theory_5 (n : ℕ) : encodable (fin n) :=
by apply_instance

variables {ι : Type*} [encodable ι]

theorem 02_Measure_Theory_6 {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
measurable_set.Union h

theorem 02_Measure_Theory_7 {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.Inter h

open measure_theory

variables {μ : measure α}

theorem 02_Measure_Theory_8 (s : set α) : μ s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), μ t :=
measure_eq_infi s

theorem 02_Measure_Theory_9  (s : ι → set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
measure_Union_le s

theorem 02_Measure_Theory_10 {f : ℕ → set α}
    (hmeas : ∀ i, measurable_set (f i)) (hdis : pairwise (disjoint on f)) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
μ.m_Union hmeas hdis

theorem 02_Measure_Theory_11 {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
iff.rfl
