import data.set.lattice
import data.nat.prime
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

theorem 01_Sets_1 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

theorem 01_Sets_2 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_iff] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

theorem 01_Sets_3 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

theorem 01_Sets_4 (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

theorem 01_Sets_5 : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

theorem 01_Sets_6 : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

theorem 01_Sets_7 : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
sorry

theorem 01_Sets_8 : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

theorem 01_Sets_9 : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

theorem 01_Sets_10 : s \ (t ∪ u) ⊆ s \ t \ u :=
sorry

theorem 01_Sets_11 : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_iff],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

theorem 01_Sets_12 : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

theorem 01_Sets_13 : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

theorem 01_Sets_14 : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

theorem 01_Sets_15 : s ∩ t = t ∩ s :=
subset.antisymm sorry sorry

theorem 01_Sets_16 : s ∩ (s ∪ t) = s :=
sorry

theorem 01_Sets_17 : s ∪ (s ∩ t) = s :=
sorry

theorem 01_Sets_18 : (s \ t) ∪ t = s ∪ t :=
sorry

theorem 01_Sets_19 : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
sorry


def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

theorem 01_Sets_20 : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

theorem 01_Sets_21 (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

theorem 01_Sets_22 (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

theorem 01_Sets_23 : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
sorry

#print prime
#print nat.prime

theorem 01_Sets_24 (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm

theorem 01_Sets_25 (n : ℕ) (h : prime n) : nat.prime n :=
by { rw nat.prime_iff, exact h }

theorem 01_Sets_26 (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff

end
section
variables (s t : set ℕ)

theorem 01_Sets_27 (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

theorem 01_Sets_28 (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

theorem 01_Sets_29 (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
sorry

theorem 01_Sets_30 (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
sorry

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

theorem 01_Sets_31 : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_iff, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

theorem 01_Sets_32 : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_iff, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

open_locale classical

theorem 01_Sets_33 : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
sorry

def primes : set ℕ := {x | nat.prime x}

theorem 01_Sets_34 : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_Union₂, refl }

theorem 01_Sets_35 : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

theorem 01_Sets_36 : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1} :=
begin
  intro x,
  contrapose!,
  simp,
  apply nat.exists_prime_and_dvd
end

theorem 01_Sets_37 : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
sorry

end

section
open set

variables {α : Type*} (s : set (set α))

theorem 01_Sets_38 : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_Union₂,
  refl
end

theorem 01_Sets_39 : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_Inter₂,
  refl
end

end

