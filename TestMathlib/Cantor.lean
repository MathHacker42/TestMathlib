
import Mathlib.Algebra.Algebra.Operations

import Mathlib.Data.Set.Basic

theorem cantor_surjective {α} (f : α → Set α) : ¬Function.Surjective f := by
  rw [Function.Surjective]
  simp
  use {z : α | z ∉ f z}
  intro y
  rw [Set.ext_iff]
  simp
  use y
  rw [iff_comm]
  exact not_iff_self

#print axioms cantor_surjective

theorem cantor_surjective_constructive {α} (f : α → Set α) : ¬Function.Surjective f := by
  intro h1
  obtain ⟨a, h2⟩ := h1 {z | z ∉ f z}
  exact iff_not_self ((Set.ext_iff.mp h2) a)

#print axioms cantor_surjective_constructive

theorem cantor_surjective_constructive_2 {α} (f : α → Set α) : ¬Function.Surjective f := by
  intro h1
  obtain ⟨a, h2⟩ := h1 {z | z ∉ f z}
  have h3 : a ∈ f a ↔ a ∉ f a := by
    nth_rewrite 1 [h2]
    rw [Set.mem_setOf]
  exact iff_not_self h3

#print axioms cantor_surjective_constructive_2

theorem cantor_surjective_constructive_3 {α} (f : α → Set α) : ¬Function.Surjective f := by
  intro h1
  obtain ⟨a, h2⟩ := h1 {z | z ∉ f z}
  have h3 : a ∈ {z | z ∉ f z} ↔ a ∉ f a := Set.mem_setOf
  rw [←h2] at h3
  exact iff_not_self h3

#print axioms cantor_surjective_constructive_3

theorem cantor_surjective_constructive_4 {α} (f : α → Set α) : ¬Function.Surjective f := by
  intro h1
  obtain ⟨a, h2⟩ := h1 {z | z ∉ f z}
  apply @iff_not_self (a ∈ f a)
  nth_rewrite 1 [h2]
  rfl

#print axioms cantor_surjective_constructive_4

lemma ImpImp {p q : Prop} : (p → (p → q)) → (p → q) := by
  intro h hp
  exact (h hp) hp

lemma IffImp {p q : Prop} : (p ↔ (p → q)) → q := by
  intro ⟨h1, h2⟩
  have hpq := ImpImp h1
  exact hpq (h2 hpq)

lemma IffNotSelf {p : Prop} : ¬ (p ↔ ¬ p) := IffImp
