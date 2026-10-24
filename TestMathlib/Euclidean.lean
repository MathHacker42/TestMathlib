import Mathlib.RingTheory.Ideal.Maps

variable {ι R : Type}

variable (ι) in
class WO where
  le : ι → ι → Prop
  wo : ∀ S : Set ι, (∀ x ∈ S, False) ∨ (∃ x ∈ S, ∀ y ∈ S, le x y)

def WOPreimage (wo : WO ι) (f : R → ι) : WO R := {
    le := fun x y ↦ wo.le (f x) (f y)
    wo := by
      intro S
      rcases wo.wo {f x | x ∈ S} with he | hm
      · left
        intro x hx
        apply he (f x)
        rw [Set.mem_setOf_eq]
        use x
      · obtain ⟨i, hi⟩ := hm
        simp at hi
        obtain ⟨⟨x, hx, hi⟩, hs⟩ := hi
        right
        use x
        simp [hx]
        intro y hy
        rw [hi]
        exact hs y hy
  }

#print axioms WOPreimage

variable [CommRing R]

variable (R) in
class Euclidean extends WO R where
  da : ∀ x d : R, ∃ n r : R, x = d * n + r ∧ le r d ∧ ¬ (le d r)

variable [ed : Euclidean R]

-- theorem EDisPID : IsPrincipalIdealRing R := {

-- }

instance : IsPrincipalIdealRing R := {
  principal := by
    intro I
    rcases ed.wo (I \ {0}) with he | hm
    · use 0
      ext x
      apply Iff.intro
      · intro hx

        sorry
      ·
        sorry
    ·
      sorry
}
