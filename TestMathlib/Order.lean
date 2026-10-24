import Mathlib.Algebra.Algebra.Operations

variable {O : Type} (r : O → O → Prop) (S : Set O)

-- def PreservedInSubsets (OrderCondition : (O → O → Prop) → Set O → Prop) :=

def ReflexiveOn := ∀ x ∈ S, r x x

def TotalOn := ∀ x ∈ S, ∀ y ∈ S, r x y ∨ r y x

lemma TotalOnIff : TotalOn r S = (S ≤ {x : O | ∀ y ∈ S, r x y ∨ r y x}) := by rfl

def WellOrderedOn := ∀ T : Set O, T ≤ S → Nonempty T → ∃ m ∈ T, ∀ t ∈ T, r m t

variable {r} {S}

lemma SubsetReflexiveOn {T : Set O} (hts : T ≤ S) (h : ReflexiveOn r S) : ReflexiveOn r T := by
  intro x hx
  apply h
  exact hts hx

lemma SubsetTotalOn {T : Set O} (hts : T ≤ S) (h : TotalOn r S) : TotalOn r T := by
  intro x hx y hy
  apply h
  · exact hts hx
  · exact hts hy

lemma DirectedOnIfReflexiveAndTotalOn (hr : ReflexiveOn r S) (ht : TotalOn r S) :
  DirectedOn r S := by
  intro x hx y hy
  rcases ht x hx y hy with hxy | hyx
  · use y
    simp [*]
    apply hr
    exact hy
  · use x
    simp [*]
    apply hr
    exact hx

-- class WellOrderedOn : Prop where
--   reflexive : ∀ a ∈ S, r a a
--   well_ordered : ∀ T : Set O, T ≤ S → Nonempty T → ∃ m ∈ T, ∀ t ∈ T, r m t

-- lemma SubsetWellOrderedOn {T : Set O} (hts : T ≤ S) (hwo : WellOrderedOn r S) :
--   WellOrderedOn r T where
--   reflexive := by
--     intro a ha
--     exact hwo.reflexive a (hts ha)
--   well_ordered := by
--     intro U hut
--     exact hwo.well_ordered U (le_trans hut hts)

-- lemma DirectedOnIfWellOrderedOn (hwo : WellOrderedOn r S) : DirectedOn r S := by
--   intro x hx y hy
--   obtain ⟨hr, hw⟩ := hwo
--   have h1 := hw {x, y}
--   have h2 : {x, y} ≤ S := by
--     intro z hz
--     rcases hz with hzx | hzy
--     · rw [hzx]
--       exact hx
--     · rw [hzy]
--       exact hy
--   have h3 := h1 h2
--   simp at h3
--   rcases h3 with hx | hy
--   · use y
--     simp [*]
--   · use x
--     simp [*]

variable {X Y : Type}

def PreOrderPreimage [Preorder Y] (f : X → Y) : Preorder X where
  le := fun a b ↦ f a ≤ f b
  le_refl := by
    intro a
    exact le_refl (f a)
  le_trans := by
    intro a b c hab hbc
    exact le_trans hab hbc

-- def PartialOrderPreimage [PartialOrder Y] [LE X] (f : X → Y)
--   (hle : ∀ a b : X, a ≤ b ↔ f a ≤ f b) (hf : Function.Injective f) :
--   PartialOrder X where
--   le_refl (a : X) := by
--     rw [hle]
--   le_trans (a b c : X) := by
--     repeat rw [hle]
--     exact le_trans
--   le_antisymm (a b: X) := by
--     repeat rw [hle]
--     intro hab hba
--     exact hf (le_antisymm hab hba)

variable {A : Type} [SetLike X A]

@[ext] theorem ext {p q : X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h


-- variable (X) in
-- def SetLikePO : PartialOrder X := {
--   le_antisymm := by
--     intro a b hab hba
--     ext c
--     apply Iff.intro
--     · intro hc
--       exact hab hc
--     · intro hc
--       exact hba hc
-- }

-- #print axioms SetLikePO

instance bazo : PartialOrder X := {
  le_antisymm := by
    intro a b hab hba
    ext c
    apply Iff.intro
    · intro hc
      exact hab hc
    · intro hc
      exact hba hc
}

#print axioms bazo

lemma LeIff {p q : X} : p ≤ q ↔ (p : Set A) ≤ (q : Set A) := by rfl

#print axioms LeIff
-- #print axioms InfSet
-- #print axioms SetLike
-- #print axioms CompleteSemilatticeInf
-- #print axioms CompleteLattice

-- instance lkk : Preorder (Set A) := {
--   le_refl := sorry
--   le_trans := sorry
--   lt := sorry
--   lt_iff_le_not_ge := sorry
-- }

-- #print axioms lkk

-- def SetLe (S T : Set A) := S < T

-- #print axioms SetLe

-- instance bwi : CompleteSemilatticeInf (Set A) := {
--   sInf := sorry
--   sInf_le := sorry
--   le_sInf := sorry
-- }

-- #print axioms bwi

def SetLikeLattice {L : Type} [SetLike L A] [InfSet L]
  (h : ∀ S : Set L, ↑(sInf S) = {a : A | ∀ s ∈ S, a ∈ s})
  : CompleteSemilatticeInf L := {
    sInf_le := by
      intro S a ha
      rw [LeIff, h S]
      intro x hx
      simp at hx
      apply hx
      exact ha
    le_sInf := by
      intro S a ha
      rw [LeIff, h S]
      intro x hx
      simp
      intro b hb
      exact ha b hb hx
  }

-- def SetLikeLattice {L : Type} [SetLike L A] [InfSet L]
--   (h : ∀ S : Set L, ↑(sInf S) = sInf {(a : Set A) | a ∈ S})
--   : CompleteSemilatticeInf L := {
--     sInf_le := by
--       intro S a ha
--       rw [LeIff, h S]
--       apply sInf_le
--       simp
--       exact ha
--     le_sInf := by
--       intro S a ha
--       rw [LeIff, h S]
--       apply le_sInf
--       simp
--       exact ha
--   }

#print axioms SetLikeLattice

variable {L : Type} [CompleteSemilatticeInf L]

instance : CompleteSemilatticeSup L := {
  sSup (S : Set L) := sInf {a : L | ∀ s ∈ S, s ≤ a}
  le_sSup := by
    intro S a ha
    apply le_sInf
    simp
    intro b hb
    exact hb a ha
  sSup_le := by
    intro S a ha
    apply sInf_le
    simp
    intro b hb
    exact ha b hb
}

def CompleteLatticeFromInf : CompleteLattice L := {
  top := sInf {}
  le_top (a : L) := by
    apply le_sInf
    simp
  bot := sSup {}
  bot_le (a : L) := by
    apply sSup_le
    simp
  sup (a b : L) := sSup {a, b}
  le_sup_left (a b : L) := by
    apply le_sSup
    simp
  le_sup_right (a b : L) := by
    apply le_sSup
    simp
  sup_le (a b c : L) := by
    intro hac hbc
    apply sSup_le
    simp
    exact And.intro hac hbc
  inf (a b : L) := sInf {a, b}
  inf_le_left (a b : L) := by
    apply sInf_le
    simp
  inf_le_right (a b : L) := by
    apply sInf_le
    simp
  le_inf (a b c : L) := by
    intro hab hac
    apply le_sInf
    simp
    exact And.intro hab hac
}

#print axioms CompleteLatticeFromInf
