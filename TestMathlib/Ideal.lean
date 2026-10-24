import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.RingTheory.Ideal.Maps
import TestMathlib.Order

variable (R : Type) [CommRing R]

-- class Ideal where
--   carrier : Set R
--   zero_mem' : 0 ∈ carrier
--   add_mem' : ∀ {a b : R}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
--   smul_mem' (c : R) {x : R} : x ∈ carrier → c * x ∈ carrier

variable {R}

-- instance bwoo : SetLike (Ideal R) R := {
--   coe := fun I ↦ I.carrier
--   coe_injective' := fun p q h => by --cases p; cases q; congr!
--     simp at h
--     exact h
-- }

-- #print axioms bwoo

-- instance : SetLike (Ideal R) R where

instance bwu : InfSet (Ideal R) := {
  sInf (S : Set (Ideal R)) := {
    carrier := {r : R | ∀ I ∈ S, r ∈ I}
    add_mem' := by
      intro a b ha hb I hi
      exact I.add_mem' (ha I hi) (hb I hi)
    zero_mem' := by
      intro I hi
      exact I.zero_mem'
    smul_mem' := by
      intro c x hx I hi
      exact I.smul_mem' c (hx I hi)
  }
}

#print axioms bwu

instance boo : CompleteSemilatticeInf (Ideal R) := by
  apply SetLikeLattice
  intro S
  ext x
  simp
  rfl

#print axioms boo

#print axioms SetLikeLattice

instance nnn : CompleteLattice (Ideal R) := CompleteLatticeFromInf

#print axioms nnn

lemma MemSInf (S : Set (Ideal R)) (r : R) : r ∈ sInf S ↔ ∀ I ∈ S, r ∈ I := by rfl

lemma SubSInf (S : Set R) (SI : Set (Ideal R)) (h : ∀ I ∈ SI, S ⊆ I) : S ⊆ ↑(sInf SI) := by
  intro r hr
  simp
  rw [MemSInf]
  intro I hi
  apply h I hi hr

@[simps]
def Span (a : R) : Ideal R where
  carrier := {b : R | a ∣ b}
  add_mem' := by
    simp
    intro a1 b ha1 hb
    obtain ⟨c, h1⟩ := ha1
    obtain ⟨d, h2⟩ := hb
    use c + d
    simp [*, mul_add]
  zero_mem' := by
    simp
  smul_mem' := by
    simp
    intro c x h
    obtain ⟨b, h⟩ := h
    use c * b
    rw [h]
    simp [← mul_assoc]
    simp [mul_comm]

@[simp]
lemma MemSpanIff (a b : R) : b ∈ Span a ↔ a ∣ b := by
  simp [Span]

lemma MemSpanSelf (a : R) : a ∈ Span a := by
  rw [MemSpanIff]

@[simp]
lemma SpanLeIff (a : R) (I : Ideal R) : Span a ≤ I ↔ a ∈ I := by
  apply Iff.intro
  · intro h
    apply h
    exact MemSpanSelf a
  · intro ha r hr
    obtain ⟨c, hc⟩ := hr
    rw [hc, mul_comm]
    exact I.smul_mem' c ha

-- def fal (I J : Ideal R) := I ≤ J

-- #print axioms fal

lemma IdealLeIff (I J : Ideal R) : I ≤ J ↔ ∀ a : R, a ∈ I → a ∈ J := by
  rfl

#print axioms IdealLeIff

@[simp]
lemma SpanLeSpanIff (a b : R) : Span b ≤ Span a ↔ a ∣ b := by
  simp

lemma IsUnitIffDvdOne {M : Type} [CommMonoid M] (a : M) : IsUnit a ↔ a ∣ 1 := by
  rw [isUnit_iff_exists, dvd_def]
  simp [mul_comm, eq_comm]

lemma IsUnitIffOneInSpan (a : R) : IsUnit a ↔ 1 ∈ Span a := by
  rw [MemSpanIff, IsUnitIffDvdOne]

lemma SpanOneEqTop : Span (1 : R) = ⊤ := by
  apply le_antisymm
  · simp
  · intro a h
    simp

lemma EqTopIffOneMem (I : Ideal R) : I = ⊤ ↔ 1 ∈ I := by
  rw [← SpanLeIff, SpanOneEqTop]
  simp

lemma OneMemTop : (1 : R) ∈ (⊤ : Ideal R) := by simp

#print axioms OneMemTop

lemma SpanZeroEqBot : Span (0 : R) = ⊥ := by
  apply le_antisymm
  · rw [SpanLeIff]
    simp
  · simp

@[simp]
lemma MemBotIffEqZero (a : R) : a ∈ (⊥ : Ideal R) ↔ a = 0 := by
  rw [← SpanZeroEqBot, MemSpanIff]
  simp

lemma IsUnitIffSpanEqTop (a : R) : IsUnit a ↔ Span a = ⊤ := by
  rw [IsUnitIffOneInSpan]
  exact (EqTopIffOneMem (Span a)).symm

lemma TopLeIffEqTop (I : Ideal R) : ⊤ ≤ I ↔ I = ⊤ := by
  simp

lemma LeBotIffEqBot (I : Ideal R) : I ≤ ⊥ ↔ I = ⊥ := by
  simp

lemma SpanEqBotIffEqZero (a : R) : Span a = ⊥ ↔ a = 0 := by
  rw [← LeBotIffEqBot, SpanLeIff]
  exact MemBotIffEqZero a

def sSpan (S : Set R) : Ideal R := sInf {I : Ideal R | S ⊆ I}

#print axioms sSpan

lemma sSpanLe (S : Set R) (I : Ideal R) (h : S ⊆ I) : sSpan S ≤ I := by --sInf_le h
  dsimp [sSpan]
  apply sInf_le
  simp
  exact h

lemma MemSSpanIff (S : Set R) (r : R) :
  r ∈ sSpan S ↔ ∀ I : Ideal R, S ⊆ I → r ∈ I := by
  dsimp [sSpan]
  rw [MemSInf]
  simp

lemma SubSSpanSelf (S : Set R) : S ⊆ sSpan S := by
  dsimp [sSpan]
  apply SubSInf
  simp
#print axioms SubSSpanSelf

-- instance barrrri : Preorder (Ideal R) where

-- lemma IdealLeTrans (I J K : Ideal R) : I ≤ J → J ≤ K → I ≤ K := le_trans

-- #print axioms IdealLeTrans

-- #print axioms Set

-- def MySubset (S T : Set R) := S ≤  sSpan T

-- #print axioms MySubset

-- lemma SetLeTrans (A B C : Set R) : A ≤ B → B ≤ C → A ≤ C := le_trans

-- #print axioms SetLeTrans

-- should maybe just define my own set lattice

lemma SubSubSSpan (S T : Set R) (h : S ⊆ T) : S ⊆ sSpan T := by
  have h1 := (SubSSpanSelf T)
  intro x hx
  exact h1 (h hx)
  -- apply le_trans h


#print axioms sSpanLe
#print axioms SubSubSSpan

lemma SSpanLeSSpan (S T : Set R) (h : S ⊆ T) : sSpan S ≤ sSpan T := by
  apply sSpanLe
  apply SubSubSSpan
  exact h

lemma sSpanSelfEq (I : Ideal R) : sSpan I = I := by
  apply le_antisymm
  · apply sSpanLe
    rfl
  · apply SubSSpanSelf

lemma IdealSpanEq (S : Set R) : Ideal.span S = sSpan S := by
  rw [Ideal.span, Submodule.span, sSpan]
  simp [sInf]
  ext r
  simp

lemma sSpanSingleton (r : R) : sSpan {r} = Span r := by
  apply le_antisymm
  · apply sSpanLe
    simp
  · simp
    apply SubSSpanSelf
    simp

lemma SpanEq (a : R) : Span a = Ideal.span {a} := by
  rw [IdealSpanEq, sSpanSingleton]

#print axioms SpanEq

-- lemma sSpanEqSup (S : Set R) : sSpan S = sSup {Span r | r ∈ S} := by

--   sorry

def Factor (I D : Ideal R) : Ideal R where
  carrier := {a : R | ∀ d ∈ D, a * d ∈ I}
  add_mem' := by
    simp
    intro a b ha hb d hd
    rw [add_mul]
    exact I.add_mem' (ha d hd) (hb d hd)
  zero_mem' := by
    simp
  smul_mem' := by
    simp
    intro c x hx d hd
    rw [mul_assoc]
    exact I.smul_mem' c (hx d hd)

instance : Mul (Ideal R) := {
  mul (I J : Ideal R) := sSpan {r : R | ∃ i ∈ I, ∃ j ∈ J, i * j = r}
}

lemma MulEq (I J : Ideal R) : I * J = sSpan {r : R | ∃ i ∈ I, ∃ j ∈ J, i * j = r} := rfl

lemma MemMul {I J : Ideal R} {i j : R} : i ∈ I → j ∈ J → i * j ∈ I * J := by
  intro hi hj
  rw [MulEq, MemSSpanIff]
  intro K h
  apply h
  simp
  use i
  simp [hi]
  use j

#print axioms MemMul

lemma MulLe (I J K : Ideal R) (h : ∀ i ∈ I, ∀ j ∈ J, i * j ∈ K) : I * J ≤ K := by
  rw [MulEq]
  apply sSpanLe
  intro r
  simp
  intro i hi j hj hij
  rw [← hij]
  exact h i hi j hj

#print axioms MulLe
#print axioms SSpanLeSSpan

lemma MulCommLe (I J : Ideal R) : I * J ≤ J * I := by
  rw [MulEq, MulEq]
  apply SSpanLeSSpan
  simp
  intro a x hx y hy hxy
  use y
  simp [hy]
  use x
  simp [hx]
  rw [← hxy]
  apply mul_comm

lemma MulComm (I J : Ideal R) : I * J = J * I := le_antisymm (MulCommLe I J) (MulCommLe J I)

#print axioms MulComm

instance : CommMagma (Ideal R) := {
  mul_comm := MulComm
}

lemma MulLeRight (I J : Ideal R) : I * J ≤ J := by
  apply MulLe
  intro a b ha
  exact J.smul_mem' a

#print axioms MulLeRight

lemma MulLeLeft (I J : Ideal R) : I * J ≤ I := by
  apply MulLe
  intro a ha b hb
  rw [mul_comm]
  exact I.smul_mem' b ha

#print axioms Factor

lemma MulLeFactor (I J K : Ideal R) (h : I ≤ Factor K J) : I * J ≤ K := by
  apply MulLe
  intro i hi j hj
  apply h at hi
  simp [Factor] at hi
  apply hi j hj

lemma MulAssocLe (I J K : Ideal R) : (I * J) * K ≤ I * (J * K) := by
  apply MulLeFactor
  apply MulLe
  intro i hi j hj
  simp [Factor]
  intro k hk
  rw [mul_assoc]
  exact MemMul hi (MemMul hj hk)

#print axioms MulAssocLe

lemma MulAssoc (I J K : Ideal R) : (I * J) * K = I * (J * K) := by
  apply le_antisymm
  · apply MulAssocLe
  · repeat rw [MulComm I, ← MulComm K]
    apply MulAssocLe

#print axioms MulAssoc

-- instance : Semigroup (Ideal R) := {
--   mul_assoc := MulAssoc
-- }

lemma TopMul (I : Ideal R) : ⊤ * I = I := by
  apply le_antisymm
  · apply MulLeRight
  · intro i hi
    rw [← one_mul i]
    exact MemMul OneMemTop hi

lemma MulTop (I : Ideal R) : I * ⊤ = I := by
  rw [MulComm]
  apply TopMul

lemma BotMul (I : Ideal R) : ⊥ * I = ⊥ := by
  apply le_antisymm
  · apply MulLeLeft
  · simp

lemma MulBot (I : Ideal R) : I * ⊥ = ⊥ := by
  rw [MulComm]
  apply BotMul

instance : CommMonoidWithZero (Ideal R) := {
  one := ⊤
  zero := ⊥
  one_mul := TopMul
  mul_one := MulTop
  zero_mul := BotMul
  mul_zero := MulBot
  mul_comm := MulComm
  mul_assoc := MulAssoc
}

instance : Semigroup (Ideal R) := {
  mul_assoc := MulAssoc
}

lemma MulLeMulRight (I J K : Ideal R) : I ≤ J → I * K ≤ J * K := by
  intro h
  apply MulLe
  intro i hi k hk
  exact MemMul (h hi) hk

lemma SSupMul (I : Ideal R) (S : Set (Ideal R)) :
  sSup S * I = sSup {J * I | J ∈ S} := by
  apply le_antisymm
  · apply MulLeFactor
    apply sSup_le
    intro K hk x hx
    simp [Factor]
    intro y hy
    have h : K * I ≤ sSup {x | ∃ J ∈ S, J * I = x} := by
      apply le_sSup
      simp
      use K
    apply h
    exact MemMul hx hy
  · apply sSup_le
    simp
    intro J hj
    apply MulLeMulRight
    exact le_sSup hj

#print axioms SSupMul

instance : Add (Ideal R) := {
  add (I J : Ideal R) := {
  carrier := {x : R | ∃ i ∈ I, ∃ j ∈ J, i + j = x}
  add_mem' := by
    simp
    intro a b ia hia ja hja ha ib hib jb hjb hb
    use ia + ib
    apply And.intro
    · exact I.add_mem' hia hib
    use ja + jb
    apply And.intro
    · exact J.add_mem' hja hjb
    rw [← ha, ← hb]
    simp [add_assoc]
    simp [← add_assoc]
    apply add_comm
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    simp
    intro c x i hi j hj hx
    use c * i
    apply And.intro
    · exact I.smul_mem' c hi
    use c * j
    apply And.intro
    · exact J.smul_mem' c hj
    rw [← mul_add, hx]
  }
}

-- instance : SMul R (Ideal R) := {
--   smul (r : R) (I : Ideal R) := {
--     carrier := {r * i | i ∈ I}
--     zero_mem' := by
--       simp
--       use 0
--       simp
--     add_mem' := by
--       simp
--       intro a b x hx ha y hy hb
--       use x + y
--       apply And.intro
--       · exact I.add_mem' hx hy
--       · rw [← ha, ← hb, mul_add]
--     smul_mem' := by
--       simp
--       intro c i hi
--       use c * i
--       apply And.intro
--       · exact I.smul_mem' c hi
--       · repeat rw [← mul_assoc]
--         rw [mul_comm r c]
--   }
-- }

-- lemma MulSInf (I : Ideal R) (S : Set (Ideal R)) :
--   I * sInf S = sInf {I * J | J ∈ S} := by
--   apply le_antisymm
--   · apply MulLe
--     intro i hi z hz
--     rw [MemSInf]
--     simp
--     intro J hj
--     rw [MemSInf] at hz
--     exact MemMul hi (hz J hj)
--   · intro x
--     rw [MemSInf]
--     simp
--     intro h


--     -- apply sInf_le
--     -- simp
--     -- use sInf S

--     sorry

-- instance : LeftDistribClass (Ideal R) := {

-- }

-- instance : CommSemiring (Ideal R) := {
--   add := sorry
--   add_assoc := sorry
--   zero_add := sorry
--   add_zero := sorry
--   nsmul := nsmulRec
--   nsmul_succ :=
--   add_comm := sorry
--   left_distrib := sorry
--   right_distrib := sorry
-- }















-- def SMulIdeal (r : R) (I : Ideal R) : Ideal R := {
--   carrier := {r * i | i ∈ I}
--   zero_mem' := by
--     simp
--     use 0
--     simp
--   add_mem' := by
--     simp
--     intro a b x hx ha y hy hb
--     use x + y
--     apply And.intro
--     · exact I.add_mem' hx hy
--     · rw [← ha, ← hb, mul_add]
--   smul_mem' := by
--     simp
--     intro c i hi
--     use c * i
--     apply And.intro
--     · exact I.smul_mem' c hi
--     · repeat rw [← mul_assoc]
--       rw [mul_comm r c]
-- }

-- #print axioms SMulIdeal

-- lemma SMulSSpan (r : R) (S : Set R) :
--   SMulIdeal r (sSpan S) = sSpan {r * x | x ∈ S} := by
--   apply le_antisymm
--   · intro x hx
--     simp [SMulIdeal] at hx
--     obtain ⟨s, hs, hx⟩ := hx
--     rw [← hx]
--     rw [MemSSpanIff]
--     intro I hi
--     -- maybe use factor ideals like in RingMisc or something idk
--     -- yeah, like define the ideal of elements z such that r * z is in I
--     -- S is a subset of that ideal, so it contains sSpan S
--     sorry
--   ·
--     sorry

-- lemma SMulIdealAssoc (a : R) (I J : Ideal R) :
--   SMulIdeal a (I * J) = (SMulIdeal a I) * J := by
--   apply le_antisymm
--   · intro r hr
--     simp [SMulIdeal] at hr

--     sorry
--   ·
--     sorry

-- -- might not need this idk
-- lemma SpanEqSupSpan (S : Set R) : sSpan S = sSup {Span r | r ∈ S} := by

--   sorry

-- lemma foo (I J K : Ideal R) :
--   I * J * K = sSpan {r : R | ∃ i ∈ I, ∃ j ∈ J, ∃ k ∈ K, r = i * j * k} := by
--   apply le_antisymm
--   · rw [SpanEqSupSpan]
--     apply MulLe
--     intro ij k hij hk
--     sorry
--   · apply sSpanLe
--     intro r hr
--     simp at hr
--     obtain ⟨i, hi, j, hj, k, hk, hr⟩ := hr
--     rw [hr]
--     apply MemMul
--     · apply MemMul
--       · exact hi
--       · exact hj
--     · exact hk
