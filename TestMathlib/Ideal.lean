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

-- instance : PartialOrder (Ideal R) := SetLikePO (Ideal R)

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

-- instance lei : Preorder (Ideal R) := {

-- }

-- #print axioms lei

#print axioms SetLikeLattice

lemma MemSInf (S : Set (Ideal R)) (r : R) : r ∈ sInf S ↔ ∀ I ∈ S, r ∈ I := by rfl

lemma SubSInf (S : Set R) (SI : Set (Ideal R)) (h : ∀ I ∈ SI, S ⊆ I) : S ⊆ ↑(sInf SI) := by
  intro r hr
  simp
  rw [MemSInf]
  intro I hi
  apply h I hi hr


-- instance : CompleteSemilatticeInf (Ideal' R) := {
--   sInf (S : Set (Ideal' R)) := {
--     carrier := {r : R | ∀ I ∈ S, r ∈ I}
--     add_mem' := by
--       intro a b ha hb I hi
--       exact I.add_mem' (ha I hi) (hb I hi)
--     zero_mem' := by
--       intro I hi
--       exact I.zero_mem'
--     smul_mem' := by
--       intro c x hx I hi
--       exact I.smul_mem' c (hx I hi)
--   }
--   sInf_le := by
--     intro S I hi r hr
--     simp at hr
--     exact hr I hi
--   le_sInf := by
--     intro S I hi r hr
--     simp
--     intro J hj
--     exact hi J hj hr
-- }



-- lemma IdealSpanEq (S : Set R) : Ideal.span S = SSpan S := by
--   have h : Ideal.span S = _intersection {I | S ⊆ I} := rfl
--   rw [h]
--   ext r
--   simp [_intersection, SSpan, Intersection]
  -- simp

  -- have h : SSpan S = ⋂ I ∈ S, I := sorry
  -- ext r
  -- have h : r ∈ Ideal.span S ↔ r ∈ sInf {p : Ideal R | S ⊆ p.carrier} := by
  --   rw [Ideal.span, Submodule.span]
  --   -- rw [iff_self]
  --   sorry
  -- rw [Ideal.span, Submodule.span]
  -- rw [foo, foo]
  -- sorry

-- #print axioms IdealSpanEq












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


-- @[simp] lemma MemCarrier {x : R} {p : Ideal R} : x ∈ p.carrier ↔ x ∈ (p : Set R) := Iff.rfl

-- @[simp] lemma MemIff (I : Ideal' R) (r : R) : r ∈ I ↔ r ∈ I.carrier := by rfl

-- @[simp] lemma MemIff
--   {S : Set R}
--   {r : R}
--   (h_zero : 0 ∈ S)
--   (h_add : ∀ {a b : R}, a ∈ S → b ∈ S → a + b ∈ S)
--   (h_smul : ∀ (c : R) {x : R}, x ∈ S → c * x ∈ S) :
--   r ∈ (⟨S, h_zero, h_add, h_smul⟩ : Ideal R)
-- ↔ r ∈ S := Iff.rfl

@[simp]
lemma MemSpanIff (a b : R) : b ∈ Span a ↔ a ∣ b := by
  simp [Span]
  -- simp
  -- rw [MemIff]
  -- · simp
  -- · simp
  --   intro c d
  --   sorry

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


def fal (I J : Ideal R) := I ≤ J

#print axioms fal

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

-- lemma BotLe (I : Ideal R) : ⊥ ≤ I := by simp



-- instance bwa : CompleteLattice (Ideal R) := CompleteLatticeFromInf

-- #print axioms bwa


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

lemma SubSubSSpan (S T : Set R) (h : S ⊆ T) : S ⊆ sSpan T := le_trans h (SubSSpanSelf T)

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

instance : Mul (Ideal R) := {
  mul (I J : Ideal R) := sSpan {r : R | ∃ i ∈ I, ∃ j ∈ J, i * j = r}
}

lemma MulEq (I J : Ideal R) : I * J = sSpan {r : R | ∃ i ∈ I, ∃ j ∈ J, i * j = r} := rfl

lemma MemMul (I J : Ideal R) (a b : R) (ha : a ∈ I) (hb : b ∈ J) : a * b ∈ I * J := by
  rw [MulEq, MemSSpanIff]
  intro K h
  apply h
  simp
  use a
  simp [ha]
  use b

#print axioms MemMul

lemma MulLe (I J K : Ideal R) (h : ∀ a b : R, a ∈ I → b ∈ J → a * b ∈ K) : I * J ≤ K := by
  rw [MulEq]
  apply sSpanLe
  intro r
  simp
  intro i hi j hj hij
  rw [← hij]
  exact h i j hi hj

#print axioms MulLe

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

lemma MulLeRight (I J : Ideal R) : I * J ≤ J := by
  apply MulLe
  intro a b ha
  exact J.smul_mem' a

lemma MulLeLeft (I J : Ideal R) : I * J ≤ I := by
  rw [MulComm]
  apply MulLeRight

-- lemma MulSSup (I : Ideal R) (S : Set (Ideal R)) : I * sSup S = sSup {I * J | J ∈ S} := by
--   apply le_antisymm
--   · apply MulLe
--     intro a b ha hb

--     sorry
--   ·
--     sorry

-- lemma MulSpanEq (I : Ideal R) (S : Set R) :
--   I * sSpan S = sSpan {r : R | ∃ i ∈ I, ∃ s ∈ S, i * s = r} := by
--   apply le_antisymm
--   · apply MulLe
--     intro a b ha hb
--     rw [MemSSpanIff] at hb
--     rw [MemSSpanIff]
--     intro J hj
--     rw [Set.subset_def] at hj
--     simp at hj
--     sorry
--   ·
--     sorry

-- -- lemma SSPanMulSSpan (S T : Set R)
-- --   : sSpan S * sSpan T = sSpan {r : R | ∃ s ∈ S, ∃ t ∈ T, s * t = r} := by
-- --   apply le_antisymm
-- --   · apply MulLe
-- --     intro a b ha hb
-- --     rw [MemSSpanIff]
-- --     intro I h

-- --     sorry
-- --   ·
-- --     sorry

-- lemma MulAssocLe (I J K : Ideal R) : (I * J) * K ≤ I * (J * K) := by
--   -- rw [← sSpanSelfEq I, ← sSpanSelfEq J, ← sSpanSelfEq K]
--   -- have h := SSPanMulSSpan (I : Set R) (J : Set R)
--   -- rw [h]


--   -- repeat rw [MulEq]
--   -- apply SSpanLeSSpan
--   -- intro a ha

--   sorry

-- lemma MulAssoc (I J K : Ideal R) : (I * J) * K = I * (J * K) := by
--   apply le_antisymm
--   · apply MulAssocLe
--   · rw [MulComm I, MulComm J, MulComm I, MulComm (J * I)]
--     apply MulAssocLe

-- instance : CommMonoidWithZero (Ideal R) := {
--   one := ⊤
--   zero := ⊥
--   one_mul (I : Ideal R) := by
--     apply le_antisymm
--     · apply MulLeRight
--     · intro i hi
--       rw [← one_mul i]
--       apply MemMul
--       · exact OneMemTop
--       · exact hi
--   mul_one (I : Ideal R) := sorry
--   zero_mul (I : Ideal R) := by
--     simp
--     apply le_antisymm
--     · apply MulLeLeft
--     · simp
--   mul_zero := sorry
--   mul_comm := MulComm
--   mul_assoc := sorry
-- }
