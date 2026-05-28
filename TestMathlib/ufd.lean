import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

variable {R : Type} [CommRing R]

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
  simp only [Span, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

lemma MemSpanSelf (a : R) : a ∈ Span a := by
  simp
  -- rw [MemSpanIff]

-- @[simp]
-- lemma IdealSpanLeIff (a : R) (I : Ideal R) : Ideal.span {a} ≤ I ↔ a ∈ I := by
--   rw [Ideal.span_le, Set.singleton_subset_iff]
--   simp

-- instance : LE (Ideal R) where le := fun I J ↦ I.carrier ⊆ J.carrier

-- def PartialOrderPreimage {X Y : Type} [PartialOrder Y] {f : X → Y} (hf : Function.Injective f) :
--   PartialOrder X  where
--   le := fun a b ↦ f a ≤ f b
--   le_refl := by
--     intro a
--     exact le_refl (f a)
--   le_trans := by
--     intro a b c hab hbc
--     exact le_trans hab hbc
--   le_antisymm := by
--     intro a b hab hba
--     exact hf (le_antisymm hab hba)
--   lt := fun a b ↦ f a ≤ f b ∧ ¬f b ≤ f a
--   lt_iff_le_not_ge : ∀ (a b : X), f a ≤ f b ∧ ¬f b ≤ f a ↔ f a ≤ f b ∧ ¬f b ≤ f a := by
--     intros
--     rfl

-- #print axioms PartialOrderPreimage

-- lemma CarrierInjective : Function.Injective (fun (I : Ideal R) ↦ I.carrier) := by
--   intro I J
--   simp

-- #print axioms CarrierInjective

-- def foo : PartialOrder (Ideal R) := PartialOrderPreimage CarrierInjective

-- #print axioms foo

instance baz : PartialOrder (Ideal R) where
  le := fun I J ↦ ∀ ⦃r : R⦄, r ∈ I → r ∈ J
  le_refl := by
    intro I r hr
    exact hr
  le_trans :=  by
    intro I J K hij hjk r hr
    exact hjk (hij hr)
  le_antisymm :=  by
    intro I J hij hji
    ext r
    apply Iff.intro (@hij r) (@hji r)
  lt := fun I J ↦ I.carrier ≤ J.carrier ∧ ¬J.carrier ≤ I.carrier
  lt_iff_le_not_ge : ∀ I J : Ideal R,
    I.carrier ≤ J.carrier ∧ ¬J.carrier ≤ I.carrier ↔
    I.carrier ≤ J.carrier ∧ ¬J.carrier ≤ I.carrier := by
    intros; rfl

#print axioms baz
-- #print axioms PartialOrder
-- #print axioms IdealRefl
-- #print axioms IdealTrans
-- #print axioms IdealAntiSymm

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

#print axioms SpanLeIff

lemma SpanEq (a : R) : Span a = Ideal.span {a} := by
  rw [Ideal.span, Submodule.span]
  simp [Set.singleton_subset_iff]
  ext r
  apply Iff.intro
  · intro hr
    simp [sInf]
    intro I ha
    obtain ⟨c, hc⟩ := hr
    rw [hc, mul_comm]
    exact I.smul_mem' c ha
  · intro hr
    simp [sInf] at hr
    apply hr
    exact MemSpanSelf a

#print axioms SpanEq

  -- apply le_antisymm
  -- ·
  --   sorry
  --   -- rw [SpanLeIff2]
  --   -- simp [IdealIntersection]
  -- ·
  --   -- sorry
  --   apply sInf_le
  --   simp


-- lemma SpanEq (a : R) : Span a = Ideal.span {a} := by
--   apply le_antisymm
--   · intro b
--     rw [MemSpanIff, dvd_def]
--     intro h
--     obtain ⟨c, h⟩ := h
--     rw [h, mul_comm]
--     apply Submodule.smul_mem'
--     simp
--     rw [← IdealSpanLeIff]
--   · simp

-- @[simp]
-- lemma SpanLeIff (a : R) (I : Ideal R) : Span a ≤ I ↔ a ∈ I := by
--   rw [SpanEq, IdealSpanLeIff]

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

lemma BotLe (I : Ideal R) : ⊥ ≤ I := by simp

def IsMaximal' (I : Ideal R) := ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤

def IsPrime' (I : Ideal R) := ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

def IsField' (R : Type) [CommRing R] := ∀ (a : R), a ≠ 0 → IsUnit a

def IsDomain' (R : Type) [CommRing R] := ∀ (a b : R), a * b = 0 → a = 0 ∨ b = 0

theorem FieldIsDomain (hr : IsField' R) : IsDomain' R := by
  intro a b h
  have h1 := hr a
  rw [← or_iff_not_imp_left] at h1
  rcases h1 with h1 | h1
  · simp [*]
  · right
    rw [isUnit_iff_exists] at *
    obtain ⟨c, h1, h2⟩ := h1
    rw [← one_mul b, ← h2, mul_assoc, h, mul_zero]

lemma IsDomainIffZeroPrime (R : Type) [CommRing R] : IsDomain' R ↔ IsPrime' (⊥ : Ideal R) := by
  rw [IsDomain', IsPrime']
  simp

lemma IsMaximalIff (I : Ideal R) :
  IsMaximal' I ↔ ∀ (J : Ideal R) (x : R), I ≤ J → x ∈ J → x ∉ I → J = ⊤ := by
  rw [IsMaximal']
  apply Iff.intro
  · intro hm J X hij hxj hxni
    rcases hm J hij with hi | ht
    · by_contra
      rw [hi] at hxj
      exact hxni hxj
    · exact ht
  · intro h J hij
    have h := h J
    simp [hij] at h
    have he : (∃ x ∈ J, x ∉ I) → J = ⊤ := by
      simp
      exact h
    rw [imp_iff_not_or] at he
    rcases he with hne | hjt
    · push_neg at hne
      left
      exact le_antisymm hne hij
    · simp [*]

theorem IsFieldIffZeroMaximal (R : Type) [CommRing R] :
  IsField' R ↔ IsMaximal' (⊥ : Ideal R) := by
  rw [IsField']
  apply Iff.intro
  · rw [IsMaximalIff]
    intro ha J x _ hxj hxnb
    rw [MemBotIffEqZero] at hxnb
    have hu := ha x hxnb
    rw [IsUnitIffSpanEqTop] at hu
    rw [← SpanLeIff, hu, TopLeIffEqTop] at hxj
    exact hxj
  · intro hj a hnz
    rw [IsUnitIffSpanEqTop]
    have hs := hj (Span a) (BotLe (Span a))
    rcases hs with hs | hs
    · rw [SpanEqBotIffEqZero] at hs
      by_contra
      exact hnz hs
    · exact hs

-- section XY

variable {X Y : Type} [CommRing X] [CommRing Y]

def PreImage (f : X →+* Y) (I : Ideal Y) : Ideal X where
  carrier := {x : X | f x ∈ I}
  add_mem' := by
    simp
    exact I.add_mem'
  zero_mem' := by
    simp
  smul_mem' := by
    simp
    intro c x
    exact I.smul_mem' (f c)

@[simp]
lemma MemPreImageIff (f : X →+* Y) (I : Ideal Y) (x : X) : x ∈ PreImage f I ↔ f x ∈ I := by
  simp [PreImage]

lemma PreImageTop (f : X →+* Y) : PreImage f ⊤ = ⊤ := by
  simp [EqTopIffOneMem]

alias surj := Function.Surjective

lemma IffWhenSurj {A B : Type} {f : A → B} (hs : surj f) (p : B → Prop) :
  (∀ a : A, p (f a)) ↔ (∀ b : B, p b) := by
  apply Iff.intro
  · intro h1 b
    obtain ⟨a, h2⟩ := hs b
    rw [← h2]
    exact h1 a
  · intro h a
    exact h (f a)

-- Should really be unified but w/e
lemma IffWhenSurj2 {A Y : Type} {f : A → Y} (hs : surj f) (p : Y → Y → Prop) :
  (∀ a b : A, p (f a) (f b)) ↔ (∀  x y : Y, p x y) := by
  apply Iff.intro
  · intro h x y
    obtain ⟨a, hx⟩ := hs x
    obtain ⟨b, hy⟩ := hs y
    rw [← hx, ← hy]
    exact h a b
  · intro h a b
    exact h (f a) (f b)

variable {f : X →+* Y}

lemma SurjPreImagePrimeIff (hf : surj f) (P : Ideal Y) :
  IsPrime' (PreImage f P) ↔ IsPrime' P := by
  simp [IsPrime']
  exact IffWhenSurj2 hf (fun a b ↦ a * b ∈ P → a ∈ P ∨ b ∈ P)

lemma IdealLeIff (I J : Ideal Y) : I ≤ J ↔ ∀ a : Y, a ∈ I → a ∈ J := by
  rfl

lemma SurjPreImageLeIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I ≤ PreImage f J ↔ I ≤ J := by
  simp [IdealLeIff]
  exact IffWhenSurj hf (fun a ↦ a ∈ I → a ∈ J)

@[simp]
lemma SurjPreImageEqIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I = PreImage f J ↔ I = J := by
  simp [le_antisymm_iff, SurjPreImageLeIff hf]

def SurjImage (hf : surj f) (I : Ideal X) : Ideal Y where
  carrier := {f x | x ∈ I}
  add_mem' := by
    simp
    intro a b x1 hx1 ha x2 hx2 hb
    use x1 + x2
    simp [*]
    exact I.add_mem' hx1 hx2
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    simp
    intro c a ha
    obtain ⟨d, hd⟩ := hf c
    use d * a
    simp [hd]
    exact I.smul_mem' d ha

lemma SurjPreImageBotMaximalIff (hf : surj f) :
  IsMaximal' (PreImage f ⊥) ↔ IsMaximal' (⊥ : Ideal Y) := by
  simp [IsMaximal']
  rw [← PreImageTop f]
  apply Iff.intro
  · intro h1 J
    have h2 := h1 (PreImage f J)
    simp [SurjPreImageEqIff hf, SurjPreImageLeIff hf] at h2
    apply h2
  · intro h2 J h4
    have h4 : J = PreImage f (SurjImage hf J) := by
      apply Ideal.ext
      intro j
      simp [SurjImage]
      apply Iff.intro
      · intro hj
        use j
      · intro h5
        obtain ⟨x, hx, h6⟩ := h5
        have h7 : j - x ∈ J := by
          apply h4
          simp [h6]
        have h8 := J.add_mem' h7 hx
        simp at h8
        exact h8
    rw [h4]
    simp [SurjPreImageEqIff hf]
    exact h2 (SurjImage hf J)

alias mk := Ideal.Quotient.mk

lemma MkSurj (I : Ideal R) : surj (mk I) :=
  Ideal.Quotient.mk_surjective

lemma PreImageMkBot (I : Ideal R) : PreImage (mk I) ⊥ = I := by
  have h : PreImage (mk I) ⊥ = RingHom.ker (mk I) := rfl
  rw [h, mk, Ideal.mk_ker]

theorem MaximalIffQuotientIsField (I : Ideal R) : IsMaximal' I ↔ IsField' (R ⧸ I) := by
  rw [IsFieldIffZeroMaximal, ← SurjPreImageBotMaximalIff (MkSurj I), PreImageMkBot I]

theorem PrimeIffQuotientIsDomain (I : Ideal R) : IsPrime' I ↔ IsDomain' (R ⧸ I) := by
  rw [IsDomainIffZeroPrime, ← SurjPreImagePrimeIff (MkSurj I) ⊥, PreImageMkBot I]

theorem MaximalIsPrime {I : Ideal R} : IsMaximal' I → IsPrime' I := by
  rw [MaximalIffQuotientIsField, PrimeIffQuotientIsDomain]
  exact FieldIsDomain

lemma IsPrimeIff (p : R) : Prime p ↔ p ≠ 0 ∧ ¬ IsUnit p ∧ IsPrime' (Span p) := by
  rw [Prime, IsPrime']
  simp

lemma ZeroNotIrreduible : ¬ Irreducible (0 : R) := by
  intro hzi
  obtain ⟨h1, h2⟩ := hzi
  have hzp : (0 : R) = (0 : R) * (0 : R) := by
    simp
  have h3 := h2 hzp
  rw [or_self_iff] at h3
  exact h1 h3

lemma IrreducibleNotZero {p : R} (hpi : Irreducible p) : p ≠ 0 := by
  intro hpz
  rw [hpz] at hpi
  exact ZeroNotIrreduible hpi

theorem SpanOfIrreducibleIsMaximal (hr : IsPrincipalIdealRing R) {p : R}
  (hp : Irreducible p) : IsMaximal' (Span p) := by
  rw [IsMaximal']
  intro J hpj
  obtain ⟨a, hja⟩ := (hr.principal J).principal
  rw [← Ideal.span, ← SpanEq] at hja
  rw [hja]
  rw [hja, SpanLeSpanIff] at hpj
  have hap := hpj
  obtain ⟨c, hc⟩ := hpj
  obtain ⟨hu, hp⟩ := hp
  rcases hp hc with hau | hcu
  · right
    rw [← IsUnitIffSpanEqTop a]
    exact hau
  · left
    rw [le_antisymm_iff, SpanLeSpanIff, SpanLeSpanIff]
    apply And.intro
    · rw [IsUnitIffDvdOne] at hcu
      obtain ⟨u, hu⟩ := hcu
      use u
      rw [hc, mul_assoc, ← hu, mul_one]
    · exact hap

theorem EuclidsLemma [IsPrincipalIdealRing R] {p : R} (hp : Irreducible p) : Prime p := by
  rw [IsPrimeIff]
  apply And.intro
  · exact IrreducibleNotZero hp
  apply And.intro
  · exact hp.not_isUnit
  apply MaximalIsPrime
  apply SpanOfIrreducibleIsMaximal
  · simp [*]
  · exact hp

#print axioms EuclidsLemma

variable {M : Type} [CancelCommMonoidWithZero M]

lemma Helper {a b p : M} (hab : p = a * b) (hnz : p ≠ 0) (h : p ∣ a) : IsUnit b := by
  obtain ⟨c, h⟩ := h
  rw [IsUnitIffDvdOne]
  rw [← mul_one p, h, mul_assoc, mul_comm c b] at hab
  use c
  exact mul_left_cancel₀ hnz hab

lemma PrimeIsIrreducible {p : M} (hp : Prime p) : Irreducible p where
  not_isUnit := by
    obtain ⟨_, hnu, _⟩ := hp
    exact hnu
  isUnit_or_isUnit := by
    intro a b hab
    have hd : p ∣ a * b := by
      use 1
      simp [hab]
    obtain ⟨hnz, _, hp⟩ := hp
    rcases hp a b hd with ha | hb
    · right
      exact Helper hab hnz ha
    · left
      rw [mul_comm] at hab
      exact Helper hab hnz hb

-- theorem PIRIsWellFounded [IsPrincipalIdealRing R] : WellFounded DvdNotUnit := sorry

instance DomainHasCancellation [IsDomain R] : CancelCommMonoidWithZero R where

-- instance PIDIsUFD [IsDomain R] [IsPrincipalIdealRing R]
--   : UniqueFactorizationMonoid R where
--   wf := by
--     -- apply WellFounded.intro
--     -- intro a
--     -- apply Acc.intro
--     -- intro y h
--     -- obtain ⟨hy, x, hx, ha⟩ := h
--     sorry
--   irreducible_iff_prime := by
--     intro a
--     apply Iff.intro
--     · exact EuclidsLemma
--     · exact PrimeIsIrreducible
