import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

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
  simp [Span]

lemma MemSpanSelf (a : R) : a ∈ Span a := by
  rw [MemSpanIff]

@[simp]
lemma IdealSpanLeIff (a : R) (I : Ideal R) : Ideal.span {a} ≤ I ↔ a ∈ I := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simp

lemma SpanEq (a : R) : Span a = Ideal.span {a} := by
  apply le_antisymm
  · intro b
    rw [MemSpanIff, dvd_def]
    intro h
    obtain ⟨c, h⟩ := h
    rw [h, mul_comm]
    apply Submodule.smul_mem'
    simp
    rw [← IdealSpanLeIff]
  · simp

@[simp]
lemma SpanLeIff (a : R) (I : Ideal R) : Span a ≤ I ↔ a ∈ I := by
  rw [SpanEq, IdealSpanLeIff]

@[simp]
lemma SpanLeSpanIff (a b : R) : Span b ≤ Span a ↔ a ∣ b := by
  simp

lemma IsUnitIffDvdOne (a : R) : IsUnit a ↔ a ∣ 1 := by
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

lemma SpanEqBotIffIsZero (a : R) : Span a = ⊥ ↔ a = 0 := by
  rw [← LeBotIffEqBot, SpanLeIff]
  exact MemBotIffEqZero a

lemma BotLe (I : Ideal R) : ⊥ ≤ I := by simp

def IsMaximal' (I : Ideal R) := ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤

def IsPrime' (I : Ideal R) := ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

def IsField' (R : Type) [CommRing R] := ∀ (a : R), a ≠  0 →  IsUnit a

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
    · rw [SpanEqBotIffIsZero] at hs
      by_contra
      exact hnz hs
    · exact hs

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

-- lemma PreImageOfPrimeIsPrime (f : X →+* Y) {P : Ideal Y} (hp : IsPrime' P) :
--   IsPrime' (PreImage f P) := by
--   rw [IsPrime']
--   simp
--   intro a b
--   exact hp (f a) (f b)

alias surj := Function.Surjective

lemma IffWhenSurj {A B : Type} {f : A → B} (hs : surj f) (p : B → Prop) :
  (∀ a : A, p (f a)) ↔ (∀ b : B, p b) := by
  apply Iff.intro
  · intro h1 b
    rw [surj, Function.Surjective] at hs
    obtain ⟨a, h2⟩ := hs b
    rw [← h2]
    exact h1 a
  · intro h a
    exact h (f a)

-- def TwoArgHelper {Y : Type} (p : Y → Y → Prop) (a : Y) := ∀ b : Y, p a b

-- def UnCurry {B : Type} (p : B → B → Prop) (bb : B × B) := p bb.1 bb.2

-- def FuncProd {A B C D : Type} (f : A → B) (g : C → D) (ac : A × C) : B × D := (f ac.1, g ac.2)


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
  -- intro a b
  -- have h := IffWhenSurj hs (TwoArgHelper p)
  -- have hs2 := surj (f × f)
  -- have h := IffWhenSurj hs (TwoArgHelper p)
  -- sorry

def PrimeHelper (P : Ideal Y) (a b : Y) := a * b ∈ P → a ∈ P ∨ b ∈ P

variable {f : X →+* Y}

lemma SurjPreImagePrimeIff (hf : surj f) (P : Ideal Y) :
  IsPrime' (PreImage f P) ↔ IsPrime' P := by
  simp [IsPrime']
  exact IffWhenSurj2 hf (PrimeHelper P)

lemma IdealLeIff (I J : Ideal Y) : I ≤ J ↔ ∀ a : Y, a ∈ I → a ∈ J := by
  rfl

def LeHelper (I J : Ideal Y) (a : Y) := a ∈ I → a ∈ J

lemma SurjPreImageLeIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I ≤ PreImage f J ↔ I ≤ J := by
  simp [IdealLeIff]
  exact IffWhenSurj hf (LeHelper I J)

@[simp]
lemma SurjPreImageEqIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I = PreImage f J ↔ I = J := by
  simp [le_antisymm_iff, SurjPreImageLeIff hf]

-- def IdealSum (I J : Ideal R) : Ideal R where
--   carrier := {x : R | ∃ i ∈ I, ∃ j ∈ J, i + j = x}
--   add_mem' := by
--     simp
--     intro a b ia hia ja hja ha ib hib jb hjb hb
--     use ia + ib
--     apply And.intro
--     · exact I.add_mem' hia hib
--     use ja + jb
--     apply And.intro
--     · exact J.add_mem' hja hjb
--     rw [← ha, ← hb]
--     simp [add_assoc]
--     simp [← add_assoc]
--     simp [add_comm]
--   zero_mem' := by
--     use 0
--     simp
--   smul_mem' := by
--     simp
--     intro c x i hi j hj hx
--     use c * i
--     apply And.intro
--     · exact I.smul_mem' c hi
--     use c * j
--     apply And.intro
--     · exact J.smul_mem' c hj
--     rw [← hx]
--     simp [mul_add]

def SurjImage (hf : surj f) (I : Ideal X) : Ideal Y where
  carrier := {y : Y | ∃ x ∈ I, f x = y}
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

-- @[simp]
-- lemma SurjImageOfPreImageEq (hf : surj f) (I : Ideal Y) :
--   SurjImage hf (PreImage f I) = I := by
--   apply Ideal.ext
--   simp [SurjImage]
--   sorry

-- lemma SurjImageSurj (hf : surj f) : surj (SurjImage hf) := by
--   intro I
--   use PreImage f I
--   exact SurjImageOfPreImageEq hf I

-- def MaximalHelper (I J : Ideal Y) := I ≤ J → J = I ∨ J = ⊤

-- lemma ForallIffForall {S : Type} (p q : S → Prop) (h : ∀ s : S, p s ↔ q s) :
--   (∀ s : S, p s) ↔ (∀ s : S, q s) := by
--   simp [h]


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

-- lemma SurjPreImageMaximalIff' (hf : surj f) (I : Ideal Y) :
--   IsMaximal' (PreImage f I) ↔ IsMaximal' I := by
--   simp [IsMaximal']
--   have h : (∀ (J : Ideal X), I ≤ SurjImage hf J → SurjImage hf J = I ∨ SurjImage hf J = ⊤)
--     ↔ ∀ (J : Ideal Y), I ≤ J → J = I ∨ J = ⊤ := IffWhenSurj (SurjImageSurj hf) (MaximalHelper I)
--   rw [← h]
--   apply ForallIffForall
--   intro J
--   apply Iff.intro
--   ·
--     sorry
--   · intro h2 h3
--     sorry

-- lemma PreImageOfSurjImageEqIff (hf : surj f) (J : Ideal X) :
--   J = PreImage f (SurjImage hf J) ↔ PreImage f ⊥ ≤ J := by
--   apply Iff.intro
--   · sorry
--   · intro h
--     apply Ideal.ext
--     intro x
--     apply Iff.intro
--     · intro hxj
--       simp [SurjImage]
--       use x
--     · intro hx
--       simp [SurjImage] at hx
--       obtain ⟨x2, hx2j, hfx⟩ := hx
--       sorry

-- lemma SurjPreImageMaximalIff (hf : surj f) (I : Ideal Y) :
--   IsMaximal' (PreImage f I) ↔ IsMaximal' I := by
--   simp [IsMaximal']
--   rw [← PreImageTop f]
--   apply Iff.intro
--   · intro h J hij
--     have h2 := h (PreImage f J) ((SurjPreImageLeIff hf I J).mpr hij)
--     simp [*] at h2
--     exact h2
--   · intro h J hp
--     have h1 := BotLe I

--     have h2 : J = PreImage f (SurjImage hf J) := sorry
--     rw [h2, SurjPreImageLeIff hf] at hp
--     rw [h2]
--     simp [SurjPreImageEqIff hf]
--     exact h (SurjImage hf J) hp

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

lemma ZeroProduct : (0 : R) = (0 : R) * (0 : R) := by
  simp

lemma IrreducibleIsNotZero {p : R} (h : Irreducible p) : p ≠ 0 := by
  intro hz
  obtain ⟨h1, h2⟩ := h
  rw [hz] at h2
  have h3 := h2 ZeroProduct
  apply h1
  rw [hz]
  cases h3
  · simp [*]
  · simp [*]

theorem IrreducibleGeneratesMaximalIdeal {p : R} (hr : IsPrincipalIdealRing R)
  (hp : Irreducible p) : IsMaximal' (Span p) := by
  rw [IsMaximalIff]
  obtain ⟨h1, h2⟩ := hp
  intro I
  obtain ⟨a, h5⟩ := (hr.principal I).principal
  rw [← Ideal.span, ← SpanEq] at h5
  rw [h5]
  intro x h6 h7 h8
  rw [SpanLeSpanIff, dvd_def] at h6
  obtain ⟨b, h6⟩ := h6
  rcases h2 h6 with ha | hb
  · rw [← IsUnitIffSpanEqTop]
    exact ha
  · rw [IsUnitIffDvdOne, dvd_def] at hb
    obtain ⟨c, h9⟩ := hb
    have h10 : a = p * c := by
      rw [h6, mul_assoc, ← h9, mul_one]
    have h11 : p ∣ a := by
      rw [dvd_def]
      use c
    rw [← SpanLeSpanIff] at h11
    by_contra
    exact h8 (h11 h7)

theorem EuclidsLemma {p : R} (hr : IsPrincipalIdealRing R) :
  Irreducible p → Prime p := by
  intro hp
  rw [IsPrimeIff]
  have hnu := hp.not_isUnit
  simp [*]
  apply And.intro
  · exact IrreducibleIsNotZero hp
  · exact MaximalIsPrime (IrreducibleGeneratesMaximalIdeal hr hp)
