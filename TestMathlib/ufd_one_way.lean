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

lemma IsUnitIffSpanEqTop (a : R) : IsUnit a ↔ Span a = ⊤ := by
  rw [IsUnitIffOneInSpan]
  exact (EqTopIffOneMem (Span a)).symm

def IsMaximal' (I : Ideal R) := ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤

def IsPrime' (I : Ideal R) := ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

def IsField' (R : Type) [CommRing R] := IsMaximal' (⊥ : Ideal R)

def IsDomain' (R : Type) [CommRing R] := IsPrime' (⊥ : Ideal R)

theorem FieldIsDomain (hf : IsField' R) : IsDomain' R := by
  intro a b h
  rcases hf (Span a) bot_le with hb | ht
  · left
    rw [← SpanLeIff, hb]
  · right
    rw [← IsUnitIffSpanEqTop, IsUnitIffDvdOne] at ht
    obtain ⟨u, hu⟩ := ht
    rw [← one_mul b, hu, mul_comm a, mul_assoc]
    exact (⊥ : Ideal R).smul_mem' u h

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

lemma PreImageOfPrimeIsPrime (f : X →+* Y) {P : Ideal Y} (hp : IsPrime' P) :
  IsPrime' (PreImage f P) := by
  rw [IsPrime']
  simp
  intro a b
  exact hp (f a) (f b)

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

lemma IdealLeIff (I J : Ideal Y) : I ≤ J ↔ ∀ a : Y, a ∈ I → a ∈ J := by
  rfl

#print axioms IdealLeIff

variable {f : X →+* Y}

lemma SurjPreImageLeIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I ≤ PreImage f J ↔ I ≤ J := by
  simp [IdealLeIff]
  exact IffWhenSurj hf (fun a ↦ a ∈ I → a ∈ J)

@[simp]
lemma SurjPreImageEqIff (hf : surj f) (I J : Ideal Y) :
  PreImage f I = PreImage f J ↔ I = J := by
  simp [le_antisymm_iff, SurjPreImageLeIff hf]

lemma MaximalIfSurjPreImageMaximal (hf : surj f) (I : Ideal Y)
  (hm : IsMaximal' (PreImage f I)) : IsMaximal' I := by
  intro J
  have h := hm (PreImage f J)
  rw [← PreImageTop f, SurjPreImageLeIff hf,
    SurjPreImageEqIff hf, SurjPreImageEqIff hf] at h
  exact h

alias mk := Ideal.Quotient.mk

lemma MkSurj (I : Ideal R) : surj (mk I) :=
  Ideal.Quotient.mk_surjective

lemma PreImageMkBot (I : Ideal R) : PreImage (mk I) ⊥ = I := by
  have h : PreImage (mk I) ⊥ = RingHom.ker (mk I) := rfl
  rw [h, mk, Ideal.mk_ker]

theorem QuotientIsFieldIfMaximal (I : Ideal R) (hi : IsMaximal' I) : IsField' (R ⧸ I) := by
  apply MaximalIfSurjPreImageMaximal (MkSurj I)
  rw [PreImageMkBot I]
  exact hi

theorem PrimeIfQuotientIsDomain (I : Ideal R) (hd : IsDomain' (R ⧸ I)) : IsPrime' I := by
  rw [← PreImageMkBot I]
  apply PreImageOfPrimeIsPrime
  exact hd

theorem MaximalIsPrime {I : Ideal R} (hm : IsMaximal' I) : IsPrime' I := by
  exact PrimeIfQuotientIsDomain I (FieldIsDomain  (QuotientIsFieldIfMaximal I hm))

lemma IsPrimeIff (p : R) : Prime p ↔ p ≠ 0 ∧ ¬ IsUnit p ∧ IsPrime' (Span p) := by
  rw [Prime, IsPrime']
  simp

lemma ZeroNotIrreduible : ¬ (Irreducible (0 : R)) := by
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

theorem SpanIrreducibleMaximal (hr : IsPrincipalIdealRing R) {p : R}
  (hp : Irreducible p) : IsMaximal' (Span p) := by
  intro J hpj
  obtain ⟨a, hja⟩ := (hr.principal J).principal
  rw [← Ideal.span, ← SpanEq] at hja
  rw [hja]
  rw [hja, SpanLeSpanIff] at hpj
  have hap := hpj
  obtain ⟨c, hc⟩ := hpj
  obtain ⟨_, hp⟩ := hp
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

theorem EuclidsLemma {p : R} (hr : IsPrincipalIdealRing R) :
  Irreducible p → Prime p := by
  intro hp
  rw [IsPrimeIff]
  have hnu := hp.not_isUnit
  simp [*]
  apply And.intro
  · exact IrreducibleNotZero hp
  · exact MaximalIsPrime (SpanIrreducibleMaximal hr hp)
