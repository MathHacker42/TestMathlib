import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import TestMathlib.Ideal

variable {R : Type} [CommRing R]

def IdealSum (I J : Ideal R) : Ideal R where
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

lemma SumLeSum (I J : Ideal R) : (IdealSum I J) ≤ (IdealSum J I) := by
  intro x
  simp [IdealSum]
  intro i hi j hj hx
  use j
  apply And.intro hj
  use i
  apply And.intro hi
  rw [add_comm, hx]

lemma SumComm (I J : Ideal R) : (IdealSum I J) = (IdealSum J I) :=
  le_antisymm (SumLeSum I J) (SumLeSum J I)

lemma LeSumLeft (I J : Ideal R) : I ≤ IdealSum I J := by
  intro i hi
  use i
  apply And.intro hi
  use 0
  simp

lemma LeSumRight (I J : Ideal R) : J ≤ IdealSum I J := by
  rw [SumComm]
  exact LeSumLeft J I

def IsMaximal' (I : Ideal R) := ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤

def IsPrime' (I : Ideal R) := ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

theorem MaximalIsPrime {I : Ideal R} (hm : IsMaximal' I) : IsPrime' I := by
  intro a b h
  rcases hm (IdealSum I (Span b)) (LeSumLeft I (Span b)) with hi | ht
  · right
    rw [← hi, ← SpanLeIff]
    apply LeSumRight
  · left
    rw [EqTopIffOneMem] at ht
    obtain ⟨i, hi, x, ⟨r, hr⟩, h1⟩ := ht
    rw [← mul_one a, ← h1, mul_add, hr, ← mul_assoc, ← mul_comm r]
    exact I.add_mem' (I.smul_mem' a hi) (I.smul_mem' r h)

lemma PrimeIff (p : R) : Prime p ↔ p ≠ 0 ∧ ¬ IsUnit p ∧ IsPrime' (Span p) := by
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
  rw [PrimeIff]
  have hnu := hp.not_isUnit
  simp [*]
  apply And.intro
  · exact IrreducibleNotZero hp
  · exact MaximalIsPrime (SpanIrreducibleMaximal hr hp)

#print axioms EuclidsLemma
