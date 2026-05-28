import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TestMathlib.Util
import TestMathlib.ufd

variable {R : Type} [CommRing R] (S : Set (Ideal R)) [hn : Nonempty S] (ι : Type) [LE ι]

-- ⦃i j : ι⦄
-- def IdealLe (X Y : Ideal R) := ∀ ⦃x : R⦄, x ∈ X → x ∈ Y

-- #print axioms IdealLe

def Ascending := DirectedOn (· ≤ ·) S

def Descending := DirectedOn (· ≥ ·) S

variable {S}

def AscendingUnion (hd : Ascending S) : Ideal R where
  carrier := {r : R | ∃ I ∈ S, r ∈ I}
  add_mem' := by
    simp
    intro a b I hi ha J hj hb
    obtain ⟨K, hk, hik, hjk⟩ := hd I hi J hj
    use K
    exact And.intro hk (K.add_mem' (hik ha) (hjk hb))
  zero_mem' := by
    obtain ⟨I, hi⟩ := hn
    simp
    use I
  smul_mem' := by
    simp
    intro c x I hi hx
    use I
    exact And.intro hi (I.smul_mem' c hx)

#print axioms AscendingUnion

lemma LeAscendingUnion (hd : Ascending S) : ∀ I ∈ S, I ≤ AscendingUnion hd := by
  intro I hi a ha
  simp [AscendingUnion]
  use I

lemma IsPIRIff : IsPrincipalIdealRing R ↔ ∀ I : Ideal R, ∃ a : R, I = Span a := by
  simp [isPrincipalIdealRing_iff, Submodule.isPrincipal_iff, SpanEq]

#print axioms IsPIRIff

def Factor (I D : Ideal R) : Ideal R where
  carrier := {a : R | ∀ d : D, a * d ∈ I}
  add_mem' := by
    intro a b
    repeat rw [Set.mem_setOf]
    intro ha hb d
    rw [add_mul]
    exact I.add_mem' (ha d) (hb d)
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x
    repeat rw [Set.mem_setOf]
    intro h d
    rw [smul_mul_assoc]
    exact I.smul_mem' c (h d)

lemma FactorLeFactor (I : Ideal R) {D E : Ideal R} (h : D ≤ E) :
  Factor I E ≤ Factor I D := by
  simp [Factor]
  intro x h1 d hd
  exact h1 d (h hd)

lemma FactorMulLe (I D : Ideal R) : (Factor I D) * D ≤ I := by
  · rw [Ideal.mul_le]
    intro s hs d hd
    simp [Factor] at hs
    exact hs d hd

-- lemma MulEqSInf (I J : Ideal R) : I * J = Ideal.span
--   {r : R | ∃ a ∈ I, ∃ b ∈ J, a + b = r} := by

--   sorry

lemma LeOfDvd {I J : Ideal R} (h : I ∣ J) : J ≤ I := by
  obtain ⟨K, hk⟩ := h
  rw [hk, Ideal.mul_le]
  intro r hr s hs
  rw [mul_comm]
  exact I.smul_mem' s hr

lemma SpanMulSpanEq (a b : R) : (Span a) * (Span b) = Span (a * b) := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    simp
    intro r har s hbs
    obtain ⟨c, hc⟩ := har
    obtain ⟨d, hd⟩ := hbs
    use c * d
    rw [hc, hd]
    rw [← mul_assoc]
    nth_rw 2 [mul_assoc]
    nth_rw 3 [mul_comm]
    repeat rw [mul_assoc]
  · rw [SpanLeIff]
    apply Ideal.mul_mem_mul
    · exact MemSpanSelf a
    · exact MemSpanSelf b
  -- repeat rw [SpanEq]
  -- rw [Ideal.span_mul_span', Set.singleton_mul_singleton]

#print axioms Ideal.mul_le
#print axioms Ideal.mul_mem_mul
#print axioms SpanMulSpanEq

lemma SpanDvdSpanIff (a b : R) : Span a ∣ Span b ↔ a ∣ b := by
  apply Iff.intro
  · rw [← SpanLeSpanIff]
    exact Ideal.le_of_dvd
  · intro h
    obtain ⟨c, hc⟩ := h
    use Span c
    rw [SpanMulSpanEq, ← hc]

#print axioms Ideal.le_of_dvd

lemma DvdAntisymm {I J : Ideal R} (hij : I ∣ J) (hji : J ∣ I) : I = J := by
  apply le_antisymm
  · exact Ideal.le_of_dvd hji
  · exact Ideal.le_of_dvd hij

variable [hp : IsPrincipalIdealRing R]

lemma FactorMulEq {I D : Ideal R} (h : I ≤ D) : (Factor I D) * D = I := by
  apply le_antisymm
  · exact FactorMulLe I D
  · rw [IsPIRIff] at hp
    obtain ⟨i, hi⟩ := hp I
    obtain ⟨d, hd⟩ := hp D
    rw [hi, hd, SpanLeIff, MemSpanIff, dvd_def] at h
    obtain ⟨c, hc⟩ := h
    rw [hi, SpanLeIff, mul_comm, hc]
    apply Ideal.mul_mem_mul
    · rw [hd]
      exact MemSpanSelf d
    · rw [mul_comm]
      simp [Factor]
      intro a ha
      rw [hd, MemSpanIff] at ha
      exact mul_dvd_mul_left c ha

lemma DvdIffLe (I D : Ideal R) : D ∣ I ↔ I ≤ D := by
  apply Iff.intro
  · exact Ideal.le_of_dvd
  · intro h
    use Factor I D
    rw [mul_comm, FactorMulEq h]

lemma AscendingUnionMem (hd : Ascending S) : AscendingUnion hd ∈ S := by
  rw [IsPIRIff] at hp
  obtain ⟨a, h1⟩ := hp (AscendingUnion hd)
  have h2 := MemSpanSelf a
  rw [← h1] at h2
  simp [AscendingUnion] at h2
  obtain ⟨I, hi, ha⟩ := h2
  rw [← SpanLeIff, ← h1] at ha
  rw [le_antisymm ha (LeAscendingUnion hd I hi)]
  exact hi

#print axioms AscendingUnionMem

variable [IsDomain R]

lemma LeftCancelDvd {A B C : Ideal R} (hz : A ≠ 0) (h : A * B ∣ A * C) : B ∣ C := by
  have _ := hp
  rw [IsPIRIff] at hp
  obtain ⟨a, ha⟩ := hp A
  obtain ⟨b, hb⟩ := hp B
  obtain ⟨c, hc⟩ := hp C
  rw [ha, hb, hc, SpanMulSpanEq, SpanMulSpanEq, SpanDvdSpanIff] at h
  rw [hb, hc, SpanDvdSpanIff]
  obtain ⟨d, hd⟩ := h
  rw [mul_assoc] at hd
  use d
  have hn : a ≠ 0 := by
    intro he
    apply hz
    rw [ha, he, SpanZeroEqBot]
    simp
  exact mul_left_cancel₀ hn hd

#print axioms LeftCancelDvd
#print axioms SpanMulSpanEq
#print axioms SpanDvdSpanIff

lemma LeftCancel {A B C : Ideal R} (hz : A ≠ 0) (h : A * B = A * C) : B = C := by
  apply DvdAntisymm
  · apply LeftCancelDvd hz
    rw [h]
  · apply LeftCancelDvd hz
    rw [h]

#print axioms DvdAntisymm
#print axioms LeftCancel
-- def

instance : CancelCommMonoidWithZero (Ideal R) where
  mul_left_cancel_of_ne_zero := by
    intro I hi
    rw [IsLeftRegular]
    intro J K
    exact LeftCancel hi

theorem DescendingIntersectionMem (ht : Descending S) (hz : sInf S ≠ 0) : (sInf S) ∈ S := by
  have h1 : Ascending {Factor (sInf S) I | I ∈ S} := by
    intro I ⟨D, hds, hdi⟩ J ⟨E, hes, hej⟩
    obtain ⟨B, hbs, hdb, heb⟩ := ht D hds E hes
    use Factor (sInf S) B
    rw [Set.mem_setOf]
    apply And.intro
    use B
    rw [← hdi, ← hej]
    exact And.intro (FactorLeFactor (sInf S) hdb) (FactorLeFactor (sInf S) heb)
  obtain ⟨I, hi, h2⟩ := AscendingUnionMem h1
  have h3 : (sInf S) ≤ I := sInf_le hi
  have h4 : I ≤ sInf S := by
    apply le_sInf
    intro J hj
    rw [← DvdIffLe, ← mul_dvd_mul_iff_left hz]
    nth_rewrite 1 [← FactorMulEq h3]
    nth_rewrite 2 [← FactorMulEq (sInf_le hj)]
    repeat rw [mul_assoc]
    rw [mul_comm J I]
    apply mul_dvd_mul_right
    rw [DvdIffLe, h2]
    apply LeAscendingUnion h1 (Factor (sInf S) J)
    rw [Set.mem_setOf]
    use J
  rw [le_antisymm h3 h4]
  exact hi

def DescendingIntersection (ht : Descending S) (hz : sInf S ≠ 0) : S := by
  use sInf S
  exact DescendingIntersectionMem ht hz

#print axioms DescendingIntersectionMem

-- variable {A : Type} (r : A → A → Prop)

-- def Directed' := ∀ x y : A, ∃ z : A, r x z ∧ r y z

-- lemma DirectedOnIff (S : Set A) : DirectedOn r S ↔ Directed' fun (x y : S) ↦ r x y := by
--   simp only [Directed', DirectedOn, Subtype.forall, Subtype.exists, exists_prop]
    -- apply Iff.intro
    -- · intro h x y
    --   obtain ⟨z, hz, hxz, hyz⟩ := h x x.mem y y.mem
    --   use { val := z, property := hz}
    -- · intro h x hx y hy
    --   obtain ⟨z, hz⟩ := h { val := x, property := hx } { val := y, property := hy}
    --   use z
    --   apply And.intro
    --   · exact z.mem
    --   · exact hz

-- variable {M : Type} [CommMonoid M]

-- def Powers (a : M) := sInf {N : Submonoid M | a ∈ N}

-- -- variable (M) in
-- -- lemma CommMonoidDvdDirected : Directed' M (· ∣ ·) := by
-- --     intro x y
-- --     use x * y
-- --     simp

-- -- lemma PowersDescending (I : Ideal R) : Descending (Powers I).carrier := by
-- --     rw [Descending]
-- --     simp [ge_iff_le]
-- --     simp [← DvdIffLe]
-- --     rw [DirectedOnIff]

-- --     -- apply CommMonoidDvdDirected

-- --     have h := CommMonoidDvdDirected (Powers I)
-- --     simp [Directed']
-- --     simp [Directed'] at h

-- --     sorry

-- lemma SubmonoidDvdDirected (N : Submonoid M) : DirectedOn (· ∣ ·) N.carrier := by
--     intro x hx y hy
--     use x * y
--     simp
--     exact mul_mem hx hy

-- lemma PowersDescending (I : Ideal R) : Descending (Powers I).carrier := by
--     dsimp [Descending]
--     simp [← DvdIffLe]
--     apply SubmonoidDvdDirected

-- instance {N : Submonoid M} : Nonempty N.carrier := sorry

-- variable (I P : Ideal R)

-- def ContainingPowers := {Q ∈ Powers P | I ≤ Q}

-- def MaxPower := sInf (ContainingPowers I P)

-- lemma ContainingPowersDescending : Descending (ContainingPowers I P) := by
--     rw [ContainingPowers, Descending, DirectedOn]
--     simp
--     intro x hx hix y hy hiy
--     use x ⊓ y
--     -- apply And.intro

--     -- simp

--     sorry

-- lemma MaxPowerInPowers {I : Ideal R} (hz : I ≠ 0) (P : Ideal R) :
--     MaxPower I P ∈ Powers P := by
--     -- have h := DescendingIntersectionMem
--     -- apply DescendingIntersectionMem (PowersDescending P)
--     sorry
