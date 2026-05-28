import Mathlib.Algebra.Algebra.Operations
import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TestMathlib.Order
import TestMathlib.Powers
import TestMathlib.RingProduct
import TestMathlib.RingLimit
import TestMathlib.RingQuotient
import TestMathlib.RingMisc
import TestMathlib.Util

variable {R : Type} [CommRing R] (S : Set (Ideal R))

def Proj {I J : Ideal R} (h : I ≤ J) : R⧸I →+* R⧸J := by
  apply quotient_lift
  use Ideal.Quotient.mk J
  rw [Set.mem_setOf, Ideal.mk_ker]
  exact h
  -- apply Ideal.Quotient.lift I (Ideal.Quotient.mk J)
  -- simp [← RingHom.mem_ker]
  -- exact h

lemma ProjCompProj {I J K : Ideal R} (hij : I ≤ J) (hjk : J ≤ K) :
  RingHom.comp (Proj hjk) (Proj hij) = Proj (le_trans hij hjk) := by
  dsimp [Proj, quotient_lift]
  apply EqSymmApply
  rfl

lemma ProjSelf {I : Ideal R} (h : I ≤ I) : Proj h = RingHom.id (R ⧸ I) := by

  sorry

def QuotientSystem := fun ⦃I J : S⦄ ↦ fun h : I ≤ J ↦ Proj h

def QuotientLimit := limit (QuotientSystem S)

def QuotientProjections := limit_projections (QuotientSystem S)

variable (R)

def NonzeroIdeals := {I : Ideal R | I ≠ 0}

def ProfiniteLimit := QuotientLimit (NonzeroIdeals R)

def ProfiniteProjections := QuotientProjections (NonzeroIdeals R)

def NonzeroPrimes := {I ∈ NonzeroIdeals R | I.IsPrime}

variable (N : NonzeroIdeals R) (P : NonzeroPrimes R)

variable {R} in
def Adic : Type := QuotientLimit (Powers P.val)

def AdicProjections := QuotientProjections (Powers P.val)

instance : CommRing (Adic P) := extract (QuotientLimit (Powers P.val))

def PAdicProduct := @product (NonzeroPrimes R) Adic

instance : CommRing (PAdicProduct R) := extract
  (@product (NonzeroPrimes R) fun P ↦ QuotientLimit (Powers P.val))

variable {R} (I : Ideal R)

def PA_PP : PAdicProduct R →+* (Adic P)
  := product_projections Adic P

def ContainingPowers := {Q ∈ Powers I | N ≤ Q}

lemma ContainingPowersInPowers : ContainingPowers N I ≤ Powers I := by
  intro Q ⟨hq, _⟩
  exact hq

instance : Nonempty (ContainingPowers N I) := by
  apply Nonempty.intro
  use ⊤
  rw [ContainingPowers]
  simp
  rw [← Ideal.one_eq_top]
  apply OneInPowers

def MaxPower := sInf (ContainingPowers N I)

def MP := R ⧸ MaxPower N P

instance : CommRing (MP N P) := extract (R ⧸ MaxPower N P)

def NProduct := product (MP N)

instance : CommRing (NProduct N) := extract (product (MP N))





variable [IsPrincipalIdealRing R] [IsDomain R]

def ToNonzero (Q : Powers P.val) :
  NonzeroIdeals R := { val := Q, property := PowersNonzero P.mem.left Q.mem}

def ForwardMap : ProfiniteLimit R →+* PAdicProduct R := by
  apply product_lift
  intro P
  apply limit_lift
  use fun Q ↦ (ProfiniteProjections R).val (ToNonzero P Q)
  intro I J h
  -- have h2 := (ProfiniteProjections R).property
  -- dsimp [system_projections] at h2
  -- have h3 := h2 I J h
  exact (ProfiniteProjections R).property (ToNonzero P I) (ToNonzero P J) h

#print axioms ForwardMap

lemma MaxPowerInContainingPowers : MaxPower N I ∈ ContainingPowers N I := by
  apply DescendingIntersectionMem
  · rw [Descending]
    apply DirectedOnIfReflexiveAndTotalOn
    · intro x hx
      simp
    · apply SubsetTotalOn (ContainingPowersInPowers N I)
      simp only [ge_iff_le, ← DvdIffLe]
      apply PowersTotalOrdered
  · intro hs
    apply N.property
    apply le_antisymm
    · rw [← hs, le_sInf_iff]
      intro Q hq
      exact hq.right
    · simp

def MaxPowerAsPower : Powers I := by
  use MaxPower N I
  apply ContainingPowersInPowers N I
  exact MaxPowerInContainingPowers N I

def MP_PA := (QuotientProjections (Powers P.val)).val (MaxPowerAsPower N P)

-- def PA_PP :=

def MP_PP := RingHom.comp (MP_PA N P) (PA_PP P)

-- def MPP := fun P ↦ MP_PP N P

def NP_PP : PAdicProduct R →+* NProduct N := by
  apply product_lift
  exact fun P ↦ MP_PP N P

def NP_R : R →+* NProduct N := by
  apply product_lift
  intro P
  exact mk (MaxPower N P)

def CRTExt : Function.Surjective (NP_R N) := sorry

def UFDConsequence : RingHom.ker (NP_R N) = ↑N := by sorry

-- noncomputable def NP_N : R ⧸ N.val ≃+* NProduct N := by
--   rw [← UFDConsequence N]
--   exact RingHom.quotientKerEquivOfSurjective (CRTExt N)

-- noncomputable def NP_N_2 : R ⧸ N.val ≃+* NProduct N where
--   toFun := sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry
--   map_mul' := sorry
--   map_add' := sorry


-- lemma BlackBox : Function.Bijective (NP_N_3 N) := sorry

-- noncomputable def foo : PAdicProduct R →+* R ⧸ N.val :=
--   RingHom.comp ((baz N).symm) (baz2 N)

def MP_N := Proj (MaxPowerInContainingPowers N P).right

noncomputable def NP_N : R ⧸ N.val →+* NProduct N := by
  apply product_lift
  exact fun P ↦  MP_N N P

noncomputable def N_NP : NProduct N →+* R ⧸ N.val := sorry

lemma N_id : (N_NP N).comp (NP_N N) = RingHom.id (R ⧸ N.val) := sorry

lemma NP_id : (NP_N N).comp (N_NP N) = RingHom.id (NProduct N) := sorry

lemma foo : (product_projections (MP N) P).comp (NP_N N) = MP_N N P := by
  rw [NP_N, proj_comp_lift]

lemma bar : product_projections (MP N) P = (MP_N N P).comp (N_NP N) := by
  rw [← foo, RingHom.comp_assoc, NP_id, RingHom.comp_id]

variable {P} in
lemma bwaaa (Q : Powers P.val) : MaxPower (ToNonzero P Q) P = Q.val := by
  dsimp [MaxPower]
  apply le_antisymm
  · apply sInf_le
    simp [ContainingPowers]
    rfl
  · apply le_sInf
    intro J hj
    exact hj.right

def MP_MP {I J : NonzeroIdeals R} (h : I ≤ J) : (MP I P) →+* (MP J P) := by
  apply Proj
  apply sInf_le_sInf
  intro Q ⟨hq, hjq⟩
  exact And.intro hq (le_trans h hjq)

noncomputable def ReverseMap : PAdicProduct R →+* ProfiniteLimit R := by
  apply limit_lift
  use fun N ↦ RingHom.comp (N_NP N) (NP_PP N)
  intro I J h
  dsimp [QuotientSystem]
  apply EqInvComp (N_id J)
  nth_rw 2 [NP_PP]
  rw [product_lift]
  apply EqInvApply
  dsimp [product_equiv]
  funext P
  rw [← RingHom.comp_assoc]
  rw [foo J]
  rw [← RingHom.comp_assoc]
  have h1 : (MP_N J P).comp (Proj h) = (MP_MP P h).comp (MP_N I P) := by
    dsimp [MP_N, MP_MP]
    repeat rw [ProjCompProj]
  rw [h1]
  rw [← RingHom.comp_assoc]
  nth_rw 2 [RingHom.comp_assoc]
  rw [← EqCompInv (NP_id I) (foo I P)]
  rw [RingHom.comp_assoc]
  dsimp [NP_PP]
  rw [proj_comp_lift]
  dsimp [MP_PP]
  rw [← RingHom.comp_assoc]
  have h2 : (MP_MP P h).comp (MP_PA I P) = MP_PA J P := by
    apply (limit_projections (QuotientSystem (Powers P.val))).property
      (MaxPowerAsPower I P) (MaxPowerAsPower J P)
  rw [h2]

theorem LeftInverse : ReverseMap.comp ForwardMap = RingHom.id (ProfiniteLimit R) := by
  apply apply_limit_proj
  intro N
  -- rw [RingHom.comp_id]
  rw [← RingHom.comp_assoc]
  dsimp [ReverseMap]
  rw [RingHom.comp_assoc]
  symm
  apply EqInvComp (N_id N)
  apply apply_product_proj
  intro P
  rw [← RingHom.comp_assoc]
  dsimp [NP_N]
  -- rw [← RingHom.comp_assoc]
  -- dsimp [NP_PP, MP_PP]
  -- rw [RingHom.comp_assoc]
  -- dsimp [PA_PP, ForwardMap]
  -- rw [proj_comp_lift]
  -- dsimp [MP_PA, QuotientProjections]
  -- rw [← QuotientProjections, ← ProfiniteProjections]
  apply (ProfiniteProjections R).property N (ToNonzero P (MaxPowerAsPower N ↑P))

theorem RightInverse : ForwardMap.comp ReverseMap = RingHom.id (PAdicProduct R) := by
  apply apply_product_proj
  intro P
  rw [RingHom.comp_id]
  rw [← RingHom.comp_assoc]
  dsimp [ForwardMap]
  apply apply_limit_proj
  intro Q
  rw [← RingHom.comp_assoc]
  rw [limit_proj_comp_lift]
  simp
  dsimp [ReverseMap]
  dsimp [ProfiniteProjections]
  dsimp [QuotientProjections]
  rw [limit_proj_comp_lift]
  simp
  obtain ⟨h1, h2⟩ := (le_antisymm_iff.mp) (bwaaa Q)
  have h3 : (Proj h1).comp (Proj h2) = RingHom.id (R ⧸ Q.val) := by
    rw [ProjCompProj, ProjSelf]
  apply CompInv h3
  have h7 : Proj h2 = MP_N (ToNonzero P Q) P := rfl
  nth_rw 1 [h7]
  rw [← RingHom.comp_assoc]
  rw [← bar]
  dsimp [NP_PP]
  rw [proj_comp_lift]
  rw [← RingHom.comp_assoc]
  rw [← QuotientProjections]
  have h6 := (QuotientProjections (Powers P.val)).property
    Q (MaxPowerAsPower (ToNonzero P Q) ↑P) h2
  dsimp [QuotientSystem] at h6
  rw [h6]
  rfl




















-- lemma NP_N_comp_mk : RingHom.comp (NP_N N) (Ideal.Quotient.mk N) = NP_R N := by
--   ext r
--   rw [RingHom.comp_apply, NP_N]
--   have h := RingHom.quotientKerEquivOfSurjective_apply_mk (CRTExt N) r
--   have h2 := UFDConsequence N
--   -- rw [h2] at h
--   rw [← h]
--   -- rw [h2]
--   -- rw [UFDConsequence N] at h
--   -- rw [← UFDConsequence N]

--   sorry

-- lemma NP_equiv : (NP_N N).toRingHom = NP_N_3 N := by
--   dsimp [NP_N_3]
--   apply EqSymmApply
--   funext P
--   dsimp [product_equiv, Proj, quotient_lift]
--   apply EqSymmApply
--   dsimp [quotient_up]
--   simp
--   -- dsimp [MP]
--   -- rw [MP]
--   -- rw [← MP]
--   rw [RingHom.comp_assoc]
--   -- dsimp [NP_N]
--   -- ext r
--   -- rw [RingHom.comp_apply]
--   -- rw [RingHom.comp_apply]
--   -- rw [NP_N]


--   -- rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
--   -- apply
--   sorry
