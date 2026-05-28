import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.Quot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

variable {R : Type} [Ring R] {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]

alias qm := Ideal.Quotient.mk

@[simp]
lemma ker_qm (I : Ideal R) [I.IsTwoSided] : RingHom.ker (qm I) = I := Ideal.mk_ker

lemma qm_surj (I : Ideal R) [I.IsTwoSided] : Function.Surjective (qm I) :=
  Ideal.Quotient.mk_surjective

@[simp]
lemma qm_eq_zero_iff {i : R} : (qm I) i = 0 ↔ i ∈ I := by
  simp [← RingHom.mem_ker]

@[simp]
lemma qm_eq_zero (i : I) : (qm I) i = 0 := by simp [*]

@[simp]
def pqm (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] :
  R →+* (R ⧸ I) × (R ⧸ J) := RingHom.prod (qm I) (qm J)

@[simp]
lemma ker_pqm (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] : RingHom.ker (pqm I J) = I ⊓ J := by
  ext x
  simp

theorem pqm_surj (h : I ⊔ J = ⊤) :
  Function.Surjective (pqm I J) := by
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup'] at h
  obtain ⟨i, j, h⟩ := h
  apply_fun pqm I J at h
  simp [*] at h
  intro b
  obtain ⟨ri, hri⟩ := (qm_surj I) b.1
  obtain ⟨rj, hrj⟩ := (qm_surj J) b.2
  use i * rj + j * ri
  simp [*]

noncomputable def pqm_iso_ker (h : I ⊔ J = ⊤) :
  R ⧸ RingHom.ker (pqm I J) ≃+* (R ⧸ I) × (R ⧸ J) :=
  RingHom.quotientKerEquivOfSurjective (pqm_surj h)

noncomputable def pqm_iso_inf (h : I ⊔ J = ⊤) :
  R ⧸ (I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [← ker_pqm]
  exact pqm_iso_ker h

noncomputable def pqm_iso_mul (h : I ⊔ J = ⊤) :
  R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [Ideal.mul_eq_inf_of_coprime h]
  exact pqm_iso_inf h

noncomputable def pqm_inv_ker (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ RingHom.ker (pqm I J) :=
  (pqm_iso_ker h).symm

noncomputable def pqm_inv_inf (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I ⊓ J) :=
  (pqm_iso_inf h).symm

noncomputable def pqm_inv_mul (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I * J) :=
  (pqm_iso_mul h).symm
