import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

variable {R : Type} [CommRing R]

theorem mul_le_right (I J : Ideal R) : I * J ≤ J := by
  rw [Submodule.mul_le]
  intro i hi j hj
  apply Submodule.smul_mem
  exact hj

theorem mul_le_left (I J : Ideal R) : I * J ≤ I := by
  rw [mul_comm]
  apply mul_le_right

theorem mul_le_inf (I J : Ideal R) : I * J ≤ I ⊓ J := by
  apply le_inf
  · apply mul_le_left
  · apply mul_le_right

theorem mul_le_mul_left_ (I J K : Ideal R) (hle : J ≤ K) : I * J ≤ I * K := by
  rw [Submodule.mul_le]
  intro i hi j hj
  exact Submodule.mul_mem_mul hi (hle hj)

theorem mul_le_mul_right_ (I J K : Ideal R) (hle : J ≤ K) : J * I ≤ K * I := by
  repeat rw [← mul_comm I]
  apply mul_le_mul_left_
  exact hle

theorem mul_sup_ (I J K : Ideal R) : I * (J ⊔ K) = I * J ⊔ I * K := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro i hi n hn
    rw [Submodule.mem_sup] at hn
    obtain ⟨j, hj, k, hk, hn⟩ := hn
    rw [← hn, mul_add]
    have hij := Submodule.mul_mem_mul hi hj
    have hik := Submodule.mul_mem_mul hi hk
    exact Submodule.add_mem_sup hij hik
  · apply sup_le
    · apply mul_le_mul_left_
      exact le_sup_left
    · apply mul_le_mul_left_
      exact le_sup_right

theorem inf_mul_sup_ (I J : Ideal R) : (I ⊓ J) * (I ⊔ J) ≤ I * J := by
  rw [Ideal.mul_sup]
  apply sup_le
  · rw [mul_comm]
    apply mul_le_mul_left_
    exact inf_le_right
  · apply mul_le_mul_right_
    exact inf_le_left

theorem mul_eq_inf {I J : Ideal R} (h : I ⊔ J = ⊤) : I * J = I ⊓ J := by
  apply le_antisymm
  · apply mul_le_inf
  · have h2 := inf_mul_sup_ I J
    rw [h, Ideal.mul_top] at h2
    exact h2

#print axioms Ideal.span_one
#print axioms Ideal.mem_span_singleton_self

theorem one_mem_top : 1 ∈ (⊤ : Ideal R) := by
  rw [← Ideal.span_one]
  apply Ideal.mem_span_singleton_self

#print axioms one_mem_top

theorem le_one_mem (I J : Ideal R) (h : 1 ∈ I) : (J ≤ I) := by
  intro x h2
  have h3 := Submodule.smul_mem I x h
  simp at h3
  exact h3

#print axioms le_one_mem

theorem eq_one_iff_one_mem (I : Ideal R) : I = ⊤ ↔ 1 ∈ I := by
  apply Iff.intro
  · intro h
    rw [h]
    exact one_mem_top
  · intro h
    apply le_antisymm
    · exact le_one_mem ⊤ I one_mem_top
    · exact le_one_mem I ⊤ h

#print axioms eq_one_iff_one_mem

theorem one_mem {I : Ideal R} (h : I = ⊤) : 1 ∈ I := by
  rw [h]
  exact one_mem_top

variable {A B C : Type} [Semiring A] [Semiring B] [Semiring C]

@[simps]
def rhp (f : A →+* B) (g : A →+* C) : A →+* B × C where
  toFun := fun x => (f x, g x)
  map_one' := by simp
  map_zero' := by simp
  map_mul' := by simp
  map_add' := by simp

@[simp]
theorem ker_rhp (f : A →+* B) (g : A →+* C) :
  RingHom.ker (rhp f g) = (RingHom.ker f) ⊓ (RingHom.ker g) := by
  ext x
  simp

alias mk := Ideal.Quotient.mk

@[simp]
theorem ker_mk (I : Ideal R) : RingHom.ker (mk I) = I := Ideal.mk_ker

theorem mk_surj (I : Ideal R) : Function.Surjective (mk I) :=
 Ideal.Quotient.mk_surjective

@[simp]
theorem mk_eq_zero {I : Ideal R} {i : R} (hi : i ∈ I) : (mk I) i = 0 := by
  simp [← RingHom.mem_ker, *]

@[simp]
def pmk (I J : Ideal R) : R →+* (R ⧸ I) × (R ⧸ J) := rhp (mk I) (mk J)

@[simp]
theorem ker_pmk (I J : Ideal R) :
  RingHom.ker (pmk I J) = I ⊓ J := by
  simp

theorem pmk_surj {I J : Ideal R} (h : I ⊔ J = ⊤) :
  Function.Surjective (pmk I J) := by
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h
  obtain ⟨i, hi, j, hj, h1⟩ := h
  apply_fun pmk I J at h1
  simp [*] at h1
  intro b
  obtain ⟨ri, hri⟩ := (mk_surj I) b.1
  obtain ⟨rj, hrj⟩ := (mk_surj J) b.2
  use i * rj + j * ri
  simp [*]

noncomputable def pmk_iso_ker {I J : Ideal R} (h : I ⊔ J = ⊤) :
  R ⧸ RingHom.ker (pmk I J) ≃+* (R ⧸ I) × (R ⧸ J) :=
  RingHom.quotientKerEquivOfSurjective (pmk_surj h)

noncomputable def pmk_iso_inf {I J : Ideal R} (h : I ⊔ J = ⊤) :
  R ⧸ (I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [← ker_pmk]
  exact pmk_iso_ker h

noncomputable def pmk_iso_mul {I J : Ideal R} (h : I ⊔ J = ⊤) :
  R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [mul_eq_inf h]
  exact pmk_iso_inf h

noncomputable def pmk_inv_ker {I J : Ideal R} (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ RingHom.ker (pmk I J) :=
  (pmk_iso_ker h).symm

noncomputable def pmk_inv_inf {I J : Ideal R} (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I ⊓ J) :=
  (pmk_iso_inf h).symm

noncomputable def pmk_inv_mul {I J : Ideal R} (h : I ⊔ J = ⊤) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I * J) :=
  (pmk_iso_mul h).symm
