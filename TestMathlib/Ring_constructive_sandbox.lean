import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.Quot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

variable {R : Type} [CommRing R]

alias mk := Ideal.Quotient.mk

@[simp]
lemma ker_mk (I : Ideal R) : RingHom.ker (mk I) = I := Ideal.mk_ker

lemma mk_surj (I : Ideal R) : Function.Surjective (mk I) :=
 Ideal.Quotient.mk_surjective

@[simp]
lemma mk_eq_zero_iff {I : Ideal R} {i : R} : (mk I) i = 0 ↔ i ∈ I  := by
  simp [← RingHom.mem_ker]

@[simp]
lemma mk_eq_zero {I : Ideal R} (i : I) : (mk I) i = 0 := by simp [*]

@[simp]
def pmk (I J : Ideal R) : R →+* (R ⧸ I) × (R ⧸ J) := RingHom.prod (mk I) (mk J)

@[simp]
lemma ker_pmk (I J : Ideal R) : RingHom.ker (pmk I J) = I ⊓ J := by
  ext x
  simp

def span (x : R) : Ideal R := Ideal.span {x}

#print axioms span

lemma ideal_le_top (I : Ideal R) : I ≤ ⊤ := OrderTop.le_top I

#print axioms ideal_le_top
#print axioms OrderTop
#print axioms OrderTop.le_top
#print axioms Ideal

def ideal_id (I : Ideal R) : Ideal R := I

#print axioms ideal_id

def comp_ideal (I J : Ideal R) := I ≤ J

#print axioms comp_ideal



def sub_ideal (I J : Ideal R) := ∀ x : R, x ∈ I → x ∈ J

#print axioms sub_ideal


def coprime1 (I J : Ideal R) : Prop := 1 ∈ I ⊔ J

#print axioms coprime1

def coprime (I J : Ideal R) : Prop := ∃ i : I, ∃ j : J, (i : R) + (j : R) = (1 : R)

#print axioms coprime


def coprime2 (I J : Ideal R) : Prop := I ⊔ J = ⊤

#print axioms coprime2

def eq_top (I : Ideal R) := I = ⊤

#print axioms eq_top

def sup (I J : Ideal R) := I ⊔ J

#print axioms sup

def sum (I J : Ideal R) := I + J

#print axioms sum

def inf (I J : Ideal R) := I ⊓ J
#print axioms inf

lemma mul_eq_inf_of_coprime {I J : Ideal R} (h : coprime I J) :
  I * J = I ⊓ J := by
  ext x
  constructor

  sorry



lemma span_le_top (x : R) : span x ≤ ⊤ := OrderTop.le_top span x

#print axioms span_le_top

theorem mem_top (x : R) : x ∈ (⊤ : Ideal R) :=
  OrderTop.le_top span x (Ideal.mem_span_singleton_self x)

-- #print axioms ⊤
#print axioms CommRing
#print axioms Ideal
#print axioms OrderTop
#print axioms OrderTop.le_top
#print axioms Ideal.span
#print axioms Ideal.mem_span_singleton_self
#print axioms mem_top

#print axioms Ideal.eq_top_iff_one
#print axioms Submodule.mem_sup'
#print axioms mk_surj

theorem pmk_surj {I J : Ideal R} (h : coprime I J) :
  Function.Surjective (pmk I J) := by
  obtain ⟨i, j, h⟩ := h
  apply_fun pmk I J at h
  simp [*] at h
  intro b
  obtain ⟨ri, hri⟩ := (mk_surj I) b.1
  obtain ⟨rj, hrj⟩ := (mk_surj J) b.2
  use i * rj + j * ri
  simp [*]

#print axioms pmk_surj

noncomputable def pmk_iso_ker {I J : Ideal R} (h : coprime I J) :
  R ⧸ RingHom.ker (pmk I J) ≃+* (R ⧸ I) × (R ⧸ J) :=
  RingHom.quotientKerEquivOfSurjective (pmk_surj h)

noncomputable def pmk_iso_inf {I J : Ideal R} (h : coprime I J) :
  R ⧸ (I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [← ker_pmk]
  exact pmk_iso_ker h

noncomputable def pmk_iso_mul {I J : Ideal R} (h : coprime I J) :
  R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  rw [Ideal.mul_eq_inf_of_coprime h]
  exact pmk_iso_inf h

noncomputable def pmk_inv_ker {I J : Ideal R} (h : coprime I J) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ RingHom.ker (pmk I J) :=
  (pmk_iso_ker h).symm

noncomputable def pmk_inv_inf {I J : Ideal R} (h : coprime I J) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I ⊓ J) :=
  (pmk_iso_inf h).symm

noncomputable def pmk_inv_mul {I J : Ideal R} (h : coprime I J) :
  (R ⧸ I) × (R ⧸ J) ≃+* R ⧸ (I * J) :=
  (pmk_iso_mul h).symm
