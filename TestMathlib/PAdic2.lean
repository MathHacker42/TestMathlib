import Mathlib.Algebra.Algebra.Operations
import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

-- variable {R S X Y Z : Type} [CommRing R] [CommRing S]

lemma surj_right_cancel {X Y Z : Type} (f : X → Y) (hs : Function.Surjective f)
    (g h : Y → Z) (he : g ∘ f = h ∘ f) : g = h := by
    ext x
    obtain ⟨y, hy⟩ := hs x
    rw [← hy]
    have h1 : (g ∘ f) y = (g ∘ f) y := rfl
    nth_rw 2 [he] at h1
    simp at h1
    exact h1

-- def comm_rings := {t : Type | CommRing t}

lemma lift_unique {R S : Type} [CommRing R] [CommRing S] {I : Ideal R}
    (f : R →+* S) (g : R ⧸ I → S) (h : g ∘ (Ideal.Quotient.mk I) = f)
    (H : ∀ a : R, a ∈ I → f a = 0) :
    Ideal.Quotient.lift I f H = g := by
    apply surj_right_cancel (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [h]
    rfl

variable {ι : Type} [Preorder ι]

class RingSystem (F : ι → Type) [∀ i : ι, CommRing (F i)]
    (f : {i j : ι} → i ≤ j → F i →+* F j)
    extends DirectedSystem F (fun ⦃_ _⦄ h ↦ f h)

def product (F : ι → Type) := Π i : ι, F i

variable {F : ι → Type} [∀ i : ι, CommRing (F i)]

def extract (R : Type) [cr : CommRing R] : CommRing R := by exact cr

instance : CommRing (product F) := extract (Π i : ι, F i)

def prod_proj (F : ι → Type) [∀ i : ι, CommRing (F i)] (i : ι) : product F →+* F i := by

    sorry

variable {f : {i j : ι} → i ≤ j → F i →+* F j}

def help (F : ι → Type) [∀ i : ι, CommRing (F i)] {i j : ι} (h : i ≤ j) :
    product F →+* product F := sorry

def limit (_ : RingSystem F f) : Subring (product F) :=
    ⨅ p : {(i, j) : ι × ι | i ≤ j}, (help F p.2).range

lemma sub_system (rs : RingSystem F f) (S : Set ι) :
    RingSystem (fun i : S ↦ F i) (fun {_ _ : S} h ↦ f h) where
    map_self := by simp [rs.map_self]
    map_map := by simp [rs.map_map]

def proj {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) : R⧸I →+* R⧸J := by
    apply Ideal.Quotient.lift I (Ideal.Quotient.mk J)
    simp [← RingHom.mem_ker]
    exact h

variable (R : Type) [CommRing R]

lemma quotient_system : RingSystem (fun I ↦ R⧸I) proj where
    map_self := by
        intro I
        rw [proj]
        have duh (f : R⧸I → R⧸I) (h_eq : f = id) : ∀ x : R⧸I, f x = x := by
            simp [h_eq]
        apply duh
        apply lift_unique
        rfl
    map_map := by
        intro K J I hij hjk
        repeat rw [proj]
        have duh (f : R⧸I →+* R⧸J) (g : R⧸J →+* R⧸K) (h : R⧸I →+* R⧸K)
            (h_eq : h = g ∘ f) : ∀ x : R⧸I, g (f x) = h x := by
            simp [h_eq]
        apply duh
        apply lift_unique
        rfl

def profinite_limit := limit (sub_system (quotient_system R) {I : Ideal R | I ≠ ⊥})

-- variable [IsPrincipalIdealRing R]
