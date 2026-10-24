import Mathlib.Algebra.Algebra.Operations
-- import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
-- import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Congruence.Defs

-- def fuu := QuotientGroup.lift
#print axioms QuotientGroup.lift
#print axioms Con.lift
-- #print axioms con_ker_eq_conKer

-- def OrCases {P Q R : Prop} (hpq : P ∨ Q) (hpr : P → R) (hqr : Q → R) :=
--     (@or_imp P Q R).mpr (And.intro hpr hqr) hpq

-- #print axioms OrCases
-- #print axioms or_not

-- def LeftCancel {X Y Z : Type} {f : Y → X} {i : X → Y} (hi : i ∘ f = id)
--     {g h : Z → Y} (hf : f ∘ g = f ∘ h) : g = h := by
--     rw [← Function.id_comp g, ← Function.id_comp h, ← hi,
--         Function.comp_assoc, Function.comp_assoc, hf]

-- lemma id_apply {X : Type} (x : X) : id x = x := by
--     simp?

-- lemma IsInjective {X Y : Type} {f : Y → X} {i : X → Y} (hi : i ∘ f = id) :
--     Function.Injective f := by
--     intro y1 y2 h
--     rw [← id_eq y1, ← id_eq y2, ← hi, Function.comp_apply, Function.comp_apply, h]

-- class Bijection (L R : Type) where
--     L_to_R : L → R
--     R_to_L : R → L
--     L_id : R_to_L ∘ L_to_R = id
--     R_id : L_to_R ∘ R_to_L = id

-- lemma LeftCanceLR {L R X : Type} (B : Bijection L R) {f g : X → L}
--     (h : B.L_to_R ∘ f = B.L_to_R ∘ g) : f = g := LeftCancel B.L_id h

-- lemma InjectiveLR {L R : Type} (B : Bijection L R) : Function.Injective B.L_to_R :=
--     IsInjective B.L_id

instance {α : Type} {f : α → α} {S : Set α} [hn : Nonempty S] : Nonempty {f x | x ∈ S} := by
    obtain ⟨s, hs⟩ := hn
    use f s
    use s




variable {X Y Z : Type}

lemma EqInvApply (f : X ≃ Y) (x : X) (y : Y) (h : f x = y) : x = f.invFun y := by
  rw [← h]
  simp

lemma EqSymmApply {f : X ≃ Y} {x : X} {y : Y} (h : f x = y) : x = f.symm y := by
  rw [← h]
  simp

lemma ApplyEquiv (f : X ≃ Y) (a b : X) (h : f a = f b) : a = b := by
  have h1 := EqSymmApply h
  simp at h1
  exact h1

variable [CommRing X] [CommRing Y] [CommRing Z]

-- lemma EqSymmComp (f : X ≃+* Y) (g : Z →+* X) (h : Z →+* Y) (he : RingHom.comp f g = h) :
--   g = RingHom.comp f.symm h := by
--   rw [← he, ← RingHom.comp_assoc]
--   simp

lemma EqInvComp {f : X →+* Y} {g : Z →+* X} {h : Z →+* Y} {i : Y →+* X}
  (hi : RingHom.comp i f = RingHom.id X) (he : RingHom.comp f g = h) : g = RingHom.comp i h := by
  rw [← he, ← RingHom.comp_assoc, hi, RingHom.id_comp]

lemma EqCompInv {f : X →+* Y} {g : X →+* Z} {h : Y →+* Z} {i : Y →+* X}
  (hi : RingHom.comp f i = RingHom.id Y) (he : h.comp f = g) : h = g.comp i := by
  rw [← he, RingHom.comp_assoc, hi, RingHom.comp_id]

lemma CompInv {f : X →+* Y} {i : Y →+* X} {g h : Z →+* X}
  (hi : i.comp f = RingHom.id X) (he : f.comp g = f.comp h) : g = h := by
  rw [EqInvComp hi he, ← RingHom.comp_assoc, hi, RingHom.id_comp]

def extract (R : Type) [cr : CommRing R] := cr

variable {R S : Type} [CommRing R] [CommRing S] {T : Subring S}

@[simps]
def subring_inclusion (S : Subring R) : S →+* R where
    toFun (s) := s
    map_one' := rfl
    map_mul' := by
        intro x y
        rfl
    map_zero' := rfl
    map_add' := by
        intro x y
        rfl

def restrict (f : R →+* S) (h : ∀ r : R, f r ∈ T) : R →+* T := {
    toFun (r) := by
        use f r
        exact h r
    map_one' := by simp; rfl
    map_mul' := by intro x y; simp
    map_add' := by intro x y; simp
    map_zero' := by simp; rfl
}








-- lemma EvalFunctions {S T : Type} {f g : S → T} (h : f = g) (x : S) : f x = g x := by
--     simp [*]



-- class MyExistsUnique {T : Type} (P : T → Prop) where
--     object : T
--     satisfies : P object
--     unique : ∀ s t : T, P s → P t → s = t

-- def ExistsUniqueFrom (he : )
