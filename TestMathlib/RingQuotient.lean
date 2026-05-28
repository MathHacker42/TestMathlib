import Mathlib.Algebra.Algebra.Operations
import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TestMathlib.Util

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S]

def quotient_up : (R⧸I →+* S) ≃ {s : R →+* S | I ≤ RingHom.ker s} where
    toFun (f) := by
        use RingHom.comp f (Ideal.Quotient.mk I)
        intro x h
        have hx : (Ideal.Quotient.mk I) x = 0 := by
            rw [← RingHom.mem_ker, Ideal.mk_ker]
            exact h
        simp [hx]
    invFun (s) := Ideal.Quotient.lift I s s.2
    left_inv := by
        rw [Function.leftInverse_iff_comp]
        ext f r;
        simp
    right_inv := by
        rw [Function.rightInverse_iff_comp]
        ext s r;
        simp

#print axioms quotient_up

def quotient_lift := (quotient_up I S).invFun
