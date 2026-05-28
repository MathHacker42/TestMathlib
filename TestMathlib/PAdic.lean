-- import Mathlib.Order.DirectedInverseSystem

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps

import TestMathlib.Ring

import Mathlib.Order.SetNotation

variable {R : Type} [CommRing R]

-- def Ideals := Set (Ideal R)

-- def inv_limit {O : Type} [Preorder O] (F : O → Type R)
--   (f : {i j : O} → i ≤ j → F i →+* F j) : Type := sorry

def test2 {X Y : Type} [CommRing X] [CommRing Y] (f : X →+* Y) : Subring (X × Y) :=
  (RingHom.prod (RingHom.id X) f).range

-- variable {ideals : Set (Ideal R)}

def quot {ideals : Set (Ideal R)} (I : ideals) := R ⧸ (I : Ideal R)

def prod (ideals : Set (Ideal R)) := Π (I : ideals), quot I

-- variable {I J : Ideal R}

-- @[simp]
def proj {I J : Ideal R} (h : I ≤ J) : R ⧸ I →+* R ⧸ J := by
  apply Ideal.Quotient.lift I (qm J)
  simp
  exact h

def inc_comp {ideals : Set (Ideal R)} {I J : ideals} (h : I ≤ J) (K : ideals) :
  (R ⧸ (I : Ideal R)) × (R ⧸ (J : Ideal R)) × (Π (I : ideals), R ⧸ (I : Ideal R))
   →+* R ⧸ (K : Ideal R) := sorry

def inc {ideals : Set (Ideal R)} {I J : ideals} (h : I ≤ J) :
  (R ⧸ (I : Ideal R)) × (R ⧸ (J : Ideal R)) × (Π (I : ideals), R ⧸ (I : Ideal R))
   →+* (Π (I : ideals), R ⧸ (I : Ideal R)) := sorry
  -- Π (I : ideals), (inc_comp h I)
  -- apply RingHom.

-- def comp {ideals : Set (Ideal R)} {I J : ideals} (h : I ≤ J) :
--   Subring (Π (I : ideals), R ⧸ (I : Ideal R)) :=
--   sorry

def inv_lim (ideals : Set (Ideal R)) : Subring (Π (I : ideals), R ⧸ (I : Ideal R)) :=
  sInf {(inc pair_h.2).range | pair_h : {pair : ideals × ideals | pair.1 ≤ pair.2}}

def inv_lim2 (ideals : Set (Ideal R)) : Subring (Π (I : ideals), R ⧸ (I : Ideal R))
  where
  carrier := {f : Π (I : ideals), R ⧸ (I : Ideal R) | ∀ p :
  {p : ideals × ideals | p.1 ≤ p.2}, proj p.2 (f p.1.1) = f p.1.2}
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry


-- def test_subring : Subring R where
--   carrier := sorry
--   mul_mem' := sorry
--   one_mem' := sorry
--   add_mem' := sorry
--   zero_mem' := sorry
--   neg_mem' := sorry

-- @[simp]
-- def proj_forgor (h : I ≤ J) : R ⧸ I → R ⧸ J := proj h

-- instance : DirectedSystem (R ⧸ ·) proj_forgor where
--   map_self _ _ := by

--     simp
--     -- simp [Ideal.Quotient.lift]

--     -- rw [Ideal.Quotient.lift_comp_mk]
--     sorry
--   map_map _ _ _ _ _ _ := by
--     sorry
