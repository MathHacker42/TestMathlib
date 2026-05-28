import Mathlib.Algebra.Algebra.Operations
import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TestMathlib.Util

variable {U : Type} (F : U → Type) [∀ i : U, CommRing (F i)] (R : Type) [CommRing R]

def product := (i : U) → F i

instance ProductCommRing : CommRing (product F) := extract (Π i : U, F i)

def projections := (i : U) → R →+* F i

def product_projections : projections F (product F) := fun i ↦ {
  toFun := fun f ↦ f i
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intro x y; rfl
  map_mul' := by intro x y; rfl
}

-- def product_lift (p : projections F R) : R →+* product F where
--     toFun := fun r ↦ fun i ↦ p i r
--     map_zero' := by simp; rfl
--     map_one' := by simp; rfl
--     map_add' := by intro x y; simp; rfl
--     map_mul' := by intro x y; simp; rfl

-- @[simps]
-- def product_up : Bijection (R →+* product F) (projections F R) where
--   L_to_R (f) := fun i ↦ RingHom.comp (product_projections F i) f
--   R_to_L (p) := {
--     toFun := fun r ↦ fun i ↦ p i r
--     map_zero' := by simp; rfl
--     map_one' := by simp; rfl
--     map_add' := by intro x y; simp; rfl
--     map_mul' := by intro x y; simp; rfl
--   }
--   L_id := rfl
--   R_id := rfl

-- @[simp]
-- def product_lift := (product_up F R).R_to_L

-- #print axioms product_up

@[simps]
def product_equiv : (R →+* product F) ≃ (projections F R) where
  toFun (f) := fun i ↦ RingHom.comp (product_projections F i) f
  invFun (p) := {
    toFun := fun r ↦ fun i ↦ p i r
    map_zero' := by simp; rfl
    map_one' := by simp; rfl
    map_add' := by intro x y; simp; rfl
    map_mul' := by intro x y; simp; rfl
  }
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    rfl
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    rfl

-- @[simp]
def product_lift := (product_equiv F R).invFun

#print axioms product_equiv

@[simp]
lemma proj_comp_lift (i : U) (p : projections F R) :
  RingHom.comp (product_projections F i) (product_lift F R p) = p i := rfl

lemma apply_product_proj {g1 g2 : R →+* product F}
    (h : ∀ i : U, (product_projections F i).comp g1 = (product_projections F i).comp g2)
    : g1 = g2 := by
    apply ApplyEquiv (product_equiv F R) g1 g2
    simp [product_equiv]
    funext i
    exact h i

-- def foo (f : R →+* product F) : projections F R :=
--     fun (i : U) ↦ RingHom.comp (product_projections F i) f

-- def lift (g : projections F R) : R →+* product F where
--     toFun := fun r ↦ fun i ↦ g i r
--     map_zero' := by
--         simp
--         rfl
--     map_one' := by
--         simp
--         rfl
--     map_add' := by
--         intro x y
--         simp
--         rfl
--     map_mul' := by
--         intro x y
--         simp
--         rfl

-- lemma bar : (foo F R) ∘ (lift F R) = id := rfl

-- lemma baz : (lift F R) ∘ (foo F R) = id := rfl












-- theorem bar : Function.Bijective (foo F R) := sorry

-- theorem bar2 : Function.Bijective
--     fun f : R →+* product F ↦ fun i : U ↦ prod_proj F i ∘ f := by
--     simp [prod_proj]

--     simp [prod_proj, Function.Bijective, Function.Injective, Function.Surjective]
--     -- apply And.intro
--     sorry

-- variable (proj : (i : U) → R →+* F i)

-- def prod_lift : R →+* product F where
--     toFun := fun r ↦ fun i ↦ proj i r
--     map_zero' := by
--         simp
--         rfl
--     map_one' := by
--         simp
--         rfl
--     map_add' := by
--         intro x y
--         simp
--         rfl
--     map_mul' := by
--         intro x y
--         simp
--         rfl

-- lemma duh : (R →+* product F) = (R →+* Π i : U, F i) := rfl

-- def prod_up : MyExistsUnique
--     fun f : R →+* product F ↦ ∀ i : U, prod_proj F i ∘ f = proj i where
--     object := prod_lift F R proj
--     satisfies := by
--         intro i
--         rfl
--     unique := by
--         simp [product, prod_proj]
--         intro f g hf hg
--         ext r i
--         have hf := hf i
--         have hg := hg i
--         have h := Eq.trans hf hg.symm
--         have h1 := EvalFunctions h r
--         simp at h1
--         exact h1
