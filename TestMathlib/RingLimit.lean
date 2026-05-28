import Mathlib.Algebra.Algebra.Operations
import Mathlib.Order.DirectedInverseSystem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import TestMathlib.Util
import TestMathlib.RingProduct

variable {ι : Type} [Preorder ι] {F : ι → Type}
    [∀ i : ι, CommRing (F i)] (f : ⦃i j : ι⦄ → i ≤ j → F i →+* F j)

def limit : Subring (product F) where
    carrier := {p : product F | ∀ i j : ι, (h : i ≤ j) → f h (p i) = p j}
    mul_mem' := by
        simp
        intro a b ha hb i j
        have foo (k : ι) : (a * b) k = (a k) * (b k) := rfl
        simp [*]
    one_mem' := by
        intro i j h
        have foo (k : ι) : (1 : product F) k = 1 := rfl
        simp [foo]
    add_mem' := by
        simp
        intro a b ha hb i j
        have foo (k : ι) : (a + b) k = (a k) + (b k) := rfl
        simp [*]
    zero_mem' := by
        intro i j h
        have foo (k : ι) : (0 : product F) k = 0 := rfl
        simp [foo]
    neg_mem' := by
        simp
        intro x hx i j h
        have foo (k : ι) : (-x) k = -(x k) := rfl
        simp [*]

instance : CommRing (limit f) := extract (limit f)

lemma eval_limit_help (x : product F) (hx : x ∈ limit f) {i j : ι} (h : i ≤ j) :
    (f h) (x i) = x j := by
    simp [limit] at hx
    exact hx i j h

variable (R : Type) [CommRing R]

@[simp]
def system_projections :=
    {p : projections F R | ∀ i j : ι, (h : i ≤ j) → RingHom.comp (f h) (p i) = p j}

def limit_projections : system_projections f (limit f) := by
    use fun i ↦ RingHom.comp (product_projections F i) (subring_inclusion (limit f))
    intro i j h
    ext x
    exact eval_limit_help f x.val x.property h

-- def Limit := {
--     limit := limit f,
--     projections := limit_projections f
-- }

-- def limit_projection (i : ι) := (limit_projections f).val i

-- variable {f} in
-- def limit_projections' (L : limit f) := limit_projections f

-- @[simp]
-- lemma limit_projections_comp {i j : ι} (h : i ≤ j) :
--     (f h) ∘ ((limit_projections f).1 i) = (limit_projections f).1 j :=
--     (limit_projections f).2 i j h

-- variable {f}

@[simps]
def limit_up : (R →+* limit f) ≃ (system_projections f R) where
    toFun (g) := by
        obtain ⟨lp, hlp⟩ := limit_projections f
        use fun i ↦ RingHom.comp (lp i) g
        simp
        intro i j h
        rw [← RingHom.comp_assoc, hlp i j h]
    invFun (p) := by
        obtain ⟨p, hp⟩ := p
        apply restrict (product_lift F R p)
        intro r i j h
        dsimp [product_lift]
        rw [← hp i j h]
        rfl
    left_inv := by
        rw [Function.leftInverse_iff_comp]
        rfl
    right_inv := by
        rw [Function.rightInverse_iff_comp]
        rfl

#print axioms limit_up

def limit_lift := (limit_up f R).invFun

lemma apply_limit_proj {g1 g2 : R →+* limit f}
    (h : ∀ i : ι, ((limit_projections f).val i).comp g1 = ((limit_projections f).val i).comp g2)
    : g1 = g2 := by
    apply ApplyEquiv (limit_up f R) g1 g2
    simp [limit_up]
    funext i
    exact h i

@[simp]
lemma limit_proj_comp_lift (i : ι) (p : system_projections f R) :
    ((limit_projections f).val i).comp (limit_lift f R p) = p.val i := rfl

-- class RingSystem extends DirectedSystem F (fun ⦃_ _⦄ h ↦ f h)

-- lemma sub_system (rs : RingSystem f) (S : Set ι) :
--     RingSystem (fun {_ _ : S} h ↦ f h) where
--     map_self := by simp [rs.map_self]
--     map_map := by simp [rs.map_map]

-- variable [DecidableEq ι]

-- def help {i j : ι} (h : i ≤ j) : product F →+* product F := by
--     apply (product_up F (product F)).R_to_L
--     intro k
--     exact if hk : k = j
--     then by rw [hk]; exact RingHom.comp (f h) (product_projections F i)
--     else product_projections F k

-- variable {f} in
-- def limit (_ : RingSystem F f) : Subring (product F) :=
--     ⨅ p : {(i, j) : ι × ι | i ≤ j}, (help F f p.2).range
