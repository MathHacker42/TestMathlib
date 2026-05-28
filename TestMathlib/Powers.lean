import TestMathlib.Chain

variable {M : Type} [Monoid M] (a : M)

def Powers := Chain (· * a) 1

lemma OneInPowers : 1 ∈ Powers a := ZeroInChain (· * a) 1

def Multiples (x : M) := {y : M | x ∣ y}

lemma MultiplesInductive (x : M) : IsInductive (· * a) x (Multiples x) := by
  apply And.intro
  · use 1
    exact (mul_one x).symm
  · intro y hy
    obtain ⟨c, hc⟩ := hy
    use c * a
    rw [hc, ← mul_assoc]

variable {a} in
lemma DvdIfLe {x y : M} (h : ChainLe (· * a) x y) : x ∣ y :=
  h (Multiples x) (MultiplesInductive a x)

theorem PowersTotalOrdered : TotalOn (· ∣ ·) (Powers a) := by
  intro x hx y hy
  rcases ChainTotalOrdered (· * a) 1 x hx y hy with hxy | hyx
  · left
    exact DvdIfLe hxy
  · right
    exact DvdIfLe hyx

#print axioms PowersTotalOrdered

variable {Z : Type} [CancelMonoidWithZero Z] {a : Z}

lemma PowersNonzero (ha : a ≠ 0) : Powers a ≤ {x : Z | x ≠ 0} := by
  apply ChainIn
  · intro h1
    apply ha
    rw [← mul_one a, h1, mul_zero]
  · dsimp
    intro x hx hxa
    apply ha
    apply mul_left_cancel₀ hx
    rw [hxa, mul_zero]

lemma ZeroNotInPowers (ha : a ≠ 0) : 0 ∉ Powers a := by
  intro hz
  apply (PowersNonzero ha) hz
  rfl

#print axioms ZeroNotInPowers
