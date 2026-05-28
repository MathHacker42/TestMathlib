import Init.Prelude
import Mathlib.Algebra.Algebra.Operations
import TestMathlib.Order

variable {A : Type} (succ : A → A) (o : A)

def IsInductive (S : Set A) := o ∈ S ∧ ∀ x ∈ S, succ x ∈ S

def Chain := sInf {S : Set A | IsInductive succ o S}

lemma ZeroInChain : o ∈ Chain succ o := by
  intro S hs
  exact hs.left

lemma SuccsInChain : ∀ x ∈ Chain succ o, succ x ∈ Chain succ o := by
  intro x hx S hs
  apply hs.right
  apply hx
  exact hs

lemma ChainIn {S : Set A} (ho : o ∈ S) (hs : ∀ x ∈ S, succ x ∈ S) : Chain succ o ≤ S := by
  intro x hx
  apply hx
  exact And.intro ho hs

lemma ChainLeZeroAndChainSucc : Chain succ o ≤ {o} ∪ Chain succ (succ o) := by
  apply ChainIn
  · left
    rfl
  · intro x hx
    right
    rcases hx with ho | hs
    · rw [ho]
      apply ZeroInChain
    · apply SuccsInChain
      exact hs

def ChainLe (x y : A) := y ∈ Chain succ x

theorem ChainTotalOrdered : TotalOn (ChainLe succ) (Chain succ o) := by
  rw [TotalOnIff]
  apply ChainIn
  · intro y hy
    left
    exact hy
  · dsimp
    intro x hx y hy
    rcases hx y hy with hxy | hyx
    · rcases ChainLeZeroAndChainSucc succ x hxy with hz | hs
      · right
        rw [hz]
        apply SuccsInChain
        apply ZeroInChain
      · left
        exact hs
    · right
      apply SuccsInChain
      exact hyx

#print axioms ChainTotalOrdered

theorem ChainWellOrdered : WellOrderedOn (ChainLe succ) (Chain succ o) := by
  intro S hs hn
  by_contra h0
  have h1 : Chain succ o ≤ {x ∈ Chain succ o | S ≤ Chain succ x} := by
    apply ChainIn
    · apply And.intro
      · apply ZeroInChain
      · exact hs
    · intro x ⟨hx, hsx⟩
      apply And.intro
      · apply SuccsInChain
        exact hx
      · intro y hy
        rcases ChainLeZeroAndChainSucc succ x (hsx hy) with hyx | hys
        · rw [hyx] at hy
          by_contra
          apply h0
          use x
          exact And.intro hy hsx
        · exact hys
  obtain ⟨x, hx⟩ := hn
  apply h0
  use x
  exact And.intro hx (h1 (hs hx)).right

#print axioms ChainWellOrdered

-- theorem ChainWellOrdered' : WellOrderedOn (ChainLe succ) (Chain succ o) := by
--   intro T ht hn
--   have h1 :
--     Chain succ o ≤ {x ∈ Chain succ o | T ≤ Chain succ x ∨ ∃ m ∈ T, T ≤ Chain succ m } := by
--     apply sInf_le
--     apply And.intro
--     · apply And.intro
--       · apply ZeroInChain
--       · left
--         exact ht
--     · intro x ⟨hx, htx⟩
--       apply And.intro
--       · apply SuccsInChain
--         exact hx
--       · rcases htx with h2 | h3
--         ·
--           sorry
--         · right
--           exact h3
--   obtain ⟨x, hx⟩ := hn
--   obtain ⟨h2, h3⟩ := h1 (ht hx)
--   rcases h3 with h4 | h5
--   · use x
--     apply And.intro hx
--     exact h4
--   · exact h5
