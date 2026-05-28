



theorem csb {A B : Type} {f : A → B} {g : B → A}
  (hf : Function.Injective f) (hg : Function.Injective g) :
  ∃ p : A → B, ∃ q : B → A, p ∘ q = id ∧  q ∘ p = id := by
  sorry
