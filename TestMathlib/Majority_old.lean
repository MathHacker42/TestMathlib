import Mathlib.Data.Set.Card

def Input (n : ℕ) := Fin n -> Prop

def Gate (n : ℕ) := Input n -> Prop

variable {n : ℕ}

def NegationPreserving (G : Gate n) :=
  ∀ I : Input n, G (fun k ↦ ¬ I k) = ¬ (G I)

def Monotonic (G : Gate n) :=
  ∀ {X Y : Input n}, (∀ k : Fin n, X k → Y k) → (G X → G Y)

def Valid (G : Gate n) := NegationPreserving G ∧ Monotonic G

noncomputable instance {p : Fin n → Prop} : Fintype {x : Fin n // p x} := by
  apply Fintype.ofInjective (fun x : {x : Fin n // p x} ↦ (x : Fin n))
  intro a b h
  simp at h
  ext
  rw [h]

def AllOn : Input n := fun _ ↦ True

def AllOff : Input n := fun _ ↦ False

lemma AllOnOnAllOffOff {G : Gate n} (hv : Valid G) : G AllOn ∧ ¬ G AllOff := by
  obtain ⟨hn, hm⟩ := hv
  have h1 : G AllOn = ¬ G AllOff := by
    rw [← hn (AllOff)]
    dsimp [AllOff]
    simp
    rfl
  have h2 : G AllOff → G AllOn := by
    apply hm
    intro _ _
    dsimp [AllOn]
  rw [h1] at h2
  simp at h2
  simp [*]

noncomputable def Off (I : Input n) := Fintype.card {k | ¬ (I k)}

noncomputable def On (I : Input n) := Fintype.card {k | I k}

lemma EqSubCardNot (p : Fin n → Prop) : Fintype.card {x // p x} =
  n - Fintype.card {x // ¬ p x} := by
  have h2 : Fintype.card { x // p x } = Fintype.card { x // ¬ ¬ p x } := by simp
  rw [h2, Fintype.card_subtype_compl]
  simp

lemma SumOffOn (I : Input n) : (Off I) + (On I) = n := by
  dsimp [Off]
  rw [Fintype.card_subtype_compl]
  simp
  dsimp [On]
  apply Nat.sub_add_cancel
  have h1 : Fintype.card { x // I x } ≤ Fintype.card (Fin n) := by
    rw [EqSubCardNot]
    simp
  simp at h1
  exact h1

def Majority (_ : Odd n) (I : Input n) :=
  Off I ≤ On I

lemma MajorityEq (h : Odd n) (I : Input n) : Majority h I =
  (n ≤ 2 * (On I)) := by
  dsimp [Majority, Off, On]
  simp
  omega

lemma MajorityPreservesNegation (h : Odd n) : NegationPreserving (Majority h) := by
  intro I
  nth_rw 2 [MajorityEq]
  dsimp [Majority]
  dsimp [Off, On]
  simp
  rw [Nat.le_sub_iff_add_le]
  · have h2 (k : ℕ) : k + k = 2 * k := by omega
    rw [h2]
    obtain ⟨k, hk⟩ := h
    simp [hk]
    rw [← Nat.le_iff_lt_add_one]
    simp
    rw [Nat.le_iff_lt_add_one]
    rw [add_assoc, h2 1, ← mul_add]
    simp
    rw [← Nat.le_iff_lt_add_one]
  · simp [← SumOffOn I]
    dsimp [On]
    simp

lemma MajorityMonotonic (ho : Odd n) : Monotonic (Majority ho) := by
  intro I J hij
  repeat rw [MajorityEq]
  intro hi
  apply le_trans hi
  simp
  apply Set.card_le_card
  simp
  exact hij

lemma MajorityIsValid (ho : Odd n) : Valid (Majority ho) := by
  apply And.intro
  · exact MajorityPreservesNegation ho
  · exact MajorityMonotonic ho

def Projection (k : Fin n) : Gate n := fun I ↦ I k

lemma ProjectionIsValid (k : Fin n) : Valid (Projection k) := by
  apply And.intro
  · intro I
    dsimp [Projection]
  · intro I J hij
    dsimp [Projection]
    exact hij k

lemma CompositionIsValid {m : ℕ} {G : Gate m} (hg : Valid G) {F : Fin m → Gate n}
  (hf : ∀ k : Fin m, Valid (F k)) :
  Valid (fun I ↦ G (fun k ↦ F k I)) := by
  apply And.intro
  · intro I
    simp
    rw [← hg.1]
    have h1 : (fun k ↦ F k fun k ↦ ¬I k) = (fun k ↦ ¬F k I) := by
      funext k
      rw [(hf k).1]
    rw [h1]
  · intro I J hij
    simp
    apply hg.2
    intro k
    apply (hf k).2
    exact hij

def M3 : Gate 3 := by
  apply Majority
  use 1
  simp

lemma M3IsValid : Valid M3 := by
  apply MajorityIsValid

def M3Combo (T : Fin 3 → Gate n) : Gate n := fun I ↦ M3 (fun j ↦ T j I)

def ContainsProjections (S : Set (Gate n)) := (∀ k : Fin n, Projection k ∈ S)

def IsM3Closed (S : Set (Gate n)) :=
  (∀ {T : Fin 3 → Gate n}, (∀ j : Fin 3, T j ∈ S) → M3Combo T ∈ S)

def M3Closure (n : ℕ) : Set (Gate n) :=
  sInf {S | ContainsProjections S ∧ IsM3Closed S}

lemma ProjectionInClosure (k : Fin n) : Projection k ∈ M3Closure n := by
  intro S
  simp
  intro hp h3
  exact hp k

lemma ClosureIsClosed : IsM3Closed (M3Closure n) := by
  dsimp [M3Closure, IsM3Closed]
  intro T ht S hs
  simp at hs
  obtain ⟨h1, h2⟩ := hs
  apply h2
  intro j
  obtain hj := ht j
  rw [Set.mem_sInter] at hj
  simp at hj
  exact hj S h1 h2

lemma ClosureSubValid : M3Closure n ⊆ {G | Valid G} := by
  apply sInf_le
  simp
  apply And.intro
  · exact ProjectionIsValid
  · intro T
    exact CompositionIsValid (M3IsValid)

lemma ClosureIsValid {G : Gate n} (hg : G ∈ M3Closure n) : Valid G :=
  ClosureSubValid hg

def Component (G : Gate n) (T : Fin 3 → Fin n) (j : Fin 3) : Gate n := fun I ↦
  G (fun k ↦ if k = T j then False else I k) ∨
  G (fun k ↦ if k = T j then True else I k) ∧ I (T (j + 1))

lemma ComponentEq (G : Gate n) (T : Fin 3 → Fin n) : (Component G T) = fun j I ↦
  G (fun k ↦ k ≠ T j ∧ I k) ∨ G (fun k ↦ k = T j ∨ I k) ∧ I (T (j + 1)) := by
  funext I
  funext j
  dsimp [Component]
  simp [imp_iff_not_or]

lemma ComponentIsNegationPreserving {G : Gate n} (hv : Valid G)
  (T : Fin 3 → Fin n) (j : Fin 3) : NegationPreserving ((Component G T) j) := by
  obtain ⟨hn, hm⟩ := hv
  intro I
  repeat rw [ComponentEq]
  -- simp
  simp [imp_iff_not_or]
  dsimp [NegationPreserving] at hn
  simp [← hn]
  simp [imp_iff_not_or]
  have h1 : (G fun k ↦ ¬k = T j ∧ ¬I k) → (G fun k ↦ k = T j ∨ ¬I k) := by
    apply hm
    intro k
    intro ⟨_, h2⟩
    right
    exact h2
  have h2 : ((G fun k ↦ k = T j ∨ ¬I k) ∧ (G fun k ↦ ¬k = T j ∧ ¬I k)) =
    (G fun k ↦ ¬k = T j ∧ ¬I k) := by
    simp
    exact h1
  rw [and_or_left, h2]

lemma ComponentIsMonotonic {G : Gate n} (hm : Monotonic G)
  (T : Fin 3 → Fin n) (j : Fin 3) : Monotonic ((Component G T) j) := by
  intro I J hij
  repeat rw [ComponentEq]
  intro hi
  dsimp [Monotonic] at hm
  rcases hi with h1 | ⟨h2, h3⟩
  · left
    apply @hm (fun k ↦ k ≠ T j ∧ I k)
    · intro k hk
      simp [*]
    · exact h1
  · right
    apply And.intro
    · apply @hm (fun k ↦ k = T j ∨ I k)
      · intro k hk
        rcases hk with hsk | hik
        · left
          exact hsk
        · right
          apply hij
          exact hik
      · exact h2
    apply hij
    exact h3

lemma ComponentIsValid {G : Gate n} (hg : Valid G) (T : Fin 3 → Fin n) (j : Fin 3) :
  Valid ((Component G T) j) := by
  apply And.intro
  · apply ComponentIsNegationPreserving
    exact hg
  · apply ComponentIsMonotonic
    exact hg.2

lemma OnOroffAtLeast2 (I : Input 3) : 2 ≤ On I ∨ 2 ≤ Off I := by
  by_contra h
  push_neg at h
  repeat rw [Nat.lt_iff_add_one_le] at h
  simp at h
  obtain ⟨hn, hf⟩ := h
  have h1 := add_le_add hf hn
  rw [SumOffOn] at h1
  simp at h1

def HelperFunction1 (G : Gate n) (I : Input n) (T : Fin 3 → Fin n) : { x // I (T x) } →
  { x // (G fun k ↦ ¬k = T x ∧ I k) ∨ I (T (x + 1)) } := by
  intro j
  use j - 1
  right
  simp
  exact j.property

def HelperFunction2 (G : Gate n) (I : Input n) (T : Fin 3 → Fin n) : { x // ¬I (T x) } →
  { x // (G fun k ↦ k = T x ∨ I k) → ¬I (T (x + 1)) } := by
  intro j
  use j - 1
  intro hgf
  simp
  exact j.property

lemma M3ComboComponents {G : Gate n} (hm : Monotonic G) (T : Fin 3 → Fin n) :
  M3Combo (Component G T) = G := by
  rw [ComponentEq]
  funext I
  dsimp [M3Combo, M3]
  rw [MajorityEq]
  dsimp [On]
  have help (m : ℕ) : 3 ≤ 2 * m ↔ m ≥ 2 := by omega
  rw [help]
  ext
  apply Iff.intro
  · contrapose
    intro hgi
    simp
    rw [EqSubCardNot]
    have help (m : ℕ) (h : 2 ≤ m) : 3 - m < 2 := by omega
    apply help
    simp
    have h0 {j : Fin 3} : (¬G fun k ↦ ¬k = T j ∧ I k) := by
      intro hgf
      apply hgi
      apply @hm (fun k ↦ ¬k = T j ∧ I k)
      · simp
      · exact hgf
    simp [h0]
    rcases OnOroffAtLeast2 (I ∘ T) with hn | hf
    · apply le_trans hn
      dsimp [On]
      have h1 : { x | I (T x) } ⊆
        { x | ((G fun k ↦ k = T x ∨ I k) → ¬I (T (x + 1))) } := by
          intro j
          simp
          intro htj
          intro hgf
          by_contra
          apply hgi
          apply @hm (fun k ↦ k = T j ∨ I k)
          · intro k h1
            rcases h1 with hktj | hik
            · rw [hktj]
              exact htj
            · exact hik
          · exact hgf
      exact Set.card_le_card h1
    · apply le_trans hf
      dsimp [Off]
      apply Fintype.card_le_of_injective (HelperFunction2 G I T)
      intro y z hyz
      simp [HelperFunction2] at hyz
      ext
      rw [hyz]
  · intro hgi
    simp
    have h0 {j : Fin 3} : (G fun k ↦ k = T j ∨ I k) := by
      apply @hm I
      · intro k hik
        right
        exact hik
      · exact hgi
    simp [h0]
    rcases OnOroffAtLeast2 (I ∘ T) with hn | hf
    · apply le_trans hn
      dsimp [On]
      apply Fintype.card_le_of_injective (HelperFunction1 G I T)
      intro y z hyz
      simp [HelperFunction1] at hyz
      ext
      rw [hyz]
    · apply le_trans hf
      dsimp [Off]
      have h3 : { x : Fin 3 | ¬I (T x) } ⊆ { x : Fin 3 |
        (G fun k ↦ ¬k = T x ∧ I k) ∨ I (T (x + 1)) } := by
        intro j
        simp
        intro hi
        left
        apply @hm I
        · intro k hik
          simp [hik]
          intro hktj
          apply hi
          rw [← hktj]
          exact hik
        · exact hgi
      exact Set.card_le_card h3

def Unused (G : Gate n) (k : Fin n) := ∀ I J : Input n,
  (∀ l : Fin n, l ≠ k → I l = J l) → (G I = G J)

def Used (G : Gate n) (k : Fin n) := ¬ Unused G k

lemma UnusedInComponent (G : Gate n) {T : Fin 3 → Fin n} (hs : Function.Injective T) (k : Fin 3) :
  Unused (Component G T k) (T k) := by
  dsimp [Unused]
  intro I J hij
  repeat rw [ComponentEq]
  simp
  have h1 : (fun k_1 ↦ ¬k_1 = T k ∧ I k_1) = (fun k_1 ↦ ¬k_1 = T k ∧ J k_1) := by
    funext l
    rcases @or_not (l = T k) with he | hn
    · simp [he]
    · simp [hn]
      rw [hij l hn]
  have h2 : (fun k_1 ↦ k_1 = T k ∨ I k_1) = (fun k_1 ↦ k_1 = T k ∨ J k_1) := by
    funext l
    rcases @or_not (l = T k) with he | hn
    · simp [he]
    · simp [hn]
      rw [hij l hn]
  have h3 : I (T (k + 1)) = J (T (k + 1)) := by
    apply hij
    intro he
    apply hs at he
    simp at he
  simp [*]

lemma UnusedInComponent2 (G : Gate n) {T : Fin 3 → Fin n}
  (hs : ∀ l : Fin 3, Used G (T l)) (j : Fin 3)
  {m : Fin n} (hm : Unused G m) : Unused (Component G T j) m := by
  have hsk : ∀ l : Fin 3, m ≠ T l := by
    intro l h
    apply hs l
    rw [← h]
    exact hm
  dsimp [Unused]
  intro I1 I2 h1
  repeat rw [ComponentEq]
  simp
  have h2 : I1 (T (j + 1)) = I2 (T (j + 1)) := h1 (T (j + 1)) (hsk (j + 1)).symm
  dsimp [Unused] at hm
  have h3 : (G fun k ↦ ¬k = T j ∧ I1 k) = (G fun k ↦ ¬k = T j ∧ I2 k) := by
    apply hm
    intro l hlm
    simp [h1 l hlm]
  have h4 : (G fun k ↦ k = T j ∨ I1 k) = (G fun k ↦ k = T j ∨ I2 k) := by
    apply hm
    intro l hlm
    simp [h1 l hlm]
  simp [*]

def UsedInputs (G : Gate n) := {k | Used G k}

noncomputable def UsedInputCount (G : Gate n) := Fintype.card (UsedInputs G)

lemma LogicHelper {P Q R : Prop} : (P ∨ Q ↔ P ∨ R) ↔ ((Q ↔ R) ∨ P) := by
  apply Iff.intro
  · intro h
    rcases @or_not P with hp | hnp
    · simp [hp]
    · simp [hnp] at h
      simp [h]
  · intro h
    rcases h with h1 | h1
    · simp [h1]
    · simp [h1]

lemma NCardEqCard (X : Set (Fin n)) : X.ncard = Fintype.card X := by
  rw [Fintype.card_eq_nat_card]
  rfl

lemma CardDiffSingletonOfMem {S : Set (Fin n)} {a : Fin n} (h : a ∈ S) :
  Fintype.card ({x ∈ S | x ≠ a}) = Fintype.card S - 1 := by
  repeat rw [← NCardEqCard]
  have h1 : {x ∈ S | x ≠ a} = S \ {a} := rfl
  rw [h1]
  exact Set.ncard_diff_singleton_of_mem h

lemma EqOnUsedHelper (k : ℕ) : ∀ G : Gate n, ∀ I J : Input n,
    (∀ k ∈ UsedInputs G, I k = J k) →
    Fintype.card {k : Fin n | I k ≠ J k} = k →
    G I = G J := by
    intro G I J hu h1
    match k with
    | 0 =>
      rw [Fintype.card_eq_zero_iff] at h1
      have hij : I = J := by
        funext k
        by_contra hne
        apply h1.false
        use k
        exact hne
      rw [hij]
    | d + 1 =>
      have h2 : Nonempty {k | I k ≠ J k} := by
        rw [← Fintype.card_pos_iff]
        rw [h1]
        simp
      obtain ⟨l, hl⟩ := h2
      simp at hl
      have h2 : Unused G l := by
        by_contra hnu
        apply hl
        simp at hu
        exact hu l hnu
      have h3 (I : Input n) : G I = G (fun k ↦ k = l ∨ I k) := by
        apply h2
        intro m hml
        simp [hml]
      rw [h3 I, h3 J]
      apply EqOnUsedHelper d
      · intro m hm
        rw [hu m hm]
      · have h4 : {k | (k = l ∨ I k) ≠ (k = l ∨ J k)} =
          {k | I k ≠ J k} \ {l} := by
          ext m
          simp
          rw [← not_or]
          rw [not_iff_not]
          exact LogicHelper
        rw [h4]
        rw [← NCardEqCard]
        rw [Set.ncard_diff_singleton_of_mem]
        · rw [NCardEqCard]
          rw [h1]
          simp
        · simp
          exact hl

lemma EqIfEqOnUsed {G : Gate n} {I J : Input n}
  (h : ∀ k ∈ UsedInputs G, I k = J k) : G I = G J := by
  apply EqOnUsedHelper (Fintype.card {k : Fin n | I k ≠ J k}) G I J h
  rfl

lemma EqProjection {G : Gate n} (hv : Valid G) {k : Fin n} (h : G fun l ↦ l = k) :
  G = Projection k := by
  obtain ⟨hn, hm⟩ := hv
  funext I
  dsimp [Projection]
  rcases @or_not (I k) with hik | hnik
  · simp [hik]
    apply @hm (fun l ↦ l = k)
    · intro l hlk
      rw [hlk]
      exact hik
    · exact h
  · simp [hnik]
    rw [← hn]
    apply @hm (fun l ↦ l = k)
    · intro l hlk
      rw [hlk]
      exact hnik
    · exact h

def Extend {X Y : Type} {S : Set Y} (f : X → S) : X → Y := fun x ↦ f x

lemma ValidInClosureHelper (k : ℕ) : ∀ {G : Gate n},
  Valid G → UsedInputCount G = k → G ∈ M3Closure n := by
  intro G hv hu
  match k with
  | 0 =>
    dsimp [UsedInputCount] at hu
    rw [Fintype.card_eq_zero_iff] at hu
    dsimp [UsedInputs] at hu
    have h1 (k : Fin n) : Unused G k := by
      by_contra hk
      rw [← Used] at hk
      apply hu.false
      use k
    have h2 (I J : Input n) : G I = G J := by
      apply EqIfEqOnUsed
      intro k hk
      by_contra
      exact hk (h1 k)
    have h3 := h2 AllOff AllOn
    have h4 := AllOnOnAllOffOff hv
    rw [h3] at h4
    simp at h4
  | 1 =>
    dsimp [UsedInputCount] at hu
    rw [← NCardEqCard] at hu
    rw [Set.ncard_eq_one] at hu
    obtain ⟨k, hk⟩ := hu
    have h1 : G = Projection k := by
      apply EqProjection hv
      have h2 : G fun l ↦ l = k = G AllOn := by
        apply EqIfEqOnUsed
        intro l hl
        rw [hk] at hl
        simp at hl
        simp [hl]
        dsimp [AllOn]
      rw [h2]
      exact (AllOnOnAllOffOff hv).1
    rw [h1]
    exact ProjectionInClosure k
  | 2 =>
    have hg := hv
    obtain ⟨hn, hm⟩ := hg
    dsimp [UsedInputCount] at hu
    rw [← NCardEqCard] at hu
    rw [Set.ncard_eq_two] at hu
    obtain ⟨x, y, hxy, hu⟩ := hu
    have h1 : (G fun k ↦ k = x) = (G fun k ↦ k ≠ y) := by
      apply EqIfEqOnUsed
      intro l hl
      rw [hu] at hl
      simp at hl
      simp
      apply Iff.intro
      · intro hlx
        rw [hlx]
        intro hxy2
        apply hxy
        ext
        rw [hxy2]
      · rw [imp_iff_not_or]
        simp
        symm
        exact hl
    rw [hn] at h1
    rcases @or_not (G fun k ↦ k = y) with hy | hny
    · rw [EqProjection hv hy]
      exact ProjectionInClosure y
    · rw [← h1] at hny
      rw [EqProjection hv hny]
      exact ProjectionInClosure x
  | (d + 3) =>
    have h1 : 3 ≤ UsedInputCount G := by
      rw [hu]
      simp
    dsimp [UsedInputCount] at h1
    rw [← Fintype.card_fin 3] at h1
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h1
    have hsi : Function.Injective (Extend f) := by
      intro i j h
      dsimp [Extend] at h
      apply f.injective
      ext
      rw [h]
    rw [← M3ComboComponents hv.2 (Extend f)]
    apply ClosureIsClosed
    intro j
    have h1 : UsedInputCount (Component G (Extend f) j) ≤ d + 3 - 1 := by
      rw [← hu]
      dsimp [UsedInputCount]
      repeat rw [← NCardEqCard]
      rw [← Set.ncard_diff_singleton_of_mem (f j).property]
      repeat rw [NCardEqCard]
      apply Set.card_le_card
      intro i hi
      simp
      apply And.intro
      · dsimp [UsedInputs, Used, Unused]
        intro hugi
        apply hi
        apply UnusedInComponent2
        intro l
        exact (f l).property
        exact hugi
      · intro hifj
        rw [hifj] at hi
        dsimp [UsedInputs] at hi
        apply hi
        apply UnusedInComponent
        exact hsi
    apply ValidInClosureHelper (UsedInputCount (Component G (Extend f) j))
      (ComponentIsValid hv (Extend f) j)
    rfl

theorem ValidInClosure {G : Gate n} (hg : Valid G) :
  G ∈ M3Closure n := by
  apply ValidInClosureHelper (UsedInputCount G) hg
  rfl

lemma MajorityInClosure (h : Odd n) : Majority h ∈ M3Closure n :=
  ValidInClosure (MajorityIsValid h)

lemma InClosureIffValid (G : Gate n) : G ∈ M3Closure n ↔ Valid G :=
  Iff.intro ClosureIsValid ValidInClosure

#print axioms InClosureIffValid
