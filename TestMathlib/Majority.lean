import Mathlib.Data.Set.Card

variable (n : Type)

def Input := n → Prop

def Gate := Input n → Prop

variable {n} {G : Gate n}

section Valid

variable (G)

def NegationPreserving := ∀ I : Input n, G (fun k ↦ ¬ I k) = ¬ (G I)

def Monotonic := ∀ {I J : Input n}, (∀ k : n, I k → J k) → (G I → G J)

def Valid := NegationPreserving G ∧ Monotonic G

end Valid

section Misc

-- only actually used for n = 1 base case
lemma AllOnOnAllOffOff (hv : Valid G) : G (fun _ ↦ True) ∧ ¬ G (fun _ ↦ False) := by
  have h1 : G (fun _ ↦ True) = ¬ G (fun _ ↦ False) := by
    rw [← hv.1]
    simp
  have h2 : G (fun _ ↦ False) → G (fun _ ↦ True) := by
    apply hv.2
    simp
  rw [h1] at h2
  simp at h2
  simp [*]

-- Not necessary, I just liked it
lemma ValidPreservesConstant (hv : Valid G) (P : Prop) : G (fun _ ↦ P) = P := by
  obtain ⟨ht, hf⟩ := AllOnOnAllOffOff hv
  rcases @or_not P with hp | hnp
  · simp [hp]
    exact ht
  · simp [hnp]
    exact hf

variable {m : Type}

variable (G) in
def IndexMap (f : n → m) := fun I ↦ G (I ∘ f)

lemma IndexMapIsValid (f : n → m) (hv : Valid G) :
  Valid (IndexMap G f) := by
  apply And.intro
  · intro I
    dsimp [IndexMap]
    rw [← hv.1]
    rfl
  · intro I J hij
    apply hv.2
    intro k
    apply hij

variable (G) in
def Compose (F : n → Gate m) := fun I ↦ G (fun k ↦ F k I)

lemma CompositionIsValid {F : n → Gate m} (hv : Valid G)
  (hf : ∀ k : n, Valid (F k)) : Valid (Compose G F) := by
  apply And.intro
  · intro I
    simp only [Compose]
    rw [← hv.1]
    apply congrArg
    funext k
    rw [(hf k).1]
  · intro I J hij
    simp [Compose]
    apply hv.2
    intro k
    apply (hf k).2
    exact hij

variable {A B P Q : Prop}

lemma LogicHelper1 (h1 : A ≤ B → P ≤ Q) (hpq : ¬ (P ≤ Q)) :
  A = P ∧ B = Q := by
  have h4 : ¬(A ≤ B) := mt h1 hpq
  simp at h4
  simp at hpq
  simp [*]

lemma LogicHelper2 (h1 : A ≤ B → P ≤ Q) (h2 : B ≤ A → Q ≤ P)
  (hpnq : P ≠ Q) : A = P ∧ B = Q := by
  have h3 : ¬ (P ≤ Q ∧ Q ≤ P) := by
    intro ⟨hpq, hqp⟩
    apply hpnq
    exact le_antisymm hpq hqp
  rw [not_and_or] at h3
  rcases h3 with hpq | hqp
  · exact LogicHelper1 h1 hpq
  · symm
    exact LogicHelper1 h2 hqp

lemma LogicHelper3 (h1 : A ≤ B → P ≤ Q) (h2 : B ≤ A → Q ≤ P) :
  Q ≠ P → A = P ∧ B ≠ P := by
  intro hpnq
  have h1 := LogicHelper2 h2 h1 hpnq
  simp [*]

end Misc

section Majority

variable [Fintype n]

noncomputable instance {p : n → Prop} : Fintype {x : n // p x} := by
  apply Fintype.ofInjective (fun x : {x : n // p x} ↦ (x : n))
  intro a b h
  simp at h
  ext
  rw [h]

noncomputable def Off (I : Input n) := Fintype.card {k | ¬ (I k)}

noncomputable def On (I : Input n) := Fintype.card {k | I k}

lemma SumOffOn (I : Input n) : (Off I) + (On I) = Fintype.card n := by
  dsimp [Off, On]
  rw [Fintype.card_subtype_compl]
  apply Nat.sub_add_cancel
  have h1 : Fintype.card { x // I x } = Fintype.card { x // ¬ ¬ I x } := by simp
  rw [h1, Fintype.card_subtype_compl]
  simp

variable (h : Odd (Fintype.card n))

def Majority (_ : Odd (Fintype.card n)) (I : Input n) : Prop := Off I ≤ On I

lemma MajorityEq (I : Input n) : Majority h I =
  (Fintype.card n ≤ 2 * On I) := by
  dsimp [Majority, Off, On]
  simp
  omega

lemma MajorityPreservesNegation : NegationPreserving (Majority h) := by
  intro I
  nth_rw 2 [MajorityEq]
  dsimp [Majority, Off, On]
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

lemma MajorityEqIff (I : Input n) (P : Prop) :
  (Majority h I = P) = (Majority h (fun k ↦ I k = P)) := by
  rcases @or_not P with hp | hnp
  · simp [hp]
  · simp [hnp]
    rw [MajorityPreservesNegation]

lemma MajorityMonotonic : Monotonic (Majority h) := by
  intro I J hij
  repeat rw [MajorityEq]
  intro hi
  apply le_trans hi
  simp
  apply Set.card_le_card
  simp
  exact hij

lemma MajorityIsValid : Valid (Majority h) := by
  apply And.intro
  · exact MajorityPreservesNegation h
  · exact MajorityMonotonic h

end Majority

section Closure

def Projection (k : n) : Gate n := fun I ↦ I k

lemma ProjectionIsValid (k : n) : Valid (Projection k) := by
  apply And.intro
  · intro I
    dsimp [Projection]
  · intro I J hij
    dsimp [Projection]
    exact hij k

-- useful for base cases
lemma EqProjection {G : Gate n} (hv : Valid G) {k : n} (h : G fun l ↦ l = k) :
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

def M3 : Gate (Fin 3) := by
  apply Majority
  use 1
  simp

lemma M3IsValid : Valid M3 := by
  apply MajorityIsValid

def M3Combo (G3 : Fin 3 → Gate n) : Gate n := Compose M3 G3

def ContainsProjections (S : Set (Gate n)) := (∀ k : n, Projection k ∈ S)

def IsM3Closed (S : Set (Gate n)) :=
  (∀ {G3 : Fin 3 → Gate n}, (∀ j : Fin 3, G3 j ∈ S) → M3Combo G3 ∈ S)

variable (n) in
def M3Closure : Set (Gate n) := sInf {S | ContainsProjections S ∧ IsM3Closed S}

lemma ProjectionInClosure (k : n) : Projection k ∈ M3Closure n := by
  intro S
  simp
  intro hp h3
  exact hp k

-- helper for base cases
lemma InClosureIf (hv : Valid G) {k : n} (h : G fun l ↦ l = k) :
  G ∈ M3Closure n := by
  apply EqProjection hv at h
  rw [h]
  apply ProjectionInClosure

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

-- forward direction
lemma ClosureSubValid : M3Closure n ⊆ {G | Valid G} := by
  apply sInf_le
  apply And.intro
  · exact ProjectionIsValid
  · intro T
    exact CompositionIsValid (M3IsValid)

lemma ClosureIsValid {G : Gate n} (hg : G ∈ M3Closure n) : Valid G :=
  ClosureSubValid hg

variable {m : Set n}

def ExtendGate (Gm : Gate m) : Gate n := IndexMap Gm (fun k ↦ k)

lemma ExtendProjectionEq (k : m) : ExtendGate (Projection k) =
  @Projection n k := rfl

lemma ExtendComboEq (T : Fin 3 → Gate m) : ExtendGate (M3Combo T) =
  M3Combo (ExtendGate ∘ T) := rfl

lemma ExtendPreimageSubClosure :
  M3Closure m ≤ {Gm : Gate m | ExtendGate Gm ∈ M3Closure n} := by
  apply sInf_le
  simp
  apply And.intro
  · intro k
    simp
    rw [ExtendProjectionEq]
    apply ProjectionInClosure
  · intro T
    simp
    intro h
    rw [ExtendComboEq]
    exact ClosureIsClosed h

lemma ExtendInClosure {Gm : Gate m} (h : Gm ∈ M3Closure m) :
  ExtendGate Gm ∈ M3Closure n := ExtendPreimageSubClosure h

end Closure

variable [DecidableEq n]

section Component

variable (G : Gate n) (T : Fin 3 ↪ n) (j : Fin 3)

def Component : Gate {k : n | k ≠ T j} := IndexMap G fun k ↦
  if h : k = T j then ⟨T (j + 1), by simp⟩ else ⟨k, h⟩

def ExtComp := ExtendGate (Component G T j)

variable {G}

lemma ComponentIsValid (hv : Valid G) : Valid ((Component G T) j) := by
  apply IndexMapIsValid (hv := hv)

lemma M3Eq (I : Input (Fin 3)) : M3 I = (On I > 1) := by
  dsimp [M3]
  rw [MajorityEq]
  simp
  have h1 := SumOffOn I
  simp at h1
  omega

lemma M3Helper (I : Input (Fin 3)) (h : ∀ j : Fin 3, ¬ (¬ I j ∧ ¬ I (j + 1))) : M3 I := by
  contrapose h
  push_neg
  rcases @or_not (∀ i, ¬ I i) with h1 | h1
  · use 0
    simp [h1]
  · push_neg at h1
    obtain ⟨i, hi⟩ := h1
    use i + 1
    rw [M3Eq] at h
    simp at h
    dsimp [On] at h
    rw [Fintype.card_le_one_iff] at h
    rw [← not_or]
    intro h0
    have ha {a : Fin 3} (hia : I (i + a)) : a = 0 := by
      have he := h ⟨i, hi⟩ ⟨i + a, hia⟩
      simp at he
      exact he
    rcases h0 with h1 | h2
    · apply ha at h1
      simp at h1
    · rw [add_assoc] at h2
      apply ha at h2
      simp at h2

lemma ComboHelper (hm : Monotonic G) (I : Input n) : ExtComp G T j I ≠ G I →
  I (T j) = G I ∧ I (T (j + 1)) ≠ G I := by
  apply LogicHelper3
  · intro hi
    apply hm
    intro k
    rcases @or_not (k = T j) with h | h
    · simp [h]
      exact hi
    · simp [h]
  · intro hi
    apply hm
    intro k
    rcases @or_not (k = T j) with h | h
    · simp [h]
      exact hi
    · simp [h]

lemma M3ComboComponents (hm : Monotonic G) : M3Combo (ExtComp G T) = G := by
  funext I
  dsimp [M3Combo, M3, Compose]
  rw [MajorityEqIff]
  apply M3Helper
  intro j ⟨h1, h2⟩
  apply ComboHelper (hm := hm) at h1
  apply ComboHelper (hm := hm) at h2
  exact h1.2 h2.1

end Component

section Induction

lemma ValidInClosureHelper {n : Type} [Fintype n] [DecidableEq n] (k : ℕ)
  {G : Gate n} (hv : Valid G) (hn : Fintype.card n = k) : G ∈ M3Closure n := by
  match k with
  | 0 =>
    rw [Fintype.card_eq_zero_iff] at hn
    have h1 : G hn.elim = ¬ G hn.elim := by
      rw [← hv.1]
      apply congrArg
      funext a
      by_contra
      exact hn.false a
    simp at h1
  | 1 =>
    rw [Fintype.card_eq_one_iff] at hn
    obtain ⟨x, hx⟩ := hn
    apply InClosureIf hv (k := x)
    simp [hx]
    exact (AllOnOnAllOffOff hv).1
  | 2 =>
    apply Fintype.equivFinOfCardEq at hn
    symm at hn
    have h1 (a : Fin 2) : 0 ≠ a ↔ 1 = a := by omega
    have h2 (k : n) (a : Fin 2) : (k = hn a) ↔ (a = hn.symm k) := by
      rw [← hn.apply_eq_iff_eq_symm_apply]
      exact Eq.comm
    have h3 : (G fun k ↦ k ≠ hn 0) = (G fun k ↦ k = hn 1) := by
      simp [h2, h1]
    rw [hv.1] at h3
    rcases @or_not (G fun k ↦ k = hn 0) with hg | hng
    · apply InClosureIf hv hg
    · rw [h3] at hng
      apply InClosureIf hv hng
  | d + 3 =>
    have h1 : Fintype.card (Fin 3) ≤ Fintype.card n := by
      simp [hn]
    obtain ⟨T⟩ := Function.Embedding.nonempty_of_card_le h1
    rw [← M3ComboComponents T hv.2]
    apply ClosureIsClosed
    intro j
    apply ExtendInClosure
    apply ValidInClosureHelper (d + 2)
    · apply ComponentIsValid (hv := hv)
    · simp [hn]

end Induction

section Results

variable [Fintype n]

theorem ValidInClosure {G : Gate n} (hv : Valid G) : G ∈ M3Closure n := by
  apply ValidInClosureHelper (Fintype.card n) hv
  rfl

lemma InClosureIffValid (G : Gate n) : G ∈ M3Closure n ↔ Valid G :=
  Iff.intro ClosureIsValid ValidInClosure

#print axioms InClosureIffValid

-- because sets are just defined as maps to Prop
variable (n) in
lemma ClosureEqValid : M3Closure n = Valid := by
  ext G
  exact InClosureIffValid G

lemma MajorityInClosure (h : Odd (Fintype.card n)) : Majority h ∈ M3Closure n :=
  ValidInClosure (MajorityIsValid h)

end Results
