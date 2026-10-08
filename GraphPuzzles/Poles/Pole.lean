import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Ring.Parity
import GraphPuzzles.Core.Tactics

/-!
# Abstract Hamiltonian cubic `3`-poles

Theorem 3.1 of Karabáš–Máčajová (every Hamiltonian cubic `3`-pole has a proper four-cover) is a
statement about a cyclic arrangement: the vertices of the Hamiltonian circuit in cyclic order,
three of them carrying the spokes, and the chords pairing up the remaining vertices.  This module
records that combinatorial data as an abstract `Pole`: positions `0, …, n - 1` along the circuit,
spokes at the positions `0`, `s₂`, `s₁` (with `0 < s₂ < s₁ < n`), and the chord involution `μ` on
the inner (non-spoke) positions.  The circuit edge `p` joins the positions `p` and `p + 1`
(the edge `n - 1` returns to `0`).

A proper four-cover is recorded by the label of every circuit edge (the set of the three
matchings `M₁, M₂, M₃` containing it; the fourth matching is the set of chords and spokes) and the
label of the chord or spoke at every position.  At each position the labels of the two circuit
edges and of the chord partition the three colours, circuit edges carry nonempty labels, the two
ends of a chord carry the same label, and each spoke carries exactly one colour.

The module also proves the parity facts (`n` is odd, the number of exterior chords of a segment
has the parity of the number of its inner vertices) and Lemma 3.3 of the paper: a pole whose three
segments are odd has a proper four-cover.
-/

namespace GraphPuzzles

/-- An abstract Hamiltonian cubic `3`-pole: `n` positions on the circuit, spokes at `0`, `s₂`, `s₁`,
and the chord involution `μ` on the inner positions. -/
structure Pole where
  /-- The number of vertices of the Hamiltonian circuit. -/
  n : ℕ
  /-- The second spoke position. -/
  s₂ : ℕ
  /-- The third spoke position. -/
  s₁ : ℕ
  /-- The chord map: the other end of the chord at an inner position. -/
  μ : ℕ → ℕ
  s₂_pos : 0 < s₂
  s₂_lt_s₁ : s₂ < s₁
  s₁_lt_n : s₁ < n
  μ_inner : ∀ p, 0 < p → p < n → p ≠ s₂ → p ≠ s₁ →
    0 < μ p ∧ μ p < n ∧ μ p ≠ s₂ ∧ μ p ≠ s₁
  μ_μ : ∀ p, 0 < p → p < n → p ≠ s₂ → p ≠ s₁ → μ (μ p) = p
  μ_ne : ∀ p, 0 < p → p < n → p ≠ s₂ → p ≠ s₁ → μ p ≠ p

namespace Pole

variable (P : Pole)

/-- Inner positions: the positions of the circuit carrying a chord rather than a spoke. -/
def Inner (p : ℕ) : Prop := 0 < p ∧ p < P.n ∧ p ≠ P.s₂ ∧ p ≠ P.s₁

instance : DecidablePred P.Inner := fun p ↦ by unfold Inner; infer_instance

/-- Spoke positions. -/
def Spoke (p : ℕ) : Prop := p = 0 ∨ p = P.s₂ ∨ p = P.s₁

instance : DecidablePred P.Spoke := fun p ↦ by unfold Spoke; infer_instance

/-- The next position along the circuit. -/
def next (p : ℕ) : ℕ := if p + 1 = P.n then 0 else p + 1

/-- The previous position along the circuit. -/
def prev (p : ℕ) : ℕ := if p = 0 then P.n - 1 else p - 1

/-- The set of inner positions. -/
def innerSet : Finset ℕ := (Finset.range P.n).filter P.Inner

/-- The number of exterior chords of a set of positions: positions of the set whose chord
partner lies outside the set. -/
def ext (T : Finset ℕ) : ℕ := (T.filter fun p ↦ P.μ p ∉ T).card

/-- The inner positions of the segment from the spoke `0` to the spoke `s₂`. -/
def T₀ : Finset ℕ := Finset.Ico 1 P.s₂

/-- The inner positions of the segment from the spoke `s₂` to the spoke `s₁`. -/
def T₁ : Finset ℕ := Finset.Ico (P.s₂ + 1) P.s₁

/-- The inner positions of the segment from the spoke `s₁` back to the spoke `0`. -/
def T₂ : Finset ℕ := Finset.Ico (P.s₁ + 1) P.n

variable {P}

theorem inner_μ {p : ℕ} (hp : P.Inner p) : P.Inner (P.μ p) :=
  P.μ_inner p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

theorem μ_μ_of_inner {p : ℕ} (hp : P.Inner p) : P.μ (P.μ p) = p :=
  P.μ_μ p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

theorem μ_ne_of_inner {p : ℕ} (hp : P.Inner p) : P.μ p ≠ p :=
  P.μ_ne p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

theorem μ_injOn {p q : ℕ} (hp : P.Inner p) (hq : P.Inner q) (h : P.μ p = P.μ q) : p = q := by
  rw [← μ_μ_of_inner hp, h, μ_μ_of_inner hq]

theorem not_inner_of_spoke {p : ℕ} (h : P.Spoke p) : ¬ P.Inner p := by
  rintro ⟨h0, -, h2, h1⟩
  rcases h with h | h | h
  · omega
  · exact h2 h
  · exact h1 h

theorem inner_or_spoke {p : ℕ} (hp : p < P.n) : P.Inner p ∨ P.Spoke p := by
  by_cases h0 : p = 0
  · exact Or.inr (Or.inl h0)
  by_cases h2 : p = P.s₂
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h1 : p = P.s₁
  · exact Or.inr (Or.inr (Or.inr h1))
  exact Or.inl ⟨Nat.pos_of_ne_zero h0, hp, h2, h1⟩

theorem inner_iff {p : ℕ} : P.Inner p ↔ p < P.n ∧ ¬ P.Spoke p := by
  constructor
  · intro h
    exact ⟨h.2.1, fun hs ↦ not_inner_of_spoke hs h⟩
  · rintro ⟨hp, hs⟩
    rcases inner_or_spoke hp with h | h
    · exact h
    · exact absurd h hs

theorem spoke_zero : P.Spoke 0 := Or.inl rfl

theorem spoke_s₂ : P.Spoke P.s₂ := Or.inr (Or.inl rfl)

theorem spoke_s₁ : P.Spoke P.s₁ := Or.inr (Or.inr rfl)

theorem spoke_lt {p : ℕ} (h : P.Spoke p) : p < P.n := by
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  rcases h with h | h | h <;> omega

theorem inner_lt {p : ℕ} (h : P.Inner p) : p < P.n := h.2.1

theorem inner_pos {p : ℕ} (h : P.Inner p) : 0 < p := h.1

theorem n_pos : 0 < P.n := by
  have := P.s₂_pos
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  omega

theorem three_lt_n : 3 ≤ P.n := by
  have := P.s₂_pos
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  omega

theorem next_lt {p : ℕ} (hp : p < P.n) : P.next p < P.n := by
  unfold next
  split_ifs <;> omega

theorem prev_lt {p : ℕ} (hp : p < P.n) : P.prev p < P.n := by
  unfold prev
  by_cases h : p = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

theorem prev_next {p : ℕ} : P.prev (P.next p) = p := by
  unfold prev next
  by_cases h : p + 1 = P.n
  · rw [if_pos h, if_pos rfl]
    omega
  · rw [if_neg h, if_neg (by omega)]
    omega

theorem next_prev {p : ℕ} (hp : p < P.n) : P.next (P.prev p) = p := by
  unfold prev next
  have := @n_pos P
  by_cases h : p = 0
  · rw [if_pos h, if_pos (by omega)]
    omega
  · rw [if_neg h, if_neg (by omega)]
    omega

theorem prev_of_pos {p : ℕ} (hp : 0 < p) : P.prev p = p - 1 := by
  unfold prev
  rw [if_neg (by omega)]

theorem prev_zero : P.prev 0 = P.n - 1 := by
  unfold prev
  rw [if_pos rfl]

theorem next_of_lt {p : ℕ} (hp : p + 1 < P.n) : P.next p = p + 1 := by
  unfold next
  rw [if_neg (by omega)]

theorem next_last : P.next (P.n - 1) = 0 := by
  unfold next
  have := @n_pos P
  rw [if_pos (by omega)]

theorem mem_innerSet {p : ℕ} : p ∈ P.innerSet ↔ P.Inner p := by
  unfold innerSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inner_lt h, h⟩⟩

theorem mem_T₀ {p : ℕ} : p ∈ P.T₀ ↔ 1 ≤ p ∧ p < P.s₂ := Finset.mem_Ico

theorem mem_T₁ {p : ℕ} : p ∈ P.T₁ ↔ P.s₂ + 1 ≤ p ∧ p < P.s₁ := Finset.mem_Ico

theorem mem_T₂ {p : ℕ} : p ∈ P.T₂ ↔ P.s₁ + 1 ≤ p ∧ p < P.n := Finset.mem_Ico

theorem inner_of_mem_T₀ {p : ℕ} (h : p ∈ P.T₀) : P.Inner p := by
  rw [mem_T₀] at h
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem inner_of_mem_T₁ {p : ℕ} (h : p ∈ P.T₁) : P.Inner p := by
  rw [mem_T₁] at h
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem inner_of_mem_T₂ {p : ℕ} (h : p ∈ P.T₂) : P.Inner p := by
  rw [mem_T₂] at h
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem card_T₀ : P.T₀.card = P.s₂ - 1 := by
  unfold T₀
  rw [Nat.card_Ico]

theorem card_T₁ : P.T₁.card = P.s₁ - P.s₂ - 1 := by
  unfold T₁
  rw [Nat.card_Ico]
  omega

theorem card_T₂ : P.T₂.card = P.n - P.s₁ - 1 := by
  unfold T₂
  rw [Nat.card_Ico]
  omega

/-- A finite set closed under a fixed-point-free involution has even cardinality. -/
theorem even_card_of_involution (f : ℕ → ℕ) (T : Finset ℕ) (hf : ∀ p ∈ T, f p ∈ T)
    (hff : ∀ p ∈ T, f (f p) = p) (hne : ∀ p ∈ T, f p ≠ p) : Even T.card := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with h | ⟨p, hp⟩
    · subst h
      exact ⟨0, rfl⟩
    · have hfp : f p ∈ T := hf p hp
      have hfp' : f p ∈ T.erase p := Finset.mem_erase.mpr ⟨hne p hp, hfp⟩
      set T' := (T.erase p).erase (f p) with hT'
      have hsub : T' ⊂ T :=
        Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset hp)
      have hmem : ∀ q, q ∈ T' ↔ q ∈ T ∧ q ≠ p ∧ q ≠ f p := by
        intro q
        rw [hT', Finset.mem_erase, Finset.mem_erase]
        tauto
      have hcard : T.card = T'.card + 2 := by
        have h2 : 2 ≤ T.card := by
          have hsub2 : ({p, f p} : Finset ℕ) ⊆ T := by
            intro q hq
            rw [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact hp
            · exact hfp
          have := Finset.card_le_card hsub2
          rwa [Finset.card_pair (hne p hp).symm] at this
        rw [hT', Finset.card_erase_of_mem hfp', Finset.card_erase_of_mem hp]
        omega
      have hev : Even T'.card := by
        refine ih T' hsub ?_ ?_ ?_
        · intro q hq
          rw [hmem] at hq ⊢
          refine ⟨hf q hq.1, ?_, ?_⟩
          · intro h
            apply hq.2.2
            rw [← h, hff q hq.1]
          · intro h
            apply hq.2.1
            rw [← hff q hq.1, h, hff p hp]
        · intro q hq
          exact hff q ((hmem q).mp hq).1
        · intro q hq
          exact hne q ((hmem q).mp hq).1
      rw [hcard]
      exact hev.add ⟨1, rfl⟩

/-- The number of exterior chords of a set of inner positions has the parity of the set. -/
theorem ext_mod_two {T : Finset ℕ} (hT : ∀ p ∈ T, P.Inner p) : P.ext T % 2 = T.card % 2 := by
  unfold ext
  have h := Finset.card_filter_add_card_filter_not (s := T) (fun p ↦ P.μ p ∉ T)
  have hev : Even ((T.filter fun p ↦ ¬ P.μ p ∉ T).card) := by
    refine even_card_of_involution P.μ _ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, not_not] at hp ⊢
      refine ⟨hp.2, ?_⟩
      rw [μ_μ_of_inner (hT p hp.1)]
      exact hp.1
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact μ_μ_of_inner (hT p hp.1)
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact μ_ne_of_inner (hT p hp.1)
  obtain ⟨k, hk⟩ := hev
  omega

/-- The spoke positions as a finite set. -/
theorem card_spokes : ((Finset.range P.n).filter P.Spoke).card = 3 := by
  have h2 := P.s₂_pos
  have h1 := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have : (Finset.range P.n).filter P.Spoke = {0, P.s₂, P.s₁} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    unfold Spoke
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨by rcases h with h | h | h <;> omega, h⟩
  rw [this, Finset.card_insert_of_notMem, Finset.card_pair]
  · omega
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

theorem card_innerSet : P.innerSet.card + 3 = P.n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range P.n) P.Inner
  have heq : (Finset.range P.n).filter (fun p ↦ ¬ P.Inner p) = (Finset.range P.n).filter P.Spoke := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, h⟩
      rcases inner_or_spoke hp with h' | h'
      · exact absurd h' h
      · exact ⟨hp, h'⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, not_inner_of_spoke h⟩
  rw [heq, card_spokes, Finset.card_range] at h
  exact h

/-- The number of vertices of a Hamiltonian cubic `3`-pole is odd. -/
theorem n_odd : Odd P.n := by
  have h := ext_mod_two (P := P) (T := P.innerSet) (fun p hp ↦ mem_innerSet.mp hp)
  have hext : P.ext P.innerSet = 0 := by
    unfold ext
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    rw [not_not, mem_innerSet]
    exact inner_μ (mem_innerSet.mp hp)
  rw [hext] at h
  have := @card_innerSet P
  rw [Nat.odd_iff]
  omega

/-- A proper four-cover of an abstract pole: the labels of the circuit edges (edge `p` joins the
positions `p` and `p + 1`) and of the chords and spokes, partitioning the three colours at each
position. -/
structure Cover (P : Pole) where
  /-- The label of the circuit edge from `p` to `p + 1`. -/
  lab : ℕ → Finset (Fin 3)
  /-- The label of the chord or spoke at position `p`. -/
  clab : ℕ → Finset (Fin 3)
  nonempty : ∀ p, p < P.n → (lab p).Nonempty
  disj₁ : ∀ p, p < P.n → Disjoint (lab (P.prev p)) (lab p)
  disj₂ : ∀ p, p < P.n → Disjoint (lab (P.prev p)) (clab p)
  disj₃ : ∀ p, p < P.n → Disjoint (lab p) (clab p)
  union : ∀ p, p < P.n → lab (P.prev p) ∪ lab p ∪ clab p = Finset.univ
  chord : ∀ p, P.Inner p → clab (P.μ p) = clab p
  spoke : ∀ p, P.Spoke p → (clab p).card = 1

theorem three_singletons_union {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x} : Finset (Fin 3)) ∪ {y} ∪ {z} = Finset.univ := by
  revert x y z
  decide

/-- A proper `3`-edge-colouring of the pole (circuit edge `p` coloured `col p`, the chord or spoke
at `p` coloured `chordcol p`) gives a proper four-cover with singleton labels. -/
def Cover.ofColouring (col chordcol : ℕ → Fin 3)
    (h₁ : ∀ p, p < P.n → col (P.prev p) ≠ col p)
    (h₂ : ∀ p, p < P.n → col (P.prev p) ≠ chordcol p)
    (h₃ : ∀ p, p < P.n → col p ≠ chordcol p)
    (hchord : ∀ p, P.Inner p → chordcol (P.μ p) = chordcol p) : P.Cover where
  lab := fun p ↦ {col p}
  clab := fun p ↦ {chordcol p}
  nonempty := fun p _ ↦ Finset.singleton_nonempty _
  disj₁ := fun p hp ↦ Finset.disjoint_singleton.mpr (h₁ p hp)
  disj₂ := fun p hp ↦ Finset.disjoint_singleton.mpr (h₂ p hp)
  disj₃ := fun p hp ↦ Finset.disjoint_singleton.mpr (h₃ p hp)
  union := fun p hp ↦ three_singletons_union (h₁ p hp) (h₂ p hp) (h₃ p hp)
  chord := fun p hp ↦ by rw [hchord p hp]
  spoke := fun p _ ↦ Finset.card_singleton _

section ThreeOdd

/-- The alternating labels along a segment whose third colour is `c`: the label `{c}` at even
offsets and the complementary pair at odd offsets. -/
def seg (c : Fin 3) (m : ℕ) : Finset (Fin 3) := if Even m then {c} else Finset.univ.erase c

theorem seg_zero (c : Fin 3) : seg c 0 = {c} := by
  unfold seg
  rw [if_pos ⟨0, rfl⟩]

theorem seg_of_even (c : Fin 3) {m : ℕ} (hm : Even m) : seg c m = {c} := by
  unfold seg
  rw [if_pos hm]

theorem seg_nonempty (c : Fin 3) (m : ℕ) : (seg c m).Nonempty := by
  unfold seg
  split_ifs
  · exact Finset.singleton_nonempty c
  · refine ⟨c + 1, ?_⟩
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    fin_cases c <;> decide

theorem seg_disjoint (c : Fin 3) (m : ℕ) : Disjoint (seg c m) (seg c (m + 1)) := by
  unfold seg
  by_cases hm : Even m
  · rw [if_pos hm, if_neg (by rw [Nat.even_add_one]; exact not_not.mpr hm)]
    rw [Finset.disjoint_singleton_left, Finset.mem_erase]
    tauto
  · rw [if_neg hm, if_pos (Nat.even_add_one.mpr hm)]
    rw [Finset.disjoint_singleton_right, Finset.mem_erase]
    tauto

theorem seg_union (c : Fin 3) (m : ℕ) : seg c m ∪ seg c (m + 1) = Finset.univ := by
  unfold seg
  by_cases hm : Even m
  · rw [if_pos hm, if_neg (by rw [Nat.even_add_one]; exact not_not.mpr hm)]
    ext i
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ,
      and_true, iff_true]
    tauto
  · rw [if_neg hm, if_pos (Nat.even_add_one.mpr hm)]
    ext i
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ,
      and_true, iff_true]
    tauto

variable (P)

/-- The edge labels of the three-odd-segments cover. -/
def threeOddLab (p : ℕ) : Finset (Fin 3) :=
  if p < P.s₂ then seg 2 p else if p < P.s₁ then seg 0 (p - P.s₂) else seg 1 (p - P.s₁)

/-- The chord labels of the three-odd-segments cover: only the spokes are labelled. -/
def threeOddClab (p : ℕ) : Finset (Fin 3) :=
  if p = 0 then {0} else if p = P.s₂ then {1} else if p = P.s₁ then {2} else ∅

variable {P}

theorem threeOddLab_of_lt_s₂ {p : ℕ} (h : p < P.s₂) : P.threeOddLab p = seg 2 p := by
  unfold threeOddLab
  rw [if_pos h]

theorem threeOddLab_of_lt_s₁ {p : ℕ} (h2 : P.s₂ ≤ p) (h : p < P.s₁) :
    P.threeOddLab p = seg 0 (p - P.s₂) := by
  unfold threeOddLab
  rw [if_neg (by omega), if_pos h]

theorem threeOddLab_of_le_s₁ {p : ℕ} (h : P.s₁ ≤ p) : P.threeOddLab p = seg 1 (p - P.s₁) := by
  unfold threeOddLab
  have := P.s₂_lt_s₁
  rw [if_neg (by omega), if_neg (by omega)]

theorem threeOddClab_of_inner {p : ℕ} (h : P.Inner p) : P.threeOddClab p = ∅ := by
  unfold threeOddClab
  rw [if_neg (Nat.pos_iff_ne_zero.mp h.1), if_neg h.2.2.1, if_neg h.2.2.2]

/-- Lemma 3.3: a pole with three odd segments has a proper four-cover.  The spoke at `0` gets
colour `0`, the spoke at `s₂` colour `1`, the spoke at `s₁` colour `2`; along the segment between
two spokes the circuit edges alternate between the third colour and the pair of the two spoke
colours. -/
def coverOfThreeOdd (h₀ : Odd P.s₂) (h₁ : Odd (P.s₁ - P.s₂)) (h₂ : Odd (P.n - P.s₁)) :
    P.Cover where
  lab := P.threeOddLab
  clab := P.threeOddClab
  nonempty := by
    intro p hp
    unfold threeOddLab
    split_ifs <;> exact seg_nonempty _ _
  disj₁ := by
    intro p hp
    have hs2 := P.s₂_pos
    have hs1 := P.s₂_lt_s₁
    have hn := P.s₁_lt_n
    by_cases h0 : p = 0
    · subst h0
      rw [prev_zero, threeOddLab_of_le_s₁ (by omega), threeOddLab_of_lt_s₂ hs2, seg_zero,
        seg_of_even 1 (by obtain ⟨k, hk⟩ := h₂; exact ⟨k, by omega⟩)]
      decide
    rw [prev_of_pos (Nat.pos_of_ne_zero h0)]
    by_cases hlt2 : p < P.s₂
    · rw [threeOddLab_of_lt_s₂ (by omega), threeOddLab_of_lt_s₂ hlt2]
      have := seg_disjoint 2 (p - 1)
      rwa [Nat.sub_add_cancel (by omega)] at this
    by_cases heq2 : p = P.s₂
    · subst heq2
      rw [threeOddLab_of_lt_s₂ (by omega), threeOddLab_of_lt_s₁ le_rfl hs1, Nat.sub_self, seg_zero,
        seg_of_even 2 (by obtain ⟨k, hk⟩ := h₀; exact ⟨k, by omega⟩)]
      decide
    by_cases hlt1 : p < P.s₁
    · rw [threeOddLab_of_lt_s₁ (by omega) (by omega), threeOddLab_of_lt_s₁ (by omega) hlt1]
      have := seg_disjoint 0 (p - 1 - P.s₂)
      rwa [show p - 1 - P.s₂ + 1 = p - P.s₂ by omega] at this
    by_cases heq1 : p = P.s₁
    · subst heq1
      rw [threeOddLab_of_lt_s₁ (by omega) (by omega), threeOddLab_of_le_s₁ le_rfl, Nat.sub_self,
        seg_zero, seg_of_even 0 (by obtain ⟨k, hk⟩ := h₁; exact ⟨k, by omega⟩)]
      decide
    rw [threeOddLab_of_le_s₁ (by omega), threeOddLab_of_le_s₁ (by omega)]
    have := seg_disjoint 1 (p - 1 - P.s₁)
    rwa [show p - 1 - P.s₁ + 1 = p - P.s₁ by omega] at this
  disj₂ := by
    intro p hp
    have hs2 := P.s₂_pos
    have hs1 := P.s₂_lt_s₁
    have hn := P.s₁_lt_n
    rcases inner_or_spoke hp with h | h
    · rw [threeOddClab_of_inner h]
      exact Finset.disjoint_empty_right _
    rcases h with h | h | h
    · subst h
      rw [prev_zero, threeOddLab_of_le_s₁ (by omega),
        seg_of_even 1 (by obtain ⟨k, hk⟩ := h₂; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_pos rfl]
      decide
    · subst h
      rw [prev_of_pos hs2, threeOddLab_of_lt_s₂ (by omega),
        seg_of_even 2 (by obtain ⟨k, hk⟩ := h₀; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_neg (by omega), if_pos rfl]
      decide
    · subst h
      rw [prev_of_pos (by omega), threeOddLab_of_lt_s₁ (by omega) (by omega),
        seg_of_even 0 (by obtain ⟨k, hk⟩ := h₁; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      decide
  disj₃ := by
    intro p hp
    have hs2 := P.s₂_pos
    have hs1 := P.s₂_lt_s₁
    have hn := P.s₁_lt_n
    rcases inner_or_spoke hp with h | h
    · rw [threeOddClab_of_inner h]
      exact Finset.disjoint_empty_right _
    rcases h with h | h | h
    · subst h
      rw [threeOddLab_of_lt_s₂ hs2, seg_zero]
      unfold threeOddClab
      rw [if_pos rfl]
      decide
    · subst h
      rw [threeOddLab_of_lt_s₁ le_rfl hs1, Nat.sub_self, seg_zero]
      unfold threeOddClab
      rw [if_neg (by omega), if_pos rfl]
      decide
    · subst h
      rw [threeOddLab_of_le_s₁ le_rfl, Nat.sub_self, seg_zero]
      unfold threeOddClab
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      decide
  union := by
    intro p hp
    have hs2 := P.s₂_pos
    have hs1 := P.s₂_lt_s₁
    have hn := P.s₁_lt_n
    by_cases h0 : p = 0
    · subst h0
      rw [prev_zero, threeOddLab_of_le_s₁ (by omega), threeOddLab_of_lt_s₂ hs2, seg_zero,
        seg_of_even 1 (by obtain ⟨k, hk⟩ := h₂; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_pos rfl]
      decide
    rw [prev_of_pos (Nat.pos_of_ne_zero h0)]
    by_cases hlt2 : p < P.s₂
    · rw [threeOddClab_of_inner ⟨by omega, by omega, by omega, by omega⟩, Finset.union_empty,
        threeOddLab_of_lt_s₂ (by omega), threeOddLab_of_lt_s₂ hlt2]
      have := seg_union 2 (p - 1)
      rwa [Nat.sub_add_cancel (by omega)] at this
    by_cases heq2 : p = P.s₂
    · subst heq2
      rw [threeOddLab_of_lt_s₂ (by omega), threeOddLab_of_lt_s₁ le_rfl hs1, Nat.sub_self, seg_zero,
        seg_of_even 2 (by obtain ⟨k, hk⟩ := h₀; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_neg (by omega), if_pos rfl]
      decide
    by_cases hlt1 : p < P.s₁
    · rw [threeOddClab_of_inner ⟨by omega, by omega, by omega, by omega⟩, Finset.union_empty,
        threeOddLab_of_lt_s₁ (by omega) (by omega), threeOddLab_of_lt_s₁ (by omega) hlt1]
      have := seg_union 0 (p - 1 - P.s₂)
      rwa [show p - 1 - P.s₂ + 1 = p - P.s₂ by omega] at this
    by_cases heq1 : p = P.s₁
    · subst heq1
      rw [threeOddLab_of_lt_s₁ (by omega) (by omega), threeOddLab_of_le_s₁ le_rfl, Nat.sub_self,
        seg_zero, seg_of_even 0 (by obtain ⟨k, hk⟩ := h₁; exact ⟨k, by omega⟩)]
      unfold threeOddClab
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      decide
    rw [threeOddClab_of_inner ⟨by omega, by omega, by omega, by omega⟩, Finset.union_empty,
      threeOddLab_of_le_s₁ (by omega), threeOddLab_of_le_s₁ (by omega)]
    have := seg_union 1 (p - 1 - P.s₁)
    rwa [show p - 1 - P.s₁ + 1 = p - P.s₁ by omega] at this
  chord := by
    intro p hp
    rw [threeOddClab_of_inner hp, threeOddClab_of_inner (inner_μ hp)]
  spoke := by
    intro p hp
    have hs2 := P.s₂_pos
    have hs1 := P.s₂_lt_s₁
    unfold threeOddClab
    rcases hp with h | h | h
    · rw [if_pos h]
      rfl
    · rw [if_neg (by omega), if_pos h]
      rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      rfl

end ThreeOdd

end Pole

end GraphPuzzles
