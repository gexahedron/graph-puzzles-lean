import GraphPuzzles.Poles.Pole
import Mathlib.Data.Nat.Nth

/-!
# Alternating cycles and their suppression

An alternating cycle of an abstract pole is recorded by the set `F` of its circuit edges: a
nonempty set of circuit edges, no two consecutive, with both ends inner, whose vertex set
`D = F ∪ (F + 1)` is closed under the chord map.  Suppressing it deletes the positions of `D`
(together with their chords) and joins the remaining positions in order; the position `p ∉ D`
becomes `r p`, the number of positions below `p` not in `D`.

Lemma 3.2 of Karabáš–Máčajová: a proper four-cover of the suppressed pole lifts to one of the
original pole.  Every circuit edge of the suppressed pole corresponds to an odd path of circuit
edges of the original pole, alternating between edges outside `F` and edges of `F`; the edges
outside `F` inherit the label of the reduced edge and the edges of `F` get the complementary
label, the chords at the deleted positions get the empty label.
-/

namespace GraphPuzzles
namespace Pole

/-- The vertex set of a set of circuit edges. -/
def dset (F : Finset ℕ) : Finset ℕ := F ∪ F.image (· + 1)

theorem mem_dset {F : Finset ℕ} {q : ℕ} : q ∈ dset F ↔ q ∈ F ∨ (1 ≤ q ∧ q - 1 ∈ F) := by
  unfold dset
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by simpa using hp⟩
  · rintro (h | ⟨h1, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q - 1, h, by omega⟩

/-- An alternating cycle: a nonempty set of circuit edges (edge `p` joins `p` and `p + 1`), no
two consecutive, with both ends inner, whose vertex set is closed under the chord map. -/
structure AltCycle (P : Pole) where
  /-- The circuit edges of the alternating cycle. -/
  F : Finset ℕ
  nonempty : F.Nonempty
  inner : ∀ p ∈ F, P.Inner p ∧ P.Inner (p + 1)
  matching : ∀ p ∈ F, p + 1 ∉ F
  closed : ∀ p ∈ F, P.μ p ∈ dset F ∧ P.μ (p + 1) ∈ dset F

namespace AltCycle

variable {P : Pole} (A : P.AltCycle)

/-- The vertex set of the alternating cycle. -/
def D : Finset ℕ := dset A.F

theorem mem_D {q : ℕ} : q ∈ A.D ↔ q ∈ A.F ∨ (1 ≤ q ∧ q - 1 ∈ A.F) := mem_dset

theorem mem_D_of_mem {p : ℕ} (hp : p ∈ A.F) : p ∈ A.D := A.mem_D.mpr (Or.inl hp)

theorem succ_mem_D_of_mem {p : ℕ} (hp : p ∈ A.F) : p + 1 ∈ A.D :=
  A.mem_D.mpr (Or.inr ⟨by omega, by simpa using hp⟩)

theorem inner_of_mem_D {q : ℕ} (hq : q ∈ A.D) : P.Inner q := by
  rcases A.mem_D.mp hq with h | ⟨h1, h⟩
  · exact (A.inner q h).1
  · have := (A.inner _ h).2
    rwa [Nat.sub_add_cancel h1] at this

theorem pos_of_mem_D {q : ℕ} (hq : q ∈ A.D) : 0 < q := (A.inner_of_mem_D hq).1

theorem lt_of_mem_D {q : ℕ} (hq : q ∈ A.D) : q < P.n := (A.inner_of_mem_D hq).2.1

theorem notMem_D_of_spoke {q : ℕ} (hq : P.Spoke q) : q ∉ A.D :=
  fun h ↦ not_inner_of_spoke hq (A.inner_of_mem_D h)

theorem zero_notMem_D : 0 ∉ A.D := A.notMem_D_of_spoke spoke_zero

theorem zero_notMem_F : 0 ∉ A.F := fun h ↦ A.zero_notMem_D (A.mem_D_of_mem h)

theorem last_notMem_F : P.n - 1 ∉ A.F := by
  intro h
  have := (A.inner _ h).2.2.1
  have := @n_pos P
  omega

/-- At a position of the cycle, exactly one of the two circuit edges belongs to `F`. -/
theorem mem_F_xor {q : ℕ} (hq : q ∈ A.D) : (q ∈ A.F ∧ q - 1 ∉ A.F) ∨ (q ∉ A.F ∧ q - 1 ∈ A.F) := by
  have hpos := A.pos_of_mem_D hq
  rcases A.mem_D.mp hq with h | ⟨-, h⟩
  · left
    refine ⟨h, fun h' ↦ A.matching _ h' ?_⟩
    rwa [Nat.sub_add_cancel hpos]
  · right
    refine ⟨fun h' ↦ A.matching _ h ?_, h⟩
    rwa [Nat.sub_add_cancel hpos]

theorem μ_mem_D {q : ℕ} (hq : q ∈ A.D) : P.μ q ∈ A.D := by
  rcases A.mem_D.mp hq with h | ⟨h1, h⟩
  · exact (A.closed q h).1
  · have := (A.closed _ h).2
    rwa [Nat.sub_add_cancel h1] at this

theorem μ_notMem_D {q : ℕ} (hq : P.Inner q) (h : q ∉ A.D) : P.μ q ∉ A.D := by
  intro h'
  have := A.μ_mem_D h'
  rw [μ_μ_of_inner hq] at this
  exact h this

/-- The relabelling of the positions surviving the suppression. -/
def r (p : ℕ) : ℕ := Nat.count (fun q ↦ q ∉ A.D) p

/-- The inverse relabelling. -/
noncomputable def rinv (q : ℕ) : ℕ := Nat.nth (fun q ↦ q ∉ A.D) q

theorem infinite_notD : (setOf fun q ↦ q ∉ A.D).Infinite := by
  have : (setOf fun q ↦ q ∉ A.D) = (↑A.D : Set ℕ)ᶜ := by
    ext q
    simp
  rw [this]
  exact Set.Finite.infinite_compl (Finset.finite_toSet A.D)

theorem r_rinv (q : ℕ) : A.r (A.rinv q) = q := Nat.count_nth_of_infinite A.infinite_notD q

theorem rinv_r {p : ℕ} (hp : p ∉ A.D) : A.rinv (A.r p) = p := Nat.nth_count hp

theorem rinv_notMem (q : ℕ) : A.rinv q ∉ A.D := Nat.nth_mem_of_infinite A.infinite_notD q

theorem r_lt_r {p p' : ℕ} (hp : p ∉ A.D) (h : p < p') : A.r p < A.r p' :=
  Nat.count_strict_mono hp h

theorem r_mono {p p' : ℕ} (h : p ≤ p') : A.r p ≤ A.r p' := Nat.count_monotone _ h

theorem r_injOn {p p' : ℕ} (hp : p ∉ A.D) (hp' : p' ∉ A.D) (h : A.r p = A.r p') : p = p' := by
  rw [← A.rinv_r hp, h, A.rinv_r hp']

theorem r_succ_of_mem {p : ℕ} (hp : p ∈ A.D) : A.r (p + 1) = A.r p := by
  unfold r
  rw [Nat.count_succ, if_neg (not_not.mpr hp), add_zero]

theorem r_succ_of_notMem {p : ℕ} (hp : p ∉ A.D) : A.r (p + 1) = A.r p + 1 := by
  unfold r
  rw [Nat.count_succ, if_pos hp]

theorem r_zero : A.r 0 = 0 := Nat.count_zero _

theorem r_one : A.r 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, A.r_succ_of_notMem A.zero_notMem_D, r_zero]

theorem r_pos {p : ℕ} (hp : 0 < p) : 0 < A.r p := by
  have := A.r_lt_r A.zero_notMem_D hp
  rwa [r_zero] at this

theorem rinv_lt_iff {q p : ℕ} : A.rinv q < p ↔ q < A.r p :=
  (Nat.lt_nth_iff_count_lt A.infinite_notD).symm

theorem r_n_lt : A.r P.n < P.n := by
  unfold r
  rw [Nat.count_eq_card_filter_range]
  have hF := A.nonempty
  obtain ⟨f, hf⟩ := hF
  have : (Finset.range P.n).filter (fun q ↦ q ∉ A.D) ⊂ Finset.range P.n := by
    rw [Finset.filter_ssubset]
    exact ⟨f, Finset.mem_range.mpr (A.lt_of_mem_D (A.mem_D_of_mem hf)), not_not.mpr (A.mem_D_of_mem hf)⟩
  have := Finset.card_lt_card this
  rwa [Finset.card_range] at this

/-- The pole obtained by suppressing the alternating cycle. -/
noncomputable def suppress : Pole where
  n := A.r P.n
  s₂ := A.r P.s₂
  s₁ := A.r P.s₁
  μ := fun q ↦ A.r (P.μ (A.rinv q))
  s₂_pos := A.r_pos P.s₂_pos
  s₂_lt_s₁ := A.r_lt_r (A.notMem_D_of_spoke spoke_s₂) P.s₂_lt_s₁
  s₁_lt_n := A.r_lt_r (A.notMem_D_of_spoke spoke_s₁) P.s₁_lt_n
  μ_inner := by
    intro q h0 hq h2 h1
    set p := A.rinv q with hp
    have hpD : p ∉ A.D := A.rinv_notMem q
    have hpn : p < P.n := A.rinv_lt_iff.mpr hq
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hp
      have := A.r_rinv q
      rw [← hp, r_zero] at this
      omega
    have hp2 : p ≠ P.s₂ := by
      intro h
      apply h2
      rw [← A.r_rinv q, ← hp, h]
    have hp1 : p ≠ P.s₁ := by
      intro h
      apply h1
      rw [← A.r_rinv q, ← hp, h]
    have hpi : P.Inner p := ⟨Nat.pos_of_ne_zero hp0, hpn, hp2, hp1⟩
    have hμi := inner_μ hpi
    have hμD := A.μ_notMem_D hpi hpD
    refine ⟨A.r_pos hμi.1, A.r_lt_r hμD hμi.2.1, ?_, ?_⟩
    · intro h
      exact hμi.2.2.1 (A.r_injOn hμD (A.notMem_D_of_spoke spoke_s₂) h)
    · intro h
      exact hμi.2.2.2 (A.r_injOn hμD (A.notMem_D_of_spoke spoke_s₁) h)
  μ_μ := by
    intro q h0 hq h2 h1
    set p := A.rinv q with hp
    have hpD : p ∉ A.D := A.rinv_notMem q
    have hpn : p < P.n := A.rinv_lt_iff.mpr hq
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hp
      have := A.r_rinv q
      rw [← hp, r_zero] at this
      omega
    have hp2 : p ≠ P.s₂ := by
      intro h
      apply h2
      rw [← A.r_rinv q, ← hp, h]
    have hp1 : p ≠ P.s₁ := by
      intro h
      apply h1
      rw [← A.r_rinv q, ← hp, h]
    have hpi : P.Inner p := ⟨Nat.pos_of_ne_zero hp0, hpn, hp2, hp1⟩
    have hμD := A.μ_notMem_D hpi hpD
    rw [A.rinv_r hμD, μ_μ_of_inner hpi, A.r_rinv]
  μ_ne := by
    intro q h0 hq h2 h1 h
    set p := A.rinv q with hp
    have hpD : p ∉ A.D := A.rinv_notMem q
    have hpn : p < P.n := A.rinv_lt_iff.mpr hq
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hp
      have := A.r_rinv q
      rw [← hp, r_zero] at this
      omega
    have hp2 : p ≠ P.s₂ := by
      intro h
      apply h2
      rw [← A.r_rinv q, ← hp, h]
    have hp1 : p ≠ P.s₁ := by
      intro h
      apply h1
      rw [← A.r_rinv q, ← hp, h]
    have hpi : P.Inner p := ⟨Nat.pos_of_ne_zero hp0, hpn, hp2, hp1⟩
    have hμD := A.μ_notMem_D hpi hpD
    have : P.μ p = p := A.r_injOn hμD hpD (by rw [h, hp, A.r_rinv])
    exact μ_ne_of_inner hpi this

theorem suppress_n : A.suppress.n = A.r P.n := rfl

theorem suppress_n_lt : A.suppress.n < P.n := A.r_n_lt

theorem suppress_μ_r {p : ℕ} (hp : p ∉ A.D) : A.suppress.μ (A.r p) = A.r (P.μ p) := by
  change A.r (P.μ (A.rinv (A.r p))) = _
  rw [A.rinv_r hp]

theorem suppress_inner_r {p : ℕ} (hp : P.Inner p) (hpD : p ∉ A.D) : A.suppress.Inner (A.r p) := by
  refine ⟨A.r_pos hp.1, A.r_lt_r hpD hp.2.1, ?_, ?_⟩
  · intro h
    exact hp.2.2.1 (A.r_injOn hpD (A.notMem_D_of_spoke spoke_s₂) h)
  · intro h
    exact hp.2.2.2 (A.r_injOn hpD (A.notMem_D_of_spoke spoke_s₁) h)

theorem suppress_spoke_r {p : ℕ} (hp : P.Spoke p) : A.suppress.Spoke (A.r p) := by
  rcases hp with h | h | h
  · left
    rw [h, r_zero]
  · right; left
    rw [h]
    rfl
  · right; right
    rw [h]
    rfl

section Lift

/-- The index of the reduced circuit edge containing the circuit edge `p`. -/
def idx (p : ℕ) : ℕ := A.r (p + 1) - 1

theorem idx_of_mem {p : ℕ} (hp : p ∈ A.D) : A.idx p = A.idx (p - 1) := by
  have hpos := A.pos_of_mem_D hp
  unfold idx
  rw [A.r_succ_of_mem hp, Nat.sub_add_cancel hpos]

theorem idx_of_notMem {p : ℕ} (hp : p ∉ A.D) : A.idx p = A.r p := by
  unfold idx
  rw [A.r_succ_of_notMem hp, Nat.add_sub_cancel]

theorem idx_of_notMem_pos {p : ℕ} (hp : p ∉ A.D) (h0 : 0 < p) : A.idx p = A.idx (p - 1) + 1 := by
  unfold idx
  rw [A.r_succ_of_notMem hp, Nat.sub_add_cancel h0, Nat.add_sub_cancel]
  have := A.r_pos h0
  omega

theorem idx_zero : A.idx 0 = 0 := by
  unfold idx
  rw [zero_add, r_one]

theorem idx_lt {p : ℕ} (hp : p < P.n) : A.idx p < A.suppress.n := by
  unfold idx
  rw [suppress_n]
  have h1 := A.r_mono (show p + 1 ≤ P.n by omega)
  have h2 := A.r_pos (@n_pos P)
  omega

theorem idx_last : A.idx (P.n - 1) = A.suppress.n - 1 := by
  unfold idx
  rw [suppress_n, Nat.sub_add_cancel (@n_pos P)]

theorem suppress_prev_idx {p : ℕ} (hp : p ∉ A.D) (h0 : 0 < p) :
    A.suppress.prev (A.idx p) = A.idx (p - 1) := by
  rw [prev_of_pos, A.idx_of_notMem_pos hp h0, Nat.add_sub_cancel]
  rw [A.idx_of_notMem hp]
  exact A.r_pos h0

variable (C : A.suppress.Cover)

/-- The lifted edge labels: edges of `F` get the complement of the label of their reduced edge,
the other edges inherit it. -/
def liftLab (p : ℕ) : Finset (Fin 3) :=
  if p ∈ A.F then (C.lab (A.idx p))ᶜ else C.lab (A.idx p)

/-- The lifted chord labels: chords of the cycle get the empty label. -/
def liftClab (p : ℕ) : Finset (Fin 3) := if p ∈ A.D then ∅ else C.clab (A.r p)

theorem lab_ne_univ {i : ℕ} (hi : i < A.suppress.n) : C.lab i ≠ Finset.univ := by
  intro h
  have hd := C.disj₁ (A.suppress.next i) (next_lt hi)
  rw [prev_next, h] at hd
  obtain ⟨j, hj⟩ := C.nonempty _ (next_lt hi)
  exact Finset.disjoint_left.mp hd (Finset.mem_univ j) hj

theorem liftLab_of_mem {p : ℕ} (hp : p ∈ A.F) : A.liftLab C p = (C.lab (A.idx p))ᶜ := by
  unfold liftLab
  rw [if_pos hp]

theorem liftLab_of_notMem {p : ℕ} (hp : p ∉ A.F) : A.liftLab C p = C.lab (A.idx p) := by
  unfold liftLab
  rw [if_neg hp]

theorem liftClab_of_mem {p : ℕ} (hp : p ∈ A.D) : A.liftClab C p = ∅ := by
  unfold liftClab
  rw [if_pos hp]

theorem liftClab_of_notMem {p : ℕ} (hp : p ∉ A.D) : A.liftClab C p = C.clab (A.r p) := by
  unfold liftClab
  rw [if_neg hp]

theorem notMem_F_of_notMem_D {p : ℕ} (hp : p ∉ A.D) : p ∉ A.F := fun h ↦ hp (A.mem_D_of_mem h)

theorem pred_notMem_F_of_notMem_D {p : ℕ} (hp : p ∉ A.D) (h0 : 0 < p) : p - 1 ∉ A.F := by
  intro h
  apply hp
  have := A.succ_mem_D_of_mem h
  rwa [Nat.sub_add_cancel h0] at this

/-- The lifted labels at a position outside the cycle are the reduced labels at its image. -/
theorem liftLab_prev_of_notMem {p : ℕ} (hp : p ∉ A.D) (hpn : p < P.n) :
    A.liftLab C (P.prev p) = C.lab (A.suppress.prev (A.r p)) ∧
      A.liftLab C p = C.lab (A.r p) := by
  refine ⟨?_, by rw [A.liftLab_of_notMem C (A.notMem_F_of_notMem_D hp), A.idx_of_notMem hp]⟩
  by_cases h0 : p = 0
  · subst h0
    rw [prev_zero, r_zero, prev_zero, A.liftLab_of_notMem C A.last_notMem_F, idx_last]
  · have h0' : 0 < p := Nat.pos_of_ne_zero h0
    rw [prev_of_pos h0', A.liftLab_of_notMem C (A.pred_notMem_F_of_notMem_D hp h0'),
      ← A.idx_of_notMem hp, suppress_prev_idx A hp h0']

/-- Lemma 3.2: lifting a proper four-cover of the suppressed pole. -/
def lift : P.Cover where
  lab := A.liftLab C
  clab := A.liftClab C
  nonempty := by
    intro p hp
    by_cases hF : p ∈ A.F
    · rw [A.liftLab_of_mem C hF]
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
      exact A.lab_ne_univ C (A.idx_lt hp)
    · rw [A.liftLab_of_notMem C hF]
      exact C.nonempty _ (A.idx_lt hp)
  disj₁ := by
    intro p hp
    by_cases hD : p ∈ A.D
    · have hpos := A.pos_of_mem_D hD
      rw [prev_of_pos hpos]
      rcases A.mem_F_xor hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [A.liftLab_of_mem C h1, A.liftLab_of_notMem C h2, A.idx_of_mem hD]
        exact disjoint_compl_right
      · rw [A.liftLab_of_notMem C h1, A.liftLab_of_mem C h2, A.idx_of_mem hD]
        exact disjoint_compl_left
    · obtain ⟨h1, h2⟩ := A.liftLab_prev_of_notMem C hD hp
      rw [h1, h2]
      exact C.disj₁ _ (A.r_lt_r hD hp)
  disj₂ := by
    intro p hp
    by_cases hD : p ∈ A.D
    · rw [A.liftClab_of_mem C hD]
      exact Finset.disjoint_empty_right _
    · obtain ⟨h1, -⟩ := A.liftLab_prev_of_notMem C hD hp
      rw [h1, A.liftClab_of_notMem C hD]
      exact C.disj₂ _ (A.r_lt_r hD hp)
  disj₃ := by
    intro p hp
    by_cases hD : p ∈ A.D
    · rw [A.liftClab_of_mem C hD]
      exact Finset.disjoint_empty_right _
    · obtain ⟨-, h2⟩ := A.liftLab_prev_of_notMem C hD hp
      rw [h2, A.liftClab_of_notMem C hD]
      exact C.disj₃ _ (A.r_lt_r hD hp)
  union := by
    intro p hp
    by_cases hD : p ∈ A.D
    · have hpos := A.pos_of_mem_D hD
      rw [A.liftClab_of_mem C hD, Finset.union_empty, prev_of_pos hpos]
      rcases A.mem_F_xor hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [A.liftLab_of_mem C h1, A.liftLab_of_notMem C h2, A.idx_of_mem hD]
        exact Finset.union_compl _
      · rw [A.liftLab_of_notMem C h1, A.liftLab_of_mem C h2, A.idx_of_mem hD]
        rw [Finset.union_comm]
        exact Finset.union_compl _
    · obtain ⟨h1, h2⟩ := A.liftLab_prev_of_notMem C hD hp
      rw [h1, h2, A.liftClab_of_notMem C hD]
      exact C.union _ (A.r_lt_r hD hp)
  chord := by
    intro p hp
    by_cases hD : p ∈ A.D
    · rw [A.liftClab_of_mem C hD, A.liftClab_of_mem C (A.μ_mem_D hD)]
    · have hμD := A.μ_notMem_D hp hD
      rw [A.liftClab_of_notMem C hD, A.liftClab_of_notMem C hμD, ← A.suppress_μ_r hD]
      exact C.chord _ (A.suppress_inner_r hp hD)
  spoke := by
    intro p hp
    have hD := A.notMem_D_of_spoke hp
    rw [A.liftClab_of_notMem C hD]
    exact C.spoke _ (A.suppress_spoke_r hp)

end Lift

end AltCycle

end Pole
end GraphPuzzles
