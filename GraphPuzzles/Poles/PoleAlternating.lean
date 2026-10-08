import GraphPuzzles.Poles.PoleReduce

/-!
# Lemma 3.6: alternating cycles in poles with two even segments

Lemma 3.6 of Karabáš–Máčajová: a Hamiltonian cubic `3`-pole whose two even segments each have at
least three exterior chords has an alternating cycle.  We prove it for the normalized abstract
poles (`Good`): the segments `T₀` and `T₂` even with at least three exterior chords each, by
strong induction on the number of positions.

The induction removes two consecutive inner positions at the end of a segment and joins their
chord partners (`reduce`), lifting an alternating cycle back (`AltCycle.unreduce`).  When both
even segments have exactly three inner positions, the two ends of the odd segment are reduced
instead; the cases in which no reduction stays in the family are settled by explicit alternating
cycles: a chord parallel to a circuit edge, two consecutive pairs joined crosswise, and the cycle
through all inner positions except the chords at the two ends of the odd segment.
-/

namespace GraphPuzzles
namespace Pole

/-- The family of Lemma 3.6, normalized: the segments `T₀` and `T₂` are even and each has at
least three exterior chords. -/
def Good (P : Pole) : Prop := Even P.s₂ ∧ Even (P.n - P.s₁) ∧ 3 ≤ P.ext P.T₀ ∧ 3 ≤ P.ext P.T₂

variable {P : Pole}

theorem ext_le_card (T : Finset ℕ) : P.ext T ≤ T.card := Finset.card_filter_le _ _

theorem all_exterior_of_card_le {T : Finset ℕ} (h : T.card ≤ P.ext T) : ∀ p ∈ T, P.μ p ∉ T := by
  have := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun p ↦ P.μ p ∉ T) T) h
  intro p hp
  rw [← this] at hp
  exact (Finset.mem_filter.mp hp).2

section Direct

/-- A chord parallel to a circuit edge is an alternating cycle. -/
def altCycleOfParallel {q : ℕ} (hq : P.Inner q) (hq1 : P.Inner (q + 1)) (h : P.μ q = q + 1) :
    P.AltCycle where
  F := {q}
  nonempty := Finset.singleton_nonempty q
  inner := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨hq, hq1⟩
  matching := by
    intro p hp h'
    rw [Finset.mem_singleton] at hp h'
    omega
  closed := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    have h' : P.μ (p + 1) = p := by
      rw [← h, μ_μ_of_inner hq]
    constructor
    · rw [h, mem_dset, Finset.mem_singleton]
      right
      exact ⟨by omega, by simp⟩
    · rw [h', mem_dset, Finset.mem_singleton]
      left
      rfl

/-- Two consecutive pairs of inner positions joined crosswise by chords form an alternating
cycle. -/
def altCycleOfPairs {q p : ℕ} (hq : P.Inner q) (hq1 : P.Inner (q + 1)) (hp : P.Inner p)
    (hp1 : P.Inner (p + 1)) (hsep : q + 1 < p ∨ p + 1 < q)
    (h : (P.μ q = p ∧ P.μ (q + 1) = p + 1) ∨ (P.μ q = p + 1 ∧ P.μ (q + 1) = p)) :
    P.AltCycle where
  F := {q, p}
  nonempty := Finset.insert_nonempty _ _
  inner := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hq, hq1⟩
    · exact ⟨hp, hp1⟩
  matching := by
    intro x hx h'
    rw [Finset.mem_insert, Finset.mem_singleton] at hx h'
    omega
  closed := by
    have hmem : ∀ x, x ∈ dset ({q, p} : Finset ℕ) ↔ x = q ∨ x = p ∨ x = q + 1 ∨ x = p + 1 := by
      intro x
      rw [mem_dset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hμp : P.μ p = q ∨ P.μ p = q + 1 := by
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · left
        rw [← h1, μ_μ_of_inner hq]
      · right
        rw [← h2, μ_μ_of_inner hq1]
    have hμp1 : P.μ (p + 1) = q ∨ P.μ (p + 1) = q + 1 := by
      rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · right
        rw [← h2, μ_μ_of_inner hq1]
      · left
        rw [← h1, μ_μ_of_inner hq]
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hmem, hmem]
    rcases hx with rfl | rfl
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
    · rcases hμp with h1 | h1 <;> rcases hμp1 with h2 | h2 <;> rw [h1, h2] <;> omega

/-- The edge set of the base-case cycle. -/
def bigF (P : Pole) (a₀ c₀ : ℕ) : Finset ℕ :=
  (Finset.range P.n).filter fun p ↦
    (p = 2 ∧ a₀ = 1) ∨ (p = 1 ∧ a₀ = 3) ∨ (p = P.s₁ + 2 ∧ c₀ = P.s₁ + 1) ∨
      (p = P.s₁ + 1 ∧ c₀ = P.s₁ + 3) ∨ (6 ≤ p ∧ p ≤ P.s₁ - 3 ∧ p % 2 = 0)

theorem mem_bigF {a₀ c₀ p : ℕ} : p ∈ bigF P a₀ c₀ ↔ p < P.n ∧
    ((p = 2 ∧ a₀ = 1) ∨ (p = 1 ∧ a₀ = 3) ∨ (p = P.s₁ + 2 ∧ c₀ = P.s₁ + 1) ∨
      (p = P.s₁ + 1 ∧ c₀ = P.s₁ + 3) ∨ (6 ≤ p ∧ p ≤ P.s₁ - 3 ∧ p % 2 = 0)) := by
  unfold bigF
  rw [Finset.mem_filter, Finset.mem_range]

set_option maxHeartbeats 2000000 in
/-- The base-case cycle: both even segments have three inner positions, the first two inner
positions of the odd segment are matched to the outer positions of one even segment and the last
two to the outer positions of the other.  The alternating cycle runs through all inner positions
except the four ends of the chords at the two ends of the odd segment. -/
def altCycleBig (hs₂ : P.s₂ = 4) (hn : P.n = P.s₁ + 4) (hs₁ : 9 ≤ P.s₁)
    {a₀ c₀ : ℕ} (ha₀ : a₀ = 1 ∨ a₀ = 3) (hc₀ : c₀ = P.s₁ + 1 ∨ c₀ = P.s₁ + 3)
    (hE : (P.μ 5 = a₀ ∧ P.μ (P.s₁ - 1) = c₀) ∨ (P.μ 5 = c₀ ∧ P.μ (P.s₁ - 1) = a₀)) :
    P.AltCycle where
  F := bigF P a₀ c₀
  nonempty := ⟨6, by
    rw [mem_bigF]
    refine ⟨by omega, ?_⟩
    right; right; right; right
    omega⟩
  inner := by
    intro p hp
    rw [mem_bigF] at hp
    obtain ⟨hpn, hp⟩ := hp
    constructor
    · refine ⟨by omega, hpn, by omega, by omega⟩
    · refine ⟨by omega, by omega, by omega, by omega⟩
  matching := by
    intro p hp hp1
    rw [mem_bigF] at hp hp1
    rcases ha₀ with rfl | rfl <;> rcases hc₀ with rfl | rfl <;> omega
  closed := by
    have hodd : P.s₁ % 2 = 1 := by
      obtain ⟨m, hm⟩ := @n_odd P
      omega
    -- the deleted set `E` and its closure under the chord map
    have hEclosed : ∀ x, x = 5 ∨ x = P.s₁ - 1 ∨ x = a₀ ∨ x = c₀ →
        P.μ x = 5 ∨ P.μ x = P.s₁ - 1 ∨ P.μ x = a₀ ∨ P.μ x = c₀ := by
      have h5 : P.Inner 5 := ⟨by omega, by omega, by omega, by omega⟩
      have hs1 : P.Inner (P.s₁ - 1) := ⟨by omega, by omega, by omega, by omega⟩
      intro x hx
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hx with rfl | rfl | rfl | rfl
        · rw [h1]; omega
        · rw [h2]; omega
        · rw [← h1, μ_μ_of_inner h5]; omega
        · rw [← h2, μ_μ_of_inner hs1]; omega
      · rcases hx with rfl | rfl | rfl | rfl
        · rw [h1]; omega
        · rw [h2]; omega
        · rw [← h2, μ_μ_of_inner hs1]; omega
        · rw [← h1, μ_μ_of_inner h5]; omega
    -- membership in the vertex set of the cycle
    have hmem : ∀ x, x ∈ dset (bigF P a₀ c₀) ↔
        P.Inner x ∧ ¬ (x = 5 ∨ x = P.s₁ - 1 ∨ x = a₀ ∨ x = c₀) := by
      intro x
      rw [mem_dset, mem_bigF, mem_bigF]
      unfold Inner
      rw [hs₂]
      rcases ha₀ with rfl | rfl <;> rcases hc₀ with rfl | rfl <;> constructor <;> intro h <;> omega
    intro p hp
    rw [mem_bigF] at hp
    have hp1 : P.Inner p ∧ P.Inner (p + 1) := by
      constructor
      · refine ⟨by omega, by omega, by omega, by omega⟩
      · refine ⟨by omega, by omega, by omega, by omega⟩
    have hpE : ¬ (p = 5 ∨ p = P.s₁ - 1 ∨ p = a₀ ∨ p = c₀) := by
      rcases ha₀ with rfl | rfl <;> rcases hc₀ with rfl | rfl <;> omega
    have hp1E : ¬ (p + 1 = 5 ∨ p + 1 = P.s₁ - 1 ∨ p + 1 = a₀ ∨ p + 1 = c₀) := by
      rcases ha₀ with rfl | rfl <;> rcases hc₀ with rfl | rfl <;> omega
    constructor
    · rw [hmem]
      refine ⟨inner_μ hp1.1, fun h ↦ hpE ?_⟩
      have := hEclosed _ h
      rw [μ_μ_of_inner hp1.1] at this
      exact this
    · rw [hmem]
      refine ⟨inner_μ hp1.2, fun h ↦ hp1E ?_⟩
      have := hEclosed _ h
      rw [μ_μ_of_inner hp1.2] at this
      exact this

end Direct

section Segments

variable {q : ℕ} (hq : P.Reducible q)
include hq

theorem reduce_T₀_of_gt (h : P.s₂ < q) : (reduce hq).T₀ = P.T₀.image (rr q) := by
  unfold T₀
  rw [reduce_s₂, rr_of_lt h, image_rr_Ico_of_le h.le]

theorem reduce_T₀_of_lt (h : q + 2 ≤ P.s₂) : (reduce hq).T₀ = (P.T₀ \ {q, q + 1}).image (rr q) := by
  unfold T₀
  rw [reduce_s₂, rr_of_ge (by omega), image_rr_Ico_sdiff hq.q_pos h]

theorem reduce_T₂_of_lt (h : q + 1 < P.s₁) : (reduce hq).T₂ = P.T₂.image (rr q) := by
  unfold T₂
  rw [reduce_s₁, reduce_n, rr_of_ge (by omega), image_rr_Ico_of_ge (by omega)]
  congr 1
  omega

theorem reduce_T₂_of_gt (h : P.s₁ < q) : (reduce hq).T₂ = (P.T₂ \ {q, q + 1}).image (rr q) := by
  unfold T₂
  rw [reduce_s₁, reduce_n, rr_of_lt h, image_rr_Ico_sdiff (by omega) hq.succ_lt]

omit hq in
theorem T₀_ne (h : P.s₂ < q) {p : ℕ} (hp : p ∈ P.T₀) : p ≠ q ∧ p ≠ q + 1 := by
  rw [mem_T₀] at hp
  omega

omit hq in
theorem T₂_ne (h : q + 1 < P.s₁) {p : ℕ} (hp : p ∈ P.T₂) : p ≠ q ∧ p ≠ q + 1 := by
  rw [mem_T₂] at hp
  omega

end Segments

/-- Lifting through a reduction whose result stays in the family. -/
theorem altCycle_of_reduce {q : ℕ} (hq : P.Reducible q)
    (hgap : P.Spoke (q - 1) ∨ P.Spoke (q + 2) ∨ q + 2 = P.n) (hgood : Good (reduce hq))
    (ih : ∀ Q : Pole, Q.n < P.n → Good Q → Nonempty Q.AltCycle) : Nonempty P.AltCycle :=
  ⟨(ih _ (reduce_n_lt hq) hgood).some.unreduce hq hgap⟩

section EStep

variable (hgood : Good P)

include hgood in
/-- Reducing at the pair after the spoke `s₁` when a partner of the pair lies in `T₂`. -/
theorem good_reduce_after_s₁ (hq : P.Reducible (P.s₁ + 1))
    (hxy : P.μ (P.s₁ + 1) ∈ P.T₂ ∨ P.μ (P.s₁ + 1 + 1) ∈ P.T₂) : Good (reduce hq) := by
  obtain ⟨he₀, he₂, hx₀, hx₂⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := hq.succ_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_lt (by omega)]
    exact he₀
  · rw [reduce_n, reduce_s₁, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k - 1, by omega⟩
  · rw [reduce_T₀_of_gt hq (by omega)]
    refine le_trans hx₀ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₀ hp)
      (fun _ hp ↦ T₀_ne (by omega) hp) ?_)
    rintro ⟨h1, h2⟩
    rw [mem_T₀] at h1 h2
    rcases hxy with h | h <;> rw [mem_T₂] at h <;> omega
  · rw [reduce_T₂_of_gt hq (by omega)]
    exact le_trans hx₂ (ext_le_reduce_of_mem hq (fun _ hp ↦ inner_of_mem_T₂ hp)
      (mem_T₂.mpr ⟨le_rfl, by omega⟩) (mem_T₂.mpr ⟨by omega, by omega⟩) hxy)

include hgood in
/-- Reducing at the pair after the spoke `s₁` when the partners of the pair before `0` both lie
in `T₀` (and the partners of the pair after `s₁` lie outside `T₂`). -/
theorem good_reduce_after_s₁' (hq : P.Reducible (P.s₁ + 1)) (h6 : 6 ≤ P.n - P.s₁)
    (hxT : P.μ (P.s₁ + 1) ∉ P.T₂) (hyT : P.μ (P.s₁ + 1 + 1) ∉ P.T₂)
    (hx''T : P.μ (P.n - 2) ∈ P.T₀) (hy''T : P.μ (P.n - 2 + 1) ∈ P.T₀) : Good (reduce hq) := by
  obtain ⟨he₀, he₂, -, -⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi := hq.inner
  have hq1i := hq.inner_succ
  have hq''i : P.Inner (P.n - 2) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''1i : P.Inner (P.n - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hx''ne : P.μ (P.n - 2) ≠ P.μ (P.s₁ + 1) ∧ P.μ (P.n - 2) ≠ P.μ (P.s₁ + 1 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hq''i hqi h; omega,
      fun h ↦ by have := μ_injOn hq''i hq1i h; omega⟩
  have hy''ne : P.μ (P.n - 2 + 1) ≠ P.μ (P.s₁ + 1) ∧ P.μ (P.n - 2 + 1) ≠ P.μ (P.s₁ + 1 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hq''1i hqi h; omega,
      fun h ↦ by have := μ_injOn hq''1i hq1i h; omega⟩
  have hx''lt := mem_T₀.mp hx''T
  have hy''lt := mem_T₀.mp hy''T
  have hcard₀ : (P.T₀.image (rr (P.s₁ + 1))).card % 2 = 1 := by
    have := reduce_T₀_of_gt hq (P := P) (by omega)
    rw [← this, card_T₀, reduce_s₂, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₀
    omega
  have hcard₂ : ((P.T₂ \ {P.s₁ + 1, P.s₁ + 1 + 1}).image (rr (P.s₁ + 1))).card % 2 = 1 := by
    have := reduce_T₂_of_gt hq (P := P) (by omega)
    rw [← this, card_T₂, reduce_s₁, reduce_n, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₂
    omega
  have hT₀ne : ∀ p ∈ P.T₀, p ≠ P.s₁ + 1 ∧ p ≠ P.s₁ + 1 + 1 := fun _ hp ↦ T₀_ne (by omega) hp
  have hT₂ne : ∀ p ∈ P.T₂ \ {P.s₁ + 1, P.s₁ + 1 + 1}, p ≠ P.s₁ + 1 ∧ p ≠ P.s₁ + 1 + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_lt (by omega)]
    exact he₀
  · rw [reduce_n, reduce_s₁, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k - 1, by omega⟩
  · rw [reduce_T₀_of_gt hq (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₀ ?_
    · rw [← reduce_T₀_of_gt hq (by omega)] at hp
      exact inner_of_mem_T₀ hp
    refine two_le_ext (x := rr (P.s₁ + 1) (P.μ (P.n - 2)))
      (y := rr (P.s₁ + 1) (P.μ (P.n - 2 + 1)))
      ((mem_image_rr hT₀ne (hT₀ne _ hx''T)).mpr hx''T)
      ((mem_image_rr hT₀ne (hT₀ne _ hy''T)).mpr hy''T) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₀ne _ hx''T) (hT₀ne _ hy''T) h
      have := μ_injOn hq''i hq''1i this
      omega
    · rw [reduce_μ_rr hq (hT₀ne _ hx''T), μred_of_ne hx''ne.1 hx''ne.2, μ_μ_of_inner hq''i,
        mem_image_rr hT₀ne (by omega), mem_T₀]
      omega
    · rw [reduce_μ_rr hq (hT₀ne _ hy''T), μred_of_ne hy''ne.1 hy''ne.2, μ_μ_of_inner hq''1i,
        mem_image_rr hT₀ne (by omega), mem_T₀]
      omega
  · rw [reduce_T₂_of_gt hq (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₂ ?_
    · rw [← reduce_T₂_of_gt hq (by omega)] at hp
      exact inner_of_mem_T₂ hp
    have hmem'' : P.n - 2 ∈ P.T₂ \ {P.s₁ + 1, P.s₁ + 1 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₂]
      omega
    have hmem''1 : P.n - 2 + 1 ∈ P.T₂ \ {P.s₁ + 1, P.s₁ + 1 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₂]
      omega
    have hq''ne : P.n - 2 ≠ P.μ (P.s₁ + 1) ∧ P.n - 2 ≠ P.μ (P.s₁ + 1 + 1) :=
      ⟨fun h ↦ hxT (by rw [← h, mem_T₂]; omega), fun h ↦ hyT (by rw [← h, mem_T₂]; omega)⟩
    have hq''1ne : P.n - 2 + 1 ≠ P.μ (P.s₁ + 1) ∧ P.n - 2 + 1 ≠ P.μ (P.s₁ + 1 + 1) :=
      ⟨fun h ↦ hxT (by rw [← h, mem_T₂]; omega), fun h ↦ hyT (by rw [← h, mem_T₂]; omega)⟩
    refine two_le_ext (x := rr (P.s₁ + 1) (P.n - 2)) (y := rr (P.s₁ + 1) (P.n - 2 + 1))
      ((mem_image_rr hT₂ne (hT₂ne _ hmem'')).mpr hmem'')
      ((mem_image_rr hT₂ne (hT₂ne _ hmem''1)).mpr hmem''1) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₂ne _ hmem'') (hT₂ne _ hmem''1) h
      omega
    · rw [reduce_μ_rr hq (hT₂ne _ hmem''), μred_of_ne hq''ne.1 hq''ne.2,
        mem_image_rr hT₂ne (by omega)]
      intro h
      rw [Finset.mem_sdiff, mem_T₂] at h
      omega
    · rw [reduce_μ_rr hq (hT₂ne _ hmem''1), μred_of_ne hq''1ne.1 hq''1ne.2,
        mem_image_rr hT₂ne (by omega)]
      intro h
      rw [Finset.mem_sdiff, mem_T₂] at h
      omega

include hgood in
/-- Reducing at the pair before the spoke `0` when the partners of the pair after `s₁` lie
outside `T₂` and the partners of the pair before `0` do not both lie in `T₀`. -/
theorem good_reduce_before_zero (hq'' : P.Reducible (P.n - 2)) (h6 : 6 ≤ P.n - P.s₁)
    (hxT : P.μ (P.s₁ + 1) ∉ P.T₂) (hyT : P.μ (P.s₁ + 1 + 1) ∉ P.T₂)
    (hboth : ¬ (P.μ (P.n - 2) ∈ P.T₀ ∧ P.μ (P.n - 2 + 1) ∈ P.T₀)) : Good (reduce hq'') := by
  obtain ⟨he₀, he₂, hx₀, -⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi : P.Inner (P.s₁ + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hq1i : P.Inner (P.s₁ + 1 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''i := hq''.inner
  have hq''1i := hq''.inner_succ
  have hx''ne : P.μ (P.s₁ + 1) ≠ P.μ (P.n - 2) ∧ P.μ (P.s₁ + 1) ≠ P.μ (P.n - 2 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hqi hq''i h; omega,
      fun h ↦ by have := μ_injOn hqi hq''1i h; omega⟩
  have hy''ne : P.μ (P.s₁ + 1 + 1) ≠ P.μ (P.n - 2) ∧ P.μ (P.s₁ + 1 + 1) ≠ P.μ (P.n - 2 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hq1i hq''i h; omega,
      fun h ↦ by have := μ_injOn hq1i hq''1i h; omega⟩
  have hxne'' : P.μ (P.s₁ + 1) ≠ P.n - 2 ∧ P.μ (P.s₁ + 1) ≠ P.n - 2 + 1 :=
    ⟨fun h ↦ hxT (by rw [h, mem_T₂]; omega), fun h ↦ hxT (by rw [h, mem_T₂]; omega)⟩
  have hyne'' : P.μ (P.s₁ + 1 + 1) ≠ P.n - 2 ∧ P.μ (P.s₁ + 1 + 1) ≠ P.n - 2 + 1 :=
    ⟨fun h ↦ hyT (by rw [h, mem_T₂]; omega), fun h ↦ hyT (by rw [h, mem_T₂]; omega)⟩
  have hcard₂ : ((P.T₂ \ {P.n - 2, P.n - 2 + 1}).image (rr (P.n - 2))).card % 2 = 1 := by
    have := reduce_T₂_of_gt hq'' (P := P) (by omega)
    rw [← this, card_T₂, reduce_s₁, reduce_n, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₂
    omega
  have hT₂ne : ∀ p ∈ P.T₂ \ {P.n - 2, P.n - 2 + 1}, p ≠ P.n - 2 ∧ p ≠ P.n - 2 + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_lt (by omega)]
    exact he₀
  · rw [reduce_n, reduce_s₁, rr_of_lt (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k - 1, by omega⟩
  · rw [reduce_T₀_of_gt hq'' (by omega)]
    exact le_trans hx₀ (ext_le_reduce_of_notMem hq'' (fun _ hp ↦ inner_of_mem_T₀ hp)
      (fun _ hp ↦ T₀_ne (by omega) hp) hboth)
  · rw [reduce_T₂_of_gt hq'' (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₂ ?_
    · rw [← reduce_T₂_of_gt hq'' (by omega)] at hp
      exact inner_of_mem_T₂ hp
    have hmemq : P.s₁ + 1 ∈ P.T₂ \ {P.n - 2, P.n - 2 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₂]
      omega
    have hmemq1 : P.s₁ + 1 + 1 ∈ P.T₂ \ {P.n - 2, P.n - 2 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₂]
      omega
    have hqne : P.s₁ + 1 ≠ P.μ (P.n - 2) ∧ P.s₁ + 1 ≠ P.μ (P.n - 2 + 1) :=
      ⟨fun h ↦ hxne''.1 (by rw [h, μ_μ_of_inner hq''i]),
        fun h ↦ hxne''.2 (by rw [h, μ_μ_of_inner hq''1i])⟩
    have hq1ne : P.s₁ + 1 + 1 ≠ P.μ (P.n - 2) ∧ P.s₁ + 1 + 1 ≠ P.μ (P.n - 2 + 1) :=
      ⟨fun h ↦ hyne''.1 (by rw [h, μ_μ_of_inner hq''i]),
        fun h ↦ hyne''.2 (by rw [h, μ_μ_of_inner hq''1i])⟩
    refine two_le_ext (x := rr (P.n - 2) (P.s₁ + 1)) (y := rr (P.n - 2) (P.s₁ + 1 + 1))
      ((mem_image_rr hT₂ne (hT₂ne _ hmemq)).mpr hmemq)
      ((mem_image_rr hT₂ne (hT₂ne _ hmemq1)).mpr hmemq1) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₂ne _ hmemq) (hT₂ne _ hmemq1) h
      omega
    · rw [reduce_μ_rr hq'' (hT₂ne _ hmemq), μred_of_ne hqne.1 hqne.2, mem_image_rr hT₂ne hxne'']
      intro h
      exact hxT (Finset.mem_sdiff.mp h).1
    · rw [reduce_μ_rr hq'' (hT₂ne _ hmemq1), μred_of_ne hq1ne.1 hq1ne.2,
        mem_image_rr hT₂ne hyne'']
      intro h
      exact hyT (Finset.mem_sdiff.mp h).1

include hgood in
/-- The induction step at the segment `T₂` (Lemma 3.6, induction step): remove the first two
inner positions after the spoke `s₁`, or the last two before the spoke `0`. -/
theorem estep_T₂ (h6 : 6 ≤ P.n - P.s₁)
    (ih : ∀ Q : Pole, Q.n < P.n → Good Q → Nonempty Q.AltCycle) : Nonempty P.AltCycle := by
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi : P.Inner (P.s₁ + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hq1i : P.Inner (P.s₁ + 1 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  by_cases hpar : P.μ (P.s₁ + 1) = P.s₁ + 1 + 1
  · exact ⟨altCycleOfParallel hqi hq1i hpar⟩
  have hq : P.Reducible (P.s₁ + 1) := ⟨hqi, hq1i, hpar⟩
  have hgap : P.Spoke (P.s₁ + 1 - 1) ∨ P.Spoke (P.s₁ + 1 + 2) ∨ P.s₁ + 1 + 2 = P.n :=
    Or.inl (by rw [Nat.add_sub_cancel]; exact spoke_s₁)
  by_cases hxy : P.μ (P.s₁ + 1) ∈ P.T₂ ∨ P.μ (P.s₁ + 1 + 1) ∈ P.T₂
  · exact altCycle_of_reduce hq hgap (good_reduce_after_s₁ hgood hq hxy) ih
  rw [not_or] at hxy
  obtain ⟨hxT, hyT⟩ := hxy
  have hq''i : P.Inner (P.n - 2) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''1i : P.Inner (P.n - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  by_cases hpar'' : P.μ (P.n - 2) = P.n - 2 + 1
  · exact ⟨altCycleOfParallel hq''i hq''1i hpar''⟩
  have hq'' : P.Reducible (P.n - 2) := ⟨hq''i, hq''1i, hpar''⟩
  have hgap'' : P.Spoke (P.n - 2 - 1) ∨ P.Spoke (P.n - 2 + 2) ∨ P.n - 2 + 2 = P.n :=
    Or.inr (Or.inr (by omega))
  by_cases hboth : P.μ (P.n - 2) ∈ P.T₀ ∧ P.μ (P.n - 2 + 1) ∈ P.T₀
  · exact altCycle_of_reduce hq hgap (good_reduce_after_s₁' hgood hq h6 hxT hyT hboth.1 hboth.2) ih
  · exact altCycle_of_reduce hq'' hgap'' (good_reduce_before_zero hgood hq'' h6 hxT hyT hboth) ih

include hgood in
/-- Reducing at the pair after the spoke `0` when a partner of the pair lies in `T₀`. -/
theorem good_reduce_after_zero (hq : P.Reducible 1) (h6 : 6 ≤ P.s₂)
    (hxy : P.μ 1 ∈ P.T₀ ∨ P.μ (1 + 1) ∈ P.T₀) : Good (reduce hq) := by
  obtain ⟨he₀, he₂, hx₀, hx₂⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₀
    exact ⟨k - 1, by omega⟩
  · rw [reduce_n, reduce_s₁, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k, by omega⟩
  · rw [reduce_T₀_of_lt hq (by omega)]
    exact le_trans hx₀ (ext_le_reduce_of_mem hq (fun _ hp ↦ inner_of_mem_T₀ hp)
      (mem_T₀.mpr ⟨le_rfl, by omega⟩) (mem_T₀.mpr ⟨by omega, by omega⟩) hxy)
  · rw [reduce_T₂_of_lt hq (by omega)]
    refine le_trans hx₂ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₂ hp)
      (fun _ hp ↦ T₂_ne (by omega) hp) ?_)
    rintro ⟨h1, h2⟩
    rw [mem_T₂] at h1 h2
    rcases hxy with h | h <;> rw [mem_T₀] at h <;> omega

include hgood in
/-- Reducing at the pair after the spoke `0` when the partners of the pair before `s₂` both lie
in `T₂` (and the partners of the pair after `0` lie outside `T₀`). -/
theorem good_reduce_after_zero' (hq : P.Reducible 1) (h6 : 6 ≤ P.s₂)
    (hxT : P.μ 1 ∉ P.T₀) (hyT : P.μ (1 + 1) ∉ P.T₀)
    (hx''T : P.μ (P.s₂ - 2) ∈ P.T₂) (hy''T : P.μ (P.s₂ - 2 + 1) ∈ P.T₂) : Good (reduce hq) := by
  obtain ⟨he₀, he₂, -, -⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi := hq.inner
  have hq1i := hq.inner_succ
  have hq''i : P.Inner (P.s₂ - 2) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''1i : P.Inner (P.s₂ - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hx''ne : P.μ (P.s₂ - 2) ≠ P.μ 1 ∧ P.μ (P.s₂ - 2) ≠ P.μ (1 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hq''i hqi h; omega,
      fun h ↦ by have := μ_injOn hq''i hq1i h; omega⟩
  have hy''ne : P.μ (P.s₂ - 2 + 1) ≠ P.μ 1 ∧ P.μ (P.s₂ - 2 + 1) ≠ P.μ (1 + 1) :=
    ⟨fun h ↦ by have := μ_injOn hq''1i hqi h; omega,
      fun h ↦ by have := μ_injOn hq''1i hq1i h; omega⟩
  have hx''lt := mem_T₂.mp hx''T
  have hy''lt := mem_T₂.mp hy''T
  have hcard₀ : ((P.T₀ \ {1, 1 + 1}).image (rr 1)).card % 2 = 1 := by
    have := reduce_T₀_of_lt hq (P := P) (by omega)
    rw [← this, card_T₀, reduce_s₂, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₀
    omega
  have hcard₂ : (P.T₂.image (rr 1)).card % 2 = 1 := by
    have := reduce_T₂_of_lt hq (P := P) (by omega)
    rw [← this, card_T₂, reduce_s₁, reduce_n, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    omega
  have hT₂ne : ∀ p ∈ P.T₂, p ≠ 1 ∧ p ≠ 1 + 1 := fun _ hp ↦ T₂_ne (by omega) hp
  have hT₀ne : ∀ p ∈ P.T₀ \ {1, 1 + 1}, p ≠ 1 ∧ p ≠ 1 + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₀
    exact ⟨k - 1, by omega⟩
  · rw [reduce_n, reduce_s₁, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k, by omega⟩
  · rw [reduce_T₀_of_lt hq (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₀ ?_
    · rw [← reduce_T₀_of_lt hq (by omega)] at hp
      exact inner_of_mem_T₀ hp
    have hmem'' : P.s₂ - 2 ∈ P.T₀ \ {1, 1 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₀]
      omega
    have hmem''1 : P.s₂ - 2 + 1 ∈ P.T₀ \ {1, 1 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₀]
      omega
    have hq''ne : P.s₂ - 2 ≠ P.μ 1 ∧ P.s₂ - 2 ≠ P.μ (1 + 1) :=
      ⟨fun h ↦ hxT (by rw [← h, mem_T₀]; omega), fun h ↦ hyT (by rw [← h, mem_T₀]; omega)⟩
    have hq''1ne : P.s₂ - 2 + 1 ≠ P.μ 1 ∧ P.s₂ - 2 + 1 ≠ P.μ (1 + 1) :=
      ⟨fun h ↦ hxT (by rw [← h, mem_T₀]; omega), fun h ↦ hyT (by rw [← h, mem_T₀]; omega)⟩
    refine two_le_ext (x := rr 1 (P.s₂ - 2)) (y := rr 1 (P.s₂ - 2 + 1))
      ((mem_image_rr hT₀ne (hT₀ne _ hmem'')).mpr hmem'')
      ((mem_image_rr hT₀ne (hT₀ne _ hmem''1)).mpr hmem''1) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₀ne _ hmem'') (hT₀ne _ hmem''1) h
      omega
    · rw [reduce_μ_rr hq (hT₀ne _ hmem''), μred_of_ne hq''ne.1 hq''ne.2,
        mem_image_rr hT₀ne (by omega)]
      intro h
      rw [Finset.mem_sdiff, mem_T₀] at h
      omega
    · rw [reduce_μ_rr hq (hT₀ne _ hmem''1), μred_of_ne hq''1ne.1 hq''1ne.2,
        mem_image_rr hT₀ne (by omega)]
      intro h
      rw [Finset.mem_sdiff, mem_T₀] at h
      omega
  · rw [reduce_T₂_of_lt hq (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₂ ?_
    · rw [← reduce_T₂_of_lt hq (by omega)] at hp
      exact inner_of_mem_T₂ hp
    refine two_le_ext (x := rr 1 (P.μ (P.s₂ - 2))) (y := rr 1 (P.μ (P.s₂ - 2 + 1)))
      ((mem_image_rr hT₂ne (hT₂ne _ hx''T)).mpr hx''T)
      ((mem_image_rr hT₂ne (hT₂ne _ hy''T)).mpr hy''T) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₂ne _ hx''T) (hT₂ne _ hy''T) h
      have := μ_injOn hq''i hq''1i this
      omega
    · rw [reduce_μ_rr hq (hT₂ne _ hx''T), μred_of_ne hx''ne.1 hx''ne.2, μ_μ_of_inner hq''i,
        mem_image_rr hT₂ne (by omega), mem_T₂]
      omega
    · rw [reduce_μ_rr hq (hT₂ne _ hy''T), μred_of_ne hy''ne.1 hy''ne.2, μ_μ_of_inner hq''1i,
        mem_image_rr hT₂ne (by omega), mem_T₂]
      omega

include hgood in
/-- Reducing at the pair before the spoke `s₂` when the partners of the pair after `0` lie
outside `T₀` and the partners of the pair before `s₂` do not both lie in `T₂`. -/
theorem good_reduce_before_s₂ (hq'' : P.Reducible (P.s₂ - 2)) (h6 : 6 ≤ P.s₂)
    (hxT : P.μ 1 ∉ P.T₀) (hyT : P.μ (1 + 1) ∉ P.T₀)
    (hboth : ¬ (P.μ (P.s₂ - 2) ∈ P.T₂ ∧ P.μ (P.s₂ - 2 + 1) ∈ P.T₂)) : Good (reduce hq'') := by
  obtain ⟨he₀, he₂, -, hx₂⟩ := hgood
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi : P.Inner 1 := ⟨by omega, by omega, by omega, by omega⟩
  have hq1i : P.Inner (1 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''i := hq''.inner
  have hq''1i := hq''.inner_succ
  have hxne'' : P.μ 1 ≠ P.s₂ - 2 ∧ P.μ 1 ≠ P.s₂ - 2 + 1 :=
    ⟨fun h ↦ hxT (by rw [h, mem_T₀]; omega), fun h ↦ hxT (by rw [h, mem_T₀]; omega)⟩
  have hyne'' : P.μ (1 + 1) ≠ P.s₂ - 2 ∧ P.μ (1 + 1) ≠ P.s₂ - 2 + 1 :=
    ⟨fun h ↦ hyT (by rw [h, mem_T₀]; omega), fun h ↦ hyT (by rw [h, mem_T₀]; omega)⟩
  have hcard₀ : ((P.T₀ \ {P.s₂ - 2, P.s₂ - 2 + 1}).image (rr (P.s₂ - 2))).card % 2 = 1 := by
    have := reduce_T₀_of_lt hq'' (P := P) (by omega)
    rw [← this, card_T₀, reduce_s₂, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₀
    omega
  have hT₀ne : ∀ p ∈ P.T₀ \ {P.s₂ - 2, P.s₂ - 2 + 1}, p ≠ P.s₂ - 2 ∧ p ≠ P.s₂ - 2 + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₀
    exact ⟨k - 1, by omega⟩
  · rw [reduce_n, reduce_s₁, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k, by omega⟩
  · rw [reduce_T₀_of_lt hq'' (by omega)]
    refine three_le_ext_of_two_le (fun p hp ↦ ?_) hcard₀ ?_
    · rw [← reduce_T₀_of_lt hq'' (by omega)] at hp
      exact inner_of_mem_T₀ hp
    have hmemq : 1 ∈ P.T₀ \ {P.s₂ - 2, P.s₂ - 2 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₀]
      omega
    have hmemq1 : 1 + 1 ∈ P.T₀ \ {P.s₂ - 2, P.s₂ - 2 + 1} := by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, mem_T₀]
      omega
    have hqne : 1 ≠ P.μ (P.s₂ - 2) ∧ 1 ≠ P.μ (P.s₂ - 2 + 1) :=
      ⟨fun h ↦ hxne''.1 (by have := μ_μ_of_inner hq''i; rw [← h] at this; exact this),
        fun h ↦ hxne''.2 (by have := μ_μ_of_inner hq''1i; rw [← h] at this; exact this)⟩
    have hq1ne : 1 + 1 ≠ P.μ (P.s₂ - 2) ∧ 1 + 1 ≠ P.μ (P.s₂ - 2 + 1) :=
      ⟨fun h ↦ hyne''.1 (by have := μ_μ_of_inner hq''i; rw [← h] at this; exact this),
        fun h ↦ hyne''.2 (by have := μ_μ_of_inner hq''1i; rw [← h] at this; exact this)⟩
    refine two_le_ext (x := rr (P.s₂ - 2) 1) (y := rr (P.s₂ - 2) (1 + 1))
      ((mem_image_rr hT₀ne (hT₀ne _ hmemq)).mpr hmemq)
      ((mem_image_rr hT₀ne (hT₀ne _ hmemq1)).mpr hmemq1) (fun h ↦ ?_) ?_ ?_
    · have := rr_injOn (hT₀ne _ hmemq) (hT₀ne _ hmemq1) h
      omega
    · rw [reduce_μ_rr hq'' (hT₀ne _ hmemq), μred_of_ne hqne.1 hqne.2, mem_image_rr hT₀ne hxne'']
      intro h
      exact hxT (Finset.mem_sdiff.mp h).1
    · rw [reduce_μ_rr hq'' (hT₀ne _ hmemq1), μred_of_ne hq1ne.1 hq1ne.2,
        mem_image_rr hT₀ne hyne'']
      intro h
      exact hyT (Finset.mem_sdiff.mp h).1
  · rw [reduce_T₂_of_lt hq'' (by omega)]
    exact le_trans hx₂ (ext_le_reduce_of_notMem hq'' (fun _ hp ↦ inner_of_mem_T₂ hp)
      (fun _ hp ↦ T₂_ne (by omega) hp) hboth)

include hgood in
/-- The induction step at the segment `T₀`: remove the first two inner positions after the
spoke `0`, or the last two before the spoke `s₂`. -/
theorem estep_T₀ (h6 : 6 ≤ P.s₂)
    (ih : ∀ Q : Pole, Q.n < P.n → Good Q → Nonempty Q.AltCycle) : Nonempty P.AltCycle := by
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hqi : P.Inner 1 := ⟨by omega, by omega, by omega, by omega⟩
  have hq1i : P.Inner (1 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  by_cases hpar : P.μ 1 = 1 + 1
  · exact ⟨altCycleOfParallel hqi hq1i hpar⟩
  have hq : P.Reducible 1 := ⟨hqi, hq1i, hpar⟩
  have hgap : P.Spoke (1 - 1) ∨ P.Spoke (1 + 2) ∨ 1 + 2 = P.n := Or.inl spoke_zero
  by_cases hxy : P.μ 1 ∈ P.T₀ ∨ P.μ (1 + 1) ∈ P.T₀
  · exact altCycle_of_reduce hq hgap (good_reduce_after_zero hgood hq h6 hxy) ih
  rw [not_or] at hxy
  obtain ⟨hxT, hyT⟩ := hxy
  have hq''i : P.Inner (P.s₂ - 2) := ⟨by omega, by omega, by omega, by omega⟩
  have hq''1i : P.Inner (P.s₂ - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  by_cases hpar'' : P.μ (P.s₂ - 2) = P.s₂ - 2 + 1
  · exact ⟨altCycleOfParallel hq''i hq''1i hpar''⟩
  have hq'' : P.Reducible (P.s₂ - 2) := ⟨hq''i, hq''1i, hpar''⟩
  have hgap'' : P.Spoke (P.s₂ - 2 - 1) ∨ P.Spoke (P.s₂ - 2 + 2) ∨ P.s₂ - 2 + 2 = P.n :=
    Or.inr (Or.inl (by rw [show P.s₂ - 2 + 2 = P.s₂ by omega]; exact spoke_s₂))
  by_cases hboth : P.μ (P.s₂ - 2) ∈ P.T₂ ∧ P.μ (P.s₂ - 2 + 1) ∈ P.T₂
  · exact altCycle_of_reduce hq hgap (good_reduce_after_zero' hgood hq h6 hxT hyT hboth.1 hboth.2)
      ih
  · exact altCycle_of_reduce hq'' hgap'' (good_reduce_before_s₂ hgood hq'' h6 hxT hyT hboth) ih

end EStep

section Base

variable (hs₂ : P.s₂ = 4) (hn : P.n = P.s₁ + 4)
include hs₂ hn

omit hs₂ in
theorem base_s₁_odd : P.s₁ % 2 = 1 := by
  obtain ⟨m, hm⟩ := @n_odd P
  omega

/-- The base case with an empty odd segment: the chords pair the two even segments. -/
theorem base_empty (hs₁ : P.s₁ = 5) (hT₀ : ∀ p ∈ P.T₀, P.μ p ∉ P.T₀) : Nonempty P.AltCycle := by
  have h1i : P.Inner 1 := ⟨by omega, by omega, by omega, by omega⟩
  have h2i : P.Inner 2 := ⟨by omega, by omega, by omega, by omega⟩
  have h3i : P.Inner 3 := ⟨by omega, by omega, by omega, by omega⟩
  have h6i : P.Inner 6 := ⟨by omega, by omega, by omega, by omega⟩
  have h7i : P.Inner 7 := ⟨by omega, by omega, by omega, by omega⟩
  have h8i : P.Inner 8 := ⟨by omega, by omega, by omega, by omega⟩
  have hμ : ∀ p, p ∈ P.T₀ → 6 ≤ P.μ p ∧ P.μ p ≤ 8 := by
    intro p hp
    have hi := inner_μ (inner_of_mem_T₀ hp)
    have := hT₀ p hp
    rw [mem_T₀] at this
    obtain ⟨a, b, c, d⟩ := hi
    omega
  have hμ1 := hμ 1 (mem_T₀.mpr ⟨le_rfl, by omega⟩)
  have hμ2 := hμ 2 (mem_T₀.mpr ⟨by omega, by omega⟩)
  have hμ3 := hμ 3 (mem_T₀.mpr ⟨by omega, by omega⟩)
  have hne12 : P.μ 1 ≠ P.μ 2 := fun h ↦ by have := μ_injOn h1i h2i h; omega
  have hne13 : P.μ 1 ≠ P.μ 3 := fun h ↦ by have := μ_injOn h1i h3i h; omega
  have hne23 : P.μ 2 ≠ P.μ 3 := fun h ↦ by have := μ_injOn h2i h3i h; omega
  rcases (show P.μ 2 = 6 ∨ P.μ 2 = 7 ∨ P.μ 2 = 8 by omega) with h | h | h
  · rcases (show P.μ 1 = 7 ∨ P.μ 1 = 8 by omega) with h' | h'
    · exact ⟨altCycleOfPairs h1i h2i h6i h7i (Or.inl (by norm_num)) (Or.inr ⟨h', h⟩)⟩
    · have h3 : P.μ 3 = 7 := by omega
      exact ⟨altCycleOfPairs h2i h3i h6i h7i (Or.inl (by norm_num)) (Or.inl ⟨h, h3⟩)⟩
  · rcases (show P.μ 1 = 6 ∨ P.μ 1 = 8 by omega) with h' | h'
    · exact ⟨altCycleOfPairs h1i h2i h6i h7i (Or.inl (by norm_num)) (Or.inl ⟨h', h⟩)⟩
    · exact ⟨altCycleOfPairs h1i h2i h7i h8i (Or.inl (by norm_num)) (Or.inr ⟨h', h⟩)⟩
  · rcases (show P.μ 1 = 6 ∨ P.μ 1 = 7 by omega) with h' | h'
    · have h3 : P.μ 3 = 7 := by omega
      exact ⟨altCycleOfPairs h2i h3i h7i h8i (Or.inl (by norm_num)) (Or.inr ⟨h, h3⟩)⟩
    · exact ⟨altCycleOfPairs h1i h2i h7i h8i (Or.inl (by norm_num)) (Or.inl ⟨h', h⟩)⟩

/-- When the pair `5, 6` is matched to `1, 3`, the positions `1` and `3` are matched into
`{5, 6}`, so no other position is matched to `1`, `3`, `5` or `6`. -/
theorem partners_of_L13 (hs₁ : 7 ≤ P.s₁) (h5 : P.μ 5 = 1 ∨ P.μ 5 = 3)
    (h6 : P.μ 6 = 1 ∨ P.μ 6 = 3) {p : ℕ} (hp : P.Inner p) (hp1 : p ≠ 1) (hp3 : p ≠ 3)
    (hp5 : p ≠ 5) (hp6 : p ≠ 6) : P.μ p ≠ 1 ∧ P.μ p ≠ 3 ∧ P.μ p ≠ 5 ∧ P.μ p ≠ 6 := by
  have h5i : P.Inner 5 := ⟨by omega, by omega, by omega, by omega⟩
  have h6i : P.Inner 6 := ⟨by omega, by omega, by omega, by omega⟩
  have hne : P.μ 5 ≠ P.μ 6 := fun h ↦ by have := μ_injOn h5i h6i h; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have : p = P.μ 1 := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5
    · rw [← h5, μ_μ_of_inner h5i] at this; omega
    · rcases h6 with h6 | h6
      · rw [← h6, μ_μ_of_inner h6i] at this; omega
      · omega
  · intro h
    have : p = P.μ 3 := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5
    · rcases h6 with h6 | h6
      · omega
      · rw [← h6, μ_μ_of_inner h6i] at this; omega
    · rw [← h5, μ_μ_of_inner h5i] at this; omega
  · intro h
    have : p = P.μ 5 := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5 <;> omega
  · intro h
    have : p = P.μ 6 := by rw [← h, μ_μ_of_inner hp]
    rcases h6 with h6 | h6 <;> omega

/-- The mirror statement for the pair `5, 6` matched to `s₁ + 1, s₁ + 3`. -/
theorem partners_of_L13' (hs₁ : 7 ≤ P.s₁) (h5 : P.μ 5 = P.s₁ + 1 ∨ P.μ 5 = P.s₁ + 3)
    (h6 : P.μ 6 = P.s₁ + 1 ∨ P.μ 6 = P.s₁ + 3) {p : ℕ} (hp : P.Inner p) (hp1 : p ≠ P.s₁ + 1)
    (hp3 : p ≠ P.s₁ + 3) (hp5 : p ≠ 5) (hp6 : p ≠ 6) :
    P.μ p ≠ P.s₁ + 1 ∧ P.μ p ≠ P.s₁ + 3 ∧ P.μ p ≠ 5 ∧ P.μ p ≠ 6 := by
  have h5i : P.Inner 5 := ⟨by omega, by omega, by omega, by omega⟩
  have h6i : P.Inner 6 := ⟨by omega, by omega, by omega, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have : p = P.μ (P.s₁ + 1) := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5
    · rw [← h5, μ_μ_of_inner h5i] at this; omega
    · rcases h6 with h6 | h6
      · rw [← h6, μ_μ_of_inner h6i] at this; omega
      · have := μ_injOn h5i h6i (h5.trans h6.symm); omega
  · intro h
    have : p = P.μ (P.s₁ + 3) := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5
    · rcases h6 with h6 | h6
      · have := μ_injOn h5i h6i (h5.trans h6.symm); omega
      · rw [← h6, μ_μ_of_inner h6i] at this; omega
    · rw [← h5, μ_μ_of_inner h5i] at this; omega
  · intro h
    have : p = P.μ 5 := by rw [← h, μ_μ_of_inner hp]
    rcases h5 with h5 | h5 <;> omega
  · intro h
    have : p = P.μ 6 := by rw [← h, μ_μ_of_inner hp]
    rcases h6 with h6 | h6 <;> omega

end Base

section BaseMain

variable (hs₂ : P.s₂ = 4) (hn : P.n = P.s₁ + 4) (hgood : Good P)
include hs₂ hn hgood

/-- Reducing at the pair `5, 6` in the base case when its partners do not both lie in one even
segment. -/
theorem good_reduce_L (hs₁ : 7 ≤ P.s₁) (hq : P.Reducible 5)
    (h₀ : ¬ (P.μ 5 ∈ P.T₀ ∧ P.μ (5 + 1) ∈ P.T₀)) (h₂ : ¬ (P.μ 5 ∈ P.T₂ ∧ P.μ (5 + 1) ∈ P.T₂)) :
    Good (reduce hq) := by
  obtain ⟨he₀, he₂, hx₀, hx₂⟩ := hgood
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_lt (by omega)]
    exact he₀
  · rw [reduce_n, reduce_s₁, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k, by omega⟩
  · rw [reduce_T₀_of_gt hq (by omega)]
    exact le_trans hx₀ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₀ hp)
      (fun _ hp ↦ T₀_ne (by omega) hp) h₀)
  · rw [reduce_T₂_of_lt hq (by omega)]
    exact le_trans hx₂ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₂ hp)
      (fun _ hp ↦ T₂_ne (by omega) hp) h₂)

/-- Reducing at the pair `s₁ - 2, s₁ - 1` in the base case when its partners do not both lie in
one even segment. -/
theorem good_reduce_R (hs₁ : 9 ≤ P.s₁) (hq : P.Reducible (P.s₁ - 2))
    (h₀ : ¬ (P.μ (P.s₁ - 2) ∈ P.T₀ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₀))
    (h₂ : ¬ (P.μ (P.s₁ - 2) ∈ P.T₂ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₂)) : Good (reduce hq) := by
  obtain ⟨he₀, he₂, hx₀, hx₂⟩ := hgood
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [reduce_s₂, rr_of_lt (by omega)]
    exact he₀
  · rw [reduce_n, reduce_s₁, rr_of_ge (by omega)]
    obtain ⟨k, hk⟩ := he₂
    exact ⟨k, by omega⟩
  · rw [reduce_T₀_of_gt hq (by omega)]
    exact le_trans hx₀ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₀ hp)
      (fun _ hp ↦ T₀_ne (by omega) hp) h₀)
  · rw [reduce_T₂_of_lt hq (by omega)]
    exact le_trans hx₂ (ext_le_reduce_of_notMem hq (fun _ hp ↦ inner_of_mem_T₂ hp)
      (fun _ hp ↦ T₂_ne (by omega) hp) h₂)

/-- The base case: both even segments have three inner positions and the odd segment is not
empty. -/
theorem base (hs₁7 : 7 ≤ P.s₁) (ih : ∀ Q : Pole, Q.n < P.n → Good Q → Nonempty Q.AltCycle) :
    Nonempty P.AltCycle := by
  have hodd := base_s₁_odd hn (P := P)
  have hT₀ : ∀ p ∈ P.T₀, P.μ p ∉ P.T₀ :=
    all_exterior_of_card_le (by rw [card_T₀, hs₂]; exact hgood.2.2.1)
  have hT₂ : ∀ p ∈ P.T₂, P.μ p ∉ P.T₂ :=
    all_exterior_of_card_le (by rw [card_T₂, hn]; have := hgood.2.2.2; omega)
  have h1i : P.Inner 1 := ⟨by omega, by omega, by omega, by omega⟩
  have h2i : P.Inner 2 := ⟨by omega, by omega, by omega, by omega⟩
  have h3i : P.Inner 3 := ⟨by omega, by omega, by omega, by omega⟩
  have h5i : P.Inner 5 := ⟨by omega, by omega, by omega, by omega⟩
  have h6i : P.Inner (5 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hs1i : P.Inner (P.s₁ + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hs2i : P.Inner (P.s₁ + 1 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hs3i : P.Inner (P.s₁ + 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
  have hs2i' : P.Inner (P.s₁ + 2) := ⟨by omega, by omega, by omega, by omega⟩
  -- the pair `5, 6`
  by_cases hparL : P.μ 5 = 5 + 1
  · exact ⟨altCycleOfParallel h5i h6i hparL⟩
  have hqL : P.Reducible 5 := ⟨h5i, h6i, hparL⟩
  have hgapL : P.Spoke (5 - 1) ∨ P.Spoke (5 + 2) ∨ 5 + 2 = P.n :=
    Or.inl (by rw [show 5 - 1 = P.s₂ by omega]; exact spoke_s₂)
  have hxi := inner_μ h5i
  have hyi := inner_μ h6i
  have hxy : P.μ 5 ≠ P.μ (5 + 1) := fun h ↦ by have := μ_injOn h5i h6i h; omega
  by_cases hL₀ : P.μ 5 ∈ P.T₀ ∧ P.μ (5 + 1) ∈ P.T₀
  · have hL₀' := hL₀
    rw [mem_T₀, mem_T₀] at hL₀'
    by_cases hadj : (P.μ 5 = 1 ∧ P.μ (5 + 1) = 1 + 1) ∨ (P.μ 5 = 1 + 1 ∧ P.μ (5 + 1) = 1) ∨
        (P.μ 5 = 2 ∧ P.μ (5 + 1) = 2 + 1) ∨ (P.μ 5 = 2 + 1 ∧ P.μ (5 + 1) = 2)
    · rcases hadj with h | h | h | h
      · exact ⟨altCycleOfPairs h5i h6i h1i h2i (Or.inr (by norm_num)) (Or.inl h)⟩
      · exact ⟨altCycleOfPairs h5i h6i h1i h2i (Or.inr (by norm_num)) (Or.inr h)⟩
      · exact ⟨altCycleOfPairs h5i h6i h2i h3i (Or.inr (by norm_num)) (Or.inl h)⟩
      · exact ⟨altCycleOfPairs h5i h6i h2i h3i (Or.inr (by norm_num)) (Or.inr h)⟩
    have h13 : (P.μ 5 = 1 ∨ P.μ 5 = 3) ∧ (P.μ (5 + 1) = 1 ∨ P.μ (5 + 1) = 3) := by omega
    by_cases hs₁7' : P.s₁ = 7
    · exfalso
      have h8i : P.Inner 8 := ⟨by omega, by omega, by omega, by omega⟩
      have h9i : P.Inner 9 := ⟨by omega, by omega, by omega, by omega⟩
      have hp8 := partners_of_L13 hs₂ hn hs₁7 h13.1 h13.2 h8i (by omega) (by omega) (by omega)
        (by omega)
      have hp9 := partners_of_L13 hs₂ hn hs₁7 h13.1 h13.2 h9i (by omega) (by omega) (by omega)
        (by omega)
      have h8T := hT₂ 8 (mem_T₂.mpr ⟨by omega, by omega⟩)
      have h9T := hT₂ 9 (mem_T₂.mpr ⟨by omega, by omega⟩)
      rw [mem_T₂] at h8T h9T
      obtain ⟨a8, b8, c8, d8⟩ := inner_μ h8i
      obtain ⟨a9, b9, c9, d9⟩ := inner_μ h9i
      have : P.μ 8 = P.μ 9 := by omega
      have := μ_injOn h8i h9i this
      omega
    have hs₁9 : 9 ≤ P.s₁ := by omega
    -- the pair `s₁ - 2, s₁ - 1`
    have hRi : P.Inner (P.s₁ - 2) := ⟨by omega, by omega, by omega, by omega⟩
    have hR1i : P.Inner (P.s₁ - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
    by_cases hparR : P.μ (P.s₁ - 2) = P.s₁ - 2 + 1
    · exact ⟨altCycleOfParallel hRi hR1i hparR⟩
    have hqR : P.Reducible (P.s₁ - 2) := ⟨hRi, hR1i, hparR⟩
    have hgapR : P.Spoke (P.s₁ - 2 - 1) ∨ P.Spoke (P.s₁ - 2 + 2) ∨ P.s₁ - 2 + 2 = P.n :=
      Or.inr (Or.inl (by rw [show P.s₁ - 2 + 2 = P.s₁ by omega]; exact spoke_s₁))
    have hx''i := inner_μ hRi
    have hy''i := inner_μ hR1i
    have hpa := partners_of_L13 hs₂ hn hs₁7 h13.1 h13.2 hRi (by omega) (by omega) (by omega)
      (by omega)
    have hpb := partners_of_L13 hs₂ hn hs₁7 h13.1 h13.2 hR1i (by omega) (by omega) (by omega)
      (by omega)
    by_cases hR₀ : P.μ (P.s₁ - 2) ∈ P.T₀ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₀
    · exfalso
      rw [mem_T₀, mem_T₀] at hR₀
      have : P.μ (P.s₁ - 2) = P.μ (P.s₁ - 2 + 1) := by omega
      have := μ_injOn hRi hR1i this
      omega
    by_cases hR₂ : P.μ (P.s₁ - 2) ∈ P.T₂ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₂
    · have hR₂' := hR₂
      rw [mem_T₂, mem_T₂] at hR₂'
      have hx''y'' : P.μ (P.s₁ - 2) ≠ P.μ (P.s₁ - 2 + 1) := fun h ↦ by
        have := μ_injOn hRi hR1i h; omega
      by_cases hadjR : (P.μ (P.s₁ - 2) = P.s₁ + 1 ∧ P.μ (P.s₁ - 2 + 1) = P.s₁ + 1 + 1) ∨
          (P.μ (P.s₁ - 2) = P.s₁ + 1 + 1 ∧ P.μ (P.s₁ - 2 + 1) = P.s₁ + 1) ∨
          (P.μ (P.s₁ - 2) = P.s₁ + 2 ∧ P.μ (P.s₁ - 2 + 1) = P.s₁ + 2 + 1) ∨
          (P.μ (P.s₁ - 2) = P.s₁ + 2 + 1 ∧ P.μ (P.s₁ - 2 + 1) = P.s₁ + 2)
      · rcases hadjR with h | h | h | h
        · exact ⟨altCycleOfPairs hRi hR1i hs1i hs2i (Or.inl (by omega)) (Or.inl h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i hs1i hs2i (Or.inl (by omega)) (Or.inr h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i hs2i' hs3i (Or.inl (by omega)) (Or.inl h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i hs2i' hs3i (Or.inl (by omega)) (Or.inr h)⟩
      have h13' : P.μ (P.s₁ - 2 + 1) = P.s₁ + 1 ∨ P.μ (P.s₁ - 2 + 1) = P.s₁ + 3 := by omega
      have e : P.s₁ - 2 + 1 = P.s₁ - 1 := by omega
      rw [e] at h13'
      exact ⟨altCycleBig hs₂ hn hs₁9 h13.1 h13' (Or.inl ⟨rfl, rfl⟩)⟩
    · exact altCycle_of_reduce hqR hgapR (good_reduce_R hs₂ hn hgood hs₁9 hqR hR₀ hR₂) ih
  by_cases hL₂ : P.μ 5 ∈ P.T₂ ∧ P.μ (5 + 1) ∈ P.T₂
  · have hL₂' := hL₂
    rw [mem_T₂, mem_T₂] at hL₂'
    by_cases hadj : (P.μ 5 = P.s₁ + 1 ∧ P.μ (5 + 1) = P.s₁ + 1 + 1) ∨
        (P.μ 5 = P.s₁ + 1 + 1 ∧ P.μ (5 + 1) = P.s₁ + 1) ∨
        (P.μ 5 = P.s₁ + 2 ∧ P.μ (5 + 1) = P.s₁ + 2 + 1) ∨
        (P.μ 5 = P.s₁ + 2 + 1 ∧ P.μ (5 + 1) = P.s₁ + 2)
    · rcases hadj with h | h | h | h
      · exact ⟨altCycleOfPairs h5i h6i hs1i hs2i (Or.inl (by omega)) (Or.inl h)⟩
      · exact ⟨altCycleOfPairs h5i h6i hs1i hs2i (Or.inl (by omega)) (Or.inr h)⟩
      · exact ⟨altCycleOfPairs h5i h6i hs2i' hs3i (Or.inl (by omega)) (Or.inl h)⟩
      · exact ⟨altCycleOfPairs h5i h6i hs2i' hs3i (Or.inl (by omega)) (Or.inr h)⟩
    have h13 : (P.μ 5 = P.s₁ + 1 ∨ P.μ 5 = P.s₁ + 3) ∧
        (P.μ (5 + 1) = P.s₁ + 1 ∨ P.μ (5 + 1) = P.s₁ + 3) := by omega
    by_cases hs₁7' : P.s₁ = 7
    · exfalso
      have hp1 := partners_of_L13' hs₂ hn hs₁7 h13.1 h13.2 h1i (by omega) (by omega) (by omega)
        (by omega)
      have hp2 := partners_of_L13' hs₂ hn hs₁7 h13.1 h13.2 h2i (by omega) (by omega) (by omega)
        (by omega)
      have h1T := hT₀ 1 (mem_T₀.mpr ⟨by omega, by omega⟩)
      have h2T := hT₀ 2 (mem_T₀.mpr ⟨by omega, by omega⟩)
      rw [mem_T₀] at h1T h2T
      obtain ⟨a1, b1, c1, d1⟩ := inner_μ h1i
      obtain ⟨a2, b2, c2, d2⟩ := inner_μ h2i
      have : P.μ 1 = P.μ 2 := by omega
      have := μ_injOn h1i h2i this
      omega
    have hs₁9 : 9 ≤ P.s₁ := by omega
    have hRi : P.Inner (P.s₁ - 2) := ⟨by omega, by omega, by omega, by omega⟩
    have hR1i : P.Inner (P.s₁ - 2 + 1) := ⟨by omega, by omega, by omega, by omega⟩
    by_cases hparR : P.μ (P.s₁ - 2) = P.s₁ - 2 + 1
    · exact ⟨altCycleOfParallel hRi hR1i hparR⟩
    have hqR : P.Reducible (P.s₁ - 2) := ⟨hRi, hR1i, hparR⟩
    have hgapR : P.Spoke (P.s₁ - 2 - 1) ∨ P.Spoke (P.s₁ - 2 + 2) ∨ P.s₁ - 2 + 2 = P.n :=
      Or.inr (Or.inl (by rw [show P.s₁ - 2 + 2 = P.s₁ by omega]; exact spoke_s₁))
    have hx''i := inner_μ hRi
    have hy''i := inner_μ hR1i
    have hpa := partners_of_L13' hs₂ hn hs₁7 h13.1 h13.2 hRi (by omega) (by omega) (by omega)
      (by omega)
    have hpb := partners_of_L13' hs₂ hn hs₁7 h13.1 h13.2 hR1i (by omega) (by omega) (by omega)
      (by omega)
    by_cases hR₂ : P.μ (P.s₁ - 2) ∈ P.T₂ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₂
    · exfalso
      rw [mem_T₂, mem_T₂] at hR₂
      have : P.μ (P.s₁ - 2) = P.μ (P.s₁ - 2 + 1) := by omega
      have := μ_injOn hRi hR1i this
      omega
    by_cases hR₀ : P.μ (P.s₁ - 2) ∈ P.T₀ ∧ P.μ (P.s₁ - 2 + 1) ∈ P.T₀
    · have hR₀' := hR₀
      rw [mem_T₀, mem_T₀] at hR₀'
      have hx''y'' : P.μ (P.s₁ - 2) ≠ P.μ (P.s₁ - 2 + 1) := fun h ↦ by
        have := μ_injOn hRi hR1i h; omega
      by_cases hadjR : (P.μ (P.s₁ - 2) = 1 ∧ P.μ (P.s₁ - 2 + 1) = 1 + 1) ∨
          (P.μ (P.s₁ - 2) = 1 + 1 ∧ P.μ (P.s₁ - 2 + 1) = 1) ∨
          (P.μ (P.s₁ - 2) = 2 ∧ P.μ (P.s₁ - 2 + 1) = 2 + 1) ∨
          (P.μ (P.s₁ - 2) = 2 + 1 ∧ P.μ (P.s₁ - 2 + 1) = 2)
      · rcases hadjR with h | h | h | h
        · exact ⟨altCycleOfPairs hRi hR1i h1i h2i (Or.inr (by omega)) (Or.inl h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i h1i h2i (Or.inr (by omega)) (Or.inr h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i h2i h3i (Or.inr (by omega)) (Or.inl h)⟩
        · exact ⟨altCycleOfPairs hRi hR1i h2i h3i (Or.inr (by omega)) (Or.inr h)⟩
      have h13' : P.μ (P.s₁ - 2 + 1) = 1 ∨ P.μ (P.s₁ - 2 + 1) = 3 := by omega
      have e : P.s₁ - 2 + 1 = P.s₁ - 1 := by omega
      rw [e] at h13'
      exact ⟨altCycleBig hs₂ hn hs₁9 h13' h13.1 (Or.inr ⟨rfl, rfl⟩)⟩
    · exact altCycle_of_reduce hqR hgapR (good_reduce_R hs₂ hn hgood hs₁9 hqR hR₀ hR₂) ih
  · exact altCycle_of_reduce hqL hgapL (good_reduce_L hs₂ hn hgood hs₁7 hqL hL₀ hL₂) ih

end BaseMain

/-- Lemma 3.6 (normalized): a pole whose segments `T₀` and `T₂` are even with at least three
exterior chords each has an alternating cycle. -/
theorem exists_altCycle_of_good :
    ∀ (n : ℕ) (P : Pole), P.n = n → Good P → Nonempty P.AltCycle := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPn hgood
    have ih' : ∀ Q : Pole, Q.n < P.n → Good Q → Nonempty Q.AltCycle :=
      fun Q hQ hQg ↦ ih Q.n (hPn ▸ hQ) Q rfl hQg
    by_cases h6 : 6 ≤ P.n - P.s₁
    · exact estep_T₂ hgood h6 ih'
    by_cases h6' : 6 ≤ P.s₂
    · exact estep_T₀ hgood h6' ih'
    obtain ⟨he₀, he₂, hx₀, hx₂⟩ := hgood
    have hc₀ := ext_le_card (P := P) P.T₀
    rw [card_T₀] at hc₀
    have hc₂ := ext_le_card (P := P) P.T₂
    rw [card_T₂] at hc₂
    have hs := P.s₂_lt_s₁
    have hsn := P.s₁_lt_n
    have hs₂ : P.s₂ = 4 := by
      obtain ⟨k, hk⟩ := he₀
      omega
    have hn : P.n = P.s₁ + 4 := by
      obtain ⟨k, hk⟩ := he₂
      omega
    by_cases hs₁ : P.s₁ = 5
    · exact base_empty hs₂ hn hs₁ (all_exterior_of_card_le (by rw [card_T₀, hs₂]; exact hx₀))
    · have hodd := base_s₁_odd hn (P := P)
      exact base hs₂ hn ⟨he₀, he₂, hx₀, hx₂⟩ (by omega) ih'

end Pole
end GraphPuzzles
