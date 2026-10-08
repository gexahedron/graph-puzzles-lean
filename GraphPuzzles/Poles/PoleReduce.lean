import GraphPuzzles.Poles.PoleSuppression

/-!
# Deleting two consecutive inner positions

The induction step of Lemma 3.6 of Karabáš–Máčajová removes two consecutive inner vertices
`u₁, u₂` of a segment, together with their chords `u₁u₁'`, `u₂u₂'`, and adds the chord `u₁'u₂'`.
This module builds that reduced pole (`reduce`), lifts alternating cycles of the reduced pole back
(`AltCycle.unreduce`, valid when one of the two neighbouring positions is a spoke), and compares
the numbers of exterior chords of the segments before and after the reduction.
-/

namespace GraphPuzzles
namespace Pole

variable (P : Pole) (q : ℕ)

/-- The relabelling of the positions other than `q`, `q + 1`. -/
def rr (p : ℕ) : ℕ := if p < q then p else p - 2

/-- The inverse relabelling. -/
def rrinv (p' : ℕ) : ℕ := if p' < q then p' else p' + 2

/-- The chord map after joining the partners of `q` and `q + 1`. -/
def μred (p : ℕ) : ℕ :=
  if p = P.μ q then P.μ (q + 1) else if p = P.μ (q + 1) then P.μ q else P.μ p

/-- The positions `q` and `q + 1` can be deleted: both inner, not joined by a chord. -/
def Reducible : Prop := P.Inner q ∧ P.Inner (q + 1) ∧ P.μ q ≠ q + 1

variable {P q}

theorem rr_rrinv (p' : ℕ) : rr q (rrinv q p') = p' := by
  unfold rr rrinv
  split_ifs <;> omega

theorem rrinv_rr {p : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) : rrinv q (rr q p) = p := by
  unfold rr rrinv
  split_ifs <;> omega

theorem rrinv_ne (p' : ℕ) : rrinv q p' ≠ q ∧ rrinv q p' ≠ q + 1 := by
  unfold rrinv
  split_ifs <;> omega

theorem rr_injOn {p p' : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) (hp' : p' ≠ q ∧ p' ≠ q + 1)
    (h : rr q p = rr q p') : p = p' := by
  rw [← rrinv_rr hp, h, rrinv_rr hp']

theorem rr_of_lt {p : ℕ} (h : p < q) : rr q p = p := by
  unfold rr
  rw [if_pos h]

theorem rr_of_ge {p : ℕ} (h : q ≤ p) : rr q p = p - 2 := by
  unfold rr
  rw [if_neg (by omega)]

theorem rrinv_of_lt {p' : ℕ} (h : p' < q) : rrinv q p' = p' := by
  unfold rrinv
  rw [if_pos h]

theorem rrinv_of_ge {p' : ℕ} (h : q ≤ p') : rrinv q p' = p' + 2 := by
  unfold rrinv
  rw [if_neg (by omega)]

theorem rr_lt_iff {p p' : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) (hp' : p' ≠ q ∧ p' ≠ q + 1) :
    rr q p < rr q p' ↔ p < p' := by
  unfold rr
  split_ifs <;> omega

section Reduce

variable (hq : P.Reducible q)
include hq

theorem Reducible.inner : P.Inner q := hq.1

theorem Reducible.inner_succ : P.Inner (q + 1) := hq.2.1

theorem Reducible.μ_ne : P.μ q ≠ q + 1 := hq.2.2

theorem Reducible.μ_succ_ne : P.μ (q + 1) ≠ q := by
  intro h
  apply hq.μ_ne
  have := μ_μ_of_inner hq.inner_succ
  rw [h] at this
  exact this

theorem Reducible.μ_ne_self : P.μ q ≠ q := μ_ne_of_inner hq.inner

theorem Reducible.μ_succ_ne_self : P.μ (q + 1) ≠ q + 1 := μ_ne_of_inner hq.inner_succ

theorem Reducible.μ_ne_μ_succ : P.μ q ≠ P.μ (q + 1) := by
  intro h
  have := μ_injOn hq.inner hq.inner_succ h
  omega

theorem Reducible.q_pos : 0 < q := hq.inner.1

theorem Reducible.succ_lt : q + 1 < P.n := hq.inner_succ.2.1

omit hq in
theorem μred_of_ne {p : ℕ} (h1 : p ≠ P.μ q) (h2 : p ≠ P.μ (q + 1)) : P.μred q p = P.μ p := by
  unfold μred
  rw [if_neg h1, if_neg h2]

omit hq in
theorem μred_μ : P.μred q (P.μ q) = P.μ (q + 1) := by
  unfold μred
  rw [if_pos rfl]

theorem μred_μ_succ : P.μred q (P.μ (q + 1)) = P.μ q := by
  unfold μred
  rw [if_neg hq.μ_ne_μ_succ.symm, if_pos rfl]

theorem μred_inner {p : ℕ} (hp : P.Inner p) : P.Inner (P.μred q p) := by
  by_cases h1 : p = P.μ q
  · rw [h1, μred_μ]
    exact inner_μ hq.inner_succ
  by_cases h2 : p = P.μ (q + 1)
  · rw [h2, μred_μ_succ hq]
    exact inner_μ hq.inner
  rw [μred_of_ne h1 h2]
  exact inner_μ hp

theorem μred_ne {p : ℕ} (hp : P.Inner p) :
    P.μred q p ≠ q ∧ P.μred q p ≠ q + 1 := by
  by_cases h1 : p = P.μ q
  · rw [h1, μred_μ]
    exact ⟨hq.μ_succ_ne, hq.μ_succ_ne_self⟩
  by_cases h2 : p = P.μ (q + 1)
  · rw [h2, μred_μ_succ hq]
    exact ⟨hq.μ_ne_self, hq.μ_ne⟩
  rw [μred_of_ne h1 h2]
  constructor
  · intro h
    apply h1
    rw [← h, μ_μ_of_inner hp]
  · intro h
    apply h2
    rw [← h, μ_μ_of_inner hp]

theorem μred_μred {p : ℕ} (hp : P.Inner p) (hp' : p ≠ q ∧ p ≠ q + 1) :
    P.μred q (P.μred q p) = p := by
  by_cases h1 : p = P.μ q
  · rw [h1, μred_μ, μred_μ_succ hq]
  by_cases h2 : p = P.μ (q + 1)
  · rw [h2, μred_μ_succ hq, μred_μ]
  rw [μred_of_ne h1 h2]
  rw [μred_of_ne (fun h ↦ hp'.1 (μ_injOn hp hq.inner h))
    (fun h ↦ hp'.2 (μ_injOn hp hq.inner_succ h)), μ_μ_of_inner hp]

theorem μred_ne_self {p : ℕ} (hp : P.Inner p) : P.μred q p ≠ p := by
  by_cases h1 : p = P.μ q
  · rw [h1, μred_μ]
    exact hq.μ_ne_μ_succ.symm
  by_cases h2 : p = P.μ (q + 1)
  · rw [h2, μred_μ_succ hq]
    exact hq.μ_ne_μ_succ
  rw [μred_of_ne h1 h2]
  exact μ_ne_of_inner hp

theorem rr_lt_n {p : ℕ} (hp : p < P.n) (hp' : p ≠ q ∧ p ≠ q + 1) : rr q p < P.n - 2 := by
  have := hq.succ_lt
  unfold rr
  split_ifs <;> omega

omit hq in
theorem rrinv_lt_n {p' : ℕ} (hp : p' < P.n - 2) : rrinv q p' < P.n := by
  unfold rrinv
  split_ifs <;> omega

theorem rr_pos {p : ℕ} (hp : 0 < p) (hp' : p ≠ q ∧ p ≠ q + 1) : 0 < rr q p := by
  have := hq.q_pos
  unfold rr
  split_ifs <;> omega

theorem spoke_ne {p : ℕ} (hp : P.Spoke p) : p ≠ q ∧ p ≠ q + 1 := by
  constructor
  · rintro rfl
    exact not_inner_of_spoke hp hq.inner
  · rintro rfl
    exact not_inner_of_spoke hp hq.inner_succ

theorem inner_rrinv_iff {p' : ℕ} :
    (0 < p' ∧ p' < P.n - 2 ∧ p' ≠ rr q P.s₂ ∧ p' ≠ rr q P.s₁) ↔ P.Inner (rrinv q p') := by
  have h2 := spoke_ne hq (P := P) spoke_s₂
  have h1 := spoke_ne hq (P := P) spoke_s₁
  have hne := rrinv_ne (q := q) p'
  have hs₂ := P.s₂_pos
  have hs := P.s₂_lt_s₁
  have hn := P.s₁_lt_n
  have hq1 := hq.succ_lt
  have hq0 := hq.q_pos
  unfold Inner
  unfold rr rrinv at *
  split_ifs at * <;> omega

/-- The reduced pole. -/
def reduce : Pole where
  n := P.n - 2
  s₂ := rr q P.s₂
  s₁ := rr q P.s₁
  μ := fun p' ↦ rr q (P.μred q (rrinv q p'))
  s₂_pos := rr_pos hq P.s₂_pos (spoke_ne hq spoke_s₂)
  s₂_lt_s₁ := (rr_lt_iff (spoke_ne hq spoke_s₂) (spoke_ne hq spoke_s₁)).mpr P.s₂_lt_s₁
  s₁_lt_n := rr_lt_n hq P.s₁_lt_n (spoke_ne hq spoke_s₁)
  μ_inner := by
    intro p' h0 hn h2 h1
    have hp := (inner_rrinv_iff hq).mp ⟨h0, hn, h2, h1⟩
    have hμ := μred_inner hq hp
    have hμne := μred_ne hq hp
    have := (inner_rrinv_iff hq (p' := rr q (P.μred q (rrinv q p')))).mpr (by
      rw [rrinv_rr hμne]; exact hμ)
    exact this
  μ_μ := by
    intro p' h0 hn h2 h1
    have hp := (inner_rrinv_iff hq).mp ⟨h0, hn, h2, h1⟩
    have hμne := μred_ne hq hp
    rw [rrinv_rr hμne, μred_μred hq hp (rrinv_ne p'), rr_rrinv]
  μ_ne := by
    intro p' h0 hn h2 h1 h
    have hp := (inner_rrinv_iff hq).mp ⟨h0, hn, h2, h1⟩
    have hμne := μred_ne hq hp
    have := rr_injOn hμne (rrinv_ne p') (by rw [h, rr_rrinv])
    exact μred_ne_self hq hp this

theorem reduce_n : (reduce hq).n = P.n - 2 := rfl

theorem reduce_s₂ : (reduce hq).s₂ = rr q P.s₂ := rfl

theorem reduce_s₁ : (reduce hq).s₁ = rr q P.s₁ := rfl

theorem reduce_n_lt : (reduce hq).n < P.n := by
  rw [reduce_n]
  have := hq.succ_lt
  omega

theorem reduce_μ_rr {p : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) :
    (reduce hq).μ (rr q p) = rr q (P.μred q p) := by
  change rr q (P.μred q (rrinv q (rr q p))) = _
  rw [rrinv_rr hp]

theorem reduce_inner_iff {p' : ℕ} : (reduce hq).Inner p' ↔ P.Inner (rrinv q p') :=
  inner_rrinv_iff hq

theorem reduce_inner_rr {p : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) :
    (reduce hq).Inner (rr q p) ↔ P.Inner p := by
  rw [reduce_inner_iff hq, rrinv_rr hp]

theorem reduce_spoke_rr {p : ℕ} (hp : p ≠ q ∧ p ≠ q + 1) (hpn : p < P.n) :
    (reduce hq).Spoke (rr q p) ↔ P.Spoke p := by
  have h1 : (reduce hq).Inner (rr q p) ↔ P.Inner p := reduce_inner_rr hq hp
  rw [Pole.inner_iff, Pole.inner_iff] at h1
  have hlt : rr q p < P.n - 2 := rr_lt_n hq hpn hp
  rw [reduce_n] at h1
  constructor
  · intro h
    by_contra h'
    exact ((h1.mpr ⟨hpn, h'⟩).2 h)
  · intro h
    by_contra h'
    exact ((h1.mp ⟨hlt, h'⟩).2 h)

theorem reduce_spoke_iff {p' : ℕ} (hp : p' < P.n - 2) :
    (reduce hq).Spoke p' ↔ P.Spoke (rrinv q p') := by
  have := reduce_spoke_rr hq (rrinv_ne p') (rrinv_lt_n hp) (P := P)
  rwa [rr_rrinv] at this

end Reduce

section Segments

variable (hq : P.Reducible q)
include hq

omit hq in
/-- The image of an interval lying below `q`. -/
theorem image_rr_Ico_of_le {a b : ℕ} (hb : b ≤ q) :
    (Finset.Ico a b).image (rr q) = Finset.Ico a b := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_Ico] at hx ⊢
    rw [rr_of_lt (by omega)]
    exact hx
  · intro h
    refine ⟨p, h, ?_⟩
    rw [Finset.mem_Ico] at h
    exact rr_of_lt (by omega)

omit hq in
/-- The image of an interval lying above `q + 1`. -/
theorem image_rr_Ico_of_ge {a b : ℕ} (ha : q + 2 ≤ a) :
    (Finset.Ico a b).image (rr q) = Finset.Ico (a - 2) (b - 2) := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_Ico] at hx ⊢
    rw [rr_of_ge (by omega)]
    omega
  · intro h
    rw [Finset.mem_Ico] at h
    refine ⟨p + 2, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · rw [rr_of_ge (by omega)]
      omega

omit hq in
/-- The image of an interval containing `q`, `q + 1`, with them removed. -/
theorem image_rr_Ico_sdiff {a b : ℕ} (ha : a ≤ q) (hb : q + 2 ≤ b) :
    ((Finset.Ico a b) \ {q, q + 1}).image (rr q) = Finset.Ico a (b - 2) := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Ico]
    unfold rr
    split_ifs <;> omega
  · intro h
    rw [Finset.mem_Ico] at h
    by_cases hp : p < q
    · refine ⟨p, ?_, rr_of_lt hp⟩
      rw [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
      omega
    · refine ⟨p + 2, ?_, ?_⟩
      · rw [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        omega
      · rw [rr_of_ge (by omega)]
        omega

omit hq in
theorem mem_image_rr {T : Finset ℕ} (hT : ∀ p ∈ T, p ≠ q ∧ p ≠ q + 1) {x : ℕ}
    (hx : x ≠ q ∧ x ≠ q + 1) : rr q x ∈ T.image (rr q) ↔ x ∈ T := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [rr_injOn (hT y hy) hx hyx] at hy
  · intro h
    exact ⟨x, h, rfl⟩

/-- The exterior chords of the image of a set in the reduced pole, counted in the original
positions with the modified chord map. -/
theorem reduce_ext_image {T : Finset ℕ} (hTi : ∀ p ∈ T, P.Inner p)
    (hT : ∀ p ∈ T, p ≠ q ∧ p ≠ q + 1) :
    (reduce hq).ext (T.image (rr q)) = (T.filter fun p ↦ P.μred q p ∉ T).card := by
  unfold ext
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro p hp
    rw [reduce_μ_rr hq (hT p hp), mem_image_rr hT (μred_ne hq (hTi p hp))]
  · intro p hp p' hp' h
    exact rr_injOn (hT p (Finset.mem_filter.mp hp).1) (hT p' (Finset.mem_filter.mp hp').1) h

/-- A segment not containing the deleted pair keeps its exterior chords unless both partners
lie in it. -/
theorem ext_le_reduce_of_notMem {T : Finset ℕ} (hTi : ∀ p ∈ T, P.Inner p)
    (hT : ∀ p ∈ T, p ≠ q ∧ p ≠ q + 1) (h : ¬ (P.μ q ∈ T ∧ P.μ (q + 1) ∈ T)) :
    P.ext T ≤ (reduce hq).ext (T.image (rr q)) := by
  rw [reduce_ext_image hq hTi hT]
  unfold ext
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_cases h1 : p = P.μ q
  · rw [h1, μred_μ]
    intro h2
    exact h ⟨h1 ▸ hp.1, h2⟩
  by_cases h2 : p = P.μ (q + 1)
  · rw [h2, μred_μ_succ hq]
    intro h1'
    exact h ⟨h1', h2 ▸ hp.1⟩
  rw [μred_of_ne h1 h2]
  exact hp.2

/-- A segment containing the deleted pair keeps its exterior chords when at least one partner
lies in it. -/
theorem ext_le_reduce_of_mem {T : Finset ℕ} (hT : ∀ p ∈ T, P.Inner p)
    (hqT : q ∈ T) (hq1T : q + 1 ∈ T) (h : P.μ q ∈ T ∨ P.μ (q + 1) ∈ T) :
    P.ext T ≤ (reduce hq).ext ((T \ {q, q + 1}).image (rr q)) := by
  have hT' : ∀ p ∈ T \ {q, q + 1}, p ≠ q ∧ p ≠ q + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hp
    exact ⟨fun h ↦ hp.2 (Or.inl h), fun h ↦ hp.2 (Or.inr h)⟩
  rw [reduce_ext_image hq (fun p hp ↦ hT p (Finset.mem_sdiff.mp hp).1) hT']
  unfold ext
  -- the injection: positions other than `q`, `q + 1` are kept; `q` is sent to `μ (q + 1)` and
  -- `q + 1` to `μ q`
  set S := T.filter (fun p ↦ P.μ p ∉ T) with hS
  let φ : ℕ → ℕ := fun p ↦ if p = q then P.μ (q + 1) else if p = q + 1 then P.μ q else p
  have hφq : φ q = P.μ (q + 1) := by simp [φ]
  have hφq1 : φ (q + 1) = P.μ q := by simp [φ]
  have hφ : ∀ x, x ≠ q → x ≠ q + 1 → φ x = x := by
    intro x h1 h2
    simp [φ, h1, h2]
  have hμq : P.μ q ∉ S := by
    rw [hS, Finset.mem_filter, not_and, not_not]
    intro _
    rw [μ_μ_of_inner hq.inner]
    exact hqT
  have hμq1 : P.μ (q + 1) ∉ S := by
    rw [hS, Finset.mem_filter, not_and, not_not]
    intro _
    rw [μ_μ_of_inner hq.inner_succ]
    exact hq1T
  have hcases : ∀ x ∈ S, (x = q ∧ φ x = P.μ (q + 1)) ∨ (x = q + 1 ∧ φ x = P.μ q) ∨
      (x ≠ q ∧ x ≠ q + 1 ∧ φ x = x ∧ x ≠ P.μ q ∧ x ≠ P.μ (q + 1)) := by
    intro x hx
    by_cases h1 : x = q
    · exact Or.inl ⟨h1, h1 ▸ hφq⟩
    by_cases h2 : x = q + 1
    · exact Or.inr (Or.inl ⟨h2, h2 ▸ hφq1⟩)
    refine Or.inr (Or.inr ⟨h1, h2, hφ x h1 h2, ?_, ?_⟩)
    · rintro rfl
      exact hμq hx
    · rintro rfl
      exact hμq1 hx
  apply Finset.card_le_card_of_injOn φ
  · intro p hp
    rw [Finset.mem_coe] at hp
    have hp' := Finset.mem_filter.mp hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    rcases hcases p hp with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨n1, n2, e, m1, m2⟩
    · rw [e]
      have hμ1 : P.μ (p + 1) ∈ T := by
        rcases h with h | h
        · exact absurd h hp'.2
        · exact h
      refine ⟨⟨hμ1, ?_⟩, ?_⟩
      · rintro (h' | h')
        · exact hq.μ_succ_ne h'
        · exact hq.μ_succ_ne_self h'
      · rw [μred_μ_succ hq]
        intro h'
        exact hp'.2 (Finset.mem_sdiff.mp h').1
    · rw [e]
      have hμ0 : P.μ q ∈ T := by
        rcases h with h | h
        · exact h
        · exact absurd h hp'.2
      refine ⟨⟨hμ0, ?_⟩, ?_⟩
      · rintro (h' | h')
        · exact hq.μ_ne_self h'
        · exact hq.μ_ne h'
      · rw [μred_μ]
        intro h'
        exact hp'.2 (Finset.mem_sdiff.mp h').1
    · rw [e]
      refine ⟨⟨hp'.1, ?_⟩, ?_⟩
      · rintro (h' | h')
        · exact n1 h'
        · exact n2 h'
      · rw [μred_of_ne m1 m2]
        intro h'
        exact hp'.2 (Finset.mem_sdiff.mp h').1
  · intro p hp p' hp' hpp'
    rw [Finset.mem_coe] at hp hp'
    rcases hcases p hp with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨n1, n2, e, m1, m2⟩ <;>
      rcases hcases p' hp' with ⟨rfl, e'⟩ | ⟨rfl, e'⟩ | ⟨n1', n2', e', m1', m2'⟩ <;>
      (try rw [e] at hpp') <;> (try rw [e'] at hpp') <;>
      first
      | rfl
      | exact hpp'
      | exact absurd hpp' hq.μ_ne_μ_succ.symm
      | exact absurd hpp' hq.μ_ne_μ_succ
      | exact absurd hpp'.symm m2'
      | exact absurd hpp'.symm m1'
      | exact absurd hpp' m2
      | exact absurd hpp' m1

omit hq in
/-- Two positions with exterior chords give at least two exterior chords. -/
theorem two_le_ext {Q : Pole} {T : Finset ℕ} {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y)
    (hμx : Q.μ x ∉ T) (hμy : Q.μ y ∉ T) : 2 ≤ Q.ext T := by
  unfold ext
  have : ({x, y} : Finset ℕ) ⊆ T.filter fun p ↦ Q.μ p ∉ T := by
    intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Finset.mem_filter]
    rcases hp with rfl | rfl
    · exact ⟨hx, hμx⟩
    · exact ⟨hy, hμy⟩
  have := Finset.card_le_card this
  rwa [Finset.card_pair hxy] at this

omit hq in
/-- An odd number of exterior chords that is at least two is at least three. -/
theorem three_le_ext_of_two_le {Q : Pole} {T : Finset ℕ} (hT : ∀ p ∈ T, Q.Inner p)
    (hodd : T.card % 2 = 1) (h2 : 2 ≤ Q.ext T) : 3 ≤ Q.ext T := by
  have := ext_mod_two hT
  omega

end Segments

section Lift

variable (hq : P.Reducible q)
variable (A : (reduce hq).AltCycle)

/-- The lifted edge predicate: edges below the gap are kept, edges above are shifted by two, and
the edge `q` is added when the joined chord belongs to the reduced cycle. -/
def liftPred (p : ℕ) : Prop :=
  if p + 1 < q then p ∈ A.F else if p = q then rr q (P.μ q) ∈ A.D
  else if q + 2 ≤ p then p - 2 ∈ A.F else False

instance : DecidablePred (liftPred hq A) := fun p ↦ by unfold liftPred; infer_instance

/-- The lifted edge set. -/
def liftF : Finset ℕ := (Finset.range P.n).filter (liftPred hq A)

theorem mem_liftF {p : ℕ} : p ∈ liftF hq A ↔ p < P.n ∧ liftPred hq A p := by
  unfold liftF
  rw [Finset.mem_filter, Finset.mem_range]

theorem liftPred_of_lt {p : ℕ} (h : p + 1 < q) : liftPred hq A p ↔ p ∈ A.F := by
  unfold liftPred
  rw [if_pos h]

theorem liftPred_q : liftPred hq A q ↔ rr q (P.μ q) ∈ A.D := by
  unfold liftPred
  rw [if_neg (by omega), if_pos rfl]

theorem liftPred_of_ge {p : ℕ} (h : q + 2 ≤ p) : liftPred hq A p ↔ p - 2 ∈ A.F := by
  unfold liftPred
  rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem liftPred_pred_q : ¬ liftPred hq A (q - 1) := by
  unfold liftPred
  have := hq.q_pos
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact id

theorem liftPred_succ_q : ¬ liftPred hq A (q + 1) := by
  unfold liftPred
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact id

include hq in
theorem F_lt_n' {p : ℕ} (hp : p ∈ A.F) : p + 1 < P.n - 2 := (A.inner p hp).2.2.1

/-- The gap edge of the reduced pole never belongs to the reduced cycle. -/
theorem gap_notMem (hgap : P.Spoke (q - 1) ∨ P.Spoke (q + 2) ∨ q + 2 = P.n) : q - 1 ∉ A.F := by
  intro h
  have hi := A.inner _ h
  have hq0 := hq.q_pos
  have hq1 := hq.succ_lt
  rcases hgap with hs | hs | hs
  · have := (reduce_spoke_rr hq (spoke_ne hq hs) (spoke_lt hs)).mpr hs
    rw [rr_of_lt (by omega)] at this
    exact not_inner_of_spoke this hi.1
  · have := (reduce_spoke_rr hq (spoke_ne hq hs) (spoke_lt hs)).mpr hs
    rw [rr_of_ge (by omega), show q + 2 - 2 = q - 1 + 1 by omega] at this
    exact not_inner_of_spoke this hi.2
  · have := hi.2.2.1
    rw [reduce_n] at this
    omega

theorem mem_D_rr_iff {x : ℕ} (hx : x ≠ q ∧ x ≠ q + 1) (hxn : x < P.n)
    (hgap : P.Spoke (q - 1) ∨ P.Spoke (q + 2) ∨ q + 2 = P.n) :
    x ∈ dset (liftF hq A) ↔ rr q x ∈ A.D := by
  have hgapF := gap_notMem hq A hgap
  have hq0 := hq.q_pos
  have hq1 := hq.succ_lt
  by_cases hx0 : x = 0
  · subst hx0
    refine iff_of_false ?_ (by rw [rr_of_lt hq0]; exact A.zero_notMem_D)
    rw [mem_dset]
    rintro (h | ⟨h, -⟩)
    · rw [mem_liftF] at h
      obtain ⟨-, h⟩ := h
      unfold liftPred at h
      split_ifs at h <;> first | exact A.zero_notMem_F h | omega
    · omega
  have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hx0
  rw [mem_dset, AltCycle.mem_D, mem_liftF, mem_liftF]
  by_cases hlt : x < q
  · rw [rr_of_lt hlt]
    by_cases hx2 : x + 1 < q
    · rw [liftPred_of_lt hq A hx2, liftPred_of_lt hq A (by omega)]
      constructor
      · rintro (⟨-, h⟩ | ⟨h1, -, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h⟩
      · rintro (h | ⟨h1, h⟩)
        · exact Or.inl ⟨hxn, h⟩
        · exact Or.inr ⟨h1, by omega, h⟩
    · -- `x = q - 1`: its edge is the gap edge
      have hxq : x = q - 1 := by omega
      subst hxq
      constructor
      · rintro (⟨-, h⟩ | ⟨h1, -, h⟩)
        · exact absurd h (liftPred_pred_q hq A)
        · rw [liftPred_of_lt hq A (by omega)] at h
          exact Or.inr ⟨h1, h⟩
      · rintro (h | ⟨h1, h⟩)
        · exact absurd h hgapF
        · exact Or.inr ⟨h1, by omega, (liftPred_of_lt hq A (by omega)).mpr h⟩
  · have hge : q + 2 ≤ x := by omega
    rw [rr_of_ge (by omega), liftPred_of_ge hq A hge]
    by_cases hx2 : x = q + 2
    · subst hx2
      rw [show q + 2 - 2 = q by omega, show q + 2 - 1 = q + 1 by omega]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
        · exact Or.inl h
        · exact absurd h (liftPred_succ_q hq A)
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl ⟨hxn, h⟩
        · exact absurd h hgapF
    · rw [liftPred_of_ge hq A (by omega)]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by rw [show x - 1 - 2 = x - 2 - 1 by omega] at h; exact h⟩
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl ⟨hxn, h⟩
        · exact Or.inr ⟨by omega, by omega, by rw [show x - 1 - 2 = x - 2 - 1 by omega]; exact h⟩

theorem q_mem_D_iff : q ∈ dset (liftF hq A) ↔ rr q (P.μ q) ∈ A.D := by
  rw [mem_dset, mem_liftF, mem_liftF, liftPred_q]
  have hq1 := hq.succ_lt
  constructor
  · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
    · exact h
    · exact absurd h (liftPred_pred_q hq A)
  · intro h
    exact Or.inl ⟨by omega, h⟩

theorem succ_q_mem_D_iff : q + 1 ∈ dset (liftF hq A) ↔ rr q (P.μ q) ∈ A.D := by
  rw [mem_dset, mem_liftF, mem_liftF, Nat.add_sub_cancel, liftPred_q]
  have hq1 := hq.succ_lt
  constructor
  · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
    · exact absurd h (liftPred_succ_q hq A)
    · exact h
  · intro h
    exact Or.inr ⟨by omega, by omega, h⟩

theorem μ_succ_rr_mem_iff : rr q (P.μ (q + 1)) ∈ A.D ↔ rr q (P.μ q) ∈ A.D := by
  constructor
  · intro h
    have := A.μ_mem_D h
    rwa [reduce_μ_rr hq ⟨hq.μ_succ_ne, hq.μ_succ_ne_self⟩, μred_μ_succ hq] at this
  · intro h
    have := A.μ_mem_D h
    rwa [reduce_μ_rr hq ⟨hq.μ_ne_self, hq.μ_ne⟩, μred_μ] at this

/-- Lifting an alternating cycle of the reduced pole. -/
def AltCycle.unreduce (hgap : P.Spoke (q - 1) ∨ P.Spoke (q + 2) ∨ q + 2 = P.n) : P.AltCycle where
  F := liftF hq A
  nonempty := by
    obtain ⟨p, hp⟩ := A.nonempty
    have hpn := F_lt_n' hq A hp
    have hgapF := gap_notMem hq A hgap
    by_cases hlt : p + 1 < q
    · exact ⟨p, (mem_liftF hq A).mpr ⟨by omega, (liftPred_of_lt hq A hlt).mpr hp⟩⟩
    · have hne : p ≠ q - 1 := fun h ↦ hgapF (h ▸ hp)
      refine ⟨p + 2, (mem_liftF hq A).mpr ⟨by omega, ?_⟩⟩
      rw [liftPred_of_ge hq A (by omega), Nat.add_sub_cancel]
      exact hp
  inner := by
    intro p hp
    rw [mem_liftF] at hp
    obtain ⟨hpn, hp⟩ := hp
    have hq0 := hq.q_pos
    have hq1 := hq.succ_lt
    by_cases hlt : p + 1 < q
    · rw [liftPred_of_lt hq A hlt] at hp
      have hi := A.inner p hp
      rw [reduce_inner_iff hq, rrinv_of_lt (by omega)] at hi
      have hi' := hi.2
      rw [reduce_inner_iff hq, rrinv_of_lt (by omega)] at hi'
      exact ⟨hi.1, hi'⟩
    by_cases hpq : p = q
    · subst hpq
      exact ⟨hq.inner, hq.inner_succ⟩
    have hge : q + 2 ≤ p := by
      unfold liftPred at hp
      rw [if_neg hlt, if_neg hpq] at hp
      by_contra h
      rw [if_neg h] at hp
      exact hp
    rw [liftPred_of_ge hq A hge] at hp
    have hi := A.inner _ hp
    rw [reduce_inner_iff hq, rrinv_of_ge (by omega), Nat.sub_add_cancel (by omega)] at hi
    have hi' := hi.2
    rw [reduce_inner_iff hq, rrinv_of_ge (by omega), show p - 2 + 1 + 2 = p + 1 by omega] at hi'
    exact ⟨hi.1, hi'⟩
  matching := by
    intro p hp hp1
    rw [mem_liftF] at hp hp1
    obtain ⟨hpn, hp⟩ := hp
    obtain ⟨-, hp1⟩ := hp1
    have hq0 := hq.q_pos
    by_cases hlt : p + 2 < q
    · rw [liftPred_of_lt hq A (by omega)] at hp
      rw [liftPred_of_lt hq A hlt] at hp1
      exact A.matching p hp hp1
    by_cases hlt' : p + 1 < q
    · -- `p + 1 = q - 1`
      rw [liftPred_of_lt hq A hlt'] at hp
      have : p + 1 = q - 1 := by omega
      rw [this] at hp1
      exact liftPred_pred_q hq A hp1
    by_cases hpq : p = q
    · subst hpq
      exact liftPred_succ_q hq A hp1
    by_cases hpq1 : p = q - 1
    · subst hpq1
      exact liftPred_pred_q hq A hp
    have hge : q + 2 ≤ p := by
      unfold liftPred at hp
      rw [if_neg hlt', if_neg hpq] at hp
      by_contra h
      rw [if_neg h] at hp
      exact hp
    rw [liftPred_of_ge hq A hge] at hp
    rw [liftPred_of_ge hq A (by omega), show p + 1 - 2 = p - 2 + 1 by omega] at hp1
    exact A.matching _ hp hp1
  closed := by
    intro p hp
    have hpF := hp
    rw [mem_liftF] at hp
    obtain ⟨hpn, hp⟩ := hp
    have hq0 := hq.q_pos
    have hq1 := hq.succ_lt
    -- the two ends of `p` and their chord partners
    have key : ∀ x, x ∈ dset (liftF hq A) → x ≠ q → x ≠ q + 1 → P.Inner x →
        P.μ x ∈ dset (liftF hq A) := by
      intro x hx hx1 hx2 hxi
      have hxD := (mem_D_rr_iff hq A ⟨hx1, hx2⟩ hxi.2.1 hgap).mp hx
      have hμD := A.μ_mem_D hxD
      rw [reduce_μ_rr hq ⟨hx1, hx2⟩] at hμD
      by_cases h1 : x = P.μ q
      · rw [h1, μ_μ_of_inner hq.inner]
        rw [q_mem_D_iff]
        rw [h1, μred_μ, μ_succ_rr_mem_iff hq A] at hμD
        exact hμD
      by_cases h2 : x = P.μ (q + 1)
      · rw [h2, μ_μ_of_inner hq.inner_succ]
        rw [succ_q_mem_D_iff]
        rw [h2, μred_μ_succ hq] at hμD
        exact hμD
      rw [μred_of_ne h1 h2] at hμD
      have hμx := inner_μ hxi
      refine (mem_D_rr_iff hq A ?_ hμx.2.1 hgap).mpr hμD
      constructor
      · intro h
        apply h1
        rw [← h, μ_μ_of_inner hxi]
      · intro h
        apply h2
        rw [← h, μ_μ_of_inner hxi]
    have hpD : p ∈ dset (liftF hq A) := mem_dset.mpr (Or.inl hpF)
    have hp1D : p + 1 ∈ dset (liftF hq A) := mem_dset.mpr (Or.inr ⟨by omega, by simpa using hpF⟩)
    by_cases hpq : p = q
    · subst hpq
      have hD := (q_mem_D_iff hq A).mp hpD
      constructor
      · exact (mem_D_rr_iff hq A ⟨hq.μ_ne_self, hq.μ_ne⟩ (inner_μ hq.inner).2.1 hgap).mpr hD
      · exact (mem_D_rr_iff hq A ⟨hq.μ_succ_ne, hq.μ_succ_ne_self⟩ (inner_μ hq.inner_succ).2.1
          hgap).mpr ((μ_succ_rr_mem_iff hq A).mpr hD)
    have hpi : P.Inner p ∧ P.Inner (p + 1) := by
      by_cases hlt : p + 1 < q
      · rw [liftPred_of_lt hq A hlt] at hp
        have hi := A.inner p hp
        rw [reduce_inner_iff hq, rrinv_of_lt (by omega)] at hi
        have hi' := hi.2
        rw [reduce_inner_iff hq, rrinv_of_lt (by omega)] at hi'
        exact ⟨hi.1, hi'⟩
      have hge : q + 2 ≤ p := by
        unfold liftPred at hp
        rw [if_neg hlt, if_neg hpq] at hp
        by_contra h
        rw [if_neg h] at hp
        exact hp
      rw [liftPred_of_ge hq A hge] at hp
      have hi := A.inner _ hp
      rw [reduce_inner_iff hq, rrinv_of_ge (by omega), Nat.sub_add_cancel (by omega)] at hi
      have hi' := hi.2
      rw [reduce_inner_iff hq, rrinv_of_ge (by omega), show p - 2 + 1 + 2 = p + 1 by omega] at hi'
      exact ⟨hi.1, hi'⟩
    have hne : p ≠ q + 1 := fun h ↦ liftPred_succ_q hq A (h ▸ hp)
    have hne' : p + 1 ≠ q := by
      intro h
      have : p = q - 1 := by omega
      exact liftPred_pred_q hq A (this ▸ hp)
    exact ⟨key p hpD hpq hne hpi.1, key (p + 1) hp1D hne' (by omega) hpi.2⟩

end Lift

end Pole
end GraphPuzzles
