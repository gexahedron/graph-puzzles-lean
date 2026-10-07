import GraphPuzzles.FinGraph.FinGraphBetween

/-!
# Atoms are not crossed by cycle-separating `4`-cuts

An *atom* is an inclusion-minimal shore of a cycle-separating `4`-edge-cut.  In a cubic graph
of girth at least five that is cyclically `4`-edge-connected, every atom lies entirely on one
side of every cycle-separating `4`-cut (Nedela–Škoviera; Chladný–Škoviera, Theorem 7.2 and
Corollary 7.3).  The proof is cut arithmetic on the four quadrants determined by the atom and
the cut: submodularity of the boundary, the forest bound for acyclic quadrants, and the fact
that two acyclic sets joined by at most one edge are acyclic.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- An atom: a minimal shore of a cycle-separating `4`-cut. -/
def IsAtom (Γ : FinGraph) (A : Finset ℕ) : Prop := Γ.CycSep A ∧ ∀ B ⊂ A, ¬ Γ.CycSep B

theorem exists_atom (h : ∃ X, Γ.CycSep X) : ∃ A, Γ.IsAtom A := by
  classical
  obtain ⟨X, hX⟩ := h
  have hmem : X ∈ Γ.Vs.powerset.filter fun Y ↦ Γ.CycSep Y := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hX.1, hX⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ Finset.card ⟨X, hmem⟩
  rw [Finset.mem_filter] at hA
  refine ⟨A, hA.2, fun B hB hBc ↦ ?_⟩
  have hBmem : B ∈ Γ.Vs.powerset.filter fun Y ↦ Γ.CycSep Y := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hBc.1, hBc⟩
  have := hmin B hBmem
  have := Finset.card_lt_card hB
  omega

/-- The boundary of a set as the edges to the three other parts of a partition. -/
theorem card_bd_eq_three (hcl : Γ.IsClosed) {Q R S T : Finset ℕ}
    (hpart : Γ.Vs \ Q = R ∪ S ∪ T) (hQR : Disjoint Q R) (hQS : Disjoint Q S) (hQT : Disjoint Q T)
    (hRS : Disjoint R S) (hRT : Disjoint R T) (hST : Disjoint S T) :
    (Γ.bd Q).card = (Γ.between Q R).card + (Γ.between Q S).card + (Γ.between Q T).card := by
  rw [bd_eq_between hcl, hpart, card_between_union_right (Finset.disjoint_union_right.mpr ⟨hQR, hQS⟩)
    hQT (Finset.disjoint_union_left.mpr ⟨hRT, hST⟩), card_between_union_right hQR hQS hRS]

section Atom

variable (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hg : Γ.Girth5) (hc4 : Γ.Cyc4Conn)
  {A Y : Finset ℕ} (hA : Γ.IsAtom A) (hY : Γ.CycSep Y)
include hcl hcub hg hc4 hA hY

omit hcl hcub hg hY in
/-- Minimality of the atom: a proper cyclic subset has boundary at least five. -/
theorem IsAtom.five_le_bd {B : Finset ℕ} (hB : B ⊂ A) (hc : Γ.HasCycle B) : 5 ≤ (Γ.bd B).card := by
  have hBV : B ⊆ Γ.Vs := hB.subset.trans hA.1.1
  have hcompl : Γ.HasCycle (Γ.Vs \ B) :=
    hA.1.2.2.2.mono (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hB.subset)
  have h4 := hc4 B hBV hc hcompl
  have hne : (Γ.bd B).card ≠ 4 := fun h ↦ hA.2 B hB ⟨hBV, h, hc, hcompl⟩
  omega

omit hcub hg hc4 hA hY in
theorem cycSep_compl (hZ : Γ.CycSep Y) : Γ.CycSep (Γ.Vs \ Y) := by
  refine ⟨Finset.sdiff_subset, ?_, hZ.2.2.2, ?_⟩
  · rw [bd_compl hcl]
    exact hZ.2.1
  · rw [Finset.sdiff_sdiff_eq_self hZ.1]
    exact hZ.2.2.1

/-- The core of the atom theorem, assuming the quadrant `A ∩ Y` is acyclic. -/
theorem IsAtom.no_cross_aux (hQ₁ : (A ∩ Y).Nonempty) (hQ₂ : (A \ Y).Nonempty)
    (hnc : ¬ Γ.HasCycle (A ∩ Y)) : False := by
  have hAV : A ⊆ Γ.Vs := hA.1.1
  have hYV : Y ⊆ Γ.Vs := hY.1
  -- quadrants
  set Q₁ := A ∩ Y with hQ₁def
  set Q₂ := A \ Y with hQ₂def
  set Q₃ := Γ.Vs \ (A ∪ Y) with hQ₃def
  set Q₄ := Y \ A with hQ₄def
  have eA : Q₁ ∪ Q₂ = A := by
    ext v; simp only [hQ₁def, hQ₂def, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have eY : Q₁ ∪ Q₄ = Y := by
    ext v; simp only [hQ₁def, hQ₄def, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have eAc : Q₃ ∪ Q₄ = Γ.Vs \ A := by
    ext v
    simp only [hQ₃def, hQ₄def, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, fun h ↦ h2 (Or.inl h)⟩
      · exact ⟨hYV h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hv : v ∈ Y
      · exact Or.inr ⟨hv, h2⟩
      · exact Or.inl ⟨h1, fun h ↦ h.elim h2 hv⟩
  have eYc : Q₂ ∪ Q₃ = Γ.Vs \ Y := by
    ext v
    simp only [hQ₂def, hQ₃def, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨hAV h1, h2⟩
      · exact ⟨h1, fun h ↦ h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      by_cases hv : v ∈ A
      · exact Or.inl ⟨hv, h2⟩
      · exact Or.inr ⟨h1, fun h ↦ h.elim hv h2⟩
  have eQ₃c : Γ.Vs \ Q₃ = A ∪ Y := by
    rw [hQ₃def, Finset.sdiff_sdiff_eq_self (Finset.union_subset hAV hYV)]
  have eQ₄c : Γ.Vs \ Q₄ = A ∪ (Γ.Vs \ Y) := by
    ext v
    simp only [hQ₄def, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hv : v ∈ A
      · exact Or.inl hv
      · exact Or.inr ⟨h1, fun h ↦ h2 ⟨h, hv⟩⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨hAV h, fun h' ↦ h'.2 h⟩
      · exact ⟨h1, fun h' ↦ h2 h'.1⟩
  have eQ₁c : Γ.Vs \ Q₁ = Q₂ ∪ Q₃ ∪ Q₄ := by
    ext v
    simp only [hQ₁def, hQ₂def, hQ₃def, hQ₄def, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : v ∈ A
      · exact Or.inl (Or.inl ⟨ha, fun hy ↦ h2 ⟨ha, hy⟩⟩)
      · by_cases hy : v ∈ Y
        · exact Or.inr ⟨hy, ha⟩
        · exact Or.inl (Or.inr ⟨h1, fun h ↦ h.elim ha hy⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨hAV h1, fun h ↦ h2 h.2⟩
      · exact ⟨h1, fun h ↦ h2 (Or.inl h.1)⟩
      · exact ⟨hYV h1, fun h ↦ h2 h.1⟩
  have eQ₂c : Γ.Vs \ Q₂ = Q₁ ∪ Q₃ ∪ Q₄ := by
    ext v
    simp only [hQ₁def, hQ₂def, hQ₃def, hQ₄def, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : v ∈ A
      · have hy : v ∈ Y := by
          by_contra hy
          exact h2 ⟨ha, hy⟩
        exact Or.inl (Or.inl ⟨ha, hy⟩)
      · by_cases hy : v ∈ Y
        · exact Or.inr ⟨hy, ha⟩
        · exact Or.inl (Or.inr ⟨h1, fun h ↦ h.elim ha hy⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨hAV h1, fun h ↦ h.2 h2⟩
      · exact ⟨h1, fun h ↦ h2 (Or.inl h.1)⟩
      · exact ⟨hYV h1, fun h ↦ h2 h.1⟩
  have eQ₃c' : Γ.Vs \ Q₃ = Q₁ ∪ Q₂ ∪ Q₄ := by
    rw [eQ₃c, ← eA, ← eY]
    ext v; simp only [Finset.mem_union]; tauto
  have eQ₄c' : Γ.Vs \ Q₄ = Q₁ ∪ Q₂ ∪ Q₃ := by
    rw [eQ₄c, ← eA, ← eYc]
    ext v; simp only [Finset.mem_union]; tauto
  -- disjointness
  have d12 : Disjoint Q₁ Q₂ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have d13 : Disjoint Q₁ Q₃ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_union_left _ (Finset.mem_inter.mp h1).1)
  have d14 : Disjoint Q₁ Q₄ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1
  have d23 : Disjoint Q₂ Q₃ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h1).1)
  have d24 : Disjoint Q₂ Q₄ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
  have d34 : Disjoint Q₃ Q₄ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mp h2).1)
  have sQ₁ : Q₁ ⊆ Γ.Vs := Finset.inter_subset_left.trans hAV
  have sQ₂ : Q₂ ⊆ Γ.Vs := Finset.sdiff_subset.trans hAV
  have sQ₃ : Q₃ ⊆ Γ.Vs := Finset.sdiff_subset
  have sQ₄ : Q₄ ⊆ Γ.Vs := Finset.sdiff_subset.trans hYV
  -- the edge counts between quadrants
  set d₁₂ := (Γ.between Q₁ Q₂).card
  set d₁₃ := (Γ.between Q₁ Q₃).card
  set d₁₄ := (Γ.between Q₁ Q₄).card
  set d₂₃ := (Γ.between Q₂ Q₃).card
  set d₂₄ := (Γ.between Q₂ Q₄).card
  set d₃₄ := (Γ.between Q₃ Q₄).card
  have e₁ : (Γ.bd Q₁).card = d₁₂ + d₁₃ + d₁₄ :=
    card_bd_eq_three hcl eQ₁c d12 d13 d14 d23 d24 d34
  have e₂ : (Γ.bd Q₂).card = d₁₂ + d₂₃ + d₂₄ := by
    rw [card_bd_eq_three hcl eQ₂c d12.symm d23 d24 d13 d14 d34, between_comm Q₂ Q₁]
  have e₃ : (Γ.bd Q₃).card = d₁₃ + d₂₃ + d₃₄ := by
    rw [card_bd_eq_three hcl eQ₃c' d13.symm d23.symm d34 d12 d14 d24, between_comm Q₃ Q₁,
      between_comm Q₃ Q₂]
  have e₄ : (Γ.bd Q₄).card = d₁₄ + d₂₄ + d₃₄ := by
    rw [card_bd_eq_three hcl eQ₄c' d14.symm d24.symm d34.symm d12 d13 d23, between_comm Q₄ Q₁,
      between_comm Q₄ Q₂, between_comm Q₄ Q₃]
  have hbA : (Γ.bd A).card = 4 := hA.1.2.1
  have hbY : (Γ.bd Y).card = 4 := hY.2.1
  have bA : (Γ.bd A).card + 2 * d₁₂ = (Γ.bd Q₁).card + (Γ.bd Q₂).card := by
    rw [← eA]; exact card_bd_union d12
  have bY : (Γ.bd Y).card + 2 * d₁₄ = (Γ.bd Q₁).card + (Γ.bd Q₄).card := by
    rw [← eY]; exact card_bd_union d14
  have bAc : (Γ.bd A).card + 2 * d₃₄ = (Γ.bd Q₃).card + (Γ.bd Q₄).card := by
    rw [← bd_compl hcl A, ← eAc]; exact card_bd_union d34
  have bYc : (Γ.bd Y).card + 2 * d₂₃ = (Γ.bd Q₂).card + (Γ.bd Q₃).card := by
    rw [← bd_compl hcl Y, ← eYc]; exact card_bd_union d23
  -- cycles
  have hcA : Γ.HasCycle A := hA.1.2.2.1
  have hcAc : Γ.HasCycle (Γ.Vs \ A) := hA.1.2.2.2
  have hcY : Γ.HasCycle Y := hY.2.2.1
  have hcYc : Γ.HasCycle (Γ.Vs \ Y) := hY.2.2.2
  have hQ₁A : Q₁ ⊂ A := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, fun h ↦ ?_⟩
    obtain ⟨v, hv⟩ := hQ₂
    have : v ∈ Q₁ := h ▸ (Finset.mem_sdiff.mp hv).1
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp this).2
  have hQ₂A : Q₂ ⊂ A := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.sdiff_subset, fun h ↦ ?_⟩
    obtain ⟨v, hv⟩ := hQ₁
    have : v ∈ Q₂ := h ▸ (Finset.mem_inter.mp hv).1
    exact (Finset.mem_sdiff.mp this).2 (Finset.mem_inter.mp hv).2
  -- forest bounds and handshake for `A`
  have fQ₁ : (Γ.edgesIn Q₁).card < Q₁.card := card_edgesIn_lt hQ₁ hnc
  have hEA : (Γ.edgesIn A).card = (Γ.edgesIn Q₁).card + (Γ.edgesIn Q₂).card + d₁₂ := by
    rw [← eA]; exact card_edgesIn_union d12
  have hhs : 3 * A.card = 2 * (Γ.edgesIn A).card + (Γ.bd A).card := three_mul_card_eq hcub hAV
  have hcardA : A.card = Q₁.card + Q₂.card := by
    rw [← eA, Finset.card_union_of_disjoint d12]
  have h5 : 5 ≤ (Γ.edgesIn A).card := five_le_card_edgesIn hg hcA
  -- `Q₄ = Y \ A` and `Q₃` cyclicity interplay
  by_cases hc₂ : Γ.HasCycle Q₂
  · -- Case IIa: `Q₂` cyclic
    have h5₂ : 5 ≤ (Γ.bd Q₂).card := IsAtom.five_le_bd hc4 hA hQ₂A hc₂
    have sub₂ := card_bd_inter_add_card_bd_union (Γ := Γ) A (Γ.Vs \ Y)
    have eI : A ∩ (Γ.Vs \ Y) = Q₂ := by
      ext v; simp only [hQ₂def, Finset.mem_inter, Finset.mem_sdiff]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hAV h.1, h.2⟩⟩
    rw [eI, ← eQ₄c, bd_compl hcl, bd_compl hcl Y, hbA, hbY] at sub₂
    have hnc₄ : ¬ Γ.HasCycle Q₄ := by
      intro h
      have := hc4 Q₄ sQ₄ h (by rw [eQ₄c]; exact hcA.mono Finset.subset_union_left)
      omega
    have hd₁₄ : 2 ≤ d₁₄ := two_le_card_between sQ₁ d14 hnc hnc₄ (by rw [eY]; exact hcY)
    have hQ₄ne : Q₄.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hnc
      rw [← eY, h, Finset.union_empty] at hcY
      exact hcY
    have hsz₄ := card_add_two_le_card_bd hcub sQ₄ hQ₄ne hnc₄
    have hpos := Finset.card_pos.mpr hQ₄ne
    have hQ₄1 : Q₄.card = 1 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hQ₄1
    -- `Q₃` has a cycle: remove `q` from `Vs \ A`
    have hc₃ : Γ.HasCycle Q₃ := by
      have hqV : q ∈ Γ.Vs := sQ₄ (hq ▸ Finset.mem_singleton_self q)
      have hq₃ : q ∉ Q₃ := fun h ↦ Finset.disjoint_left.mp d34 h (hq ▸ Finset.mem_singleton_self q)
      have hAc : Γ.Vs \ A = insert q Q₃ := by
        rw [← eAc, hq, Finset.union_singleton]
      have hdeg : Γ.degIn (Γ.edgesIn (insert q Q₃)) q ≤ 1 := by
        rw [degIn_edgesIn_insert hg hcl hq₃ hqV]
        have : (Γ.between Q₃ {q}).card = d₃₄ := by rw [← hq]
        omega
      have := HasCycle.erase hqV (hAc ▸ hcAc) hdeg
      rwa [Finset.erase_insert hq₃] at this
    have h4₃ := hc4 Q₃ sQ₃ hc₃ (by rw [eQ₃c]; exact hcA.mono Finset.subset_union_left)
    omega
  · -- Case IIb: both `Q₁` and `Q₂` acyclic
    have hd₁₂ : 2 ≤ d₁₂ := two_le_card_between sQ₁ d12 hnc hc₂ (by rw [eA]; exact hcA)
    have fQ₂ : (Γ.edgesIn Q₂).card < Q₂.card := card_edgesIn_lt hQ₂ hc₂
    -- from the handshake: `|A| ≤ 2 d₁₂` and `|A| ≥ 5`
    have hA5 : 5 ≤ A.card := by omega
    have hA2 : A.card ≤ 2 * d₁₂ := by omega
    by_cases hc₄ : Γ.HasCycle Q₄
    · have h4₄ := hc4 Q₄ sQ₄ hc₄ (by rw [eQ₄c]; exact hcA.mono Finset.subset_union_left)
      by_cases hc₃ : Γ.HasCycle Q₃
      · have h4₃ := hc4 Q₃ sQ₃ hc₃ (by rw [eQ₃c]; exact hcA.mono Finset.subset_union_left)
        omega
      · have hd₂₃ : 2 ≤ d₂₃ := two_le_card_between sQ₂ d23 hc₂ hc₃ (by rw [eYc]; exact hcYc)
        omega
    · have hd₁₄ : 2 ≤ d₁₄ := two_le_card_between sQ₁ d14 hnc hc₄ (by rw [eY]; exact hcY)
      by_cases hc₃ : Γ.HasCycle Q₃
      · have h4₃ := hc4 Q₃ sQ₃ hc₃ (by rw [eQ₃c]; exact hcA.mono Finset.subset_union_left)
        omega
      · have hd₂₃ : 2 ≤ d₂₃ := two_le_card_between sQ₂ d23 hc₂ hc₃ (by rw [eYc]; exact hcYc)
        have hd₃₄ : 2 ≤ d₃₄ := two_le_card_between sQ₃ d34 hc₃ hc₄ (by rw [eAc]; exact hcAc)
        omega

omit hcub hg in
/-- Case I of the atom theorem: both quadrants inside the atom are cyclic. -/
theorem IsAtom.no_cross_cyclic (hQ₁ : (A ∩ Y).Nonempty) (hQ₂ : (A \ Y).Nonempty)
    (hc₁ : Γ.HasCycle (A ∩ Y)) (hc₂ : Γ.HasCycle (A \ Y)) : False := by
  have hAV : A ⊆ Γ.Vs := hA.1.1
  have hYV : Y ⊆ Γ.Vs := hY.1
  set Q₃ := Γ.Vs \ (A ∪ Y) with hQ₃def
  set Q₄ := Y \ A with hQ₄def
  have eAc : Q₃ ∪ Q₄ = Γ.Vs \ A := by
    ext v
    simp only [hQ₃def, hQ₄def, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, fun h ↦ h2 (Or.inl h)⟩
      · exact ⟨hYV h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hv : v ∈ Y
      · exact Or.inr ⟨hv, h2⟩
      · exact Or.inl ⟨h1, fun h ↦ h.elim h2 hv⟩
  have eQ₃c : Γ.Vs \ Q₃ = A ∪ Y := by
    rw [hQ₃def, Finset.sdiff_sdiff_eq_self (Finset.union_subset hAV hYV)]
  have eQ₄c : Γ.Vs \ Q₄ = A ∪ (Γ.Vs \ Y) := by
    ext v
    simp only [hQ₄def, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hv : v ∈ A
      · exact Or.inl hv
      · exact Or.inr ⟨h1, fun h ↦ h2 ⟨h, hv⟩⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨hAV h, fun h' ↦ h'.2 h⟩
      · exact ⟨h1, fun h' ↦ h2 h'.1⟩
  have d34 : Disjoint Q₃ Q₄ := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_union_right _ (Finset.mem_sdiff.mp h2).1)
  have sQ₃ : Q₃ ⊆ Γ.Vs := Finset.sdiff_subset
  have sQ₄ : Q₄ ⊆ Γ.Vs := Finset.sdiff_subset.trans hYV
  have hQ₁A : A ∩ Y ⊂ A := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, fun h ↦ ?_⟩
    obtain ⟨v, hv⟩ := hQ₂
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have : v ∈ A ∩ Y := by rw [h]; exact hvA
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp this).2
  have hQ₂A : A \ Y ⊂ A := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.sdiff_subset, fun h ↦ ?_⟩
    obtain ⟨v, hv⟩ := hQ₁
    have hvA : v ∈ A := (Finset.mem_inter.mp hv).1
    have : v ∈ A \ Y := by rw [h]; exact hvA
    exact (Finset.mem_sdiff.mp this).2 (Finset.mem_inter.mp hv).2
  have h5₁ := IsAtom.five_le_bd hc4 hA hQ₁A hc₁
  have h5₂ := IsAtom.five_le_bd hc4 hA hQ₂A hc₂
  have hbA : (Γ.bd A).card = 4 := hA.1.2.1
  have hbY : (Γ.bd Y).card = 4 := hY.2.1
  have hcA : Γ.HasCycle A := hA.1.2.2.1
  have hcAc : Γ.HasCycle (Γ.Vs \ A) := hA.1.2.2.2
  have sub₁ := card_bd_inter_add_card_bd_union (Γ := Γ) A Y
  rw [← eQ₃c, bd_compl hcl, hbA, hbY] at sub₁
  have sub₂ := card_bd_inter_add_card_bd_union (Γ := Γ) A (Γ.Vs \ Y)
  have eI : A ∩ (Γ.Vs \ Y) = A \ Y := by
    ext v; simp only [Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hAV h.1, h.2⟩⟩
  rw [eI, ← eQ₄c, bd_compl hcl, bd_compl hcl Y, hbA, hbY] at sub₂
  have hnc₃ : ¬ Γ.HasCycle Q₃ := by
    intro h
    have := hc4 Q₃ sQ₃ h (by rw [eQ₃c]; exact hcA.mono Finset.subset_union_left)
    omega
  have hnc₄ : ¬ Γ.HasCycle Q₄ := by
    intro h
    have := hc4 Q₄ sQ₄ h (by rw [eQ₄c]; exact hcA.mono Finset.subset_union_left)
    omega
  have hd₃₄ := two_le_card_between sQ₃ d34 hnc₃ hnc₄ (by rw [eAc]; exact hcAc)
  have bAc : (Γ.bd A).card + 2 * (Γ.between Q₃ Q₄).card = (Γ.bd Q₃).card + (Γ.bd Q₄).card := by
    rw [← bd_compl hcl A, ← eAc]; exact card_bd_union d34
  omega

/-- **The atom theorem.**  An atom lies on one side of every cycle-separating `4`-cut. -/
theorem IsAtom.subset_or_subset_compl : A ⊆ Y ∨ A ⊆ Γ.Vs \ Y := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  have hAV : A ⊆ Γ.Vs := hA.1.1
  have hQ₂ : (A \ Y).Nonempty := by
    rw [Finset.not_subset] at h1
    obtain ⟨v, hv, hv'⟩ := h1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩
  have hQ₁ : (A ∩ Y).Nonempty := by
    rw [Finset.not_subset] at h2
    obtain ⟨v, hv, hv'⟩ := h2
    refine ⟨v, Finset.mem_inter.mpr ⟨hv, ?_⟩⟩
    by_contra hvY
    exact hv' (Finset.mem_sdiff.mpr ⟨hAV hv, hvY⟩)
  by_cases hc₁ : Γ.HasCycle (A ∩ Y)
  · by_cases hc₂ : Γ.HasCycle (A \ Y)
    · exact IsAtom.no_cross_cyclic hcl hc4 hA hY hQ₁ hQ₂ hc₁ hc₂
    · -- apply the auxiliary lemma to the complementary cut
      have hY' := cycSep_compl hcl hY
      have e1 : A ∩ (Γ.Vs \ Y) = A \ Y := by
        ext v; simp only [Finset.mem_inter, Finset.mem_sdiff]
        exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hAV h.1, h.2⟩⟩
      have e2 : A \ (Γ.Vs \ Y) = A ∩ Y := by
        ext v; simp only [Finset.mem_inter, Finset.mem_sdiff, not_and, not_not]
        exact ⟨fun h ↦ ⟨h.1, h.2 (hAV h.1)⟩, fun h ↦ ⟨h.1, fun _ ↦ h.2⟩⟩
      exact IsAtom.no_cross_aux hcl hcub hg hc4 hA hY' (e1 ▸ hQ₂) (e2 ▸ hQ₁) (e1 ▸ hc₂)
  · exact IsAtom.no_cross_aux hcl hcub hg hc4 hA hY hQ₁ hQ₂ hc₁

end Atom

end FinGraph
end GraphPuzzles
