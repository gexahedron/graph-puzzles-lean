import GraphPuzzles.Cuts.TightCutDecomposition

/-!
# Transport of matchings and cuts through contractions

Matching extension across a separating cut preserves exactly the selected edges
on the retained shore. Consequently tight cuts descend through separating cuts
and lift through tight cuts, with their crossing counts preserved.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Represent the retained part of a vertex set as a shore avoiding the contraction pole. -/
noncomputable def contractShore (X Z : Finset V) : Finset (Option X) := by
  classical
  exact Finset.univ.filter fun v ↦ match v with
    | none => False
    | some v => v.1 ∈ Z

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem none_not_mem_contractShore (X Z : Finset V) : none ∉ contractShore X Z := by
  simp [contractShore]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem some_mem_contractShore (X Z : Finset V) (v : X) :
    some v ∈ contractShore X Z ↔ v.1 ∈ Z := by simp [contractShore]

omit [Fintype V] in
theorem sourceShore_contractShore (X Z : Finset V) :
    sourceShore X (contractShore X Z) = X ∩ Z := by
  ext v
  simp only [sourceShore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, some_mem_contractShore, Finset.mem_inter]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hv, hz⟩
    exact ⟨⟨v, hv⟩, hz, rfl⟩

/-- Restrict an edge set to the edge type of a shore contraction. -/
def contractMatching (X : Finset V) (M : Finset E) : Finset (H.meets X) :=
  Finset.univ.filter fun e ↦ e.1 ∈ M

@[simp]
theorem mem_contractMatching (X : Finset V) (M : Finset E) (e : H.meets X) :
    e ∈ H.contractMatching X M ↔ e.1 ∈ M := by simp [contractMatching]

theorem matchingVector_contractMatching (X : Finset V) (M : Finset E) :
    matchingVector (H.contractMatching X M) = fun e ↦ matchingVector M e.1 := by
  funext e
  simp only [matchingVector, mem_contractMatching]

/-- A perfect matching cannot properly contain another perfect matching. -/
theorem IsPerfectMatching.eq_of_subset {M N : Finset E} (hM : H.IsPerfectMatching M)
    (hN : H.IsPerfectMatching N) (hs : M ⊆ N) : M = N := by
  have hle (e : E) : matchingVector M e ≤ matchingVector N e := by
    by_cases he : e ∈ M
    · simp [matchingVector, he, hs he]
    · simpa only [matchingVector, if_neg he] using hN.isFractional.nonneg e
  have hh := eq_of_le_of_weightedDegree_eq hle
    (fun v ↦ (hN.isFractional.degree v).trans (hM.isFractional.degree v).symm)
  ext e
  have he := congr_fun hh e
  by_cases h : e ∈ M <;> by_cases h' : e ∈ N <;> simp_all [matchingVector]

theorem IsPerfectMatching.contractMatching_eq_of_subset {X : Finset V}
    {M : Finset (H.meets X)} (hM : (H.contract X).IsPerfectMatching M)
    {P : Finset E} (hP : H.IsPerfectMatching P) (hc : (P ∩ H.dangling X).card = 1)
    (hsub : M.image Subtype.val ⊆ P) : H.contractMatching X P = M := by
  apply (hM.eq_of_subset (hP.contract_of_crossing_one X hc) ?_).symm
  intro e he
  exact (mem_contractMatching X P e).mpr (hsub (Finset.mem_image.mpr ⟨e, he, rfl⟩))

/-- An extended contraction matching has exactly the original restriction. -/
theorem IsPerfectMatching.extend_contract_exact {X : Finset V}
    {M : Finset (H.meets X)} (hM : (H.contract X).IsPerfectMatching M)
    (hopp : (H.contract (Finset.univ \ X)).IsMatchingCovered) :
    ∃ P, H.IsPerfectMatching P ∧ (P ∩ H.dangling X).card = 1 ∧
      H.contractMatching X P = M := by
  obtain ⟨P, hP, hsub, hc⟩ := hM.extend_contract hopp
  exact ⟨P, hP, hc, hM.contractMatching_eq_of_subset hP hc hsub⟩

/-- Any cut avoiding the contraction vertex has the same crossing count before and after
restriction. This identity does not require the edge set to be a matching. -/
theorem contractMatching_crossing (X : Finset V) (Y : Finset (Option X))
    (hn : none ∉ Y) (M : Finset E) :
    (H.contractMatching X M ∩ (H.contract X).dangling Y).card =
      (M ∩ H.dangling (sourceShore X Y)).card := by
  have hh := contract_cutWeight_sourceShore (H := H) X Y hn (matchingVector M)
  rw [← matchingVector_contractMatching] at hh
  simp only [cutWeight_matchingVector] at hh
  exact_mod_cast hh

/-- Tight cuts of a tight-cut contraction are tight in the original graph. -/
theorem IsTightCut.lift_contract {X : Finset V} (ht : H.IsTightCut X)
    {Y : Finset (Option X)} (hY : (H.contract X).IsTightCut Y) (hn : none ∉ Y) :
    H.IsTightCut (sourceShore X Y) := by
  intro M hM
  rw [← contractMatching_crossing X Y hn M]
  exact hY _ (hM.contract_of_crossing_one X (ht M hM))

/-- A tight cut descends whenever matchings extend from the retained shore. -/
theorem IsTightCut.descend_contract {X : Finset V} {Y : Finset (Option X)}
    (ht : H.IsTightCut (sourceShore X Y)) (hn : none ∉ Y)
    (hopp : (H.contract (Finset.univ \ X)).IsMatchingCovered) :
    (H.contract X).IsTightCut Y := by
  intro M hM
  obtain ⟨P, hP, _, heq⟩ := hM.extend_contract_exact hopp
  rw [← heq, contractMatching_crossing X Y hn P]
  exact ht P hP

/-- Tightness is preserved in both directions through a separating tight cut. -/
theorem IsTightCut.contract_iff {X : Finset V} (ht : H.IsTightCut X)
    (hs : H.IsSeparatingCut X) (Y : Finset (Option X)) (hn : none ∉ Y) :
    (H.contract X).IsTightCut Y ↔ H.IsTightCut (sourceShore X Y) :=
  ⟨fun h ↦ ht.lift_contract h hn, fun h ↦ h.descend_contract hn hs.2⟩

/-- Every crossing count realized in a contraction is realized in the original graph. -/
theorem exists_matching_crossing_of_contract {X : Finset V} {Y : Finset (Option X)}
    (hn : none ∉ Y) (hopp : (H.contract (Finset.univ \ X)).IsMatchingCovered)
    {n : ℕ} (h : ∃ M, (H.contract X).IsPerfectMatching M ∧
      (M ∩ (H.contract X).dangling Y).card = n) :
    ∃ P, H.IsPerfectMatching P ∧ (P ∩ H.dangling (sourceShore X Y)).card = n := by
  obtain ⟨M, hM, hm⟩ := h
  obtain ⟨P, hP, _, heq⟩ := hM.extend_contract_exact hopp
  exact ⟨P, hP, by rw [← contractMatching_crossing X Y hn, heq, hm]⟩

/-- Through a tight separating cut the sets of crossing counts agree exactly. -/
theorem IsTightCut.exists_matching_crossing_iff {X : Finset V} (ht : H.IsTightCut X)
    (hs : H.IsSeparatingCut X) (Y : Finset (Option X)) (hn : none ∉ Y) (n : ℕ) :
    (∃ M, (H.contract X).IsPerfectMatching M ∧ (M ∩ (H.contract X).dangling Y).card = n) ↔
      ∃ P, H.IsPerfectMatching P ∧ (P ∩ H.dangling (sourceShore X Y)).card = n := by
  constructor
  · exact exists_matching_crossing_of_contract hn hs.2
  · rintro ⟨P, hP, hp⟩
    exact ⟨_, hP.contract_of_crossing_one X (ht P hP),
      (contractMatching_crossing X Y hn P).trans hp⟩

/-- A pair of cohesive, nested cuts remains separating after contracting the outer shore.
The inner shore is represented in the contraction without its pole. -/
theorem IsCohesiveCuts.separating_contract {X : Finset V} {Y : Finset (Option X)}
    (hC : H.IsCohesiveCuts {X, sourceShore X Y}) (hc : (H.contract X).IsConnected)
    (hY : Y.Nonempty) (hYC : (Finset.univ \ Y).Nonempty) (hn : none ∉ Y) :
    (H.contract X).IsSeparatingCut Y := by
  apply isSeparatingCut_of_crossing_one hc hY hYC
  intro e
  obtain ⟨M, hM, he, hm⟩ := hC e.1
  refine ⟨H.contractMatching X M, hM.contract_of_crossing_one X (hm X (by simp)),
    (mem_contractMatching X M e).mpr he, ?_⟩
  rw [contractMatching_crossing X Y hn M]
  exact hm _ (by simp)

end GraphPuzzles.LoopMultigraph
