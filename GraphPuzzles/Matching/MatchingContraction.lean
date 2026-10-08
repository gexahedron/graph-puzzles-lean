import GraphPuzzles.Matching.MatchingSubgraph

/-! Restricting and gluing perfect matchings across an odd cut. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem dangling_compl (X : Finset V) : H.dangling (Finset.univ \ X) = H.dangling X := by
  ext e
  simp only [mem_dangling, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

omit [DecidableEq E] in
theorem dangling_subset_meets (X : Finset V) : H.dangling X ⊆ H.meets X := by
  intro e he
  rw [mem_dangling] at he
  rw [mem_meets]
  by_cases h0 : H.endAt e 0 ∈ X
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    tauto

theorem contract_degreeIn_image_some (X : Finset V) (M : Finset {e // e ∈ H.meets X})
    (v : {v // v ∈ X}) :
    (H.contract X).degreeIn M (some v) = H.degreeIn (M.image Subtype.val) v.1 := by
  unfold degreeIn
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
    Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [contract_endAt_eq_some_iff]
  · intro e _ f _ h
    exact Subtype.ext h

theorem contract_ends_none (X : Finset V) (e : {e // e ∈ H.meets X}) :
    (∑ k : Fin 2, if (H.contract X).endAt e k = none then (1 : ℕ) else 0) =
      if e.1 ∈ H.dangling X then 1 else 0 := by
  rw [Fin.sum_univ_two]
  simp only [contract_endAt_eq_none_iff, mem_dangling]
  obtain ⟨k, hk⟩ := mem_meets.mp e.2
  by_cases h0 : H.endAt e.1 0 ∈ X <;> by_cases h1 : H.endAt e.1 1 ∈ X
  all_goals simp [h0, h1]
  fin_cases k <;> contradiction

theorem contract_degreeIn_none (X : Finset V) (M : Finset {e // e ∈ H.meets X}) :
    (H.contract X).degreeIn M none = (M.image Subtype.val ∩ H.dangling X).card := by
  unfold degreeIn
  rw [Finset.card_filter, Finset.sum_product]
  simp only [contract_ends_none]
  rw [← Finset.sum_image (f := fun e ↦ if e ∈ H.dangling X then (1 : ℕ) else 0)
    (by intro e _ f _ h; exact Subtype.ext h)]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  rfl

/-- A matching of the contraction is a pole matching using one boundary edge. -/
theorem IsPerfectMatching.contract_to_pole {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M) :
    H.IsPoleMatching X (M.image Subtype.val) ∧
      (M.image Subtype.val ∩ H.dangling X).card = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact f.2
  · intro v hv
    rw [← contract_degreeIn_image_some X M ⟨v, hv⟩, hM]
  · rw [← contract_degreeIn_none, hM]

/-- The unique boundary edge chosen by a perfect matching of a contraction. -/
noncomputable def IsPerfectMatching.contractBoundary {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M) : E :=
  (Finset.card_eq_one.mp hM.contract_to_pole.2).choose

theorem IsPerfectMatching.contract_boundary_inter {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M) :
    M.image Subtype.val ∩ H.dangling X = {hM.contractBoundary} :=
  (Finset.card_eq_one.mp hM.contract_to_pole.2).choose_spec

theorem IsPerfectMatching.contract_boundary_mem {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M) :
    hM.contractBoundary ∈ M.image Subtype.val ∧ hM.contractBoundary ∈ H.dangling X := by
  apply Finset.mem_inter.mp
  rw [hM.contract_boundary_inter]
  exact Finset.mem_singleton_self _

theorem IsPerfectMatching.contract_boundary_iff {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M)
    {e : E} (he : e ∈ H.dangling X) : e ∈ M.image Subtype.val ↔ e = hM.contractBoundary := by
  have h := hM.contract_boundary_inter
  have hi : e ∈ M.image Subtype.val ↔ e ∈ M.image Subtype.val ∩ H.dangling X := by simp [he]
  rw [hi, h, Finset.mem_singleton]

/-- Pole matchings that agree on the boundary glue to a perfect matching. -/
theorem IsPoleMatching.glue {X : Finset V} {P Q : Finset E}
    (hP : H.IsPoleMatching X P) (hQ : H.IsPoleMatching (Finset.univ \ X) Q)
    (hag : ∀ e ∈ H.dangling X, e ∈ P ↔ e ∈ Q) : H.IsPerfectMatching (P ∪ Q) := by
  intro v
  by_cases hv : v ∈ X
  · rw [degreeIn_union_eq_left_of]
    · exact hP.2 v hv
    · rintro e he ⟨k, hk⟩
      have hd : e ∈ H.dangling X := mem_dangling_of_mem_meets
        (X := X) (Y := Finset.univ \ X)
        (fun _ hX hXC ↦ (Finset.mem_sdiff.mp hXC).2 hX) (hQ.1 he) (hk ▸ hv)
      exact (hag e hd).mpr he
  · rw [Finset.union_comm, degreeIn_union_eq_left_of]
    · exact hQ.2 v (by simp [hv])
    · rintro e he ⟨k, hk⟩
      have hm : e ∈ H.meets (Finset.univ \ X) := mem_meets.mpr ⟨k, by simp [hk, hv]⟩
      obtain ⟨j, hj⟩ := mem_meets.mp (hP.1 he)
      have hd : e ∈ H.dangling X := mem_dangling_of_mem_meets
        (X := X) (Y := Finset.univ \ X)
        (fun _ hX hXC ↦ (Finset.mem_sdiff.mp hXC).2 hX) hm hj
      exact (hag e hd).mp he

/-- Matchings of opposite contractions glue when they choose the same boundary edge. -/
theorem glue_contract_matchings {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}}
    {N : Finset {e // e ∈ H.meets (Finset.univ \ X)}}
    (hM : (H.contract X).IsPerfectMatching M)
    (hN : (H.contract (Finset.univ \ X)).IsPerfectMatching N)
    (hag : ∀ e ∈ H.dangling X, e ∈ M.image Subtype.val ↔ e ∈ N.image Subtype.val) :
    H.IsPerfectMatching (M.image Subtype.val ∪ N.image Subtype.val) :=
  hM.contract_to_pole.1.glue hN.contract_to_pole.1 hag

theorem contract_boundary_agreement {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}}
    {N : Finset {e // e ∈ H.meets (Finset.univ \ X)}}
    (hM : (H.contract X).IsPerfectMatching M)
    (hN : (H.contract (Finset.univ \ X)).IsPerfectMatching N)
    (heq : hM.contractBoundary = hN.contractBoundary) :
    ∀ e ∈ H.dangling X, e ∈ M.image Subtype.val ↔ e ∈ N.image Subtype.val := by
  intro e he
  have he' : e ∈ H.dangling (Finset.univ \ X) := by rwa [dangling_compl]
  rw [hM.contract_boundary_iff he, hN.contract_boundary_iff he', heq]

theorem glue_contract_cut_card {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}}
    {N : Finset {e // e ∈ H.meets (Finset.univ \ X)}}
    (hM : (H.contract X).IsPerfectMatching M)
    (hN : (H.contract (Finset.univ \ X)).IsPerfectMatching N)
    (heq : hM.contractBoundary = hN.contractBoundary) :
    ((M.image Subtype.val ∪ N.image Subtype.val) ∩ H.dangling X).card = 1 := by
  have hag := contract_boundary_agreement hM hN heq
  have hsame : (M.image Subtype.val ∪ N.image Subtype.val) ∩ H.dangling X =
      M.image Subtype.val ∩ H.dangling X := by
    ext e
    by_cases he : e ∈ H.dangling X
    · simp [he, ← hag e he]
    · simp [he]
  rw [hsame]
  exact hM.contract_to_pole.2

/-- A contraction matching extends across a matching-covered opposite shore. -/
theorem IsPerfectMatching.extend_contract {X : Finset V}
    {M : Finset {e // e ∈ H.meets X}} (hM : (H.contract X).IsPerfectMatching M)
    (hopp : (H.contract (Finset.univ \ X)).IsMatchingCovered) :
    ∃ P, H.IsPerfectMatching P ∧ M.image Subtype.val ⊆ P ∧ (P ∩ H.dangling X).card = 1 := by
  let e := hM.contractBoundary
  have he := hM.contract_boundary_mem.2
  have he' : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
  obtain ⟨N, hN, heN⟩ := hopp.2 ⟨e, dangling_subset_meets _ he'⟩
  have heN' : e ∈ N.image Subtype.val := Finset.mem_image.mpr ⟨_, heN, rfl⟩
  have heq : hM.contractBoundary = hN.contractBoundary := (hN.contract_boundary_iff he').mp heN'
  exact ⟨_, glue_contract_matchings hM hN (contract_boundary_agreement hM hN heq),
    Finset.subset_union_left, glue_contract_cut_card hM hN heq⟩

/-- Campos--Lucchesi Lemma 4.1, forward direction: every edge lies in a matching
that crosses a separating cut exactly once. -/
theorem IsSeparatingCut.exists_perfectMatching_through {X : Finset V}
    (hs : H.IsSeparatingCut X) (e : E) :
    ∃ P, H.IsPerfectMatching P ∧ e ∈ P ∧ (P ∩ H.dangling X).card = 1 := by
  have oneSide (Y : Finset V) (hsep : H.IsSeparatingCut Y) (he : e ∈ H.meets Y) :
      ∃ P, H.IsPerfectMatching P ∧ e ∈ P ∧ (P ∩ H.dangling Y).card = 1 := by
    obtain ⟨M, hM, heM⟩ := hsep.1.2 ⟨e, he⟩
    obtain ⟨P, hP, hsub, hcard⟩ := hM.extend_contract hsep.2
    exact ⟨P, hP, hsub (Finset.mem_image.mpr ⟨_, heM, rfl⟩), hcard⟩
  by_cases he : e ∈ H.meets X
  · exact oneSide X hs he
  · have he' : e ∈ H.meets (Finset.univ \ X) := by
      apply mem_meets.mpr
      refine ⟨0, ?_⟩
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun h ↦ he (mem_meets.mpr ⟨0, h⟩)
    have hs' : H.IsSeparatingCut (Finset.univ \ X) := by
      refine ⟨hs.2, ?_⟩
      have hh : Finset.univ \ (Finset.univ \ X) = X := by ext v; simp
      rw [hh]
      exact hs.1
    simpa only [dangling_compl] using oneSide (Finset.univ \ X) hs' he'

end GraphPuzzles.LoopMultigraph
