import GraphPuzzles.Matching.Bipartite.VertexMatchingBipartite

/-! Replacing one side of a perfect matching while retaining every boundary label. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsPerfectMatching.poleMatching_inter_meets {M : Finset E}
    (hM : H.IsPerfectMatching M) (X : Finset V) :
    H.IsPoleMatching X (M ∩ H.meets X) := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro w hw
  have he : H.degreeIn (M ∩ H.meets X) w = H.degreeIn M w := by
    unfold degreeIn
    congr 1
    ext ⟨e, k⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_inter]
    constructor
    · exact fun hh ↦ ⟨hh.1.1, hh.2⟩
    · rintro ⟨hm, hk⟩
      exact ⟨⟨hm, mem_meets.mpr ⟨k, hk.symm ▸ hw⟩⟩, hk⟩
  exact he.trans (hM w)

/-- A vertex matching at a contraction pole replaces the retained side
of an original perfect matching if all boundary labels agree. -/
theorem IsVertexMatching.extend_preserving_boundary {R : Finset V}
    {N : Finset (H.meets R)} (hN : (H.contract R).IsVertexMatching none N)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (hag : ∀ e (he : e ∈ H.dangling R),
      (⟨e, dangling_subset_meets R he⟩ : H.meets R) ∈ N ↔ e ∈ M) :
    ∃ P, H.IsPerfectMatching P ∧ H.contractMatching R P = N := by
  let Q := M ∩ H.meets (Finset.univ \ R)
  have hQ : H.IsPoleMatching (Finset.univ \ R) Q := hM.poleMatching_inter_meets _
  have hP : H.IsPoleMatching R (N.image Subtype.val) := by
    refine ⟨?_, ?_⟩
    · intro e he
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
      exact f.2
    · intro w hw
      rw [← contract_degreeIn_image_some R N ⟨w, hw⟩]
      exact hN (some ⟨w, hw⟩) (by simp)
  have hmem (e : H.meets R) : e.1 ∈ N.image Subtype.val ↔ e ∈ N := by
    constructor
    · intro he
      obtain ⟨f, hf, he⟩ := Finset.mem_image.mp he
      exact (Subtype.ext he : f = e) ▸ hf
    · intro he
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hmatch : H.IsPerfectMatching (N.image Subtype.val ∪ Q) := by
    apply hP.glue hQ
    intro e he
    have hcompl : e ∈ H.meets (Finset.univ \ R) := by
      apply dangling_subset_meets
      simpa only [dangling_compl] using he
    rw [hmem ⟨e, dangling_subset_meets R he⟩, hag e he]
    simp only [Q, Finset.mem_inter, hcompl, and_true]
  refine ⟨_, hmatch, ?_⟩
  ext e
  rw [mem_contractMatching, Finset.mem_union, hmem]
  constructor
  · rintro (he | he)
    · exact he
    · have hm := (Finset.mem_inter.mp he).1
      have hec := (Finset.mem_inter.mp he).2
      obtain ⟨k, hk⟩ := mem_meets.mp e.2
      have hed := mem_dangling_of_mem_meets
        (X := R) (Y := Finset.univ \ R)
        (fun _ hx hxc ↦ (Finset.mem_sdiff.mp hxc).2 hx) hec hk
      exact (hag e.1 hed).mpr hm
  · exact Or.inl

end GraphPuzzles.LoopMultigraph
