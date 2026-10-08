import GraphPuzzles.Reduction.Removable.EdgeRestriction

/-! Mutual dependence and removable doubletons of labelled edges. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every perfect matching containing the first edge also contains the second. -/
def EdgeDepends (H : LoopMultigraph V E) (e f : E) : Prop :=
  ∀ M, H.IsPerfectMatching M → e ∈ M → f ∈ M

/-- Two labelled edges occur together in every perfect matching. -/
def MutuallyDependent (H : LoopMultigraph V E) (e f : E) : Prop :=
  ∀ M, H.IsPerfectMatching M → (e ∈ M ↔ f ∈ M)

/-- Delete two labelled edges and retain all vertices. -/
def deletePair (H : LoopMultigraph V E) (e f : E) := H.restrictEdges (Finset.univ \ {e, f})

/-- A removable doubleton has matching-covered deletion, but neither edge is
individually removable. -/
structure IsRemovableDoubleton (H : LoopMultigraph V E) (e f : E) : Prop where
  ne : e ≠ f
  matchingCovered : (H.deletePair e f).IsMatchingCovered
  not_left : ¬ H.IsRemovable e
  not_right : ¬ H.IsRemovable f

theorem IsRemovableDoubleton.symm {e f : E} (hd : H.IsRemovableDoubleton e f) :
    H.IsRemovableDoubleton f e := by
  refine ⟨hd.ne.symm, ?_, hd.not_right, hd.not_left⟩
  change (H.restrictEdges (Finset.univ \ {f, e})).IsMatchingCovered
  rw [Finset.pair_comm f e]
  exact hd.matchingCovered

omit [DecidableEq V] [DecidableEq E] in
theorem IsConnected.restrictEdges_mono {S T : Finset E}
    (hc : (H.restrictEdges S).IsConnected) (hst : S ⊆ T) :
    (H.restrictEdges T).IsConnected := by
  intro c he
  exact hc c (fun e ↦ he ⟨e.1, hst e.2⟩)

/-- Matching-coveredness of an edge restriction, using original edge labels. -/
theorem isMatchingCovered_restrictEdges_of_cover {S : Finset E}
    (hc : (H.restrictEdges S).IsConnected)
    (ha : ∀ e ∈ S, ∃ M, H.IsPerfectMatching M ∧ M ⊆ S ∧ e ∈ M) :
    (H.restrictEdges S).IsMatchingCovered := by
  refine ⟨hc, ?_⟩
  intro e
  obtain ⟨M, hM, hMS, heM⟩ := ha e.1 e.2
  obtain ⟨N, hN, hNM⟩ := hM.exists_restrictEdges hMS
  refine ⟨N, hN, ?_⟩
  have heN : e.1 ∈ N.image Subtype.val := hNM.symm ▸ heM
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp heN
  exact (Subtype.ext hfe : f = e) ▸ hf

theorem IsMatchingCovered.restrictEdges_cover {S : Finset E}
    (hm : (H.restrictEdges S).IsMatchingCovered) {e : E} (he : e ∈ S) :
    ∃ M, H.IsPerfectMatching M ∧ M ⊆ S ∧ e ∈ M := by
  obtain ⟨N, hN, heN⟩ := hm.2 ⟨e, he⟩
  refine ⟨N.image Subtype.val, hN.of_restrictEdges, ?_,
    Finset.mem_image.mpr ⟨⟨e, he⟩, heN, rfl⟩⟩
  intro f hf
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
  exact g.2

omit [DecidableEq E] in
theorem IsMatchingCovered.exists_perfectMatching_of_ne (hm : H.IsMatchingCovered)
    {u v : V} (huv : u ≠ v) : ∃ M, H.IsPerfectMatching M := by
  obtain ⟨e, _⟩ := hm.1.dangling_nonempty (X := {u}) (Finset.singleton_nonempty u)
    ⟨v, by simp [Ne.symm huv]⟩
  obtain ⟨M, hM, _⟩ := hm.2 e
  exact ⟨M, hM⟩

/-- A removable doubleton consists of mutually dependent edges. -/
theorem IsRemovableDoubleton.mutuallyDependent {e f : E}
    (hd : H.IsRemovableDoubleton e f) : H.MutuallyDependent e f := by
  have one {e f : E} (h : H.IsRemovableDoubleton e f) : H.EdgeDepends e f := by
    intro M hM he
    by_contra hf
    apply h.not_right
    have hsub : Finset.univ \ {e, f} ⊆ Finset.univ.erase f := by
      intro g hg
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hg
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    apply isMatchingCovered_restrictEdges_of_cover
      (h.matchingCovered.1.restrictEdges_mono hsub)
    intro g hg
    by_cases hge : g = e
    · subst g
      exact ⟨M, hM, fun a ha ↦ Finset.mem_erase.mpr
        ⟨ne_of_mem_of_not_mem ha hf, Finset.mem_univ _⟩, he⟩
    · have hgS : g ∈ Finset.univ \ {e, f} := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hg
        simp [hge, hg]
      obtain ⟨N, hN, hNS, hgN⟩ := h.matchingCovered.restrictEdges_cover hgS
      exact ⟨N, hN, hNS.trans hsub, hgN⟩
  exact fun M hM ↦ ⟨one hd M hM, one hd.symm M hM⟩

theorem MutuallyDependent.matchingVector_eq {e f : E} (hd : H.MutuallyDependent e f)
    {M : Finset E} (hM : H.IsPerfectMatching M) : matchingVector M e = matchingVector M f := by
  simp only [matchingVector, hd M hM]

/-- Restrict a component family along inclusion of retained edge labels. -/
def ComponentFamily.restrictEdgesSubset {B : Finset V} {S T : Finset E}
    (F : (H.restrictEdges T).ComponentFamily B) (hst : S ⊆ T) :
    (H.restrictEdges S).ComponentFamily B where
  parts := F.parts
  nonempty := F.nonempty
  avoid := F.avoid
  closed := fun Q hQ e k ↦ F.closed Q hQ ⟨e.1, hst e.2⟩ k
  pairwise := F.pairwise
  cover := F.cover

end GraphPuzzles.LoopMultigraph
