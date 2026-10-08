import GraphPuzzles.Reduction.Removable.RemovableContraction

/-! Basic removable-edge lifting across separating cuts. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- An internal edge removable on one side of a separating cut is
removable in the original graph. -/
theorem IsSeparatingCut.removable_of_internal {X : Finset V}
    (hs : H.IsSeparatingCut X) (hXC : (Finset.univ \ X).Nonempty)
    {e : H.meets X} (hi : ∀ k, H.endAt e.1 k ∈ X)
    (hr : (H.contract X).IsRemovable e) : H.IsRemovable e.1 := by
  have heXC : e.1 ∉ H.meets (Finset.univ \ X) := by
    intro he
    obtain ⟨k, hk⟩ := mem_meets.mp he
    exact (Finset.mem_sdiff.mp hk).2 (hi k)
  have hl : ((H.deleteEdge e.1).contract X).IsMatchingCovered :=
    (deleteContractIso X e).symm.isMatchingCovered hr
  have hright : ((H.deleteEdge e.1).contract (Finset.univ \ X)).IsMatchingCovered :=
    (deleteAwayContractIso (Finset.univ \ X) e.1 heXC).symm.isMatchingCovered hs.2
  exact (show (H.deleteEdge e.1).IsSeparatingCut X from ⟨hl, hright⟩).isMatchingCovered hXC

/-- A cut edge removable in both contractions is removable before
splicing the two sides. -/
theorem removable_of_both_contractions {X : Finset V}
    (hXC : (Finset.univ \ X).Nonempty) {e : E}
    (hl : e ∈ H.meets X) (hr : e ∈ H.meets (Finset.univ \ X))
    (hleft : (H.contract X).IsRemovable ⟨e, hl⟩)
    (hright : (H.contract (Finset.univ \ X)).IsRemovable ⟨e, hr⟩) :
    H.IsRemovable e := by
  have hsep : (H.deleteEdge e).IsSeparatingCut X :=
    ⟨(deleteContractIso X ⟨e, hl⟩).symm.isMatchingCovered hleft,
      (deleteContractIso (Finset.univ \ X) ⟨e, hr⟩).symm.isMatchingCovered hright⟩
  exact hsep.isMatchingCovered hXC

end GraphPuzzles.LoopMultigraph
