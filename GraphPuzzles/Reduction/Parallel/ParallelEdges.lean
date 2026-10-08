import GraphPuzzles.Reduction.Removable.EdgeDependence
import GraphPuzzles.Matching.MatchingOn

/-! Removing one of two parallel labelled edges preserves matching-coveredness. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
/-- Edges with the same unordered ends are parallel, regardless of their orientations. -/
theorem Joins.parallel {e f : E} {u v : V} (he : H.Joins e u v)
    (hf : H.Joins f u v) : H.Joins f (H.endAt e 0) (H.endAt e 1) := by
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simpa only [h0, h1] using hf
  · simpa only [h0, h1] using H.joins_comm.mp hf

/-- In a matching-covered multigraph, an edge with a distinct parallel edge is removable. -/
theorem IsMatchingCovered.isRemovable_of_parallel (hm : H.IsMatchingCovered)
    {e f : E} (hne : e ≠ f) (hp : H.Joins f (H.endAt e 0) (H.endAt e 1)) :
    H.IsRemovable e := by
  apply isMatchingCovered_restrictEdges_of_cover
  · intro c hc
    apply hm.1 c
    intro g
    by_cases hge : g = e
    · subst g
      have hf := hc ⟨f, by simp [hne.symm]⟩
      change c (H.endAt f 0) = c (H.endAt f 1) at hf
      rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simpa only [h0, h1] using hf
      · simpa only [h0, h1] using hf.symm
    · exact hc ⟨g, by simp [hge]⟩
  · intro g hg
    have hge : g ≠ e := (Finset.mem_erase.mp hg).1
    obtain ⟨M, hM, hgM⟩ := hm.2 g
    by_cases heM : e ∈ M
    · have hP := hM.erase_edge heM
      have hS : Finset.univ \ {H.endAt e 0, H.endAt e 1} =
          ((Finset.univ.erase (H.endAt e 0)).erase (H.endAt e 1)) := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_erase, and_true, not_or]
        exact and_comm
      rw [hS] at hP
      refine ⟨insert f (M.erase e), hP.insert_perfect hp (hm.loopless e), ?_, ?_⟩
      · intro a ha
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hne.symm
        · exact (Finset.mem_erase.mp ha).1
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hge, hgM⟩)
    · exact ⟨M, hM, fun a ha ↦ Finset.mem_erase.mpr
        ⟨ne_of_mem_of_not_mem ha heM, Finset.mem_univ _⟩, hgM⟩

end GraphPuzzles.LoopMultigraph
