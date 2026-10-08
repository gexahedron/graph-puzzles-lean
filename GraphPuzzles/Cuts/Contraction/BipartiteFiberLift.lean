import GraphPuzzles.Bricks.RobustNearBrick
import GraphPuzzles.Cuts.Contraction.ContractionBarrierLift

/-! Bipartiteness of a fiber persists when a bipartite contracted shore is expanded. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem IsBipartiteOn.expandedContractShore_of_pole_not_mem {X : Finset V}
    {Q : Finset (Option X)} (hb : (H.contract X).IsBipartiteOn Q) (hn : none ∉ Q) :
    H.IsBipartiteOn (LoopMultigraph.expandedContractShore X Q) := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c ∘ contractVertex X, ?_⟩
  intro e h0 h1
  have h0Q := (mem_expandedContractShore X Q _).mp h0
  have h1Q := (mem_expandedContractShore X Q _).mp h1
  have h0X : H.endAt e 0 ∈ X := by
    by_contra hh
    exact hn (by simpa only [contractVertex, dif_neg hh] using h0Q)
  exact hc ⟨e, mem_meets.mpr ⟨0, h0X⟩⟩ h0Q h1Q

omit [DecidableEq E] in
/-- An induced bipartite region lifts through a contraction whose discarded
shore has a bipartite contraction. This includes regions containing the pole. -/
theorem IsBipartiteOn.expandedContractShore {X : Finset V} {Q : Finset (Option X)}
    (hb : (H.contract X).IsBipartiteOn Q)
    (hC : (H.contract (Finset.univ \ X)).IsBipartite) :
    H.IsBipartiteOn (LoopMultigraph.expandedContractShore X Q) := by
  by_cases hn : none ∈ Q
  · have hsub : Finset.univ \ X ⊆ LoopMultigraph.expandedContractShore X Q := by
      intro v hv
      have hvX := (Finset.mem_sdiff.mp hv).2
      simpa only [mem_expandedContractShore, contractVertex, dif_neg hvX] using hn
    have hI : (H.contract ((Finset.univ \ X) ∩ LoopMultigraph.expandedContractShore X Q)).IsBipartite := by
      rwa [Finset.inter_eq_left.mpr hsub]
    apply IsBipartiteOn.glue_contract_region hI
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
    have he : poleShore X (LoopMultigraph.expandedContractShore X Q) = Q := by
      ext v
      cases v with
      | none => simp [hn]
      | some v =>
        simp only [some_mem_poleShore, mem_expandedContractShore, contractVertex_some]
    rwa [he]
  · exact hb.expandedContractShore_of_pole_not_mem hn

end GraphPuzzles.LoopMultigraph
