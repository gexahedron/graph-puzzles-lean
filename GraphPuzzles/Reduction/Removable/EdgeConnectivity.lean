import GraphPuzzles.Reduction.Removable.EdgeDependence
import GraphPuzzles.Matching.MatchingOn

/-! Three-edge-connectivity and perfect matchings avoiding an edge. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every cut with two nonempty shores contains at least three labelled edges. -/
def IsThreeEdgeConnected (H : LoopMultigraph V E) : Prop :=
  ∀ X : Finset V, X.Nonempty → (Finset.univ \ X).Nonempty → 3 ≤ (H.dangling X).card

/-- Deleting any two edges of a three-edge-connected graph leaves it connected. -/
theorem IsThreeEdgeConnected.connected_deletePair (h3 : H.IsThreeEdgeConnected) (e f : E) :
    (H.deletePair e f).IsConnected := by
  intro c he u v
  by_contra huv
  let X := Finset.univ.filter fun w ↦ c w = c u
  have hu : u ∈ X := by simp [X]
  have hv : v ∈ Finset.univ \ X := by simp [X, Ne.symm huv]
  have hsub : H.dangling X ⊆ {e, f} := by
    intro g hg
    by_contra hng
    have hgS : g ∈ Finset.univ \ {e, f} := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hng⟩
    have hh : c (H.endAt g 0) = c (H.endAt g 1) := he ⟨g, hgS⟩
    exact (mem_dangling.mp hg) (by simp only [X, Finset.mem_filter, Finset.mem_univ,
      true_and, hh])
  have hlo := h3 X ⟨u, hu⟩ ⟨v, hv⟩
  have hhi := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

/-- Contracting a nonempty shore preserves three-edge-connectivity. -/
theorem IsThreeEdgeConnected.contract (h3 : H.IsThreeEdgeConnected) (X : Finset V)
    (hXC : (Finset.univ \ X).Nonempty) : (H.contract X).IsThreeEdgeConnected := by
  have side (Y : Finset (Option X)) (hn : none ∉ Y) (hY : Y.Nonempty) :
      3 ≤ ((H.contract X).dangling Y).card := by
    have hZ : (sourceShore X Y).Nonempty := by
      apply Finset.card_pos.mp
      rw [card_sourceShore X Y hn]
      exact Finset.card_pos.mpr hY
    have hZC : (Finset.univ \ sourceShore X Y).Nonempty := by
      obtain ⟨v, hv⟩ := hXC
      exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦
        (Finset.mem_sdiff.mp hv).2 (sourceShore_subset X Y h)⟩⟩
    have hh := contractMatching_crossing (H := H) X Y hn Finset.univ
    simp only [contractMatching, Finset.mem_univ, Finset.filter_true, Finset.univ_inter] at hh
    rw [hh]
    exact h3 _ hZ hZC
  intro Y hY hYC
  by_cases hn : none ∈ Y
  · simpa only [dangling_compl] using side (Finset.univ \ Y) (by simp [hn]) hYC
  · exact side Y hn hY

/-- If deleting an edge preserves connectivity, some perfect matching of a
matching-covered graph avoids that edge. -/
theorem IsMatchingCovered.exists_perfectMatching_omitting (hm : H.IsMatchingCovered)
    {f : E} (hc : (H.deleteEdge f).IsConnected) :
    ∃ M, H.IsPerfectMatching M ∧ f ∉ M := by
  obtain ⟨g, hg⟩ := hc.dangling_nonempty (X := {H.endAt f 0})
    (Finset.singleton_nonempty _) ⟨H.endAt f 1, by simp [Ne.symm (hm.loopless f)]⟩
  have hgf : g.1 ≠ f := (Finset.mem_erase.mp g.2).1
  have hinc : ∃ k : Fin 2, H.endAt g.1 k = H.endAt f 0 := by
    have hh := mem_dangling.mp hg
    change ¬ (H.endAt g.1 0 ∈ ({H.endAt f 0} : Finset V) ↔
      H.endAt g.1 1 ∈ ({H.endAt f 0} : Finset V)) at hh
    by_cases h0 : H.endAt g.1 0 = H.endAt f 0
    · exact ⟨0, h0⟩
    · exact ⟨1, by simpa [h0] using hh⟩
  obtain ⟨k, hk⟩ := hinc
  obtain ⟨M, hM, hgM⟩ := hm.2 g.1
  refine ⟨M, hM, fun hfM ↦ ?_⟩
  exact hgf (congrArg Prod.fst (eq_incidence_of_degreeIn_one (hM _) hgM hfM hk rfl))

end GraphPuzzles.LoopMultigraph
