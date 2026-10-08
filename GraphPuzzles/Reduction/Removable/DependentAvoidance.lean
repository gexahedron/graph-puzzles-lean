import GraphPuzzles.Matching.Barriers.VertexMatchingBarrier
import GraphPuzzles.Reduction.Removable.RemovableClass

/-! The dependence-class avoidance argument in Campos–Lucchesi Proposition 5.5. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- If deleting an edge away from a vertex matching and its hub leaves a
factor-critical hub-deleted graph, every edge depending on it also avoids
the matching and the hub. This is the argument of Proposition 5.5. -/
theorem EdgeDepends.avoids_vertexMatching_of_factorCritical_delete {e f : E}
    (hd : H.EdgeDepends f e) (hm : H.IsMatchingCovered) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (he : e ∉ M) (hev : ∀ k, H.endAt e k ≠ v)
    (hfc : (H.deleteEdge e).IsFactorCritical (Finset.univ.erase v)) :
    f ∉ M ∧ ∀ k, H.endAt f k ≠ v := by
  by_cases hfe : f = e
  · subst f
    exact ⟨he, hev⟩
  obtain ⟨P₀, hP₀, _⟩ := hm.2 e
  have heven := hP₀.isFractional.card_even
  obtain ⟨N, hN, hNM⟩ := hM.exists_restrictEdges (S := Finset.univ.erase e)
    (fun g hg ↦ Finset.mem_erase.mpr ⟨fun hh ↦ he (hh ▸ hg), Finset.mem_univ _⟩)
  obtain ⟨P, hP⟩ := hN.exists_perfectMatching_of_factorCritical heven
    (fun g ↦ hm.loopless g.1) hfc
  let a : Finset.univ.erase e := ⟨f, by simp [hfe]⟩
  have ha : ¬ ∃ Q, (H.deleteEdge e).IsPerfectMatching Q ∧ a ∈ Q := by
    rintro ⟨Q, hQ, haQ⟩
    have hfQ : f ∈ Q.image Subtype.val := Finset.mem_image.mpr ⟨a, haQ, rfl⟩
    have heQ := hd _ hQ.of_restrictEdges hfQ
    obtain ⟨g, _, hge⟩ := Finset.mem_image.mp heQ
    exact (Finset.mem_erase.mp g.2).1 hge
  obtain ⟨B, hf0, hf1, F, hB⟩ :=
    hP.exists_barrier_of_inadmissible_edge (e := a) (hm.loopless f) ha
  have hv := hB.hub_not_mem_of_factorCritical F hfc (e := a) (hm.loopless f) hf0 hf1
  have haN := hB.vertexMatching_not_mem F hv hN heven (e := a) hf0 hf1
  refine ⟨?_, fun k hk ↦ ?_⟩
  · intro hfM
    obtain ⟨b, hbN, hbf⟩ := Finset.mem_image.mp (hNM.symm ▸ hfM)
    have hba : b = a := Subtype.ext hbf
    exact haN (hba ▸ hbN)
  · fin_cases k
    · exact hv (hk ▸ hf0)
    · exact hv (hk ▸ hf1)

/-- The one-edge-ear case of the odd-wheel theorem: factor-criticality after
deleting an edge away from the specified matching and hub yields a removable
edge or doubleton avoiding both. No ear decomposition is assumed in this lemma. -/
theorem IsNearBrick.exists_removable_avoiding_of_factorCritical_delete
    (hn : H.IsNearBrick) (h3 : H.IsThreeEdgeConnected) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {e : E} (he : e ∉ M) (hev : ∀ k, H.endAt e k ≠ v)
    (hfc : (H.deleteEdge e).IsFactorCritical (Finset.univ.erase v)) :
    ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧ H.IsRemovableDoubleton f g) := by
  obtain ⟨f, hf, hr | ⟨g, hg, hr⟩⟩ := hn.exists_removable_or_doubleton_dependingOn h3 e
  · obtain ⟨hfM, hfv⟩ := hf.avoids_vertexMatching_of_factorCritical_delete
      hn.matchingCovered hM he hev hfc
    exact ⟨f, hfM, hfv, Or.inl hr⟩
  · obtain ⟨hfM, hfv⟩ := hf.avoids_vertexMatching_of_factorCritical_delete
      hn.matchingCovered hM he hev hfc
    obtain ⟨hgM, hgv⟩ := hg.avoids_vertexMatching_of_factorCritical_delete
      hn.matchingCovered hM he hev hfc
    exact ⟨f, hfM, hfv, Or.inr ⟨g, hgM, hgv, hr⟩⟩

theorem IsBrick.exists_removable_avoiding_of_factorCritical_delete
    (hb : H.IsBrick) {v : V} {M : Finset E} (hM : H.IsVertexMatching v M)
    {e : E} (he : e ∉ M) (hev : ∀ k, H.endAt e k ≠ v)
    (hfc : (H.deleteEdge e).IsFactorCritical (Finset.univ.erase v)) :
    ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧ H.IsRemovableDoubleton f g) :=
  hb.isNearBrick.exists_removable_avoiding_of_factorCritical_delete hb.isThreeEdgeConnected
    hM he hev hfc

end GraphPuzzles.LoopMultigraph
