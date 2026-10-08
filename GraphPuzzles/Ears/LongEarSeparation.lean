import GraphPuzzles.Ears.LastOddEar
import GraphPuzzles.Matching.Bipartite.FactorCriticalContraction

/-! The two shores associated with a nontrivial last odd ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- A positive-length prefix in a loopless graph contains two distinct
vertices, since it contains an edge. -/
theorem one_lt_oldVertices_card (hq : 1 < q)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : 1 < L.oldVertices.card := by
  have hc := L.earlier.count_le_card
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < L.oldEdges.card by omega)
  have hs := mem_edgesIn.mp (L.earlier.forget.edgesIn he)
  exact Finset.one_lt_card.mpr ⟨_, hs 0, _, hs 1, hl e⟩

/-- The complement of the old prefix consists exactly of the hub and the
internal vertices of the marked ear. -/
theorem oldVertices_compl {v : V} (hT : T = Finset.univ.erase v) :
    Finset.univ \ L.oldVertices = insert v L.ear.interior.toFinset := by
  have hvertices : L.oldVertices ∪ L.ear.interior.toFinset = Finset.univ.erase v :=
    L.vertices_eq.trans hT
  have hv : v ∉ L.oldVertices := by
    intro hv
    have hh := hvertices ▸ Finset.mem_union_left L.ear.interior.toFinset hv
    simp at hh
  ext w
  have ha : w ∈ L.ear.interior.toFinset → w ∉ L.oldVertices :=
    fun hw ↦ L.ear.avoids w (List.mem_toFinset.mp hw)
  have hh := Finset.ext_iff.mp hvertices w
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true] at hh
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hw : w = v
  · subst w
    simp [hv]
  · tauto

/-- The long-ear case supplies a nontrivial cut: the old prefix has an
edge, while its complement contains the hub and an internal vertex. -/
theorem oldVertices_nontrivial {v : V} (hT : T = Finset.univ.erase v)
    (hq : 1 < q) (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hi : L.ear.interior ≠ []) : IsNontrivialCut L.oldVertices := by
  refine ⟨L.one_lt_oldVertices_card hq hl, ?_⟩
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hi
  have hwT : w ∈ Finset.univ.erase v := hT ▸ L.vertices_eq ▸
    Finset.mem_union_right L.oldVertices (List.mem_toFinset.mpr hw)
  rw [L.oldVertices_compl hT]
  exact Finset.one_lt_card.mpr ⟨v, by simp, w, by simp [hw],
    (Finset.mem_erase.mp hwT).1.symm⟩

/-- Completing Proposition 5.10 suffices to discharge the long-ear case
of the odd-wheel theorem, using Proposition 5.11 on both shores. -/
theorem not_solid_of_factorCritical_hub (hb : H.IsBrick) {v : V}
    (hT : T = Finset.univ.erase v) (hq : 1 < q) (hi : L.ear.interior ≠ [])
    (hfc : H.IsFactorCritical (insert v L.ear.interior.toFinset)) : ¬ H.IsSolid := by
  apply hb.not_solid_of_factorCritical_shores
    (L.oldVertices_nontrivial hT hq hb.matchingCovered.loopless hi)
    L.earlier.forget.isFactorCritical
  simpa only [L.oldVertices_compl hT] using hfc

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
