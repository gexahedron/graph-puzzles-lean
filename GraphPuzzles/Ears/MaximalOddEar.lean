import GraphPuzzles.Ears.LastOddEar

/-! Moving an old-shore matching edge before the last nonmatching ear raises its index. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

include L in
/-- Complete a marked prefix by adding all remaining matching edges. -/
theorem complete (hG : G ⊆ H.edgesIn T) :
    ∃ n, H.HasIndexedOddEarDecomposition M r n q T G := by
  classical
  let F := G \ (L.oldEdges ∪ L.labels.toFinset)
  exact ⟨q + F.toList.length,
    L.complete_in_order hG F.toList F.nodup_toList (by simp [F])⟩

/-- Move a matching-tail edge with both ends in the old shore before the
marked ear. This produces a valid marked prefix with index increased by one. -/
def advance_by_old_edge {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    (hs : e ∈ H.edgesIn L.oldVertices) : H.LastOutsideOddEar M r (q + 1) T G where
  positive := Nat.succ_pos _
  oldVertices := L.oldVertices
  oldEdges := insert e L.oldEdges
  oldIndex := L.oldIndex
  ear := L.ear
  labels := L.labels
  earlier := by
    have hD := L.earlier.append_matching_edge hs
      (fun hf ↦ (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hf)) (L.tail_mem he)
    simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel L.positive] using hD
  walk := L.walk
  fresh := by
    apply Finset.disjoint_left.mpr
    intro f hf hl
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hl)
    · exact Finset.disjoint_left.mp L.fresh hf hl
  outside := L.outside
  vertices_eq := L.vertices_eq
  edges_subset := by
    intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (Finset.mem_sdiff.mp he).1
      · exact L.edges_subset (Finset.mem_union_left _ hf)
    · exact L.edges_subset (Finset.mem_union_right _ hf)
  tail_mem := by
    intro f hf
    apply L.tail_mem
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hf).1, ?_⟩
    intro hg
    apply (Finset.mem_sdiff.mp hf).2
    rcases Finset.mem_union.mp hg with hg | hg
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hg)
    · exact Finset.mem_union_right _ hg

/-- At a maximum index no later matching edge lies wholly in the older
shore. This is the first rerouting step in Proposition 5.7. -/
theorem tail_edge_not_old (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) :
    e ∉ H.edgesIn L.oldVertices := by
  intro hs
  obtain ⟨n, hD⟩ := (L.advance_by_old_edge he hs).complete hG
  have hle := hmax.2 r n (q + 1) hD
  omega

/-- Consequently every matching-tail edge has an end in the interior of
the last nonmatching ear. -/
theorem tail_edge_has_internal_end (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) :
    ∃ k, H.endAt e k ∈ L.ear.interior := by
  classical
  by_contra hn
  push Not at hn
  apply L.tail_edge_not_old hmax hG he
  apply mem_edgesIn.mpr
  intro k
  have hk := (mem_edgesIn.mp (hG (Finset.mem_sdiff.mp he).1)) k
  rw [← L.vertices_eq] at hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact hk
  · exact (hn k (List.mem_toFinset.mp hk)).elim

/-- In the maximal-index singleton-ear case the matching tail is empty:
the singleton can be moved past any later edge to increase the index. -/
theorem tail_empty_of_singleton (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) (hi : L.ear.interior = []) :
    G \ (L.oldEdges ∪ L.labels.toFinset) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨k, hk⟩ := L.tail_edge_has_internal_end hmax hG he
  simp only [hi, List.not_mem_nil] at hk

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
