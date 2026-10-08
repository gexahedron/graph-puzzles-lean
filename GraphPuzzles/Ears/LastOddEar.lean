import GraphPuzzles.Ears.IndexedOddEar
import GraphPuzzles.Reduction.Removable.EdgeRestriction

/-! The last nonmatching ear and the single-edge tail of an odd-ear decomposition. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The prefix ending in the last ear outside `M`. All final vertices have
already appeared, and all remaining edges belong to `M`. -/
structure LastOutsideOddEar (H : LoopMultigraph V E) (M : Finset E)
    (r : V) (q : ℕ) (T : Finset V) (G : Finset E) where
  positive : 0 < q
  oldVertices : Finset V
  oldEdges : Finset E
  oldIndex : ℕ
  ear : H.OddEar oldVertices
  labels : List E
  earlier : H.HasIndexedOddEarDecomposition M r (q - 1) oldIndex oldVertices oldEdges
  walk : H.EdgeChain ear.start labels (ear.interior ++ [ear.finish])
  fresh : Disjoint oldEdges labels.toFinset
  outside : ¬ labels.toFinset ⊆ M
  vertices_eq : ear.vertices = T
  edges_subset : oldEdges ∪ labels.toFinset ⊆ G
  tail_mem : G \ (oldEdges ∪ labels.toFinset) ⊆ M

/-- Proposition 5.4: every ear after the last nonmatching ear is a singleton,
so the prefix ending in that ear spans the final vertex set. -/
theorem HasIndexedOddEarDecomposition.lastOutside {M G : Finset E} {r : V}
    {n q : ℕ} {T : Finset V}
    (h : H.HasIndexedOddEarDecomposition M r n q T G) (hq : 0 < q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) : Nonempty (H.LastOutsideOddEar M r q T G) := by
  induction h with
  | start => omega
  | @attach_outside n q S F old A es hw hf hm _ =>
    exact ⟨{
      positive := Nat.succ_pos _
      oldVertices := S
      oldEdges := F
      oldIndex := q
      ear := A
      labels := es
      earlier := by simpa using old
      walk := hw
      fresh := hf
      outside := hm
      vertices_eq := rfl
      edges_subset := Finset.Subset.refl _
      tail_mem := by simp }⟩
  | @attach_mem n q S F old A es hw hf hm ih =>
    have hAS := A.vertices_eq_of_labels_subset hw hm (fun w hw ↦
      hd w (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)))
    obtain ⟨L⟩ := ih hq (fun w hw ↦ hd w (Finset.mem_union_left _ hw))
    exact ⟨{
      positive := L.positive
      oldVertices := L.oldVertices
      oldEdges := L.oldEdges
      oldIndex := L.oldIndex
      ear := L.ear
      labels := L.labels
      earlier := L.earlier
      walk := L.walk
      fresh := L.fresh
      outside := L.outside
      vertices_eq := L.vertices_eq.trans hAS.symm
      edges_subset := L.edges_subset.trans Finset.subset_union_left
      tail_mem := by
        intro e he
        obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp he with he | he
        · exact L.tail_mem (Finset.mem_sdiff.mpr ⟨he, hn⟩)
        · exact hm he }⟩

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- Index one means that the marked ear is a closed ear attached at the
initial singleton, with no preceding edges. -/
theorem first_ear (hq : q = 1) : L.oldVertices = {r} ∧ L.oldEdges = ∅ ∧
    L.ear.start = r ∧ L.ear.finish = r := by
  subst q
  obtain ⟨hS, hF⟩ := L.earlier.count_zero
  exact ⟨hS, hF, Finset.mem_singleton.mp (hS ▸ L.ear.start_mem),
    Finset.mem_singleton.mp (hS ▸ L.ear.finish_mem)⟩

/-- The graph just before the matching tail has exactly the marked index. -/
theorem prefix_attach :
    H.HasIndexedOddEarDecomposition M r q q T (L.oldEdges ∪ L.labels.toFinset) := by
  have hh := L.earlier.attach_outside L.ear L.labels L.walk L.fresh L.outside
  simpa only [Nat.sub_add_cancel L.positive, L.vertices_eq] using hh

/-- Every permutation of the remaining edge labels is an admissible matching
tail. This describes the actual decomposition, including its original labels. -/
theorem complete_in_order (hG : G ⊆ H.edgesIn T) (es : List E) (hn : es.Nodup)
    (he : es.toFinset = G \ (L.oldEdges ∪ L.labels.toFinset)) :
    H.HasIndexedOddEarDecomposition M r (q + es.length) q T G := by
  have hD := L.prefix_attach.append_matching_edges es hn (by
    rw [he]
    exact Finset.disjoint_left.mpr fun _ hf hg ↦ (Finset.mem_sdiff.mp hg).2 hf)
    (by rw [he]; exact fun _ hf ↦ hG (Finset.mem_sdiff.mp hf).1)
    (by rw [he]; exact L.tail_mem)
  have hg : (L.oldEdges ∪ L.labels.toFinset) ∪ es.toFinset = G := by
    rw [he, Finset.union_sdiff_of_subset L.edges_subset]
  exact hg ▸ hD

/-- A singleton last nonmatching ear may be deleted: its preceding prefix
already spans the final vertices and uses none of that edge. Maximality of
the index is not needed for this factor-criticality conclusion. -/
theorem factorCritical_delete_of_singleton (hi : L.ear.interior = []) :
    ∃ e, L.labels = [e] ∧ e ∉ M ∧ e ∈ G ∧ (H.deleteEdge e).IsFactorCritical T := by
  obtain ⟨e, he⟩ := L.ear.labels_singleton_of_interior_nil L.walk hi
  have heM : e ∉ M := by
    intro hem
    exact L.outside (by simpa [he] using hem)
  have heG : e ∈ G := L.edges_subset (Finset.mem_union_right _ (by simp [he]))
  have heF : e ∉ L.oldEdges := fun hef ↦
    Finset.disjoint_left.mp L.fresh hef (by simp [he])
  have hT : L.oldVertices = T := by simpa [OddEar.vertices, hi] using L.vertices_eq
  have hc := L.earlier.forget.isFactorCritical_restrictEdges.restrictEdges_mono
    (G := Finset.univ.erase e) (fun f hf ↦
      Finset.mem_erase.mpr ⟨fun hfe ↦ heF (hfe ▸ hf), Finset.mem_univ _⟩)
  exact ⟨e, he, heM, heG, hT ▸ hc⟩

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
