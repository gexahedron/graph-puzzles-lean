import GraphPuzzles.Ears.MaximalOddEar
import GraphPuzzles.Ears.EdgeChainOperations

/-! Reversal and the two-ear replacement test for a maximal last nonmatching ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem HasIndexedOddEarDecomposition.attach_with_index {M F : Finset E}
    {r : V} {n q : ℕ} {S : Finset V}
    (hD : H.HasIndexedOddEarDecomposition M r n q S F) (A : H.OddEar S) (es : List E)
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish])) (hf : Disjoint F es.toFinset) :
    ∃ j, H.HasIndexedOddEarDecomposition M r (n + 1) j A.vertices (F ∪ es.toFinset) := by
  classical
  by_cases hm : es.toFinset ⊆ M
  · exact ⟨q, hD.attach_mem A es hw hf hm⟩
  · exact ⟨n + 1, hD.attach_outside A es hw hf hm⟩

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- Reversing the marked ear preserves its index, old prefix and matching tail. -/
def reverse : H.LastOutsideOddEar M r q T G where
  positive := L.positive
  oldVertices := L.oldVertices
  oldEdges := L.oldEdges
  oldIndex := L.oldIndex
  ear := L.ear.reverse
  labels := L.labels.reverse
  earlier := L.earlier
  walk := L.ear.reverse_walk L.walk
  fresh := by simpa using L.fresh
  outside := by simpa using L.outside
  vertices_eq := L.ear.reverse_vertices.trans L.vertices_eq
  edges_subset := by simpa using L.edges_subset
  tail_mem := by simpa using L.tail_mem

/-- Replace the marked ear by two odd ears that cover all its vertices
and labels. If the second ear is outside the matching, the index increases. -/
theorem two_ear_replacement (A : H.OddEar L.oldVertices) (as : List E)
    (ha : H.EdgeChain A.start as (A.interior ++ [A.finish]))
    (hfa : Disjoint L.oldEdges as.toFinset)
    (B : H.OddEar A.vertices) (bs : List E)
    (hb : H.EdgeChain B.start bs (B.interior ++ [B.finish]))
    (hfb : Disjoint (L.oldEdges ∪ as.toFinset) bs.toFinset) (hm : ¬ bs.toFinset ⊆ M)
    (hv : B.vertices = T)
    (hs : (L.oldEdges ∪ as.toFinset) ∪ bs.toFinset ⊆ G)
    (hc : L.oldEdges ∪ L.labels.toFinset ⊆ (L.oldEdges ∪ as.toFinset) ∪ bs.toFinset) :
    Nonempty (H.LastOutsideOddEar M r (q + 1) T G) := by
  obtain ⟨j, hD⟩ := L.earlier.attach_with_index A as ha hfa
  exact ⟨{
    positive := Nat.succ_pos _
    oldVertices := A.vertices
    oldEdges := L.oldEdges ∪ as.toFinset
    oldIndex := j
    ear := B
    labels := bs
    earlier := by simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel L.positive] using hD
    walk := hb
    fresh := hfb
    outside := hm
    vertices_eq := hv
    edges_subset := hs
    tail_mem := fun e he ↦ L.tail_mem (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp he).1, fun hg ↦ (Finset.mem_sdiff.mp he).2 (hc hg)⟩) }⟩

/-- Maximality excludes every such two-ear replacement. -/
theorem no_two_ear_replacement (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T)
    (A : H.OddEar L.oldVertices) (as : List E)
    (ha : H.EdgeChain A.start as (A.interior ++ [A.finish]))
    (hfa : Disjoint L.oldEdges as.toFinset)
    (B : H.OddEar A.vertices) (bs : List E)
    (hb : H.EdgeChain B.start bs (B.interior ++ [B.finish]))
    (hfb : Disjoint (L.oldEdges ∪ as.toFinset) bs.toFinset) (hm : ¬ bs.toFinset ⊆ M)
    (hv : B.vertices = T)
    (hs : (L.oldEdges ∪ as.toFinset) ∪ bs.toFinset ⊆ G)
    (hc : L.oldEdges ∪ L.labels.toFinset ⊆ (L.oldEdges ∪ as.toFinset) ∪ bs.toFinset) : False := by
  obtain ⟨L'⟩ := L.two_ear_replacement A as ha hfa B bs hb hfb hm hv hs hc
  obtain ⟨n, hD⟩ := L'.complete hG
  have hle := hmax.2 r n (q + 1) hD
  omega

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
