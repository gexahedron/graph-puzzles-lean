import GraphPuzzles.Ears.EarChordRerouting

/-! Re-rooting the first closed ear and excluding matching tails at maximal index one. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {T : Finset V}
variable (L : H.LastOutsideOddEar M r 1 T G)

/-- Re-root the first closed ear at any of its internal vertices, rotating
its original labels and retaining precisely the same matching tail. -/
theorem rotate_first {w : V} (hw : w ∈ L.ear.interior) :
    ∃ L' : H.LastOutsideOddEar M w 1 T G, L'.labels.toFinset = L.labels.toFinset := by
  obtain ⟨hS, hF, hs, ht⟩ := L.first_ear rfl
  obtain ⟨l, t, hi⟩ := List.append_of_mem hw
  have hn := List.nodup_append.mp (hi ▸ L.ear.nodup)
  have hnt := List.nodup_cons.mp hn.2.1
  have hr : r ∉ L.ear.interior := fun hr ↦ L.ear.avoids r hr (by simp [hS])
  have hwr : w ≠ r := fun hh ↦ hr (hh ▸ hw)
  have hc : H.EdgeChain r L.labels (l ++ w :: (t ++ [r])) := by
    simpa only [hs, ht, hi, List.append_assoc, List.cons_append] using L.walk
  obtain ⟨as, bs, hab, ha, hb⟩ := hc.split l (t ++ [r])
  have hc' : H.EdgeChain w (bs ++ as) (t ++ r :: (l ++ [w])) := hb.append ha
  let A : H.OddEar {w} := {
    start := w
    finish := w
    interior := t ++ r :: l
    start_mem := Finset.mem_singleton_self _
    finish_mem := Finset.mem_singleton_self _
    nodup := by
      refine List.nodup_append.mpr ⟨hnt.2, List.nodup_cons.mpr ⟨?_, hn.1⟩, ?_⟩
      · intro hrl
        exact hr (by simp [hi, hrl])
      · intro a ha b hb hab
        rcases List.mem_cons.mp hb with hbr | hbl
        · exact hr (by simp [hi, ← hbr, ← hab, ha])
        · exact hn.2.2 b hbl a (by simp [ha]) hab.symm
    avoids := by
      intro a ha haw
      have haw' := Finset.mem_singleton.mp haw
      subst a
      rcases List.mem_append.mp ha with hwt | hwl
      · exact hnt.1 hwt
      · rcases List.mem_cons.mp hwl with hwr' | hwl
        · exact hwr hwr'
        · exact hn.2.2 w hwl w (by simp) rfl
    even := by
      have he := L.ear.even
      rw [hi, Nat.even_iff] at he
      rw [Nat.even_iff]
      simp only [List.length_append, List.length_cons] at he ⊢
      omega
    chain := by simpa only [List.cons_append, List.append_assoc] using hc'.isChain }
  have hwa : H.EdgeChain A.start (bs ++ as) (A.interior ++ [A.finish]) := by
    simpa only [A, List.append_assoc, List.cons_append] using hc'
  have heq : (bs ++ as).toFinset = L.labels.toFinset := by
    ext e
    simp only [List.mem_toFinset, List.mem_append, hab]
    tauto
  have hv : A.vertices = T := by
    refine (show A.vertices = L.ear.vertices from ?_).trans L.vertices_eq
    ext a
    simp only [OddEar.vertices, A, hS, hi, Finset.mem_union, Finset.mem_singleton,
      List.mem_toFinset, List.mem_append, List.mem_cons]
    tauto
  let L' : H.LastOutsideOddEar M w 1 T G := {
    positive := by decide
    oldVertices := {w}
    oldEdges := ∅
    oldIndex := 0
    ear := A
    labels := bs ++ as
    earlier := .start
    walk := hwa
    fresh := by simp
    outside := by rw [heq]; exact L.outside
    vertices_eq := hv
    edges_subset := by simpa only [Finset.empty_union, heq, hF] using L.edges_subset
    tail_mem := by simpa only [Finset.empty_union, heq, hF] using L.tail_mem }
  exact ⟨L', heq⟩

/-- At maximum index one the first odd closed ear contains all final
edges. Re-rooting at an endpoint of any remaining edge would make that
edge incident with the old shore, contrary to Proposition 5.7. -/
theorem tail_empty_of_index_one (hmax : H.IsMaximumOddEarIndex M T G 1)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) :
    G \ (L.oldEdges ∪ L.labels.toFinset) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hw := L.tail_edge_ends_internal hmax hG hd he 0
  obtain ⟨L', hlabels⟩ := L.rotate_first hw
  have hF := (L.first_ear rfl).2.1
  have hF' := (L'.first_ear rfl).2.1
  have he' : e ∈ G \ (L'.oldEdges ∪ L'.labels.toFinset) := by
    simpa only [hF', hlabels, hF] using he
  have hw' := L'.tail_edge_ends_internal hmax hG hd he' 0
  exact L'.ear.avoids _ hw' (by simp [(L'.first_ear rfl).1])

/-- The index-one marked ear is the entire final edge set. -/
theorem labels_eq_of_index_one (hmax : H.IsMaximumOddEarIndex M T G 1)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) :
    L.labels.toFinset = G := by
  have hF := (L.first_ear rfl).2.1
  have he := L.tail_empty_of_index_one hmax hG hd
  have hs : L.labels.toFinset ⊆ G := by simpa only [hF, Finset.empty_union] using L.edges_subset
  have ht : G ⊆ L.labels.toFinset := by
    simpa only [hF, Finset.empty_union] using Finset.sdiff_eq_empty_iff_subset.mp he
  exact Finset.Subset.antisymm hs ht

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
