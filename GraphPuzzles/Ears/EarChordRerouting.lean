import GraphPuzzles.Ears.EarExternalRerouting

/-! Matching-tail chords cut off even-length segments of the last nonmatching ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

set_option maxHeartbeats 600000 in
/-- Bypassing an odd segment with a later matching edge and then attaching
that segment as a second ear contradicts maximality of the marked index. -/
theorem no_odd_chord_segment (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {x y : V} (hexy : H.Joins e x y) (hd : H.degreeIn M x ≤ 1)
    (l m t : List V) (hi : L.ear.interior = l ++ x :: (m ++ y :: t))
    (hm : Even m.length) : False := by
  have hn := List.nodup_append.mp (hi ▸ L.ear.nodup)
  have hnx := List.nodup_cons.mp hn.2.1
  have hnm := List.nodup_append.mp hnx.2
  have hc : H.EdgeChain L.ear.start L.labels
      (l ++ x :: (m ++ y :: (t ++ [L.ear.finish]))) := by
    simpa only [hi, List.append_assoc, List.cons_append] using L.walk
  obtain ⟨as, ds, had, ha, hdw⟩ := hc.split l (m ++ y :: (t ++ [L.ear.finish]))
  obtain ⟨bs, cs, hbc, hb, hc⟩ := hdw.split m (t ++ [L.ear.finish])
  have hne : e ∉ L.labels := fun heL ↦
    (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ (List.mem_toFinset.mpr heL))
  have hna : Disjoint L.oldEdges (as ++ e :: cs).toFinset := by
    apply Finset.disjoint_left.mpr
    intro f hf hfl
    rcases List.mem_append.mp (List.mem_toFinset.mp hfl) with hfa | hfl
    · exact Finset.disjoint_left.mp L.fresh hf (by simp [had, hfa])
    · rcases List.mem_cons.mp hfl with rfl | hfc
      · exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hf)
      · exact Finset.disjoint_left.mp L.fresh hf (by simp [had, hbc, hfc])
  have hnb : Disjoint (L.oldEdges ∪ (as ++ e :: cs).toFinset) bs.toFinset := by
    apply Finset.disjoint_left.mpr
    intro f hf hfb
    have hfbs := List.mem_toFinset.mp hfb
    have hnd := List.nodup_append.mp (had ▸ L.ear.labels_nodup L.walk)
    rcases Finset.mem_union.mp hf with hf | hf
    · exact Finset.disjoint_left.mp L.fresh hf (by simp [had, hbc, hfbs])
    · rcases List.mem_append.mp (List.mem_toFinset.mp hf) with hfa | hfl
      · exact hnd.2.2 f hfa f (by simp [hbc, hfbs]) rfl
      · rcases List.mem_cons.mp hfl with rfl | hfc
        · exact hne (by simp [had, hbc, hfbs])
        · exact (List.nodup_append.mp (hbc ▸ hnd.2.1)).2.2 f hfbs f hfc rfl
  have hwa : H.EdgeChain L.ear.start (as ++ e :: cs)
      (l ++ x :: y :: (t ++ [L.ear.finish])) := ha.append (.cons hexy hc)
  let A : H.OddEar L.oldVertices := {
    start := L.ear.start
    finish := L.ear.finish
    interior := l ++ x :: y :: t
    start_mem := L.ear.start_mem
    finish_mem := L.ear.finish_mem
    nodup := by
      refine List.nodup_append.mpr ⟨hn.1, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨fun hx ↦ hnx.1 (List.mem_append_right _ hx), hnm.2.1⟩
      · intro a ha b hb hab
        apply hn.2.2 a ha b ?_ hab
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hb)
    avoids := by
      intro a ha
      apply L.ear.avoids a
      rw [hi]
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      tauto
    even := by
      have hv := L.ear.even
      rw [hi, Nat.even_iff] at hv
      rw [Nat.even_iff] at hm ⊢
      simp only [List.length_append, List.length_cons] at hv ⊢
      omega
    chain := by simpa only [List.cons_append, List.append_assoc] using hwa.isChain }
  let B : H.OddEar A.vertices := {
    start := x
    finish := y
    interior := m
    start_mem := Finset.mem_union_right _ (by simp [A])
    finish_mem := Finset.mem_union_right _ (by simp [A])
    nodup := hnm.1
    avoids := by
      intro a hami has
      rcases Finset.mem_union.mp has with has | has
      · exact L.ear.avoids a (by simp [hi, hami]) has
      · have ham : a ∈ l ∨ a = x ∨ a = y ∨ a ∈ t := by simpa only [A,
          List.mem_toFinset, List.mem_append, List.mem_cons] using has
        rcases ham with hal | hax | hay | hat
        · exact hn.2.2 a hal a (by simp [hami]) rfl
        · exact hnx.1 (List.mem_append_left _ (hax ▸ hami))
        · exact hnm.2.2 a hami y (by simp) hay
        · exact hnm.2.2 a hami a (by simp [hat]) rfl
    even := hm
    chain := hb.isChain }
  have hwa' : H.EdgeChain A.start (as ++ e :: cs) (A.interior ++ [A.finish]) := by
    simpa only [A, List.append_assoc, List.cons_append] using hwa
  have hnbM : ¬ bs.toFinset ⊆ M := hb.not_subset_of_matching_at_start (by simp)
    (L.tail_mem he) (fun hf ↦ hne (by simp [had, hbc, hf])) hexy.exists_end hd
  have hnew : (L.oldEdges ∪ (as ++ e :: cs).toFinset) ∪ bs.toFinset =
      insert e (L.oldEdges ∪ L.labels.toFinset) := by
    ext f
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      List.mem_append, List.mem_cons, had, hbc]
    tauto
  apply L.no_two_ear_replacement hmax hG A (as ++ e :: cs) hwa' hna B bs hb hnb hnbM
  · refine (show B.vertices = L.ear.vertices from ?_).trans L.vertices_eq
    ext a
    simp only [OddEar.vertices, A, B, hi, Finset.mem_union, List.mem_toFinset,
      List.mem_append, List.mem_cons]
    tauto
  · rw [hnew]
    exact Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp he).1, L.edges_subset⟩
  · rw [hnew]
    exact Finset.subset_insert _ _

/-- Proposition 5.7, the parity assertion: the segment between the ordered
internal endpoints of a matching-tail edge has even length. -/
theorem tail_edge_even_segment (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1)
    {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) {x y : V}
    (hexy : H.Joins e x y) (l m t : List V)
    (hi : L.ear.interior = l ++ x :: (m ++ y :: t)) : Even (m.length + 1) := by
  have hx : x ∈ T := L.vertices_eq ▸ Finset.mem_union_right L.oldVertices
    (List.mem_toFinset.mpr (by simp [hi]))
  by_contra hn
  have hm : Even m.length := by
    rw [Nat.even_iff] at hn ⊢
    omega
  exact L.no_odd_chord_segment hmax hG he hexy (hd x hx) l m t hi hm

/-- Both assertions of Proposition 5.7 in one witness: the original labelled
edge joins two distinct internal vertices, and the segment between them has
even length. The lists give their order along the marked ear. -/
theorem tail_edge_internal_even (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1)
    {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) :
    ∃ (l m t : List V) (x y : V), L.ear.interior = l ++ x :: (m ++ y :: t) ∧
      H.Joins e x y ∧ Even (m.length + 1) := by
  have hends := L.tail_edge_ends_internal hmax hG hd he
  have heM := L.tail_mem he
  have hne : H.endAt e 0 ≠ H.endAt e 1 := by
    intro heq
    have hv := (mem_edgesIn.mp (hG (Finset.mem_sdiff.mp he).1)) 0
    have hinc : (e, (0 : Fin 2)) = (e, (1 : Fin 2)) := by
      apply Finset.card_le_one_iff.mp (hd _ hv)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heM, Finset.mem_univ _⟩, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heM, Finset.mem_univ _⟩, heq.symm⟩
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd hinc
    norm_num at h01
  obtain ⟨l, t, hi⟩ := List.append_of_mem (hends 0)
  by_cases hy : H.endAt e 1 ∈ l
  · obtain ⟨a, b, hab⟩ := List.append_of_mem hy
    have hi' : L.ear.interior = a ++ H.endAt e 1 :: (b ++ H.endAt e 0 :: t) := by
      simp only [hi, hab, List.append_assoc, List.cons_append]
    have hj : H.Joins e (H.endAt e 1) (H.endAt e 0) := Or.inr ⟨rfl, rfl⟩
    exact ⟨a, b, t, _, _, hi', hj, L.tail_edge_even_segment hmax hG hd he hj a b t hi'⟩
  · have hyt : H.endAt e 1 ∈ t := by
      have hh := hends 1
      rw [hi] at hh
      rcases List.mem_append.mp hh with hh | hh
      · exact (hy hh).elim
      · rcases List.mem_cons.mp hh with hh | hh
        · exact (hne hh.symm).elim
        · exact hh
    obtain ⟨m, u, hmu⟩ := List.append_of_mem hyt
    have hi' : L.ear.interior = l ++ H.endAt e 0 :: (m ++ H.endAt e 1 :: u) := by
      simp only [hi, hmu]
    have hj : H.Joins e (H.endAt e 0) (H.endAt e 1) := Or.inl ⟨rfl, rfl⟩
    exact ⟨l, m, u, _, _, hi', hj, L.tail_edge_even_segment hmax hG hd he hj l m u hi'⟩

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
