import GraphPuzzles.Ears.EarRerouting

/-! A matching-tail edge cannot join the last ear's interior to its older shore. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- If the segment from the old endpoint to `w` has even length, replacing
the marked ear by that segment followed by a tail edge to the old shore,
then its odd remaining segment, increases the index. -/
theorem no_old_end_of_odd_prefix (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {w z : V} (hez : H.Joins e w z) (hz : z ∈ L.oldVertices)
    (hd : H.degreeIn M w ≤ 1) (l t : List V)
    (hi : L.ear.interior = l ++ w :: t) (hl : Odd l.length) : False := by
  have hn := List.nodup_append.mp (hi ▸ L.ear.nodup)
  have hnt := List.nodup_cons.mp hn.2.1
  have hc : H.EdgeChain L.ear.start L.labels (l ++ w :: (t ++ [L.ear.finish])) := by
    simpa only [hi, List.append_assoc, List.cons_append] using L.walk
  obtain ⟨as, bs, hab, ha, hb⟩ := hc.split l (t ++ [L.ear.finish])
  have hne : e ∉ L.labels := fun hm ↦
    (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ (List.mem_toFinset.mpr hm))
  have hna : Disjoint L.oldEdges (as ++ [e]).toFinset := by
    apply Finset.disjoint_left.mpr
    intro f hf hfl
    rcases List.mem_append.mp (List.mem_toFinset.mp hfl) with hfl | hfl
    · exact Finset.disjoint_left.mp L.fresh hf (by simp [hab, hfl])
    · have hfe := List.mem_singleton.mp hfl
      subst f
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hf)
  have hnb : Disjoint (L.oldEdges ∪ (as ++ [e]).toFinset) bs.toFinset := by
    apply Finset.disjoint_left.mpr
    intro f hf hfb
    have hfbs := List.mem_toFinset.mp hfb
    rcases Finset.mem_union.mp hf with hf | hf
    · exact Finset.disjoint_left.mp L.fresh hf (by simp [hab, hfbs])
    · rcases List.mem_append.mp (List.mem_toFinset.mp hf) with hfa | hfe
      · have hnd := List.nodup_append.mp (hab ▸ L.ear.labels_nodup L.walk)
        exact hnd.2.2 f hfa f hfbs rfl
      · have hfe' := List.mem_singleton.mp hfe
        subst f
        exact hne (by simp [hab, hfbs])
  have hwa : H.EdgeChain L.ear.start (as ++ [e]) (l ++ w :: [z]) :=
    ha.append (.cons hez (.nil _))
  let A : H.OddEar L.oldVertices := {
    start := L.ear.start
    finish := z
    interior := l ++ [w]
    start_mem := L.ear.start_mem
    finish_mem := hz
    nodup := List.nodup_append.mpr ⟨hn.1, by simp, fun x hx y hy hxy ↦
      hn.2.2 x hx w (by simp) (hxy.trans (List.mem_singleton.mp hy))⟩
    avoids := fun x hx ↦ L.ear.avoids x (by
      rw [hi]
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · simp [List.mem_singleton.mp hx])
    even := by rw [Nat.odd_iff] at hl; rw [Nat.even_iff]; simp only [List.length_append,
      List.length_singleton]; omega
    chain := by simpa only [List.cons_append, List.append_assoc, List.singleton_append,
      List.nil_append]
      using hwa.isChain }
  let B : H.OddEar A.vertices := {
    start := w
    finish := L.ear.finish
    interior := t
    start_mem := Finset.mem_union_right _ (by simp [A])
    finish_mem := Finset.mem_union_left _ L.ear.finish_mem
    nodup := hnt.2
    avoids := by
      intro x hx hxs
      rcases Finset.mem_union.mp hxs with hxs | hxs
      · exact L.ear.avoids x (by simp [hi, hx]) hxs
      · have hxl : x ∈ l ∨ x = w := by simpa [A, or_comm] using hxs
        rcases hxl with hxl | rfl
        · exact hn.2.2 x hxl x (by simp [hx]) rfl
        · exact hnt.1 hx
    even := by
      have heven := L.ear.even
      rw [Nat.even_iff, hi] at heven
      rw [Nat.odd_iff] at hl
      rw [Nat.even_iff]
      simp only [List.length_append, List.length_cons] at heven
      omega
    chain := hb.isChain }
  have hwa' : H.EdgeChain A.start (as ++ [e]) (A.interior ++ [A.finish]) := by
    simpa only [A, List.append_assoc, List.singleton_append] using hwa
  have hnbM : ¬ bs.toFinset ⊆ M := hb.not_subset_of_matching_at_start (by simp)
    (L.tail_mem he) (fun hm ↦ hne (by simp [hab, hm])) hez.exists_end hd
  have hnew : (L.oldEdges ∪ (as ++ [e]).toFinset) ∪ bs.toFinset =
      insert e (L.oldEdges ∪ L.labels.toFinset) := by
    ext f
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      List.mem_append, List.mem_singleton, hab]
    tauto
  apply L.no_two_ear_replacement hmax hG A (as ++ [e]) hwa' hna B bs hb hnb hnbM
  · refine (show B.vertices = L.ear.vertices from ?_).trans L.vertices_eq
    ext x
    simp only [OddEar.vertices, A, B, hi, Finset.mem_union, List.mem_toFinset,
      List.mem_append, List.mem_cons]
    tauto
  · rw [hnew]
    exact Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp he).1, L.edges_subset⟩
  · rw [hnew]
    exact Finset.subset_insert _ _

/-- Either orientation of the marked odd ear gives the even prefix required
by the replacement above. -/
theorem no_old_end (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {w z : V} (hw : w ∈ L.ear.interior) (hez : H.Joins e w z)
    (hz : z ∈ L.oldVertices) (hd : H.degreeIn M w ≤ 1) : False := by
  obtain ⟨l, t, hi⟩ := List.append_of_mem hw
  by_cases hl : Odd l.length
  · exact L.no_old_end_of_odd_prefix hmax hG he hez hz hd l t hi hl
  · have ht : Odd t.length := by
      have heven := L.ear.even
      rw [hi, Nat.even_iff] at heven
      rw [Nat.odd_iff] at hl ⊢
      simp only [List.length_append, List.length_cons] at heven
      omega
    have hr : L.reverse.ear.interior = t.reverse ++ w :: l.reverse := by
      simp [reverse, OddEar.reverse, hi, List.append_assoc]
    exact L.reverse.no_old_end_of_odd_prefix hmax hG (by simpa [reverse] using he)
      hez hz hd t.reverse l.reverse hr (by simpa using ht)

/-- Proposition 5.7, the endpoint assertion: both ends of every matching-tail
edge are internal vertices of the last nonmatching ear. -/
theorem tail_edge_ends_internal (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1)
    {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) :
    ∀ k, H.endAt e k ∈ L.ear.interior := by
  obtain ⟨i, hi⟩ := L.tail_edge_has_internal_end hmax hG he
  have hwT : H.endAt e i ∈ T := (mem_edgesIn.mp (hG (Finset.mem_sdiff.mp he).1)) i
  intro k
  have hkT := (mem_edgesIn.mp (hG (Finset.mem_sdiff.mp he).1)) k
  rw [← L.vertices_eq] at hkT
  rcases Finset.mem_union.mp hkT with hk | hk
  · exfalso
    have hno := L.no_old_end (z := H.endAt e k) hmax hG he hi
    fin_cases i <;> fin_cases k
    · exact L.ear.avoids _ hi hk
    · exact hno (Or.inl ⟨rfl, rfl⟩) hk (hd _ hwT)
    · exact hno (Or.inr ⟨rfl, rfl⟩) hk (hd _ hwT)
    · exact L.ear.avoids _ hi hk
  · exact List.mem_toFinset.mp hk

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
