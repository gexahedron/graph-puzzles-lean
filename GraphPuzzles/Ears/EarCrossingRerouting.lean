import GraphPuzzles.Ears.EarChordRerouting

/-! Crossing matching-tail chords cut the last nonmatching ear into even segments. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- Three successive replacement ears, the last outside the matching,
would increase the marked index by two. -/
theorem no_three_ear_replacement (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T)
    (A : H.OddEar L.oldVertices) (as : List E)
    (ha : H.EdgeChain A.start as (A.interior ++ [A.finish]))
    (hfa : Disjoint L.oldEdges as.toFinset)
    (B : H.OddEar A.vertices) (bs : List E)
    (hb : H.EdgeChain B.start bs (B.interior ++ [B.finish]))
    (hfb : Disjoint (L.oldEdges ∪ as.toFinset) bs.toFinset)
    (C : H.OddEar B.vertices) (cs : List E)
    (hc : H.EdgeChain C.start cs (C.interior ++ [C.finish]))
    (hfc : Disjoint ((L.oldEdges ∪ as.toFinset) ∪ bs.toFinset) cs.toFinset)
    (hm : ¬ cs.toFinset ⊆ M) (hv : C.vertices = T)
    (hs : ((L.oldEdges ∪ as.toFinset) ∪ bs.toFinset) ∪ cs.toFinset ⊆ G)
    (hcover : L.oldEdges ∪ L.labels.toFinset ⊆
      ((L.oldEdges ∪ as.toFinset) ∪ bs.toFinset) ∪ cs.toFinset) : False := by
  obtain ⟨j, hD⟩ := L.earlier.attach_with_index A as ha hfa
  obtain ⟨k, hD'⟩ := hD.attach_with_index B bs hb hfb
  let L' : H.LastOutsideOddEar M r (q + 2) T G := {
    positive := by omega
    oldVertices := B.vertices
    oldEdges := (L.oldEdges ∪ as.toFinset) ∪ bs.toFinset
    oldIndex := k
    ear := C
    labels := cs
    earlier := by
      have := L.positive
      convert hD' using 1; omega
    walk := hc
    fresh := hfc
    outside := hm
    vertices_eq := hv
    edges_subset := hs
    tail_mem := fun e he ↦ L.tail_mem (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp he).1, fun hg ↦ (Finset.mem_sdiff.mp he).2 (hcover hg)⟩) }
  obtain ⟨n, hD''⟩ := L'.complete hG
  have hle := hmax.2 r n (q + 2) hD''
  omega

set_option maxHeartbeats 600000 in
/-- Two crossing tail chords cannot have odd consecutive segments between
all four endpoints: the crossed route and the two bypassed segments form
three odd ears, contradicting maximality. -/
theorem no_odd_crossing_segments (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) {e f : E}
    (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    (hf : f ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {x u y v : V} (hexy : H.Joins e x y) (hfuv : H.Joins f u v)
    (hd : H.degreeIn M y ≤ 1)
    (p m n o t : List V)
    (hi : L.ear.interior = p ++ x :: (m ++ u :: (n ++ y :: (o ++ v :: t))))
    (hm : Even m.length) (ho : Even o.length) : False := by
  have hn := hi ▸ L.ear.nodup
  have hnP := List.nodup_append.mp hn
  have hnX := List.nodup_cons.mp hnP.2.1
  have hnM := List.nodup_append.mp hnX.2
  have hnU := List.nodup_cons.mp hnM.2.1
  have hnN := List.nodup_append.mp hnU.2
  have hnY := List.nodup_cons.mp hnN.2.1
  have hnO := List.nodup_append.mp hnY.2
  have hw : H.EdgeChain L.ear.start L.labels
      (p ++ x :: (m ++ u :: (n ++ y :: (o ++ v :: (t ++ [L.ear.finish]))))) := by
    simpa only [hi, List.append_assoc, List.cons_append] using L.walk
  obtain ⟨as, rest₁, h₁, ha, hw₁⟩ := hw.split p
    (m ++ u :: (n ++ y :: (o ++ v :: (t ++ [L.ear.finish]))))
  obtain ⟨bs, rest₂, h₂, hb, hw₂⟩ := hw₁.split m
    (n ++ y :: (o ++ v :: (t ++ [L.ear.finish])))
  obtain ⟨cs, rest₃, h₃, hc, hw₃⟩ := hw₂.split n
    (o ++ v :: (t ++ [L.ear.finish]))
  obtain ⟨ds, es, h₄, hdw, ht⟩ := hw₃.split o (t ++ [L.ear.finish])
  have hlabels : L.labels = as ++ (bs ++ (cs ++ (ds ++ es))) := by
    simp only [h₁, h₂, h₃, h₄]
  have hnlabels : (as ++ (bs ++ (cs ++ (ds ++ es)))).Nodup :=
    hlabels ▸ L.ear.labels_nodup L.walk
  have hnAs := List.nodup_append.mp hnlabels
  have hnBs := List.nodup_append.mp hnAs.2.1
  have hnCs := List.nodup_append.mp hnBs.2.1
  have hnDs := List.nodup_append.mp hnCs.2.1
  have hne : e ∉ L.labels := fun h ↦ (Finset.mem_sdiff.mp he).2
    (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  have hnf : f ∉ L.labels := fun h ↦ (Finset.mem_sdiff.mp hf).2
    (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  have hwa : H.EdgeChain L.ear.start (as ++ e :: (cs.reverse ++ f :: es))
      (p ++ x :: y :: (n.reverse ++ u :: v :: (t ++ [L.ear.finish]))) :=
    ha.append (.cons hexy (hc.reverse.append (.cons hfuv ht)))
  let A : H.OddEar L.oldVertices := {
    start := L.ear.start
    finish := L.ear.finish
    interior := p ++ x :: y :: (n.reverse ++ u :: v :: t)
    start_mem := L.ear.start_mem
    finish_mem := L.ear.finish_mem
    nodup := by
      refine List.nodup_append.mpr ⟨hnP.1, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · intro hx
          apply hnX.1
          simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hx ⊢
          clear * - hx
          tauto
        · refine List.nodup_cons.mpr ⟨?_, ?_⟩
          · intro hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hnN.2.2 y (List.mem_reverse.mp hy) y (by simp) rfl
            · rcases List.mem_cons.mp hy with hy | hy
              · exact hnU.1 (by simp [← hy])
              · exact hnY.1 (List.mem_append_right _ hy)
          · refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr hnN.1, ?_, ?_⟩
            · refine List.nodup_cons.mpr ⟨?_, hnO.2.1⟩
              intro hu
              apply hnU.1
              simp only [List.mem_cons] at hu
              simp only [List.mem_append, List.mem_cons]
              clear * - hu
              tauto
            · intro a ha b hb hab
              have han := List.mem_reverse.mp ha
              rcases List.mem_cons.mp hb with hbu | hb
              · exact hnU.1 (by simp [← hab.trans hbu, han])
              · exact hnN.2.2 a han b (List.mem_cons_of_mem _
                  (List.mem_append_right _ hb)) hab
      · intro a ha b hb hab
        apply hnP.2.2 a ha b ?_ hab
        simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hb ⊢
        clear * - hb
        tauto
    avoids := by
      intro a ha
      apply L.ear.avoids a
      simp only [hi, List.mem_append, List.mem_cons, List.mem_reverse] at ha ⊢
      clear * - ha
      tauto
    even := by
      have h := L.ear.even
      rw [hi, Nat.even_iff] at h
      rw [Nat.even_iff] at hm ho ⊢
      simp only [List.length_append, List.length_cons, List.length_reverse] at h ⊢
      omega
    chain := by simpa only [List.cons_append, List.append_assoc] using hwa.isChain }
  let B : H.OddEar A.vertices := {
    start := x
    finish := u
    interior := m
    start_mem := Finset.mem_union_right _ (by simp [A])
    finish_mem := Finset.mem_union_right _ (by simp [A])
    nodup := hnM.1
    avoids := by
      intro a ha has
      rcases Finset.mem_union.mp has with has | has
      · exact L.ear.avoids a (by simp [hi, ha]) has
      · simp only [A, List.mem_toFinset, List.mem_append, List.mem_cons,
          List.mem_reverse] at has
        rcases has with hap | hax | hay | han | hau | hav | hat
        · exact hnP.2.2 a hap a (by simp [ha]) rfl
        · exact hnX.1 (by simp [← hax, ha])
        · exact hnM.2.2 a ha y (by simp) hay
        · exact hnM.2.2 a ha a (by simp [han]) rfl
        · exact hnM.2.2 a ha u (by simp) hau
        · exact hnM.2.2 a ha v (by simp) hav
        · exact hnM.2.2 a ha a (by simp [hat]) rfl
    even := hm
    chain := hb.isChain }
  let C : H.OddEar B.vertices := {
    start := y
    finish := v
    interior := o
    start_mem := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [A]))
    finish_mem := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [A]))
    nodup := hnO.1
    avoids := by
      intro a ha has
      simp only [OddEar.vertices, A, B, Finset.mem_union, List.mem_toFinset,
        List.mem_append, List.mem_cons, List.mem_reverse] at has
      rcases has with (has | has) | has
      · exact L.ear.avoids a (by simp [hi, ha]) has
      · rcases has with hap | hax | hay | han | hau | hav | hat
        · exact hnP.2.2 a hap a (by simp [ha]) rfl
        · exact hnX.1 (by simp [← hax, ha])
        · exact hnY.1 (by simp [← hay, ha])
        · exact hnN.2.2 a han a (by simp [ha]) rfl
        · exact hnU.1 (by simp [← hau, ha])
        · exact hnO.2.2 a ha v (by simp) hav
        · exact hnO.2.2 a ha a (by simp [hat]) rfl
      · exact hnM.2.2 a has a (by simp [ha]) rfl
    even := ho
    chain := hdw.isChain }
  have hwa' : H.EdgeChain A.start (as ++ e :: (cs.reverse ++ f :: es))
      (A.interior ++ [A.finish]) := by
    simpa only [A, List.append_assoc, List.cons_append] using hwa
  have hna : Disjoint L.oldEdges (as ++ e :: (cs.reverse ++ f :: es)).toFinset := by
    apply Finset.disjoint_left.mpr
    intro a ha hal
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_reverse] at hal
    rcases hal with has | rfl | hcs | rfl | hes
    · exact Finset.disjoint_left.mp L.fresh ha (by simp [hlabels, has])
    · exact (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ ha)
    · exact Finset.disjoint_left.mp L.fresh ha (by simp [hlabels, hcs])
    · exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_union_left _ ha)
    · exact Finset.disjoint_left.mp L.fresh ha (by simp [hlabels, hes])
  have hnb : Disjoint (L.oldEdges ∪ (as ++ e :: (cs.reverse ++ f :: es)).toFinset)
      bs.toFinset := by
    apply Finset.disjoint_left.mpr
    intro a ha hab
    have hab' := List.mem_toFinset.mp hab
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.disjoint_left.mp L.fresh ha (by simp [hlabels, hab'])
    · simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_reverse] at ha
      have hea : a ≠ e := fun h ↦ hne (by simp [hlabels, ← h, hab'])
      have hfa : a ≠ f := fun h ↦ hnf (by simp [hlabels, ← h, hab'])
      rcases ha with has | hae | hcs | haf | hes
      · exact hnAs.2.2 a has a (by simp [hab']) rfl
      · exact hea hae
      · exact hnBs.2.2 a hab' a (by simp [hcs]) rfl
      · exact hfa haf
      · exact hnBs.2.2 a hab' a (by simp [hes]) rfl
  have hnc : Disjoint ((L.oldEdges ∪ (as ++ e :: (cs.reverse ++ f :: es)).toFinset) ∪
      bs.toFinset) ds.toFinset := by
    apply Finset.disjoint_left.mpr
    intro a ha had
    have had' := List.mem_toFinset.mp had
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.disjoint_left.mp L.fresh ha (by simp [hlabels, had'])
      · simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_reverse] at ha
        have hea : a ≠ e := fun h ↦ hne (by simp [hlabels, ← h, had'])
        have hfa : a ≠ f := fun h ↦ hnf (by simp [hlabels, ← h, had'])
        rcases ha with has | hae | hcs | haf | hes
        · exact hnAs.2.2 a has a (by simp [had']) rfl
        · exact hea hae
        · exact hnCs.2.2 a hcs a (by simp [had']) rfl
        · exact hfa haf
        · exact hnDs.2.2 a had' a hes rfl
    · exact hnBs.2.2 a (List.mem_toFinset.mp ha) a (by simp [had']) rfl
  have hnotM : ¬ ds.toFinset ⊆ M := hdw.not_subset_of_matching_at_start (by simp)
    (L.tail_mem he) (fun h ↦ hne (by simp [hlabels, h]))
    (H.joins_comm.mp hexy).exists_end hd
  have hnew : ((L.oldEdges ∪ (as ++ e :: (cs.reverse ++ f :: es)).toFinset) ∪
      bs.toFinset) ∪ ds.toFinset = insert e (insert f (L.oldEdges ∪ L.labels.toFinset)) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      List.mem_append, List.mem_cons, List.mem_reverse, hlabels]
    clear * - L
    tauto
  apply L.no_three_ear_replacement hmax hG A _ hwa' hna B bs hb hnb C ds hdw hnc hnotM
  · refine (show C.vertices = L.ear.vertices from ?_).trans L.vertices_eq
    ext a
    simp only [OddEar.vertices, A, B, C, hi, Finset.mem_union, List.mem_toFinset,
      List.mem_append, List.mem_cons, List.mem_reverse]
    clear * - L
    tauto
  · rw [hnew]
    exact Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp he).1,
      Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp hf).1, L.edges_subset⟩⟩
  · rw [hnew]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

/-- Proposition 5.8: if two matching-tail chords have alternating endpoints
on the marked ear, all three intervening segments have even length. -/
theorem tail_crossing_even_segments (hmax : H.IsMaximumOddEarIndex M T G q)
    (hG : G ⊆ H.edgesIn T) (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) {e f : E}
    (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    (hf : f ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {x u y v : V} (hexy : H.Joins e x y) (hfuv : H.Joins f u v)
    (p m n o t : List V)
    (hi : L.ear.interior = p ++ x :: (m ++ u :: (n ++ y :: (o ++ v :: t)))) :
    Even (m.length + 1) ∧ Even (n.length + 1) ∧ Even (o.length + 1) := by
  have hx : Even ((m ++ u :: n).length + 1) :=
    L.tail_edge_even_segment hmax hG hd he hexy p (m ++ u :: n) (o ++ v :: t)
      (by simpa only [List.append_assoc, List.cons_append] using hi)
  have hu : Even ((n ++ y :: o).length + 1) :=
    L.tail_edge_even_segment hmax hG hd hf hfuv (p ++ x :: m) (n ++ y :: o) t
      (by simpa only [List.append_assoc, List.cons_append] using hi)
  have hyT : y ∈ T := L.vertices_eq ▸ Finset.mem_union_right L.oldVertices
    (List.mem_toFinset.mpr (by simp [hi]))
  have hm : Even (m.length + 1) := by
    by_contra h
    have hm' : Even m.length := by rw [Nat.even_iff] at h ⊢; omega
    have ho' : Even o.length := by
      rw [Nat.even_iff] at hx hu hm' ⊢
      simp only [List.length_append, List.length_cons] at hx hu
      omega
    exact L.no_odd_crossing_segments hmax hG he hf hexy hfuv (hd y hyT)
      p m n o t hi hm' ho'
  rw [Nat.even_iff] at hx hu hm ⊢
  simp only [List.length_append, List.length_cons] at hx hu
  constructor
  · exact hm
  · constructor <;> rw [Nat.even_iff] <;> omega

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
