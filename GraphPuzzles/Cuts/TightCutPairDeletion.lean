import GraphPuzzles.Matching.Barriers.RestrictedBarrier

/-! The pair-deletion case of the ELP tight-cut argument. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem image_induced_filter (U X : Finset V) :
    ((Finset.univ : Finset U).filter fun z ↦ z.1 ∈ X).image Subtype.val = U ∩ X := by
  ext z
  simp [Finset.mem_image, Subtype.exists, and_comm]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem image_induced_compl_filter (U X : Finset V) :
    (Finset.univ \ ((Finset.univ : Finset U).filter fun z ↦ z.1 ∈ X)).image Subtype.val = U \ X := by
  ext z
  simp [Finset.mem_image, Subtype.exists, and_comm]

/-- After deleting the ends of a tight-cut edge, the surviving cut is inadmissible. -/
theorem IsTightCut.pairDeletion_inadmissible {X : Finset V} (ht : H.IsTightCut X)
    {u v : V} (hu : u ∈ X) (hv : v ∉ X) {e : E} (he : H.Joins e u v) :
    (H.induced (Finset.univ \ {u, v})).IsInadmissibleCut
      (Finset.univ.filter fun z ↦ z.1 ∈ X) := by
  intro M hM
  let U : Finset V := Finset.univ \ {u, v}
  have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
  have hUV : U = (Finset.univ.erase u).erase v := by ext z; simp [U]; tauto
  have hP := hM.of_induced
  change H.IsPerfectMatchingOn U _ at hP
  rw [hUV] at hP
  have hfull := hP.insert_perfect he huv
  have heD : e ∈ H.dangling X := by
    apply mem_dangling.mpr
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp_all
  have hcount := ht _ hfull
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hfM, hfD⟩ := Finset.mem_inter.mp hf
  have hd := (mem_dangling (K := H.induced U)).mp hfD
  have hfDX : f.1 ∈ H.dangling X := by
    apply mem_dangling.mpr
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, induced_endAt] using hd
  have hfe : f.1 = e := Finset.card_le_one.mp hcount.le _
    (Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f, hfM, rfl⟩), hfDX⟩) _
    (Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, heD⟩)
  obtain ⟨k, hk⟩ := he.exists_end
  have hku := (mem_edgesIn.mp f.2) k
  rw [hfe, hk] at hku
  simp at hku

/-- If the odd parts after deleting `u,v` lie in `X` and the only edge
from `v` into `X` ends at `u`, adjoining `u` lifts them to a nontrivial barrier. -/
theorem IsBicritical.not_barrier_of_pairDeletion (hb : H.IsBicritical)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    {u v : V} {X U : Finset V} (hU : U = Finset.univ \ {u, v})
    (hu : u ∈ X) (_hv : v ∉ X)
    (honly : ∀ z ∈ X, (∃ e : E, H.Joins e v z) → z = u)
    {B : Finset U} (F : (H.induced U).ComponentFamily B) (hF : F.IsBarrier)
    (hB : B.Nonempty) (hQX : ∀ Q ∈ F.odd, Q.image Subtype.val ⊆ X) : False := by
  let C := F.of_induced.odd
  let Z := B.image Subtype.val
  have huU : u ∉ U := by simp [hU]
  have huZ : u ∉ Z := fun h ↦ huU (image_induced_vertices_subset B h)
  have hZne : Z.Nonempty := hB.image _
  have hcount : C.card = Z.card := by
    rw [F.of_induced_odd_card, card_image_induced_vertices]
    exact hF
  have hCX : ∀ Q ∈ C, Q ⊆ X := by
    intro Q hQ
    change Q ∈ F.of_induced.odd at hQ
    rw [F.of_induced_odd] at hQ
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    exact hQX R hR
  have hbound := hb.closed_odd_parts_bound hM C (insert u Z)
    (fun Q hQ ↦ F.of_induced.nonempty Q (F.of_induced.mem_odd.mp hQ).1)
    (fun Q hQ z hz hn ↦ by
      apply F.of_induced.avoid Q (F.of_induced.mem_odd.mp hQ).1 z hz
      rcases Finset.mem_insert.mp hn with rfl | hzB
      · exact Finset.mem_union_left _ (by simp [huU])
      · exact Finset.mem_union_right _ hzB)
    (fun Q hQ e k hk hn ↦ by
      apply F.of_induced.closed Q (F.of_induced.mem_odd.mp hQ).1 e k hk
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · have hr : H.endAt e (Fin.rev k) = u ∨ H.endAt e (Fin.rev k) = v := by
          simpa only [hU, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _),
            Finset.mem_insert, Finset.mem_singleton] using hh
        rcases hr with hr | hr
        · exact hn (Finset.mem_insert.mpr (Or.inl hr))
        · have hj : H.Joins e v (H.endAt e k) := by
            fin_cases k
            · exact Or.inr ⟨rfl, hr⟩
            · exact Or.inl ⟨hr, rfl⟩
          have hku := honly _ (hCX Q hQ hk) ⟨e, hj⟩
          exact F.of_induced.avoid Q (F.of_induced.mem_odd.mp hQ).1 _ hk
            (Finset.mem_union_left _ (by simp [hku, huU]))
      · exact hn (Finset.mem_insert_of_mem hh))
    (fun Q hQ R hR hne ↦ F.of_induced.pairwise Q (F.of_induced.mem_odd.mp hQ).1
      R (F.of_induced.mem_odd.mp hR).1 hne)
    (fun Q hQ ↦ (F.of_induced.mem_odd.mp hQ).2)
    (by rw [Finset.card_insert_of_notMem huZ, hcount])
  rw [Finset.card_insert_of_notMem huZ] at hbound
  have hp := Finset.card_pos.mpr hZne
  omega

/-- The mutual-single-neighbour case contradicts bicriticality when both
induced shores remain connected after deleting the ends of the edge. -/
theorem IsTightCut.not_bicritical_of_mutual_unique {X : Finset V} (ht : H.IsTightCut X)
    (hm : H.IsMatchingCovered) (hb : H.IsBicritical) (hX : IsNontrivialCut X)
    {u v : V} (hu : u ∈ X) (hv : v ∉ X) {e : E} (he : H.Joins e u v)
    (hleft : H.IsConnectedOn (X.erase u))
    (hright : H.IsConnectedOn ((Finset.univ \ X).erase v))
    (huonly : ∀ z, z ∉ X → (∃ f : E, H.Joins f u z) → z = v)
    (hvonly : ∀ z ∈ X, (∃ f : E, H.Joins f v z) → z = u) : False := by
  classical
  let U : Finset V := Finset.univ \ {u, v}
  let A : Finset U := Finset.univ.filter fun z ↦ z.1 ∈ X
  have hA : A.image Subtype.val = X.erase u := by
    rw [image_induced_filter]
    ext z
    simp only [U, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · tauto
    · rintro ⟨hzu, hzX⟩
      exact ⟨fun h ↦ h.elim hzu (fun hzv ↦ hv (hzv ▸ hzX)), hzX⟩
  have hAC : (Finset.univ \ A).image Subtype.val = (Finset.univ \ X).erase v := by
    rw [image_induced_compl_filter]
    ext z
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · tauto
    · rintro ⟨hzv, hzX⟩
      exact ⟨fun h ↦ h.elim (fun hzu ↦ hzX (hzu.symm ▸ hu)) hzv, hzX⟩
  have haN : A.Nonempty := by
    have hp : 0 < (X.erase u).card := by rw [Finset.card_erase_of_mem hu]; have hh := hX.1; omega
    exact Finset.image_nonempty.mp (hA.symm ▸ Finset.card_pos.mp hp)
  have haCN : (Finset.univ \ A).Nonempty := by
    have hvC : v ∈ Finset.univ \ X := by simp [hv]
    have hp : 0 < ((Finset.univ \ X).erase v).card := by
      rw [Finset.card_erase_of_mem hvC]; have hh := hX.2; omega
    exact Finset.image_nonempty.mp (hAC.symm ▸ Finset.card_pos.mp hp)
  have huv : u ≠ v := fun h ↦ hv (h ▸ hu)
  obtain ⟨P, hP⟩ := hb u v huv
  have hPU : H.IsPerfectMatchingOn U P := by
    convert hP using 1
    ext z
    simp [U]
    tauto
  have hn : (H.induced U).IsInadmissibleCut A := ht.pairDeletion_inadmissible hu hv he
  obtain ⟨B, F, hF, hs⟩ := hn.exists_DMBarrier_in_shore hPU.induced haN haCN
    ((induced_connectedOn_iff U A).mpr (hA.symm ▸ hleft))
    ((induced_connectedOn_iff U (Finset.univ \ A)).mpr (hAC.symm ▸ hright))
  obtain ⟨M, hM, _⟩ := hm.2 e
  rcases hs with ⟨_, hQ⟩ | ⟨_, hQ⟩
  · apply hb.not_barrier_of_pairDeletion hM rfl hu hv hvonly F hF.isBarrier hF.nonempty
    intro Q hQo z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp (hQ Q hQo hw)).2
  · have hU : U = Finset.univ \ {v, u} := by rw [Finset.pair_comm]
    apply hb.not_barrier_of_pairDeletion (X := Finset.univ \ X) hM hU (by simp [hv]) (by simp [hu])
      (fun z hz hh ↦ huonly z (Finset.mem_sdiff.mp hz).2 hh) F hF.isBarrier hF.nonempty
    intro Q hQo z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hh := (Finset.mem_sdiff.mp (hQ Q hQo hw)).2
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_univ] using hh

end GraphPuzzles.LoopMultigraph
