import GraphPuzzles.Cuts.Shores.DeletedTightShore

/-! Matching balance and extensions in the bipartite shores of Section 6. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {Y : Finset V}

namespace BipartiteRestorationShore

variable (P : H.BipartiteRestorationShore e Y)

/-- The restored edge contributes the only defect to bipartite degree
balance. This identity applies to arbitrary edge sets, including matchings
with vertices deleted. -/
theorem degree_balance (M : Finset E) :
    (∑ w ∈ P.large, H.degreeIn M w) + (if e ∈ M then 2 else 0) =
      (∑ w ∈ P.small, H.degreeIn M w) + (M ∩ H.dangling Y).card := by
  have hedge (f : E) : H.endsIn P.large f + (if f = e then 2 else 0) =
      H.endsIn P.small f + (if f ∈ H.dangling Y then 1 else 0) := by
    have hd0 : ¬ (H.endAt f 0 ∈ P.small ∧ H.endAt f 0 ∈ P.large) :=
      fun h ↦ Finset.disjoint_left.mp P.disjoint h.1 h.2
    have hd1 : ¬ (H.endAt f 1 ∈ P.small ∧ H.endAt f 1 ∈ P.large) :=
      fun h ↦ Finset.disjoint_left.mp P.disjoint h.1 h.2
    have hl := P.large_independent f
    by_cases hfe : f = e
    · subst f
      obtain ⟨k, hk⟩ := mem_meets.mp P.edge_meets_small
      have hsome : H.endAt e 0 ∈ P.small ∨ H.endAt e 1 ∈ P.small := by
        fin_cases k
        · exact Or.inl hk
        · exact Or.inr hk
      have h0 := P.edge_avoids_large 0
      have h1 := P.edge_avoids_large 1
      unfold endsIn
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [← P.union_eq]
      by_cases ha0 : H.endAt e 0 ∈ P.small <;> by_cases ha1 : H.endAt e 1 ∈ P.small <;>
        simp_all [mem_dangling, Finset.mem_union]
    · have h0 := P.other_edges f hfe 0
      have h1 := P.other_edges f hfe 1
      change H.endAt f 0 ∈ P.small → H.endAt f 1 ∈ P.large at h0
      change H.endAt f 1 ∈ P.small → H.endAt f 0 ∈ P.large at h1
      unfold endsIn
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [← P.union_eq]
      by_cases ha0 : H.endAt f 0 ∈ P.small <;> by_cases ha1 : H.endAt f 1 ∈ P.small <;>
        by_cases hb0 : H.endAt f 0 ∈ P.large <;> by_cases hb1 : H.endAt f 1 ∈ P.large <;>
        simp_all [mem_dangling, Finset.mem_union]
  have hh := Finset.sum_congr (s₁ := M) rfl (fun f _ ↦ hedge f)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_boole, Finset.filter_mem_eq_inter] at hh
  rw [sum_degreeIn_eq, sum_degreeIn_eq]
  exact hh

omit [DecidableEq E] in
/-- A deleted-vertex perfect matching has one incidence at every
undeleted vertex of a shore. -/
private theorem sum_degree_deleted {D S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn (Finset.univ \ D) M) :
    (∑ w ∈ S, H.degreeIn M w) = (S \ D).card := by
  have hdegree (w : V) : H.degreeIn M w = if w ∉ D then 1 else 0 := by
    by_cases hw : w ∈ D
    · rw [if_neg (not_not_intro hw)]
      exact hM.degree_zero (by simp [hw])
    · rw [if_pos hw]
      exact hM.2 w (by simp [hw])
  simp only [hdegree]
  have hfilter : S.filter (fun w ↦ w ∉ D) = S \ D := by
    ext w
    simp
  rw [← hfilter, Finset.card_filter]

/-- The degree-balance identity for a matching after deleting an
arbitrary finite vertex set. -/
theorem matching_balance {D : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn (Finset.univ \ D) M) :
    (P.large \ D).card + (if e ∈ M then 2 else 0) =
      (P.small \ D).card + (M ∩ H.dangling Y).card := by
  simpa only [sum_degree_deleted hM] using P.degree_balance M

/-- Deleting one small-side vertex and a vertex outside the shore
forces two matching edges across its boundary. -/
theorem crossing_two_of_delete_small {v z : V} (hv : v ∈ P.small) (hz : z ∉ Y)
    {M : Finset E} (hM : H.IsPerfectMatchingOn (Finset.univ \ {v, z}) M)
    (he : e ∉ M) : (M ∩ H.dangling Y).card = 2 := by
  have hvL : v ∉ P.large := Finset.disjoint_left.mp P.disjoint hv
  have hzA : z ∉ P.small := fun h ↦ hz (P.union_eq ▸ Finset.mem_union_left _ h)
  have hzB : z ∉ P.large := fun h ↦ hz (P.union_eq ▸ Finset.mem_union_right _ h)
  have hA : P.small \ {v, z} = P.small.erase v := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ⟨hw, hn⟩
      exact ⟨fun h ↦ hn (Or.inl h), hw⟩
    · rintro ⟨hn, hw⟩
      exact ⟨hw, fun h ↦ h.elim hn (fun h ↦ hzA (h ▸ hw))⟩
  have hB : P.large \ {v, z} = P.large := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    exact Finset.disjoint_right.mpr (by
      intro w hw hwL
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hvL hwL
      · exact hzB ((Finset.mem_singleton.mp hw) ▸ hwL))
  have hh := P.matching_balance hM
  rw [hA, hB, if_neg he, add_zero, Finset.card_erase_of_mem hv, P.card_large] at hh
  have hp := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Deleting two large-side vertices forces the restored edge into the
matching and leaves it as the unique boundary matching edge. -/
theorem crossing_one_of_delete_two_large {x y : V}
    (hx : x ∈ P.large) (hy : y ∈ P.large) (hxy : x ≠ y)
    {M : Finset E} (hM : H.IsPerfectMatchingOn (Finset.univ \ {x, y}) M) :
    e ∈ M ∧ (M ∩ H.dangling Y).card = 1 := by
  have hxA : x ∉ P.small := Finset.disjoint_right.mp P.disjoint hx
  have hyA : y ∉ P.small := Finset.disjoint_right.mp P.disjoint hy
  have hA : P.small \ {x, y} = P.small := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    exact Finset.disjoint_right.mpr (by
      intro w hw hwA
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hxA hwA
      · exact hyA ((Finset.mem_singleton.mp hw) ▸ hwA))
  have hsub : ({x, y} : Finset V) ⊆ P.large :=
    Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
  have hB := Finset.card_sdiff_of_subset hsub
  rw [Finset.card_pair hxy] at hB
  have hh := P.matching_balance hM
  rw [hA, hB, P.card_large] at hh
  have htwo : 2 ≤ P.large.card := by
    simpa only [Finset.card_pair hxy] using Finset.card_le_card hsub
  rw [P.card_large] at htwo
  by_cases he : e ∈ M
  · exact ⟨he, by rw [if_pos he] at hh; omega⟩
  · rw [if_neg he] at hh
    omega

include P in
/-- A matching covering the shore and using the restored edge has
three boundary edges even if it covers only part of the rest of the graph. -/
theorem crossing_three_of_covers_shore {M : Finset E}
    (hM : ∀ w ∈ Y, H.degreeIn M w = 1) (he : e ∈ M) :
    (M ∩ H.dangling Y).card = 3 := by
  have hA : (∑ w ∈ P.small, H.degreeIn M w) = P.small.card := by
    rw [Finset.sum_congr rfl (fun w hw ↦ hM w (P.union_eq ▸ Finset.mem_union_left _ hw))]
    simp
  have hB : (∑ w ∈ P.large, H.degreeIn M w) = P.large.card := by
    rw [Finset.sum_congr rfl (fun w hw ↦ hM w (P.union_eq ▸ Finset.mem_union_right _ hw))]
    simp
  have hh := P.degree_balance M
  rw [hA, hB, if_pos he, P.card_large] at hh
  omega

/-- Proposition 6.5's local matching extension. The old boundary has
three possible exterior neighbours. Deleting one of them and the small-side
endpoint of the restored edge forces the other two into the local matching. -/
theorem exists_matchingOn_three_neighbors (hbic : H.IsBicritical)
    {v w x y z : V} (he : H.Joins e v w) (hv : v ∈ P.small)
    (hwY : w ∉ Y) (hxY : x ∉ Y) (hyY : y ∉ Y) (hzY : z ∉ Y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hwx : w ≠ x) (hwy : w ≠ y)
    (hboundary : ∀ f, f ≠ e → ∀ k, H.endAt f k ∈ Y → H.endAt f (Fin.rev k) ∉ Y →
      H.endAt f (Fin.rev k) ∈ ({x, y, z} : Finset V)) :
    ∃ M, H.IsPerfectMatchingOn (Y ∪ {x, y, w}) M ∧ e ∈ M ∧
      (M ∩ H.dangling Y).card = 3 := by
  have hvY : v ∈ Y := P.union_eq ▸ Finset.mem_union_left _ hv
  have hvz : v ≠ z := ne_of_mem_of_not_mem hvY hzY
  have hvw : v ≠ w := ne_of_mem_of_not_mem hvY hwY
  obtain ⟨N, hN₀⟩ := hbic v z hvz
  have hN : H.IsPerfectMatchingOn (Finset.univ \ {v, z}) N := by
    convert hN₀ using 1
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, and_true, not_or]
    exact and_comm
  have heN : e ∉ N := by
    intro heN
    obtain ⟨i, hi⟩ := he.exists_end
    have hh := hN.1 e heN i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hi, true_or, not_true_eq_false] at hh
  have htwo := P.crossing_two_of_delete_small hv hzY hN heN
  have hdegx : H.degreeIn N x = 1 :=
    hN.2 x (by simp [hxz, ne_of_mem_of_not_mem hvY hxY |>.symm])
  have hdegy : H.degreeIn N y = 1 :=
    hN.2 y (by simp [hyz, ne_of_mem_of_not_mem hvY hyY |>.symm])
  have ends_avoid (f : E) (hf : f ∈ N) (k : Fin 2) :
      H.endAt f k ≠ v ∧ H.endAt f k ≠ z := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hN.1 f hf k
  have outside_xy {f : E} (hf : f ∈ N) {k : Fin 2}
      (hi : H.endAt f k ∈ Y) (ho : H.endAt f (Fin.rev k) ∉ Y) :
      H.endAt f (Fin.rev k) = x ∨ H.endAt f (Fin.rev k) = y := by
    have hh := hboundary f (ne_of_mem_of_not_mem hf heN) k hi ho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · exact ((ends_avoid f hf _).2 hh).elim
  have cut_ends (f : E) (hf : f ∈ N ∩ H.dangling Y) :
      ∃ k, (H.endAt f k = x ∨ H.endAt f k = y) ∧ H.endAt f (Fin.rev k) ∈ Y := by
    obtain ⟨hfN, hfD⟩ := Finset.mem_inter.mp hf
    have hd := mem_dangling.mp hfD
    by_cases h0 : H.endAt f 0 ∈ Y
    · have h1 : H.endAt f 1 ∉ Y := fun h ↦ hd ⟨fun _ ↦ h, fun _ ↦ h0⟩
      exact ⟨1, outside_xy hfN h0 h1, h0⟩
    · have h1 : H.endAt f 1 ∈ Y := by tauto
      exact ⟨0, outside_xy hfN h1 h0, h1⟩
  have through {q r : V} (hdeg : H.degreeIn N r = 1)
      (hcover : ∀ f ∈ N ∩ H.dangling Y, ∃ k, H.endAt f k = q ∨ H.endAt f k = r) :
      ∃ f ∈ N ∩ H.dangling Y, ∃ k, H.endAt f k = q := by
    by_contra hn
    push Not at hn
    have hr (f : E) (hf : f ∈ N ∩ H.dangling Y) : ∃ k, H.endAt f k = r := by
      obtain ⟨k, hk⟩ := hcover f hf
      exact ⟨k, hk.resolve_left (hn f hf k)⟩
    have hc : (N ∩ H.dangling Y).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro f hf g hg
      obtain ⟨i, hi⟩ := hr f hf
      obtain ⟨j, hj⟩ := hr g hg
      exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hdeg
        (Finset.mem_inter.mp hf).1 (Finset.mem_inter.mp hg).1 hi hj)
    omega
  have hthroughx := through hdegy (fun f hf ↦ by
    obtain ⟨k, hk, _⟩ := cut_ends f hf
    exact ⟨k, hk⟩)
  have hthroughy := through hdegx (fun f hf ↦ by
    obtain ⟨k, hk, _⟩ := cut_ends f hf
    exact ⟨k, hk.symm⟩)
  have partner_inside {q : V} (hq : q ∉ Y) (hdeg : H.degreeIn N q = 1)
      (hthrough : ∃ f ∈ N ∩ H.dangling Y, ∃ k, H.endAt f k = q)
      {g : E} (hg : g ∈ N) {j : Fin 2} (hj : H.endAt g j = q) :
      H.endAt g (Fin.rev j) ∈ Y := by
    obtain ⟨f, hf, k, hk⟩ := hthrough
    have hfk : H.endAt f (Fin.rev k) ∈ Y := by
      have hd := mem_dangling.mp (Finset.mem_inter.mp hf).2
      have hkn : H.endAt f k ∉ Y := fun h ↦ hq (hk ▸ h)
      fin_cases k
      · exact of_not_not (fun h ↦ hd ⟨fun hh ↦ (hkn hh).elim, fun hh ↦ (h hh).elim⟩)
      · exact of_not_not (fun h ↦ hd ⟨fun hh ↦ (h hh).elim, fun hh ↦ (hkn hh).elim⟩)
    have hh := eq_incidence_of_degreeIn_one hdeg hg (Finset.mem_inter.mp hf).1 hj hk
    have hend := congrArg (fun p : E × Fin 2 ↦ H.endAt p.1 (Fin.rev p.2)) hh
    exact hend.symm ▸ hfk
  let S := Y.erase v ∪ ({x, y} : Finset V)
  have hST : S ⊆ Finset.univ \ {v, z} := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨htv, htY⟩ := Finset.mem_erase.mp ht
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htv, ne_of_mem_of_not_mem htY hzY⟩⟩
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · simp [hxz, ne_of_mem_of_not_mem hvY hxY |>.symm]
      · rw [Finset.mem_singleton.mp ht]
        simp [hyz, ne_of_mem_of_not_mem hvY hyY |>.symm]
  have hclosed : ∀ f ∈ N, ∀ k, H.endAt f k ∈ S → H.endAt f (Fin.rev k) ∈ S := by
    intro f hf k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · by_cases ho : H.endAt f (Fin.rev k) ∈ Y
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(ends_avoid f hf _).1, ho⟩)
      · exact Finset.mem_union_right _ (by simpa only [Finset.mem_insert,
          Finset.mem_singleton] using outside_xy hf (Finset.mem_erase.mp hk).2 ho)
    · have ho : H.endAt f (Fin.rev k) ∈ Y := by
        rcases Finset.mem_insert.mp hk with hk | hk
        · exact partner_inside hxY hdegx hthroughx hf hk
        · exact partner_inside hyY hdegy hthroughy hf (Finset.mem_singleton.mp hk)
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(ends_avoid f hf _).1, ho⟩)
  have hNS := hN.restrict hST hclosed
  have hdisj : Disjoint S ({v, w} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro t ht hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact (Finset.notMem_erase _ _) ht
      · rcases Finset.mem_insert.mp ht with h | h
        · exact hxY (h ▸ hvY)
        · exact hyY ((Finset.mem_singleton.mp h) ▸ hvY)
    · rw [Finset.mem_singleton.mp hp] at ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hwY (Finset.mem_of_mem_erase ht)
      · simp only [Finset.mem_insert, Finset.mem_singleton, hwx, hwy, or_self] at ht
  have hglue := hNS.union (he.isPerfectMatchingOn hvw) hdisj
  have hU : S ∪ {v, w} = Y ∪ {x, y, w} := by
    ext t
    by_cases htv : t = v
    · subst t
      simp [S, hvY]
    · simp only [S, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton, htv, false_or]
      tauto
  rw [hU] at hglue
  refine ⟨_, hglue, Finset.mem_union_right _ (Finset.mem_singleton_self e), ?_⟩
  exact P.crossing_three_of_covers_shore (fun t ht ↦ hglue.2 t (Finset.mem_union_left _ ht))
    (Finset.mem_union_right _ (Finset.mem_singleton_self e))

end BipartiteRestorationShore

end GraphPuzzles.LoopMultigraph
