import GraphPuzzles.Matching.Barriers.BarrierCore
import GraphPuzzles.Matching.Barriers.ComponentRetention

/-! Extend bijective matchings of a barrier core through its factor-critical components. -/

namespace GraphPuzzles.LoopMultigraph.ComponentFamily

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)

/-- Every perfect matching restricts to a matching on the vertices outside the
barrier and its odd components. -/
theorem IsBarrier.matching_remainder (hb : F.IsBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) :
    H.IsPerfectMatchingOn (remainder F.odd Z) (M ∩ H.edgesIn (remainder F.odd Z)) := by
  apply hM.on_univ.restrict (Finset.subset_univ _)
  intro e he k hk
  obtain ⟨hkZ, hkQ⟩ := (mem_remainder F.odd Z _).mp hk
  have hnZ : H.endAt e (Fin.rev k) ∉ Z := by
    intro hz
    have hpos : 0 < H.endsIn Z e := Finset.card_pos.mpr ⟨Fin.rev k,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    have hh := hb.endsIn_of_matching F hM he
    have hin : e ∈ F.odd.biUnion H.dangling := by
      by_contra hn
      rw [if_neg hn] at hh
      omega
    obtain ⟨Q, hQ, heQ⟩ := Finset.mem_biUnion.mp hin
    obtain ⟨j, hj, _, _⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ).1 heQ
    have hjk : j = k := by
      by_contra hn
      have hjrev : j = Fin.rev k :=
        (show ∀ a b : Fin 2, a ≠ b → a = Fin.rev b by decide) j k hn
      rw [hjrev] at hj
      exact F.avoid Q (F.mem_odd.mp hQ).1 _ hj hz
    exact hkQ Q hQ (hjk ▸ hj)
  apply (mem_remainder F.odd Z _).mpr
  refine ⟨hnZ, ?_⟩
  intro Q hQ hother
  have hh := F.closed Q (F.mem_odd.mp hQ).1 e (Fin.rev k) hother (by simpa using hkZ)
  exact hkQ Q hQ (by simpa using hh)

/-- A bijection from odd components to barrier vertices, represented by chosen
labelled edges, extends to a perfect matching when those components are factor-critical. -/
theorem IsBarrier.exists_perfectMatching_of_core_edges (hb : F.IsBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (hfc : ∀ Q ∈ F.odd, H.IsFactorCritical Q)
    (f : F.odd → Z) (hf : Function.Bijective f)
    (edge : F.odd → E) (idx : F.odd → Fin 2)
    (hin : ∀ Q, H.endAt (edge Q) (idx Q) ∈ Q.1)
    (hout : ∀ Q, H.endAt (edge Q) (Fin.rev (idx Q)) = (f Q).1) :
    ∃ N, H.IsPerfectMatching N ∧ ∀ Q, edge Q ∈ N := by
  classical
  have hlocal (Q : F.odd) : ∃ P, H.IsPerfectMatchingOn (insert (f Q).1 Q.1) P ∧ edge Q ∈ P := by
    obtain ⟨P, hP⟩ := hfc Q.1 Q.2 _ (hin Q)
    have hz : (f Q).1 ∉ Q.1 := fun h ↦ F.avoid Q.1 (F.mem_odd.mp Q.2).1 _ h (f Q).2
    have hj : H.Joins (edge Q) (H.endAt (edge Q) (idx Q)) (f Q).1 := by
      have ho := hout Q
      rcases (show idx Q = 0 ∨ idx Q = 1 by omega) with hi | hi
      · exact Or.inl ⟨congrArg (H.endAt (edge Q)) hi.symm, by simpa [hi] using ho⟩
      · exact Or.inr ⟨by simpa [hi] using ho, congrArg (H.endAt (edge Q)) hi.symm⟩
    exact ⟨insert (edge Q) P, hP.insert_boundary (hin Q) hz hj, Finset.mem_insert_self _ _⟩
  choose part hp hedge using hlocal
  let S : F.odd → Finset V := fun Q ↦ insert (f Q).1 Q.1
  have hdisj (Q R : F.odd) (hne : Q ≠ R) : Disjoint (S Q) (S R) := by
    apply Finset.disjoint_left.mpr
    intro v hvQ hvR
    rcases Finset.mem_insert.mp hvQ with hzQ | hvQ <;>
      rcases Finset.mem_insert.mp hvR with hzR | hvR
    · exact hne (hf.1 (Subtype.ext (hzQ.symm.trans hzR)))
    · exact F.avoid R.1 (F.mem_odd.mp R.2).1 v hvR (hzQ.symm ▸ (f Q).2)
    · exact F.avoid Q.1 (F.mem_odd.mp Q.2).1 v hvQ (hzR.symm ▸ (f R).2)
    · exact hne (Subtype.ext (F.eq_of_mem (F.mem_odd.mp Q.2).1 (F.mem_odd.mp R.2).1 hvQ hvR))
  have hU : Finset.univ.biUnion S = Z ∪ F.odd.biUnion id := by
    ext v
    constructor
    · intro hv
      obtain ⟨Q, _, hv⟩ := Finset.mem_biUnion.mp hv
      rcases Finset.mem_insert.mp hv with hz | hv
      · exact Finset.mem_union_left _ (hz.symm ▸ (f Q).2)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Q.1, Q.2, hv⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hz | hv
      · obtain ⟨Q, hQ⟩ := hf.2 ⟨v, hz⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨Q, Finset.mem_univ _, Finset.mem_insert.mpr (Or.inl ?_)⟩
        exact (congrArg Subtype.val hQ).symm
      · obtain ⟨Q, hQ, hv⟩ := Finset.mem_biUnion.mp hv
        exact Finset.mem_biUnion.mpr ⟨⟨Q, hQ⟩, Finset.mem_univ _, Finset.mem_insert_of_mem hv⟩
  have hP := IsPerfectMatchingOn.biUnion Finset.univ S part (fun Q _ ↦ hp Q)
    (fun Q _ R _ hne ↦ hdisj Q R hne)
  have hR := hb.matching_remainder F hM
  have hd : Disjoint (Finset.univ.biUnion S) (remainder F.odd Z) := by
    rw [hU]
    exact Finset.disjoint_sdiff
  have hall := hP.union hR hd
  have hsets : (Finset.univ.biUnion S) ∪ remainder F.odd Z = Finset.univ := by
    rw [hU]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  refine ⟨Finset.univ.biUnion part ∪ (M ∩ H.edgesIn (remainder F.odd Z)), ?_, ?_⟩
  · exact IsPerfectMatchingOn.of_univ (hsets ▸ hall)
  · intro Q
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨Q, Finset.mem_univ _, hedge Q⟩)

end GraphPuzzles.LoopMultigraph.ComponentFamily
