import GraphPuzzles.Matching.Barriers.RestrictedBarrier
import GraphPuzzles.Cuts.MinimalTightShore

/-! The spanning edge restriction used in the ELP tight-cut argument. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Restrict a perfect matching to a spanning subgraph containing its edges. -/
theorem IsPerfectMatching.exists_restrictEdges {M S : Finset E}
    (hM : H.IsPerfectMatching M) (hMS : M ⊆ S) :
    ∃ N, (H.restrictEdges S).IsPerfectMatching N ∧ N.image Subtype.val = M := by
  let N : Finset S := Finset.univ.filter fun e ↦ e.1 ∈ M
  have heq : N.image Subtype.val = M := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hf).2
    · intro he
      exact Finset.mem_image.mpr ⟨⟨e, hMS he⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  exact ⟨N, fun v ↦ by rw [← restrictEdges_degreeIn, heq]; exact hM v, heq⟩

/-- Keep all edges except those joining `u` to another vertex of `X`. -/
def crossRestriction (H : LoopMultigraph V E) (X : Finset V) (u : V) : Finset E :=
  Finset.univ.filter fun e ↦ ∀ k : Fin 2,
    H.endAt e k = u → H.endAt e (Fin.rev k) ∉ X

omit [DecidableEq E] in
@[simp] theorem mem_crossRestriction {X : Finset V} {u : V} {e : E} :
    e ∈ H.crossRestriction X u ↔
      ∀ k : Fin 2, H.endAt e k = u → H.endAt e (Fin.rev k) ∉ X := by
  simp [crossRestriction]

omit [DecidableEq E] in
theorem mem_crossRestriction_of_avoids {X : Finset V} {u : V} {e : E}
    (h0 : H.endAt e 0 ≠ u) (h1 : H.endAt e 1 ≠ u) : e ∈ H.crossRestriction X u := by
  apply mem_crossRestriction.mpr
  intro k hk
  fin_cases k
  · exact (h0 hk).elim
  · exact (h1 hk).elim

omit [DecidableEq E] in
theorem mem_crossRestriction_of_dangling {X : Finset V} {u : V} (hu : u ∈ X)
    {e : E} (he : e ∈ H.dangling X) : e ∈ H.crossRestriction X u := by
  apply mem_crossRestriction.mpr
  intro k hk hn
  have hX := mem_dangling.mp he
  fin_cases k
  · exact hX ⟨fun _ ↦ hn, fun _ ↦ hk.symm ▸ hu⟩
  · exact hX ⟨fun _ ↦ hk.symm ▸ hu, fun _ ↦ hn⟩

/-- The restriction still has a perfect matching through any boundary edge at `u`. -/
theorem IsMatchingCovered.crossRestriction_matchable (hm : H.IsMatchingCovered)
    {X : Finset V} {u v : V} (hu : u ∈ X) (hv : v ∉ X)
    {e : E} (he : H.Joins e u v) :
    ∃ N, (H.restrictEdges (H.crossRestriction X u)).IsPerfectMatching N := by
  obtain ⟨M, hM, heM⟩ := hm.2 e
  have heD : e ∈ H.dangling X := by
    apply mem_dangling.mpr
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp_all
  obtain ⟨j, hj⟩ := he.exists_end
  have hMS : M ⊆ H.crossRestriction X u := by
    intro f hf
    by_cases hfe : f = e
    · exact hfe ▸ mem_crossRestriction_of_dangling hu heD
    · apply mem_crossRestriction_of_avoids <;> intro hh <;>
        exact hfe (congrArg Prod.fst (eq_incidence_of_degreeIn_one (hM u) hf heM hh hj))
  obtain ⟨N, hN, _⟩ := hM.exists_restrictEdges hMS
  exact ⟨N, hN⟩

/-- Removing the internal edges at `u` makes the boundary of `X - u`
inadmissible, because every matching already uses its unique crossing at `u`. -/
theorem IsTightCut.crossRestriction_inadmissible {X : Finset V} (ht : H.IsTightCut X)
    {u : V} (hu : u ∈ X) :
    (H.restrictEdges (H.crossRestriction X u)).IsInadmissibleCut (X.erase u) := by
  intro M hM
  let G := H.restrictEdges (H.crossRestriction X u)
  have hpos : 0 < G.degreeIn M u := by rw [hM u]; omega
  obtain ⟨⟨e, k⟩, hk⟩ := Finset.card_pos.mp hpos
  obtain ⟨hem, hku⟩ := Finset.mem_filter.mp hk
  have heM := (Finset.mem_product.mp hem).1
  have hother := (mem_crossRestriction.mp e.2) k hku
  have heD : e.1 ∈ H.dangling X := by
    apply mem_dangling.mpr
    fin_cases k <;> simp_all [G, restrictEdges]
  have htM := ht (M.image Subtype.val) hM.of_restrictEdges
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hfM, hfD⟩ := Finset.mem_inter.mp hf
  have hd := (mem_dangling (K := H.restrictEdges (H.crossRestriction X u))).mp hfD
  change ¬ (H.endAt f.1 0 ∈ X.erase u ↔ H.endAt f.1 1 ∈ X.erase u) at hd
  have hfu (j : Fin 2) : H.endAt f.1 j ≠ u := by
    intro hj
    have hn := (mem_crossRestriction.mp f.2) j hj
    fin_cases j <;> simp_all
  have hfDX : f.1 ∈ H.dangling X := by
    apply mem_dangling.mpr
    simpa [Finset.mem_erase, hfu] using hd
  have hfe : f.1 = e.1 := Finset.card_le_one.mp htM.le _
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨f, hfM, rfl⟩, hfDX⟩) _
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨e, heM, rfl⟩, heD⟩)
  exact hfu k (hfe.symm ▸ hku)

omit [DecidableEq E] in
/-- Connectivity of the first shore survives this edge restriction. -/
theorem IsConnectedOn.crossRestriction_erase {X : Finset V} {u : V}
    (hc : H.IsConnectedOn (X.erase u)) :
    (H.restrictEdges (H.crossRestriction X u)).IsConnectedOn (X.erase u) := by
  intro c he
  apply hc c
  intro e h0 h1
  exact he ⟨e, mem_crossRestriction_of_avoids (Finset.mem_erase.mp h0).1
    (Finset.mem_erase.mp h1).1⟩ h0 h1

omit [DecidableEq E] in
/-- The opposite shore together with `u` stays connected through a boundary edge. -/
theorem IsConnectedOn.crossRestriction_compl_erase {X : Finset V} {u v : V}
    (hc : H.IsConnectedOn (Finset.univ \ X)) (hu : u ∈ X) (hv : v ∉ X)
    {e : E} (he : H.Joins e u v) :
    (H.restrictEdges (H.crossRestriction X u)).IsConnectedOn (Finset.univ \ X.erase u) := by
  intro c hedge
  have hvC : v ∈ Finset.univ \ X := by simp [hv]
  have hsub : Finset.univ \ X ⊆ Finset.univ \ X.erase u := by
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh ↦
      (Finset.mem_sdiff.mp hw).2 (Finset.mem_erase.mp hh).2⟩
  have hlocal : ∀ w ∈ Finset.univ \ X, c w = c v := by
    intro w hw
    apply hc c ?_ w hw v hvC
    intro f h0 h1
    have h0u : H.endAt f 0 ≠ u := fun h ↦ (Finset.mem_sdiff.mp h0).2 (h.symm ▸ hu)
    have h1u : H.endAt f 1 ≠ u := fun h ↦ (Finset.mem_sdiff.mp h1).2 (h.symm ▸ hu)
    exact hedge ⟨f, mem_crossRestriction_of_avoids h0u h1u⟩ (hsub h0) (hsub h1)
  have heD : e ∈ H.dangling X := by
    apply mem_dangling.mpr
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp_all
  have huc : u ∈ Finset.univ \ X.erase u := by simp
  have huv : c u = c v := by
    have hh := hedge ⟨e, mem_crossRestriction_of_dangling hu heD⟩
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact h0 ▸ h1 ▸ hh (h0.symm ▸ huc) (h1.symm ▸ hsub hvC)
    · exact (h0 ▸ h1 ▸ hh (h0.symm ▸ hsub hvC) (h1.symm ▸ huc)).symm
  have hall : ∀ w ∈ Finset.univ \ X.erase u, c w = c v := by
    intro w hw
    by_cases hwu : w = u
    · exact hwu ▸ huv
    · exact hlocal w (by simpa [hwu] using hw)
  exact fun a ha b hb ↦ (hall a ha).trans (hall b hb).symm

/-- Under the proposed brick conditions, a good tight-cut boundary vertex
can have only one neighbour on the other shore. -/
theorem IsTightCut.unique_cross_neighbor (ht : H.IsTightCut X)
    (hm : H.IsMatchingCovered) (hb : H.IsBicritical) (hc : H.ConnectedAfterDeletingPairs)
    {u v : V} (hu : u ∈ X) (hv : v ∉ X) (hX : 2 ≤ X.card)
    (hleft : H.IsConnectedOn (X.erase u))
    (hright : H.IsConnectedOn (Finset.univ \ X)) {e : E} (he : H.Joins e u v) :
    ∀ z, z ∉ X → (∃ f : E, H.Joins f u z) → z = v := by
  classical
  let S := H.crossRestriction X u
  let A := X.erase u
  have hA : A.Nonempty := Finset.card_pos.mp (by
    dsimp [A]
    rw [Finset.card_erase_of_mem hu]
    omega)
  have hAC : (Finset.univ \ A).Nonempty := ⟨u, by simp [A]⟩
  obtain ⟨N, hN⟩ := hm.crossRestriction_matchable hu hv he
  obtain ⟨B, F, hF, hshore⟩ := (ht.crossRestriction_inadmissible hu).exists_DMBarrier_in_shore
    hN hA hAC hleft.crossRestriction_erase (hright.crossRestriction_compl_erase hu hv he)
  have hgap : ∃ a, a ∉ B ∧ ∀ Q ∈ F.odd, a ∉ Q := by
    rcases hshore with ⟨hBA, hQA⟩ | ⟨hBA, hQA⟩
    · obtain ⟨a, ha⟩ := hAC
      exact ⟨a, fun h ↦ (Finset.mem_sdiff.mp ha).2 (hBA h),
        fun Q hQ h ↦ (Finset.mem_sdiff.mp ha).2 (hQA Q hQ h)⟩
    · obtain ⟨a, ha⟩ := hA
      exact ⟨a, fun h ↦ (Finset.mem_sdiff.mp (hBA h)).2 ha,
        fun Q hQ h ↦ (Finset.mem_sdiff.mp (hQA Q hQ h)).2 ha⟩
  have hS : ∀ f : E, H.endAt f 0 ≠ u → H.endAt f 1 ≠ u → f ∈ S :=
    fun _ h0 h1 ↦ mem_crossRestriction_of_avoids h0 h1
  obtain ⟨M, hM, _⟩ := hm.2 e
  obtain ⟨_, K, hK, huK⟩ := hF.isBarrier.exists_odd_part_of_restrict F hb hM hF.nonempty hS hgap
  have hQside : ∀ Q ∈ F.odd, Q ⊆ Finset.univ \ A := by
    rcases hshore with ⟨_, hQ⟩ | ⟨_, hQ⟩
    · exact (Finset.notMem_erase u X (hQ K hK huK)).elim
    · exact hQ
  have hout : ∀ Q ∈ F.odd, ∀ f : E, f ∉ S → ∀ k : Fin 2,
      H.endAt f k ∈ Q → H.endAt f k = u := by
    intro Q hQ f hf k hk
    have hh := (Finset.mem_sdiff.mp (hQside Q hQ hk)).2
    have hrem : ∃ j : Fin 2, H.endAt f j = u ∧ H.endAt f (Fin.rev j) ∈ X := by
      simpa only [S, mem_crossRestriction, not_forall, Classical.not_imp, not_not,
        exists_prop] using hf
    obtain ⟨j, hj, hjX⟩ := hrem
    by_contra hku
    apply hh
    apply Finset.mem_erase.mpr
    refine ⟨hku, ?_⟩
    fin_cases j <;> fin_cases k <;> simp_all
  obtain ⟨w, hw⟩ := hF.isBarrier.unique_neighbor_of_restrict F hb hc hM hF.nonempty hS hgap hout
  have huv : v ≠ u := fun h ↦ hv (h.symm ▸ hu)
  have through (z : V) (hz : z ∉ X) (f : E) (hf : H.Joins f u z) : f ∈ S := by
    apply mem_crossRestriction_of_dangling hu
    apply mem_dangling.mpr
    rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp_all
  have hvw := hw v huv ⟨e, through v hv e he, he⟩
  intro z hz ⟨f, hf⟩
  exact (hw z (fun h ↦ hz (h.symm ▸ hu)) ⟨f, through z hz f hf, hf⟩).trans hvw.symm

end GraphPuzzles.LoopMultigraph
