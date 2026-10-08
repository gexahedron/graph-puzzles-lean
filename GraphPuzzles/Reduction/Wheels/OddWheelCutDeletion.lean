import GraphPuzzles.Reduction.Wheels.OddWheelCutReduction
import GraphPuzzles.Reduction.Wheels.OddWheelRemovability

/-! The avoided-edge part of Proposition 6.8 and its final-case consequence. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A perfect matching avoiding the deleted edge preserves nontightness.
Near-brick contractions then reconstruct a near-brick. -/
theorem IsPerfectMatching.nearBrick_deleteEdge_of_contractions {M : Finset E}
    (hM : H.IsPerfectMatching M) {e : E} (heM : e ∉ M) {X : Finset V}
    (hcross : 1 < (M ∩ H.dangling X).card)
    (hl : ((H.deleteEdge e).contract X).IsNearBrick)
    (hr : ((H.deleteEdge e).contract (Finset.univ \ X)).IsNearBrick) :
    (H.deleteEdge e).IsNearBrick ∧ (H.deleteEdge e).IsRobustCut X := by
  obtain ⟨N, hN, hNM⟩ := hM.exists_restrictEdges
    (S := Finset.univ.erase e) (by intro f hf; simp [ne_of_mem_of_not_mem hf heM])
  have hnt : ¬ (H.deleteEdge e).IsTightCut X := by
    intro ht
    have hh := ht N hN
    change (N ∩ (H.restrictEdges (Finset.univ.erase e)).dangling X).card = 1 at hh
    rw [← restrictEdges_crossing (H := H) (Finset.univ.erase e) N X, hNM] at hh
    omega
  have hrob : (H.deleteEdge e).IsRobustCut X := ⟨hnt, hl, hr⟩
  have hX := hM.nontrivial_of_crossing_gt_one hcross
  have hmc := hrob.isSeparatingCut.isMatchingCovered
    (Finset.card_pos.mp (by have := hX.2; omega))
  exact ⟨hrob.isNearBrick hmc, hrob⟩

/-- Each original cut label is a removable spoke of a sufficiently large
odd-wheel contraction. -/
theorem OddWheel.isRemovable_cut_label {X : Finset V}
    (W : (H.contract X).OddWheel none) (h5 : 5 ≤ X.card)
    {e : E} (he : e ∈ H.dangling X) :
    (H.contract X).IsRemovable ⟨e, dangling_subset_meets X he⟩ := by
  have hlen : W.labels.length = X.card := by
    have hh := W.rim_card_eq_length
    simp only [Finset.card_erase_of_mem (Finset.mem_univ none), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe, Nat.add_sub_cancel] at hh
    exact hh.symm
  let a : H.meets X := ⟨e, dangling_subset_meets X he⟩
  have hex : ∃ k, (H.contract X).endAt a k = none := by
    by_cases h0 : H.endAt e 0 ∈ X
    · refine ⟨1, (contract_endAt_eq_none_iff _ _ _).mpr ?_⟩
      have hh := mem_dangling.mp he
      tauto
    · exact ⟨0, (contract_endAt_eq_none_iff _ _ _).mpr h0⟩
  obtain ⟨k, hk⟩ := hex
  apply W.isRemovable_spoke (by omega) (w := (H.contract X).endAt a (Fin.rev k))
  fin_cases k
  · exact Or.inl ⟨hk, rfl⟩
  · exact Or.inr ⟨rfl, hk⟩

/-- In the two-wheel case, every cut edge avoided by a nontight matching
is b-removable. This is the avoided-edge branch of Proposition 6.8. -/
theorem IsRobustCut.deleteEdge_of_avoided_oddWheel_spoke {X : Finset V}
    (hr : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card) {e : E}
    (he : e ∈ H.dangling X) (heM : e ∉ M) :
    (H.deleteEdge e).IsNearBrick ∧ (H.deleteEdge e).IsRobustCut X := by
  obtain ⟨Wl⟩ := hwl
  obtain ⟨Wr⟩ := hwr
  have hc : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
  have hcl : 5 ≤ X.card := h5.trans (hM.crossing_le_card X)
  have hcr : 5 ≤ (Finset.univ \ X).card := by
    have hh := hM.crossing_le_card (Finset.univ \ X)
    rw [dangling_compl] at hh
    omega
  have hl := (deleteContractIso X ⟨e, dangling_subset_meets X he⟩).symm.isNearBrick
    (hr.leftNear.deleteEdge_of_solid hsl (Wl.isRemovable_cut_label hcl he))
  have hh := (deleteContractIso (Finset.univ \ X) ⟨e, dangling_subset_meets _ hc⟩).symm.isNearBrick
    (hr.rightNear.deleteEdge_of_solid hsr (Wr.isRemovable_cut_label hcr hc))
  exact hM.nearBrick_deleteEdge_of_contractions heM (by omega) hl hh

/-- If no selected cut edge is b-removable, every nontight matching of
size at least five contains the entire selected cut. -/
theorem IsRobustCut.cut_subset_matching_of_oddWheels {X : Finset V}
    (hr : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card)
    (hdel : ∀ e ∈ H.dangling X, ¬ (H.deleteEdge e).IsNearBrick) :
    H.dangling X ⊆ M := by
  intro e he
  by_contra heM
  exact hdel e he (hr.deleteEdge_of_avoided_oddWheel_spoke hsl hsr hwl hwr hM h5 he heM).1

/-- Every retained rim vertex has an original edge crossing the shore. -/
theorem IsOddWheel.exists_incident_cut_edge {X : Finset V}
    (hw : (H.contract X).IsOddWheel none) {w : V} (hwX : w ∈ X) :
    ∃ e ∈ H.dangling X, ∃ k, H.endAt e k = w := by
  obtain ⟨W⟩ := hw
  obtain ⟨e, he⟩ := W.spokes (some ⟨w, hwX⟩) (by simp)
  obtain ⟨z, hz, hj⟩ := (contract_joins_none_some e ⟨w, hwX⟩).mp he
  refine ⟨e.1, ?_, (H.joins_comm.mp hj).exists_end⟩
  rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simp [mem_dangling, h0, h1, hwX, hz]

/-- A matching containing all spokes of two opposite wheel contractions
equals the whole selected cut. In particular that cut is a perfect matching. -/
theorem IsPerfectMatching.eq_cut_of_oddWheel_contractions {X : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatching M) (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hsub : H.dangling X ⊆ M) : M = H.dangling X := by
  have hpos (w : V) : 0 < H.degreeIn (H.dangling X) w := by
    have hex : ∃ e ∈ H.dangling X, ∃ k, H.endAt e k = w := by
      by_cases hw : w ∈ X
      · exact hwl.exists_incident_cut_edge hw
      · simpa only [dangling_compl] using hwr.exists_incident_cut_edge (by simp [hw])
    exact (H.degreeIn_pos_iff_mem_edgeSupport _ w).mpr (H.mem_edgeSupport_iff.mpr hex)
  have hc : H.IsPerfectMatching (H.dangling X) := by
    intro w
    have hle : H.degreeIn (H.dangling X) w ≤ H.degreeIn M w := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hsub (Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩, he⟩
    have hh := hM w
    have hh' := hpos w
    omega
  exact (hc.eq_of_subset hM hsub).symm

end GraphPuzzles.LoopMultigraph
