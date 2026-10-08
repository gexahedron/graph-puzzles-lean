import GraphPuzzles.Reduction.Removable.RemovableNearBrick

/-! Lifting an internal removable edge from a solid robust-cut contraction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Matching-covered contractions reconstruct a matching-covered graph. -/
theorem IsSeparatingCut.isMatchingCovered {X : Finset V} (hs : H.IsSeparatingCut X)
    (hXC : (Finset.univ \ X).Nonempty) : H.IsMatchingCovered := by
  refine ⟨?_, fun e ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hXC
    intro c he u v
    let d : Option X → Bool := fun t ↦ t.elim (c w) (fun t ↦ c t.1)
    have hd (a : V) : d (contractVertex X a) = c a := by
      by_cases ha : a ∈ X
      · simp [d, contractVertex, ha]
      · simpa only [contractVertex, dif_neg ha, d, Option.elim_none] using
          hs.compl.connectedOn c (fun e _ _ ↦ he e) w hw a (by simp [ha])
    have hdc (e : H.meets X) : d ((H.contract X).endAt e 0) =
        d ((H.contract X).endAt e 1) := by
      change d (contractVertex X (H.endAt e.1 0)) = d (contractVertex X (H.endAt e.1 1))
      rw [hd, hd, he]
    have hconst (a : V) : c a = c w := by
      by_cases ha : a ∈ X
      · exact hs.1.1 d hdc (some ⟨a, ha⟩) none
      · exact hs.compl.connectedOn c (fun e _ _ ↦ he e) a (by simp [ha]) w hw
    exact (hconst u).trans (hconst v).symm
  · obtain ⟨M, hM, he, _⟩ := hs.exists_perfectMatching_through e
    exact ⟨M, hM, he⟩

/-- Deleting a retained edge commutes with contraction. -/
def deleteContractIso (X : Finset V) (e : H.meets X) :
    EndpointIso ((H.deleteEdge e.1).contract X) ((H.contract X).deleteEdge e) := by
  have heq : (Finset.univ.filter fun f : H.meets X ↦ f.1 ∈ Finset.univ.erase e.1) =
      Finset.univ.erase e := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact not_congr Subtype.val_inj
  have hi := restrictContractIso (H := H) (Finset.univ.erase e.1) X
  rw [heq] at hi
  exact hi

/-- An edge outside a retained shore disappears in its contraction. -/
def deleteAwayContractIso (X : Finset V) (e : E) (he : e ∉ H.meets X) :
    EndpointIso ((H.deleteEdge e).contract X) (H.contract X) where
  vertexEquiv := Equiv.refl _
  edgeEquiv :=
    { toFun := fun f ↦ ⟨f.1.1, (restrictEdges_mem_meets _ f.1 X).mp f.2⟩
      invFun := fun f ↦ ⟨⟨f.1, Finset.mem_erase.mpr
        ⟨fun h ↦ he (h ▸ f.2), Finset.mem_univ _⟩⟩,
        (restrictEdges_mem_meets _ _ X).mpr f.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  endEquiv _ := Equiv.refl _
  map_endAt _ _ := rfl

/-- The edge-lifting step in Campos--Lucchesi Proposition 6.7. An internal
removable edge of a solid robust-cut contraction, avoided by a matching that
crosses the cut more than once, is removable in the original graph and leaves
a near-brick with the same robust cut. -/
theorem IsRobustCut.deleteEdge_of_internal_removable {X : Finset V}
    (hr : H.IsRobustCut X) (hs : (H.contract X).IsSolid) {e : H.meets X}
    (heX : ∀ k, H.endAt e.1 k ∈ X) (heR : (H.contract X).IsRemovable e)
    {M : Finset E} (hM : H.IsPerfectMatching M) (heM : e.1 ∉ M)
    (hcross : 1 < (M ∩ H.dangling X).card) :
    H.IsRemovable e.1 ∧ (H.deleteEdge e.1).IsRobustCut X ∧
      (H.deleteEdge e.1).IsNearBrick := by
  have hl : ((H.deleteEdge e.1).contract X).IsNearBrick :=
    (deleteContractIso X e).symm.isNearBrick (hr.leftNear.deleteEdge_of_solid hs heR)
  have heXC : e.1 ∉ H.meets (Finset.univ \ X) := by
    intro he
    obtain ⟨k, hk⟩ := mem_meets.mp he
    exact (Finset.mem_sdiff.mp hk).2 (heX k)
  have hright : ((H.deleteEdge e.1).contract (Finset.univ \ X)).IsNearBrick :=
    (deleteAwayContractIso (Finset.univ \ X) e.1 heXC).symm.isNearBrick hr.rightNear
  obtain ⟨N, hN, hNM⟩ := hM.exists_restrictEdges
    (S := Finset.univ.erase e.1) (by intro f hf; simp [ne_of_mem_of_not_mem hf heM])
  have hn : ¬ (H.deleteEdge e.1).IsTightCut X := by
    intro ht
    have hh := ht N hN
    change (N ∩ (H.restrictEdges (Finset.univ.erase e.1)).dangling X).card = 1 at hh
    rw [← restrictEdges_crossing (H := H) (Finset.univ.erase e.1) N X, hNM] at hh
    omega
  have hrob : (H.deleteEdge e.1).IsRobustCut X := ⟨hn, hl, hright⟩
  have hnt := hM.nontrivial_of_crossing_gt_one hcross
  have hmc := hrob.isSeparatingCut.isMatchingCovered
    (Finset.card_pos.mp (by have hh := hnt.2; omega))
  exact ⟨hmc, hrob, hrob.isNearBrick hmc⟩

end GraphPuzzles.LoopMultigraph
