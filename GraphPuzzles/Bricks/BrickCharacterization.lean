import GraphPuzzles.Cuts.TightCutRestriction
import GraphPuzzles.Cuts.TightCutPairDeletion

/-!
# The tight-cut characterization of bricks

The bicritical case of the Edmonds--Lovász--Pulleyblank argument: a
matching-covered graph with connected pair deletions and no nontrivial
barrier has no nontrivial tight cut. The proof uses the minimal-shore and
DM-barrier lemmas, without an external matching-theoretic input.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Both shores of a separating cut induce connected graphs. -/
theorem IsSeparatingCut.connectedOn {X : Finset V} (hs : H.IsSeparatingCut X) :
    H.IsConnectedOn X := by
  have hh := hs.1.connectedOn_delete none
  have heq : contractShore X X = Finset.univ.erase none := by
    ext v
    cases v with
    | none => simp
    | some v => simp [v.2]
  rw [← heq] at hh
  exact (contract_connectedOn_iff (Finset.Subset.refl X)).mp hh

/-- Bicriticality and connectivity after deleting two vertices exclude
every nontrivial tight cut in a matching-covered graph. -/
theorem IsBicritical.tight_trivial (hb : H.IsBicritical) (hm : H.IsMatchingCovered)
    (hc : H.ConnectedAfterDeletingPairs) :
    ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X := by
  intro X ht hX
  obtain ⟨Y, htY, hY, u, hu, v, hv, e, he, hleft, hright⟩ :=
    hm.exists_tight_cut_with_good_edge ⟨X, ht, hX⟩
  have hs := htY.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  have huonly := htY.unique_cross_neighbor hm hb hc hu hv hY.1 hleft hs.compl.connectedOn he
  have hvY : v ∈ Finset.univ \ Y := by simp [hv]
  have huYC : u ∉ Finset.univ \ Y := by simp [hu]
  have hvonly := htY.compl.unique_cross_neighbor hm hb hc hvY huYC hY.2 hright
    (by simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y)] using hs.connectedOn)
    (H.joins_comm.mp he)
  exact htY.not_bicritical_of_mutual_unique hm hb hY hu hv he hleft hright huonly
    (fun z hz hh ↦ hvonly z (by simp [hz]) hh)

/-- The converse direction of the brick characterization. -/
theorem IsMatchingCovered.isBrick_of_bicritical (hm : H.IsMatchingCovered)
    (hnb : ¬ H.IsBipartite) (hb : H.IsBicritical) (hc : H.ConnectedAfterDeletingPairs) :
    H.IsBrick := ⟨hnb, hm, hb.tight_trivial hm hc⟩

/-- The brick definition by tight cuts agrees with the bicritical and
pair-deletion characterization in the endpoint-multigraph model. -/
theorem isBrick_iff_bicritical_connectedAfterDeletingPairs :
    H.IsBrick ↔ ¬ H.IsBipartite ∧ H.IsMatchingCovered ∧
      H.IsBicritical ∧ H.ConnectedAfterDeletingPairs := by
  constructor
  · intro h
    exact ⟨h.notBipartite, h.matchingCovered, h.isBicritical h.matchingCovered.loopless,
      h.connectedAfterDeletingPairs h.matchingCovered.loopless⟩
  · rintro ⟨hn, hm, hb, hc⟩
    exact hm.isBrick_of_bicritical hn hb hc

end GraphPuzzles.LoopMultigraph
