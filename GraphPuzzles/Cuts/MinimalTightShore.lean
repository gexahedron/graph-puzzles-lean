import GraphPuzzles.Cuts.Shores.PeripheralVertex
import GraphPuzzles.Cuts.Shores.TerminalConnectivity
import GraphPuzzles.Cuts.Contraction.ContractionConnectivity
import GraphPuzzles.Bricks.NearBrick

/-!
# Minimal shores of nontrivial tight cuts

A minimal nontrivial tight shore has a boundary edge whose two ends can be
deleted from their respective induced shores without disconnecting them.
This is the minimal-shore lemma used in the ELP proof.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- An inclusion-minimal shore defining a nontrivial tight cut. -/
structure IsMinimalTightShore (H : LoopMultigraph V E) (X : Finset V) : Prop where
  isTightCut : H.IsTightCut X
  nontrivial : IsNontrivialCut X
  minimal : ∀ Y, Y ⊆ X → H.IsTightCut Y → IsNontrivialCut Y → Y = X

/-- A nontrivial tight cut supplies an inclusion-minimal tight shore. -/
theorem exists_minimal_tight_shore
    (hex : ∃ X : Finset V, H.IsTightCut X ∧ IsNontrivialCut X) :
    ∃ X, H.IsMinimalTightShore X := by
  classical
  let C := Finset.univ.filter fun X : Finset V ↦ H.IsTightCut X ∧ IsNontrivialCut X
  obtain ⟨X₀, ht₀, hn₀⟩ := hex
  have hC : C.Nonempty := ⟨X₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀, hn₀⟩⟩
  obtain ⟨X, hX, hmin⟩ := C.exists_min_image Finset.card hC
  obtain ⟨ht, hn⟩ := (Finset.mem_filter.mp hX).2
  refine ⟨X, ht, hn, ?_⟩
  intro Y hYX htY hnY
  exact Finset.eq_of_subset_of_card_le hYX (hmin Y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htY, hnY⟩))

/-- The contraction retaining a minimal tight shore has no nontrivial tight cut. -/
theorem IsMinimalTightShore.contract_terminal {X : Finset V} (hX : H.IsMinimalTightShore X) :
    ∀ Y, (H.contract X).IsTightCut Y → ¬ IsNontrivialCut Y := by
  intro Y htY hnY
  have hex : ∃ R : Finset (Option X), none ∉ R ∧
      (H.contract X).IsTightCut R ∧ IsNontrivialCut R := by
    by_cases hn : none ∈ Y
    · exact ⟨Finset.univ \ Y, by simp [hn], htY.compl, hnY.compl⟩
    · exact ⟨Y, hn, htY, hnY⟩
  obtain ⟨R, hnR, htR, hR⟩ := hex
  have heq := hX.minimal (sourceShore X R) (sourceShore_subset X R)
    (hX.isTightCut.lift_contract htR hnR) (hX.nontrivial.sourceShore hR hnR)
  have hcard := card_sourceShore X R hnR
  rw [heq] at hcard
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_coe] at hsum
  have hh := hR.2
  omega

/-- Carvalho--Lucchesi--Murty Lemma 3.1: a minimal nontrivial tight shore
has a boundary edge whose ends leave connected induced shores after deletion. -/
theorem IsMinimalTightShore.exists_good_boundary_edge {X : Finset V}
    (hX : H.IsMinimalTightShore X) (hm : H.IsMatchingCovered) :
    ∃ u ∈ X, ∃ v, v ∉ X ∧ ∃ e : E, H.Joins e u v ∧
      H.IsConnectedOn (X.erase u) ∧ H.IsConnectedOn ((Finset.univ \ X).erase v) := by
  have hXne : X.Nonempty := Finset.card_pos.mp (by have hh := hX.nontrivial.1; omega)
  have hXCne : (Finset.univ \ X).Nonempty :=
    Finset.card_pos.mp (by have hh := hX.nontrivial.2; omega)
  have hs := hX.isTightCut.isSeparatingCut hm hXne hXCne
  have hS : (Finset.univ.erase (none : Option ↥(Finset.univ \ X))).Nonempty := by
    obtain ⟨v, hv⟩ := hXCne
    exact ⟨some ⟨v, hv⟩, by simp⟩
  obtain ⟨w, hwn, f, hf, hc⟩ := hs.2.exists_neighbor_connected_delete none hS
  cases w with
  | none => exact (hwn rfl).elim
  | some v =>
    obtain ⟨u, hu, hj⟩ := (contract_joins_none_some f v).mp hf
    have huX : u ∈ X := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hu
    have hvX : v.1 ∉ X := (Finset.mem_sdiff.mp v.2).2
    have hcR := (contract_connectedOn_delete_iff (Finset.univ \ X) v).mp hc
    let uX : X := ⟨u, huX⟩
    have heL : f.1 ∈ H.meets X := by
      obtain ⟨k, hk⟩ := hj.exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ huX⟩
    let g : H.meets X := ⟨f.1, heL⟩
    have hg : (H.contract X).Joins g none (some uX) :=
      (contract_joins_none_some g uX).mpr ⟨v.1, hvX, H.joins_comm.mp hj⟩
    have hcL := hs.1.connectedOn_delete_adjacent_of_no_tight hX.contract_terminal
      (show (none : Option X) ≠ some uX by simp) hg
    exact ⟨u, huX, v.1, hvX, f.1, hj,
      (contract_connectedOn_delete_iff X uX).mp hcL, hcR⟩

/-- A matching-covered graph with a nontrivial tight cut has one with the
good boundary edge required by the ELP barrier argument. -/
theorem IsMatchingCovered.exists_tight_cut_with_good_edge (hm : H.IsMatchingCovered)
    (hex : ∃ X : Finset V, H.IsTightCut X ∧ IsNontrivialCut X) :
    ∃ X, H.IsTightCut X ∧ IsNontrivialCut X ∧
      ∃ u ∈ X, ∃ v, v ∉ X ∧ ∃ e : E, H.Joins e u v ∧
        H.IsConnectedOn (X.erase u) ∧ H.IsConnectedOn ((Finset.univ \ X).erase v) := by
  obtain ⟨X, hX⟩ := exists_minimal_tight_shore hex
  exact ⟨X, hX.isTightCut, hX.nontrivial, hX.exists_good_boundary_edge hm⟩

end GraphPuzzles.LoopMultigraph
