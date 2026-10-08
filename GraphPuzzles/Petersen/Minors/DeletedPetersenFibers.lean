import GraphPuzzles.Petersen.Minors.TightMinorBipartiteFibers
import GraphPuzzles.Cuts.Shores.DeletedTightShore

/-! The finite family of expansion shores in Section 6, Proposition 6.3. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

namespace PetersenFiberModel

variable (Q : H.PetersenFiberModel X)

/-- The actual original-vertex shores that were expanded from terminal vertices. -/
def nonsingletonFibers : Finset (Finset V) :=
  (Finset.univ.filter fun w ↦ 2 ≤ (Q.quotient.fiber w).card).image Q.quotient.fiber

theorem mem_nonsingletonFibers (Y : Finset V) :
    Y ∈ Q.nonsingletonFibers ↔ ∃ w, 2 ≤ (Q.quotient.fiber w).card ∧ Q.quotient.fiber w = Y := by
  simp only [nonsingletonFibers, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem nonsingletonFibers_disjoint {Y Z : Finset V}
    (hY : Y ∈ Q.nonsingletonFibers) (hZ : Z ∈ Q.nonsingletonFibers) (hne : Y ≠ Z) :
    Disjoint Y Z := by
  obtain ⟨w, _, rfl⟩ := (Q.mem_nonsingletonFibers Y).mp hY
  obtain ⟨z, _, rfl⟩ := (Q.mem_nonsingletonFibers Z).mp hZ
  exact Q.quotient.fiber_disjoint (fun h ↦ hne (congrArg Q.quotient.fiber h))

theorem vertex_card : Fintype.card Q.Vertex = 10 := by
  have hh := Fintype.card_congr Q.petersen.some.vertexEquiv
  simpa only [Fintype.card_fin] using hh

variable {e : E} (R : (H.deleteEdge e).PetersenFiberModel X)

/-- Each nonsingleton fiber is a nontrivial tight bipartite contraction
of the deleted graph and contains an endpoint of the restored edge. -/
theorem deleted_shore_properties (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) :
    IsNontrivialCut Y ∧ (H.deleteEdge e).IsTightCut Y ∧
      ((H.deleteEdge e).contract Y).IsBipartite ∧ e ∈ H.meets Y := by
  obtain ⟨w, hw, rfl⟩ := (R.mem_nonsingletonFibers Y).mp hY
  have hnt := R.quotient.fiber_nontrivial (by rw [R.vertex_card]; decide) hw
  have ht := R.quotient.tight_fiber w
  have hs := ht.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hnt.1; omega))
    (Finset.card_pos.mp (by have hh := hnt.2; omega))
  have hB := (hbi w).contract_of_separating hs
  exact ⟨hnt, ht, hB, hb.edge_meets_deleted_tight_shore hr hnt ht hB⟩

/-- There are at most two expansion shores. -/
theorem card_nonsingletonFibers_le_two (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w)) :
    R.nonsingletonFibers.card ≤ 2 := by
  apply hb.card_deleted_tight_shores_le_two hr
    (fun _ hY _ hZ hne ↦ R.nonsingletonFibers_disjoint hY hZ hne)
  intro Y hY
  have hh := R.deleted_shore_properties hb hr hm hbi hY
  exact ⟨hh.1, hh.2.1, hh.2.2.1⟩

/-- An internal restored edge places every expansion shore on its own
side of the selected cut. -/
theorem deleted_shore_subset (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (heX : ∀ k, H.endAt e k ∈ X) {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) :
    Y ⊆ X := by
  have hh := R.deleted_shore_properties hb hr hm hbi hY
  obtain ⟨w, _, rfl⟩ := (R.mem_nonsingletonFibers Y).mp hY
  apply hb.deleted_tight_shore_subset hr heX hh.1 hh.2.1 hh.2.2.1
  simpa only [R.selected_eq] using R.quotient.fiber_side R.cut w

theorem deleted_shore_restoration (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) :
    Nonempty (H.BipartiteRestorationShore e Y) := by
  have hh := R.deleted_shore_properties hb hr hm hbi hY
  exact hb.bipartiteRestorationShore hr hh.1 hh.2.1 hh.2.2.1

end PetersenFiberModel

/-- Package a deleted-edge Petersen certificate with the expansion-shore
properties needed by the subsequent matching constructions. -/
theorem IsBrick.exists_deletedPetersenFibers (hb : H.IsBrick) {e : E}
    (hr : H.IsRemovable e) (hn : (H.deleteEdge e).IsNearBrick)
    (hp : (H.deleteEdge e).HasTightPetersenMinor X) :
    ∃ R : (H.deleteEdge e).PetersenFiberModel X,
      (∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w)) ∧
      R.nonsingletonFibers.card ≤ 2 ∧
      (∀ Y ∈ R.nonsingletonFibers, IsNontrivialCut Y ∧ (H.deleteEdge e).IsTightCut Y ∧
        ((H.deleteEdge e).contract Y).IsBipartite ∧ e ∈ H.meets Y) ∧
      ((∀ k, H.endAt e k ∈ X) → ∀ Y ∈ R.nonsingletonFibers, Y ⊆ X) := by
  obtain ⟨R, hR⟩ := hp.exists_bipartite_fiberModel hn
  exact ⟨R, hR, R.card_nonsingletonFibers_le_two hb hr hn.matchingCovered hR,
    fun _ hY ↦ R.deleted_shore_properties hb hr hn.matchingCovered hR hY,
    fun heX _ hY ↦ R.deleted_shore_subset hb hr hn.matchingCovered hR heX hY⟩

end GraphPuzzles.LoopMultigraph
