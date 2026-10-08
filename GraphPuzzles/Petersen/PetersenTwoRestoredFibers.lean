import GraphPuzzles.Petersen.PetersenTwoExpansionMatching
import GraphPuzzles.Petersen.PetersenAdjacentExpansionMatching
import GraphPuzzles.Petersen.PetersenBoundaryFibers

/-! Assembling the two-nonsingleton-fiber part of Section 6, Case 6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- If both restored-edge endpoints lie in different expanded fibers on
one shore, the adjacent and nonadjacent Petersen patches give three crossings. -/
theorem exists_three_crossing_two_restored_fibers
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (heX : ∀ k, H.endAt e k ∈ X)
    (hne : R.canonicalVertex (H.endAt e 0) ≠ R.canonicalVertex (H.endAt e 1))
    (h0 : 2 ≤ (R.canonicalFiber (R.canonicalVertex (H.endAt e 0))).card)
    (h1 : 2 ≤ (R.canonicalFiber (R.canonicalVertex (H.endAt e 1))).card) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  let p := R.canonicalVertex (H.endAt e 0)
  let q := R.canonicalVertex (H.endAt e 1)
  have hpF : R.canonicalFiber p ∈ R.nonsingletonFibers :=
    (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm p, h0, rfl⟩
  have hqF : R.canonicalFiber q ∈ R.nonsingletonFibers :=
    (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm q, h1, rfl⟩
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hpF
  obtain ⟨Q⟩ := R.deleted_shore_restoration hb hr hm hbi hqF
  have small_end {r : Fin 10} (S : H.BipartiteRestorationShore e (R.canonicalFiber r))
      {k : Fin 2} (hk : R.canonicalVertex (H.endAt e k) = r) : H.endAt e k ∈ S.small := by
    have hs : H.endAt e k ∈ S.small ∪ S.large := S.union_eq.symm ▸ (R.mem_canonicalFiber _ _).mpr hk
    exact (Finset.mem_union.mp hs).resolve_right (S.edge_avoids_large k)
  have hv := small_end P (k := 0) rfl
  have hw := small_end Q (k := 1) rfl
  have hs : ∀ r, r ≠ p → r ≠ q → (R.canonicalFiber r).card ≤ 1 :=
    fun _ hp hq ↦ R.singleton_away_from_restored_endpoints hb hr hm hbi hp hq
  have hp : p ∈ R.canonicalCut := (R.mem_canonicalCut _).mpr (heX 0)
  have hq : q ∈ R.canonicalCut := (R.mem_canonicalCut _).mpr (heX 1)
  have he : H.Joins e (H.endAt e 0) (H.endAt e 1) := Or.inl ⟨rfl, rfl⟩
  by_cases hadj : ∃ f, LoopMultigraph.petersen.Joins f p q
  · exact R.exists_three_crossing_adjacent_expansions P Q (hb.isBicritical hb.matchingCovered.loopless)
      (hb.connectedAfterDeletingPairs hb.matchingCovered.loopless) h0 hs he hv hw hne.symm hp hq hadj
  · exact R.exists_three_crossing_two_expansions P Q (hb.isBicritical hb.matchingCovered.loopless) hs he hv hw
      hne.symm hp hq (fun f hf ↦ hadj ⟨f, hf⟩)

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
