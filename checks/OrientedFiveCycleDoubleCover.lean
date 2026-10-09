import GraphPuzzles.Claims.OrientedFiveCycleDoubleCover

/-! Independent checks of Definition 1.1, Lemma 1.2 and Theorem 2.1 in
Graph Puzzles III.3-preview. The vertex and edge universes are independent. -/

open GraphPuzzles GraphPuzzles.LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

-- Every chosen optimal triple has its entire core as one indexed member.
example (hs : H.IsSnark) (hd : H.HasColoringDefect 3)
    (M : H.MatchingTriple) (hopt : M.IsOptimal) :
    ∃ D : H.OrientedCycleDoubleCover 5, ∃ i, (D.cycles i).edges = M.core :=
  Claims.defect_three_oriented_five_prescribed_core hs hd M hopt

-- Unpack both cover conditions, rather than merely checking nonemptiness.
example (hs : H.IsSnark) (hd : H.HasColoringDefect 3)
    (M : H.MatchingTriple) (hopt : M.IsOptimal) :
    ∃ D : H.OrientedCycleDoubleCover 5,
      (∃ i, (D.cycles i).edges = M.core) ∧
      (∀ e, (Finset.univ.filter fun i ↦ e ∈ (D.cycles i).edges).card = 2) ∧
      ∀ e i j, i ≠ j → e ∈ (D.cycles i).edges → e ∈ (D.cycles j).edges →
        (D.cycles i).tail e ≠ (D.cycles j).tail e := by
  obtain ⟨D, hD⟩ := Claims.defect_three_oriented_five_prescribed_core hs hd M hopt
  exact ⟨D, hD, D.coveredTwice, D.opposite⟩

example (hs : H.IsSnark) (hd : H.HasColoringDefect 3) :
    Nonempty (H.OrientedCycleDoubleCover 5) :=
  Claims.defect_three_oriented_five hs hd

example (hs : H.IsSnark) (hc : H.HasHexagonalCore) :
    Nonempty (H.OrientedCycleDoubleCover 5) :=
  Claims.hexagonal_core_oriented_five hs hc

-- The numerical core bridge retains the specified matching triple.
example (hs : H.IsSnark) (M : H.MatchingTriple) (hopt : M.IsOptimal)
    (hu : M.uncovered.card = 3) :
    ∃ ends : E → (Fin 2 ≃ Fin 2), ∃ X : (H.relabelEnds ends).Hexagon,
      X.edgeSet = M.core ∧ Nonempty X.ExteriorColoring :=
  hopt.exists_hexagonalCore_eq_core hu hs.cubic hs.loopless hs.notColourable

-- Lemma 1.2 is formalized by its more general local balance condition.
-- Reference directions are supplied arbitrarily by the caller.
example (ref : E → Fin 2) (p q : E → Fin 5) (hpq : ∀ e, p e ≠ q e)
    (hbal : ∀ w r,
      (Finset.univ.filter fun x : H.halfEdgesAt w ↦ otail ref p q x.1 = r).card =
      (Finset.univ.filter fun x : H.halfEdgesAt w ↦ ohead ref p q x.1 = r).card) :
    ∃ D : H.OrientedCycleDoubleCover 5, ∀ r,
      (D.cycles r).edges = Finset.univ.filter fun e ↦ p e = r ∨ q e = r :=
  H.exists_orientedCover_of_labels ref p q hpq hbal
