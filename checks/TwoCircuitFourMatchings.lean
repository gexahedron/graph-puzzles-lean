import GraphPuzzles

/-! Independent checks of the prescribed matching, exact index, permutation corollary
and fully discharged matching-theory inputs in Graph Puzzles IV.2-preview. -/

open GraphPuzzles GraphPuzzles.LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

example (F : H.TwoCircuitFactor) (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    ∃ M : Fin 4 → Finset E, M 0 = Finset.univ \ (F.A.edges ∪ F.B.edges) ∧
      (∀ i w, H.degreeIn (M i) w = 1) ∧ ∀ e, ∃ i, e ∈ M i :=
  Claims.two_circuit_four_matchings_prescribed F hs hnotP

example (F : H.TwoCircuitFactor) (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    (∃ M : Fin 4 → Finset E, (∀ i w, H.degreeIn (M i) w = 1) ∧
      ∀ e, ∃ i, e ∈ M i) ∧
    ∀ k < 4, ¬ ∃ M : Fin k → Finset E,
      (∀ i w, H.degreeIn (M i) w = 1) ∧ ∀ e, ∃ i, e ∈ M i :=
  Claims.two_circuit_perfect_matching_index_four F hs hnotP

example (F : H.TwoCircuitFactor) (hF : F.IsInduced)
    (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    Claims.PerfectMatchingIndexEq H 4 ∧
      ∃ M : Fin 4 → Finset E, M 0 = F.compl ∧
        (∀ i w, H.degreeIn (M i) w = 1) ∧ ∀ e, ∃ i, e ∈ M i :=
  Claims.permutation_four_matchings F hF hs hnotP

example : KMThreePole.{u, v} := Claims.karabas_macajova

example (hs : H.IsSimple) (hb : H.IsBrick) (hnotP : ¬ H.IsPetersen)
    (X : Finset V) (hX : H.IsSeparatingCut X) (hnt : IsNontrivialCut X) :
    ∃ N, H.IsPerfectMatching N ∧ (N ∩ H.dangling X).card = 3 :=
  Claims.campos_lucchesi H hs hb hnotP X hX hnt
