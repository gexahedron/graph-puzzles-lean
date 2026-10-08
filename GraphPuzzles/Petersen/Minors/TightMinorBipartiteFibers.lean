import GraphPuzzles.Petersen.Minors.TightMinorFibers
import GraphPuzzles.Petersen.Minors.TightPetersenBipartite
import GraphPuzzles.Cuts.Contraction.BipartiteFiberLift

/-! In a near-brick, the fibers of a terminal Petersen model induce bipartite subgraphs. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A near-brick Petersen certificate flattens into tight fibers that are
all bipartite on the original vertex set. -/
theorem HasTightPetersenMinor.exists_bipartite_fiberModel {X : Finset V}
    (h : H.HasTightPetersenMinor X) (hn : H.IsNearBrick) :
    ∃ Q : H.PetersenFiberModel X, ∀ w, H.IsBipartiteOn (Q.quotient.fiber w) := by
  induction h with
  | @here V E _ _ _ _ G S hp hs =>
    let Q : G.PetersenFiberModel S := {
      Vertex := _
      Edge := _
      graph := _
      quotient := TightVertexQuotient.refl _
      petersen := hp
      cut := _
      strict := hs
      selected_eq := by ext v; simp [TightVertexQuotient.preimage, TightVertexQuotient.refl] }
    refine ⟨Q, ?_⟩
    intro w
    have he : Q.quotient.fiber w = {w} := by
      ext v
      simp [Q, TightVertexQuotient.fiber, TightVertexQuotient.preimage, TightVertexQuotient.refl]
    rw [he]
    exact (bipartite_contract_of_card_le_one hn.matchingCovered.loopless
      (by simp : ({w} : Finset _).card ≤ 1)).induced_of_contract
  | contract Y ht hY X hp tail ih =>
    have hb := hn.tight_contractions_of_petersenMinor ht hY tail
    obtain ⟨Q, hQ⟩ := ih hb.1
    let R := TightVertexQuotient.prependContract ht
      (Finset.card_pos.mp (by have := hY.2; omega)) Q.quotient
    let P : PetersenFiberModel _ (sourceShore Y X) := {
      Vertex := Q.Vertex
      Edge := Q.Edge
      graph := Q.graph
      quotient := R
      petersen := Q.petersen
      cut := Q.cut
      strict := Q.strict
      selected_eq := by
        have he : R.preimage Q.cut = expandedContractShore Y (Q.quotient.preimage Q.cut) := by
          ext v
          simp [R, TightVertexQuotient.prependContract]
        rw [he, Q.selected_eq, expandedContractShore_eq_source Y X hp] }
    refine ⟨P, ?_⟩
    intro w
    have he : R.fiber w = expandedContractShore Y (Q.quotient.fiber w) := by
      ext v
      simp [R, TightVertexQuotient.prependContract]
    change IsBipartiteOn _ (R.fiber w)
    rw [he]
    exact (hQ w).expandedContractShore hb.2
  | compl _ ih =>
    obtain ⟨Q, hQ⟩ := ih hn
    exact ⟨{ Q with
      cut := Finset.univ \ Q.cut
      strict := Q.strict.compl
      selected_eq := by rw [Q.quotient.preimage_compl, Q.selected_eq] }, hQ⟩
  | iso f _ ih =>
    obtain ⟨Q, hQ⟩ := ih (f.symm.isNearBrick hn)
    let P : PetersenFiberModel _ _ := {
      Vertex := Q.Vertex
      Edge := Q.Edge
      graph := Q.graph
      quotient := Q.quotient.mapSource f
      petersen := Q.petersen
      cut := Q.cut
      strict := Q.strict
      selected_eq := by
        have he : (Q.quotient.mapSource f).preimage Q.cut =
            f.mapVertices (Q.quotient.preimage Q.cut) := by
          ext v
          obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
          simp [TightVertexQuotient.mapSource, f.mem_mapVertices]
        rw [he, Q.selected_eq] }
    refine ⟨P, ?_⟩
    intro w
    have he : (Q.quotient.mapSource f).fiber w = f.mapVertices (Q.quotient.fiber w) := by
      ext v
      obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
      simp [TightVertexQuotient.mapSource, f.mem_mapVertices]
    change IsBipartiteOn _ ((Q.quotient.mapSource f).fiber w)
    rw [he]
    exact f.isBipartiteOn (hQ w)

end GraphPuzzles.LoopMultigraph
