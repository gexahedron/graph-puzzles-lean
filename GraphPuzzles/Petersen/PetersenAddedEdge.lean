import GraphPuzzles.Petersen.PetersenAddedEdgeCertificate
import GraphPuzzles.Petersen.PetersenCuts
import GraphPuzzles.Reduction.Parallel.ParallelReduction
import GraphPuzzles.Reduction.Removable.EdgeRestriction

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

private def petersenAddedEdgeMap {e : E} (f : EndpointIso (H.deleteEdge e) petersen)
    (g : E) : Fin 16 :=
  if h : g = e then 15 else (f.edgeEquiv ⟨g, by simp [h]⟩).castSucc

private noncomputable def petersenAddedReduction {e : E}
    (f : EndpointIso (H.deleteEdge e) petersen) :
    ParallelReduction H
      (petersenAddEdge (f.vertexEquiv (H.endAt e 0)) (f.vertexEquiv (H.endAt e 1))) where
  vertexEquiv := f.vertexEquiv
  edgeMap := petersenAddedEdgeMap f
  edge_surjective t := by
    by_cases ht : t.val < 15
    · let g := f.edgeEquiv.symm ⟨t.val, ht⟩
      refine ⟨g.val, ?_⟩
      have hg : g.val ≠ e := (Finset.mem_erase.mp g.property).1
      simp only [petersenAddedEdgeMap, dif_neg hg]
      change (f.edgeEquiv (f.edgeEquiv.symm ⟨t.val, ht⟩)).castSucc = t
      simp only [Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · have heq : t = 15 := Fin.ext (by have h := t.isLt; omega)
      exact ⟨e, by simp [petersenAddedEdgeMap, heq]⟩
  joins_iff g a b := by
    by_cases hg : g = e
    · subst g
      simp [petersenAddedEdgeMap, Joins, petersenAddEdge]
    · let g' : Finset.univ.erase e := ⟨g, by simp [hg]⟩
      simpa [petersenAddedEdgeMap, hg, Joins, petersenAddEdge,
        (f.edgeEquiv g').isLt, g', deleteEdge, restrictEdges] using f.joins_iff g' a b

/-- The labelled added-edge construction handles either canonical orientation. -/
theorem petersenAddEdge_exists_crossing_three (u v : Fin 10)
    (hne : u ≠ v) (hnew : ∀ e, ¬ petersen.Joins e u v)
    {X : Finset (Fin 10)} (hs : petersen.IsSeparatingCut X)
    (hX : IsNontrivialCut X) :
    ∃ M, (petersenAddEdge u v).IsPerfectMatching M ∧
      (M ∩ (petersenAddEdge u v).dangling X).card = 3 := by
  obtain ⟨i, rfl | rfl⟩ := hs.eq_petersenMatchingShore hX
  · exact petersenAddEdge_exists_crossing_three_canonical i u v hne hnew
  · simpa only [dangling_compl] using
      petersenAddEdge_exists_crossing_three_canonical i u v hne hnew

/-- The matching construction of source Lemma 2.8, with arbitrary labels. -/
theorem IsSimple.exists_crossing_three_of_petersen_deleteEdge (hsimple : H.IsSimple)
    {e : E} (hp : (H.deleteEdge e).IsPetersen) {X : Finset V}
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  let f := hp.some
  let u := f.vertexEquiv (H.endAt e 0)
  let v := f.vertexEquiv (H.endAt e 1)
  have huv : u ≠ v := fun h ↦ hsimple.loopless e (f.vertexEquiv.injective h)
  have hnew : ∀ g, ¬ petersen.Joins g u v := by
    intro g hg
    let g' := f.edgeEquiv.symm g
    have hg' : (H.deleteEdge e).Joins g' (H.endAt e 0) (H.endAt e 1) := by
      apply (f.joins_iff g' _ _).mpr
      simpa [g', u, v] using hg
    have heq : e = g'.val := hsimple.no_parallel e g'.val hg'
    exact (Finset.mem_erase.mp g'.property).1 heq.symm
  have hnt := (f.nontrivial_mapVertices X).mpr hX
  have hsep : petersen.IsSeparatingCut (f.mapVertices X) := by
    apply isSeparatingCut_of_crossing_one petersen_isConnected
      (Finset.card_pos.mp (by have h := hnt.1; omega))
      (Finset.card_pos.mp (by have h := hnt.2; omega))
    intro g
    obtain ⟨g, rfl⟩ := f.edgeEquiv.surjective g
    obtain ⟨N, hN, hg, hc⟩ := hs.exists_perfectMatching_through g
    exact ⟨f.mapEdges N, f.isPerfectMatching hN, (f.mem_mapEdges N g).mpr hg,
      (f.crossing_map N X).trans hc⟩
  obtain ⟨N, hN, hc⟩ := petersenAddEdge_exists_crossing_three u v huv hnew hsep hnt
  let F := (petersenAddedReduction f).toEndpointIso hsimple
  have hmap : F.mapVertices X = f.mapVertices X := rfl
  refine ⟨F.symm.mapEdges N, F.symm.isPerfectMatching hN, ?_⟩
  have hh := F.crossing_map (F.symm.mapEdges N) X
  rw [F.mapEdges_symm_mapEdges, hmap] at hh
  exact hh.symm.trans hc

/-- Campos--Lucchesi Lemma 2.8. The witness proof needs only separation before
adding the edge, so no additional separating hypothesis after addition is required. -/
theorem IsSimple.cutCharacteristic_three_of_petersen_deleteEdge (hsimple : H.IsSimple)
    {e : E} (hp : (H.deleteEdge e).IsPetersen) {X : Finset V}
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X) :
    H.cutCharacteristic X = 3 := by
  classical
  have hc := hp.some.symm.isConnected petersen_isConnected
  have ho := hs.odd_shore hc hX
  exact (cutCharacteristic_eq_three_iff ho).mpr
    (hsimple.exists_crossing_three_of_petersen_deleteEdge hp hs hX)

end GraphPuzzles.LoopMultigraph
