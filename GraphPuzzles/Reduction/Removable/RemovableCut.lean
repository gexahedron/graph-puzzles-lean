import GraphPuzzles.Reduction.Removable.EdgeRestriction
import GraphPuzzles.Matching.Barriers.BarrierInternalEdge
import GraphPuzzles.Matching.Bipartite.FactorCriticalBipartite
import GraphPuzzles.Cuts.CutWitness

/-!
# Strictly separating cuts and removable edges

The minimal-cut argument of Campos--Lucchesi Lemma 3.4 uses precedence
in the original graph, even for cuts separating the edge-deleted graph.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem IsBipartiteOn.contract_sourceShore {X : Finset V} {Q : Finset (Option X)}
    (hb : H.IsBipartiteOn (sourceShore X Q)) (hn : none ∉ Q) :
    (H.contract X).IsBipartiteOn Q := by
  obtain ⟨c, hc⟩ := hb
  let d : Option X → Bool := fun v ↦ v.elim false (fun v ↦ c v.1)
  refine ⟨d, ?_⟩
  intro e h0 h1
  have h0s := (contract_mem_sourceShore X Q hn e 0).mpr h0
  have h1s := (contract_mem_sourceShore X Q hn e 1).mpr h1
  simpa only [d, contract_endAt, dif_pos (sourceShore_subset X Q h0s),
    dif_pos (sourceShore_subset X Q h1s), Option.elim_some] using hc e.1 h0s h1s

/-- A contraction which loses matching-coveredness after restoring an edge has
a strictly smaller cut that is still strictly separating after deletion. -/
theorem IsStrictlySeparatingCut.exists_predecessor_of_bad_contraction {e : E} {X : Finset V}
    (hs : (H.deleteEdge e).IsStrictlySeparatingCut X) (hm : H.IsMatchingCovered)
    (hr : H.IsRemovable e) (hn : ¬ (H.contract X).IsMatchingCovered) :
    ∃ Y, (H.deleteEdge e).IsStrictlySeparatingCut Y ∧ H.CutStrictlyPrecedes Y X := by
  classical
  let S := Finset.univ.erase e
  let T : Finset (H.meets X) := Finset.univ.filter fun f ↦ f.1 ∈ S
  let K := H.contract X
  have hmc : (K.restrictEdges T).IsMatchingCovered :=
    (restrictContractIso S X).isMatchingCovered hs.separating.1
  have hnb : ¬ (K.restrictEdges T).IsBipartite :=
    fun h ↦ hs.leftNonbipartite ((restrictContractIso S X).symm.isBipartite h)
  obtain ⟨f, hfT, hf⟩ := hmc.exists_omitted_inadmissible hn
  have hfe : f.1 = e := by simpa [T, S] using hfT
  have hnt := hs.nontrivial hr
  obtain ⟨M₀, hM₀, hc₀⟩ := hs.separating.exists_crossing_one hr.1 hnt
  have horig : H.IsPerfectMatching (M₀.image Subtype.val) := hM₀.of_restrictEdges
  have hcross : ((M₀.image Subtype.val) ∩ H.dangling X).card = 1 := by
    rw [restrictEdges_crossing]
    exact hc₀
  have hK := horig.contract_of_crossing_one X hcross
  obtain ⟨B₀, h0, h1, F₀, hF₀⟩ :=
    hK.exists_barrier_of_inadmissible_edge (contract_loopless X hm.loopless f) hf
  obtain ⟨B, hB, F, hF⟩ := hF₀.exists_maximal
  have hf0 : K.endAt f 0 ∈ B := hB h0
  have hf1 : K.endAt f 1 ∈ B := hB h1
  obtain ⟨M, hM, hfM⟩ := hm.2 f.1
  have hnone : none ∈ B := ContractionBarrier.none_mem_of_internal_edge F hF.isBarrier
    (hs.separating.odd_shore hr.1 hnt) hf0 hf1 hM hfM
  let R := F.restrictEdges T
  have hbR : R.IsBarrier := hF.isBarrier
  have hlarge : ∃ Q ∈ F.odd, 2 ≤ Q.card := by
    by_contra hno
    push Not at hno
    have hsingle : ∀ Q ∈ R.odd, Q ≠ ∅ → Q.card = 1 := by
      intro Q hQ _
      have hp := Finset.card_pos.mpr (F.nonempty Q (F.mem_odd.mp hQ).1)
      have hh := hno Q hQ
      omega
    have hh := hbR.bipartiteOn_compl R hmc ⟨none, hnone⟩ hsingle
    obtain ⟨c, hc⟩ := hh
    exact hnb ⟨c, fun f ↦ hc f (by simp) (by simp)⟩
  obtain ⟨Q, hQ, hcard⟩ := hlarge
  have hnQ := ContractionBarrier.none_not_mem F hnone (F.mem_odd.mp hQ).1
  have hfc := hF.factorCritical_parts F hK (F.mem_odd.mp hQ).1
  have hnon : ¬ (K.restrictEdges T).IsBipartiteOn Q := by
    intro h
    have hb : K.IsBipartiteOn Q := h.of_restrictEdges (by
      intro g hg0 _
      by_contra hg
      have hge : g.1 = e := by simpa [T, S] using hg
      have hgf : g = f := Subtype.ext (hge.trans hfe.symm)
      subst g
      exact F.avoid Q (F.mem_odd.mp hQ).1 _ hg0 hf0)
    have hh := hfc.card_le_one_of_bipartiteOn hb
    omega
  have hstrict := ContractionBarrier.strictlyPrecedes_of_internal_edge F hF.isBarrier
    hnone hf0 hf1 hQ hM hfM
  have hsub := sourceShore_subset X Q
  have hY : (sourceShore X Q).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_sourceShore X Q hnQ]
    omega
  have hYC : (Finset.univ \ sourceShore X Q).Nonempty := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (show 0 < (Finset.univ \ X).card by have hh := hnt.2; omega)
    exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ (Finset.mem_sdiff.mp hv).2 (hsub h)⟩⟩
  have hsep : (H.deleteEdge e).IsSeparatingCut (sourceShore X Q) :=
    (hstrict.1.restrictEdges S).isSeparatingCut hs.separating hr.1
      (ContractionBarrier.source_odd F hnone hQ) hY hYC
  refine ⟨sourceShore X Q, ⟨hsep, ?_, ?_⟩, hstrict⟩
  · intro hb
    have hh := (restrictContractIso S X).isBipartiteOn
      (hb.induced_of_contract.contract_sourceShore hnQ)
    have heq : (restrictContractIso (H := H) S X).mapVertices Q = Q := by
      ext v
      simp [EndpointIso.mapVertices, restrictContractIso]
    rw [heq] at hh
    exact hnon hh
  · intro hb
    apply hs.rightNonbipartite
    apply IsBipartiteOn.contract_of_separating _ hs.separating.compl
    apply hb.induced_of_contract.mono
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ (Finset.mem_sdiff.mp hv).2 (hsub h)⟩

/-- Campos--Lucchesi Lemma 3.4: a minimal strictly separating cut of the
edge-deleted graph is strictly separating in the original graph. -/
theorem IsStrictlySeparatingCut.of_deleteEdge_minimal {e : E} {X : Finset V}
    (hs : (H.deleteEdge e).IsStrictlySeparatingCut X) (hm : H.IsMatchingCovered)
    (hr : H.IsRemovable e)
    (hmin : ∀ Y, (H.deleteEdge e).IsStrictlySeparatingCut Y →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) : H.IsStrictlySeparatingCut X := by
  have hleft : (H.contract X).IsMatchingCovered := by
    by_contra hn
    obtain ⟨Y, hY, hp⟩ := hs.exists_predecessor_of_bad_contraction hm hr hn
    exact hmin Y hY hp.1 hp
  have hright : (H.contract (Finset.univ \ X)).IsMatchingCovered := by
    by_contra hn
    obtain ⟨Y, hY, hp⟩ := hs.compl.exists_predecessor_of_bad_contraction hm hr hn
    have hpX : H.CutStrictlyPrecedes Y X := by
      simpa only [CutStrictlyPrecedes, CutPrecedes, dangling_compl] using hp
    exact hmin Y hY hpX.1 hpX
  refine ⟨⟨hleft, hright⟩, ?_, ?_⟩
  · intro hb
    exact hs.leftNonbipartite (IsBipartiteOn.contract_of_separating
      (hb.induced_of_contract.restrictEdges (Finset.univ.erase e)) hs.separating)
  · intro hb
    exact hs.rightNonbipartite (IsBipartiteOn.contract_of_separating
      (hb.induced_of_contract.restrictEdges (Finset.univ.erase e)) hs.separating.compl)

/-- Every strictly separating cut after removable-edge deletion has a preceding
cut which is strictly separating both before and after deletion. -/
theorem IsStrictlySeparatingCut.exists_preceding_before_deletion {e : E} {X : Finset V}
    (hs : (H.deleteEdge e).IsStrictlySeparatingCut X) (hm : H.IsMatchingCovered)
    (hr : H.IsRemovable e) :
    ∃ Y, H.IsStrictlySeparatingCut Y ∧ (H.deleteEdge e).IsStrictlySeparatingCut Y ∧
      H.CutPrecedes Y X := by
  classical
  let C := Finset.univ.filter fun Y ↦
    (H.deleteEdge e).IsStrictlySeparatingCut Y ∧ H.CutPrecedes Y X
  have hC : C.Nonempty := ⟨X, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hs, CutPrecedes.refl X⟩⟩
  obtain ⟨Y, hY, hmin⟩ := exists_minimal_cut (H := H) C hC
  obtain ⟨hYs, hYX⟩ := (Finset.mem_filter.mp hY).2
  refine ⟨Y, hYs.of_deleteEdge_minimal hm hr ?_, hYs, hYX⟩
  intro Z hZ hZY
  exact hmin Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZ, hZY.trans hYX⟩)

/-- Solid matching-covered graphs remain solid after removable-edge deletion. -/
theorem IsSolid.deleteEdge (hs : H.IsSolid) (hm : H.IsMatchingCovered)
    {e : E} (hr : H.IsRemovable e) : (H.deleteEdge e).IsSolid := by
  intro X hX
  obtain ⟨Y, hY, _, _⟩ := hX.exists_preceding_before_deletion hm hr
  exact hs Y hY

end GraphPuzzles.LoopMultigraph
