import GraphPuzzles.Matching.Barriers.DeletedBarrierCount
import GraphPuzzles.Reduction.Removable.RemovableContraction

/-! A removable doubleton of a near-brick exposes a bipartition. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
/-- On a connected shore, any two proper bipartitions give the same relation
of belonging to one colour class. -/
theorem IsConnectedOn.bipartition_eq_iff {S : Finset V} (hs : H.IsConnectedOn S)
    (c d : V → Bool)
    (hc : ∀ e, H.endAt e 0 ∈ S → H.endAt e 1 ∈ S → c (H.endAt e 0) ≠ c (H.endAt e 1))
    (hd : ∀ e, H.endAt e 0 ∈ S → H.endAt e 1 ∈ S → d (H.endAt e 0) ≠ d (H.endAt e 1))
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) : c u = c v ↔ d u = d v := by
  have he (e : E) (h0 : H.endAt e 0 ∈ S) (h1 : H.endAt e 1 ∈ S) :
      Bool.xor (c (H.endAt e 0)) (d (H.endAt e 0)) =
        Bool.xor (c (H.endAt e 1)) (d (H.endAt e 1)) := by
    have hcc := hc e h0 h1
    have hdd := hd e h0 h1
    cases hc0 : c (H.endAt e 0) <;> cases hc1 : c (H.endAt e 1) <;>
      cases hd0 : d (H.endAt e 0) <;> cases hd1 : d (H.endAt e 1) <;> simp_all
  have hh := hs (fun w ↦ Bool.xor (c w) (d w)) he u hu v hv
  cases hcu : c u <;> cases hcv : c v <;> cases hdu : d u <;> cases hdv : d v <;> simp_all

namespace ComponentFamily

variable {B : Finset V} (F : H.ComponentFamily B)

/-- When every other odd part is a singleton, membership in the barrier is
an explicit bipartition of the complement of the selected part. -/
theorem IsBarrier.barrierColor_compl (hb : F.IsBarrier) (hm : H.IsMatchingCovered)
    (hB : B.Nonempty) {Q : Finset V}
    (hsingle : ∀ R ∈ F.odd, R ≠ Q → R.card = 1)
    (e : E) (h0 : H.endAt e 0 ∈ Finset.univ \ Q) (_h1 : H.endAt e 1 ∈ Finset.univ \ Q) :
    decide (H.endAt e 0 ∈ B) ≠ decide (H.endAt e 1 ∈ B) := by
  by_cases hb0 : H.endAt e 0 ∈ B
  · have hb1 : H.endAt e 1 ∉ B := by
      intro hb1
      exact hb.edge_not_admissible hb0 hb1 (hm.2 e)
    simp [hb0, hb1]
  · have hb1 : H.endAt e 1 ∈ B := by
      by_contra hn1
      obtain ⟨R, hR, hvR⟩ := F.cover _ hb0
      have hRQ : R ≠ Q := fun h ↦ (Finset.mem_sdiff.mp h0).2 (h ▸ hvR)
      have hc := hsingle R (hb.mem_odd_of_mem F hm hB hR) hRQ
      have hvR' := F.closed R hR e 0 hvR hn1
      exact hm.loopless e (Finset.card_le_one_iff.mp hc.le hvR hvR')
    simp [hb0, hb1]

end ComponentFamily

/-- A removable doubleton supplies a maximal barrier after deleting one edge,
containing both ends of the other edge. -/
theorem IsRemovableDoubleton.exists_maximal_barrier {e f : E}
    (hd : H.IsRemovableDoubleton e f) (hm : H.IsMatchingCovered) :
    ∃ P, (H.deleteEdge f).IsPerfectMatching P ∧ ∃ B,
      H.endAt e 0 ∈ B ∧ H.endAt e 1 ∈ B ∧
      ∃ F : (H.deleteEdge f).ComponentFamily B, F.IsMaximalBarrier := by
  obtain ⟨P, hP⟩ := hd.matchingCovered.exists_perfectMatching_of_ne (hm.loopless e)
  have hPo : H.IsPerfectMatching (P.image Subtype.val) := hP.of_restrictEdges
  obtain ⟨N, hN, _⟩ := hPo.exists_restrictEdges (S := Finset.univ.erase f) (by
    intro g hg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
    have ha := a.2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at ha
    exact Finset.mem_erase.mpr ⟨ha.2, Finset.mem_univ _⟩)
  let a : Finset.univ.erase f := ⟨e, by simp [hd.ne]⟩
  have hna : ¬ ∃ M, (H.deleteEdge f).IsPerfectMatching M ∧ a ∈ M := by
    rintro ⟨M, hM, haM⟩
    have heM : e ∈ M.image Subtype.val := Finset.mem_image.mpr ⟨a, haM, rfl⟩
    have hfM := (hd.mutuallyDependent _ hM.of_restrictEdges).mp heM
    obtain ⟨g, _, hgf⟩ := Finset.mem_image.mp hfM
    exact (Finset.mem_erase.mp g.2).1 hgf
  obtain ⟨B₀, he0, he1, F₀, hF₀⟩ :=
    hN.exists_barrier_of_inadmissible_edge (e := a) (hm.loopless e) hna
  obtain ⟨B, hB, F, hF⟩ := hF₀.exists_maximal
  exact ⟨N, hN, B, hB he0, hB he1, F, hF⟩

/-- The barrier parts exposed by a removable doubleton of a near-brick are
singletons. Otherwise a tight cut would have two nonbipartite contractions. -/
theorem IsRemovableDoubleton.barrier_parts_singleton {e f : E}
    (hd : H.IsRemovableDoubleton e f) (hn : H.IsNearBrick) {B : Finset V}
    (F : (H.deleteEdge f).ComponentFamily B) (hF : F.IsMaximalBarrier)
    {P : Finset (Finset.univ.erase f)} (hP : (H.deleteEdge f).IsPerfectMatching P)
    (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B) :
    ∀ Q ∈ F.odd, Q.card = 1 := by
  let S := Finset.univ \ {e, f}
  have hsub : S ⊆ Finset.univ.erase f := by
    intro g hg
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    exact Finset.mem_erase.mpr ⟨hg.2, Finset.mem_univ _⟩
  let R := F.restrictEdgesSubset hsub
  have hbR : R.IsBarrier := hF.isBarrier
  have hmR : (H.restrictEdges S).IsMatchingCovered := hd.matchingCovered
  intro Q hQ
  have hQp := (F.mem_odd.mp hQ).1
  have hQne := F.nonempty Q hQp
  have hQC : (Finset.univ \ Q).Nonempty := ⟨H.endAt e 0,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q hQp _ h he0⟩⟩
  have ht : H.IsTightCut Q := hF.isBarrier.isTightCut_of_mutuallyDependent F hd.ne
    he0 he1 hd.mutuallyDependent hQ
  have hfc := hF.factorCritical_parts F hP hQp
  by_contra hcard
  have hp := Finset.card_pos.mpr hQne
  have hnb : ¬ (H.contract Q).IsBipartite := by
    intro h
    have hh := hfc.card_le_one_of_bipartiteOn
      (h.induced_of_contract.restrictEdges (Finset.univ.erase f))
    omega
  have hnt : IsNontrivialCut Q := by
    refine ⟨by omega, ?_⟩
    have hs : {H.endAt e 0, H.endAt e 1} ⊆ Finset.univ \ Q := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q hQp _ h he0⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q hQp _ h he1⟩
    have hh := Finset.card_le_card hs
    rwa [Finset.card_pair (hn.matchingCovered.loopless e)] at hh
  have hbc := (hn.noStrictTightCut Q ht hnt).resolve_left hnb
  obtain ⟨c, hc⟩ := hbc.induced_of_contract
  have hsingle : ∀ T ∈ R.odd, T ≠ Q → T.card = 1 := by
    intro T hT hTQ
    have hTp := (F.mem_odd.mp hT).1
    have hTC : T ⊆ Finset.univ \ Q := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦
        Finset.disjoint_left.mp (F.pairwise T hTp Q hQp hTQ) hv h⟩
    have hb : (H.deleteEdge f).IsBipartiteOn T :=
      (IsBipartiteOn.restrictEdges ((show H.IsBipartiteOn (Finset.univ \ Q) from ⟨c, hc⟩).mono hTC)
        (Finset.univ.erase f))
    have hle := (hF.factorCritical_parts F hP hTp).card_le_one_of_bipartiteOn hb
    have hpos := Finset.card_pos.mpr (F.nonempty T hTp)
    omega
  have hconn := ((hbR.isTightCut R hQ).isSeparatingCut hmR hQne hQC).compl.connectedOn
  have heC (k : Fin 2) : H.endAt e k ∈ Finset.univ \ Q := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    apply F.avoid Q hQp _ h
    fin_cases k <;> assumption
  have hsame := hconn.bipartition_eq_iff c (fun v ↦ decide (v ∈ B))
    (fun g ↦ hc g.1)
    (hbR.barrierColor_compl R hmR ⟨H.endAt e 0, he0⟩ hsingle)
    (heC 0) (heC 1)
  apply hc e (heC 0) (heC 1)
  exact hsame.mpr (by simp [he0, he1])

/-- The bipartizing conclusion needed from Campos--Lucchesi Lemma 2.10 for
removable doubletons. The two restored edges lie within opposite colour classes. -/
theorem IsRemovableDoubleton.exists_bipartition {e f : E}
    (hd : H.IsRemovableDoubleton e f) (hn : H.IsNearBrick) :
    ∃ c : V → Bool, c (H.endAt e 0) = true ∧ c (H.endAt e 1) = true ∧
      c (H.endAt f 0) = false ∧ c (H.endAt f 1) = false ∧
      ∀ g, g ≠ e → g ≠ f → c (H.endAt g 0) ≠ c (H.endAt g 1) := by
  obtain ⟨P, hP, B, he0, he1, F, hF⟩ := hd.exists_maximal_barrier hn.matchingCovered
  have hsingle := hd.barrier_parts_singleton hn F hF hP he0 he1
  obtain ⟨M, hM, heM⟩ := hn.matchingCovered.2 e
  have hfM := (hd.mutuallyDependent M hM).mp heM
  have hfB := hF.isBarrier.deleted_edge_avoids F hd.ne he0 he1 hM heM hfM
  let S := Finset.univ \ {e, f}
  have hsub : S ⊆ Finset.univ.erase f := by
    intro g hg
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    exact Finset.mem_erase.mpr ⟨hg.2, Finset.mem_univ _⟩
  let R := F.restrictEdgesSubset hsub
  have hbR : R.IsBarrier := hF.isBarrier
  refine ⟨fun v ↦ decide (v ∈ B), by simp [he0], by simp [he1],
    by simp [hfB 0], by simp [hfB 1], ?_⟩
  intro g hge hgf
  exact hbR.barrierColor_compl R hd.matchingCovered ⟨H.endAt e 0, he0⟩
    (Q := ∅) (fun Q hQ _ ↦ hsingle Q hQ) ⟨g, by simp [S, hge, hgf]⟩ (by simp) (by simp)

theorem IsRemovableDoubleton.bipartite_deletePair {e f : E}
    (hd : H.IsRemovableDoubleton e f) (hn : H.IsNearBrick) :
    (H.deletePair e f).IsBipartite := by
  obtain ⟨c, _, _, _, _, hc⟩ := hd.exists_bipartition hn
  refine ⟨c, fun g ↦ ?_⟩
  have hg := g.2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hg
  exact hc g.1 hg.1 hg.2

end GraphPuzzles.LoopMultigraph
