import GraphPuzzles.Reduction.Removable.DependentBarrier
import GraphPuzzles.Reduction.Removable.DoubletonBipartite

/-! Mutually dependent edges of a near-brick expose a bipartition when their
deletion remains connected. This includes every three-edge-connected near-brick. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Equal changes in two Boolean colours leave their exclusive-or unchanged. -/
theorem bool_xor_eq_of_ne {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    Bool.xor a c = Bool.xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- With connected pair deletion, all maximal-barrier parts exposed by a
mutually dependent pair in a near-brick are singletons. -/
theorem MutuallyDependent.barrier_parts_singleton {e f : E}
    (hd : H.MutuallyDependent e f) (hef : e ≠ f) (hn : H.IsNearBrick)
    (hconn : (H.deletePair e f).IsConnected) {B : Finset V}
    (F : (H.deleteEdge f).ComponentFamily B) (hF : F.IsMaximalBarrier)
    {P : Finset (Finset.univ.erase f)} (hP : (H.deleteEdge f).IsPerfectMatching P)
    (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B) :
    ∀ Q ∈ F.parts, Q.card = 1 := by
  have hu := fun g ↦ hF.isBarrier.internal_edge_unique F hn.matchingCovered hef hd
    he0 he1 (g := g)
  intro Q hQ
  have hQo : Q ∈ F.odd := F.mem_odd.mpr ⟨hQ, hF.odd_parts F hP hQ⟩
  have hQne := F.nonempty Q hQ
  have ht : H.IsTightCut Q := hF.isBarrier.isTightCut_of_mutuallyDependent F hef he0 he1 hd hQo
  have hfc := hF.factorCritical_parts F hP hQ
  by_contra hcard
  have hp := Finset.card_pos.mpr hQne
  have hnb : ¬ (H.contract Q).IsBipartite := by
    intro h
    have hh := hfc.card_le_one_of_bipartiteOn
      (h.induced_of_contract.restrictEdges (Finset.univ.erase f))
    omega
  have heC (k : Fin 2) : H.endAt e k ∈ Finset.univ \ Q := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h
    apply F.avoid Q hQ _ h
    fin_cases k <;> assumption
  have hnt : IsNontrivialCut Q := by
    refine ⟨by omega, ?_⟩
    have hsub : {H.endAt e 0, H.endAt e 1} ⊆ Finset.univ \ Q := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact heC 0
      · exact heC 1
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_pair (hn.matchingCovered.loopless e)] at hh
  have hbc := (hn.noStrictTightCut Q ht hnt).resolve_left hnb
  have hsingle : ∀ T ∈ F.parts, T ≠ Q → T.card = 1 := by
    intro T hT hTQ
    have hTC : T ⊆ Finset.univ \ Q := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦
        Finset.disjoint_left.mp (F.pairwise T hT Q hQ hTQ) hv h⟩
    have hb := (hbc.induced_of_contract.mono hTC).restrictEdges (Finset.univ.erase f)
    have hle := (hF.factorCritical_parts F hP hT).card_le_one_of_bipartiteOn hb
    have hpos := Finset.card_pos.mpr (F.nonempty T hT)
    omega
  obtain ⟨c, hc⟩ := hbc
  let a : V → Bool := fun v ↦ c (contractVertex (Finset.univ \ Q) v)
  let b : V → Bool := fun v ↦ decide (v ∈ B)
  have hxor (g : ↥(Finset.univ \ {e, f})) :
      Bool.xor (a (H.endAt g.1 0)) (b (H.endAt g.1 0)) =
        Bool.xor (a (H.endAt g.1 1)) (b (H.endAt g.1 1)) := by
    have hg := g.2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    by_cases hm : g.1 ∈ H.meets (Finset.univ \ Q)
    · have ha : a (H.endAt g.1 0) ≠ a (H.endAt g.1 1) := hc ⟨g.1, hm⟩
      have hb : b (H.endAt g.1 0) ≠ b (H.endAt g.1 1) :=
        F.barrierColor_except_part hn.matchingCovered.loopless hsingle hu hg.1 hg.2 hm
      exact bool_xor_eq_of_ne ha hb
    · have houtside (k : Fin 2) : H.endAt g.1 k ∉ Finset.univ \ Q :=
        fun h ↦ hm (mem_meets.mpr ⟨k, h⟩)
      have hin (k : Fin 2) : H.endAt g.1 k ∈ Q := by simpa using houtside k
      have hB (k : Fin 2) : H.endAt g.1 k ∉ B := F.avoid Q hQ _ (hin k)
      simp [a, b, contractVertex, hin, hB]
  have hh := hconn (fun v ↦ Bool.xor (a v) (b v)) hxor (H.endAt e 0) (H.endAt e 1)
  have heA : a (H.endAt e 0) ≠ a (H.endAt e 1) := hc ⟨e, mem_meets.mpr ⟨0, heC 0⟩⟩
  apply heA
  exact Bool.not_inj (by simpa only [b, he0, he1, decide_true, Bool.xor_true] using hh)

/-- Two distinct mutually dependent edges bipartize a near-brick if deleting
them leaves it connected. The edges lie within opposite colour classes. -/
theorem MutuallyDependent.exists_bipartition_of_connected_deletePair {e f : E}
    (hd : H.MutuallyDependent e f) (hef : e ≠ f) (hn : H.IsNearBrick)
    (hc : (H.deletePair e f).IsConnected) :
    ∃ c : V → Bool, c (H.endAt e 0) = true ∧ c (H.endAt e 1) = true ∧
      c (H.endAt f 0) = false ∧ c (H.endAt f 1) = false ∧
      ∀ g, g ≠ e → g ≠ f → c (H.endAt g 0) ≠ c (H.endAt g 1) := by
  have hcf : (H.deleteEdge f).IsConnected := hc.restrictEdges_mono (by
    intro g hg
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hg
    exact Finset.mem_erase.mpr ⟨hg.2, Finset.mem_univ _⟩)
  obtain ⟨P, hP, B, he0, he1, F, hF⟩ := hd.exists_maximal_barrier hef hn.matchingCovered hcf
  have hsingle := hd.barrier_parts_singleton hef hn hc F hF hP he0 he1
  obtain ⟨M, hM, heM⟩ := hn.matchingCovered.2 e
  have hfB := hF.isBarrier.deleted_edge_avoids F hef he0 he1 hM heM ((hd M hM).mp heM)
  refine ⟨fun v ↦ decide (v ∈ B), by simp [he0], by simp [he1],
    by simp [hfB 0], by simp [hfB 1], ?_⟩
  intro g hge hgf
  exact F.barrierColor_except_part hn.matchingCovered.loopless
    (Q := ∅) (fun R hR _ ↦ hsingle R hR)
    (fun g ↦ hF.isBarrier.internal_edge_unique F hn.matchingCovered hef hd he0 he1)
    hge hgf (mem_meets.mpr ⟨0, by simp⟩)

/-- The bipartizing assertion of Campos--Lucchesi Lemma 2.10, for any two
distinct mutually dependent edges of a three-edge-connected near-brick. -/
theorem MutuallyDependent.bipartite_deletePair {e f : E}
    (hd : H.MutuallyDependent e f) (hef : e ≠ f)
    (hn : H.IsNearBrick) (h3 : H.IsThreeEdgeConnected) :
    (H.deletePair e f).IsBipartite := by
  obtain ⟨c, _, _, _, _, hc⟩ :=
    hd.exists_bipartition_of_connected_deletePair hef hn (h3.connected_deletePair e f)
  refine ⟨c, fun g ↦ ?_⟩
  have hg := g.2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hg
  exact hc g.1 hg.1 hg.2

end GraphPuzzles.LoopMultigraph
