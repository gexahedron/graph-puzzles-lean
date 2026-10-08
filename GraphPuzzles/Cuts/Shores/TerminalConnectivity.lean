import GraphPuzzles.Cuts.Shores.VertexDeletionConnectivity

/-! Adjacent vertices do not separate a matching-covered graph with no nontrivial tight cut. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {u v : V} (F : H.ComponentFamily {u, v})

theorem card_le_one_of_even_of_no_tight (huv : u ≠ v)
    (ht : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X)
    (heven : ∀ Q ∈ F.parts, Even Q.card) : F.parts.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro Q hQ R hR
  by_contra hne
  have heQ := heven Q hQ
  have heR := heven R hR
  have hpQ := Finset.card_pos.mpr (F.nonempty Q hQ)
  have hpR := Finset.card_pos.mpr (F.nonempty R hR)
  have hQ2 : 2 ≤ Q.card := by rw [Nat.even_iff] at heQ; omega
  have hR2 : 2 ≤ R.card := by rw [Nat.even_iff] at heR; omega
  apply ht (insert u Q) (F.tight_insert_of_even huv hQ heQ)
  constructor
  · exact hQ2.trans (Finset.card_le_card (Finset.subset_insert _ _))
  · have hsub : R ⊆ Finset.univ \ insert u Q := by
      intro w hw
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      rcases Finset.mem_insert.mp hh with hwu | hwQ
      · exact F.avoid R hR w hw (Finset.mem_insert.mpr (Or.inl hwu))
      · exact Finset.disjoint_left.mp (F.pairwise Q hQ R hR hne) hwQ hw
    exact hR2.trans (Finset.card_le_card hsub)

end ComponentFamily

/-- In a terminal tight-cut contraction, deleting the ends of any edge leaves
a connected graph. Only the absence of nontrivial tight cuts is used. -/
theorem IsMatchingCovered.connectedOn_delete_adjacent_of_no_tight
    (hm : H.IsMatchingCovered) (ht : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X)
    {u v : V} (huv : u ≠ v) {e : E} (he : H.Joins e u v) :
    H.IsConnectedOn ((Finset.univ.erase u).erase v) := by
  obtain ⟨M, hM, heM⟩ := hm.2 e
  have hP : H.IsPerfectMatchingOn (Finset.univ \ {u, v}) (M.erase e) := by
    have hh := hM.erase_edge heM
    have heq : ({H.endAt e 0, H.endAt e 1} : Finset V) = {u, v} := by
      rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, Finset.pair_comm]
    rwa [heq] at hh
  intro c hc a ha b hb
  have hdel (w : V) : w ∈ (Finset.univ.erase u).erase v ↔ w ∉ ({u, v} : Finset V) := by
    simp [and_comm]
  obtain ⟨F, hF⟩ := exists_componentFamily_of_coloring (H := H) {u, v} c
    (fun f h0 h1 ↦ hc f ((hdel _).mpr h0) ((hdel _).mpr h1))
  have hcard := F.card_le_one_of_even_of_no_tight huv ht
    (fun Q hQ ↦ F.even_parts_of_matching hP hQ)
  obtain ⟨Q, hQ, haQ⟩ := F.cover a ((hdel a).mp ha)
  obtain ⟨R, hR, hbR⟩ := F.cover b ((hdel b).mp hb)
  have hQR := Finset.card_le_one.mp hcard Q hQ R hR
  subst R
  exact hF Q hQ a haQ b hbR

end GraphPuzzles.LoopMultigraph
