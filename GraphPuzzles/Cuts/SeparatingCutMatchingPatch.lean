import GraphPuzzles.Matching.MatchingContraction
import GraphPuzzles.Matching.MatchingOn

/-! Deleting the endpoints of a separating-cut edge leaves a patch avoiding the cut. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Choose a matching whose unique cut edge joins `p` to `q`, then erase that edge. -/
theorem IsSeparatingCut.exists_zero_crossing_matchingOn {X : Finset V}
    (hs : H.IsSeparatingCut X) {p q : V} (hp : p ∈ X) (hq : q ∉ X)
    {e : E} (he : H.Joins e p q) :
    ∃ M, H.IsPerfectMatchingOn (Finset.univ \ {p, q}) M ∧
      (M ∩ H.dangling X).card = 0 := by
  have heD : e ∈ H.dangling X := by
    apply mem_dangling.mpr
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using (show ¬ (p ∈ X ↔ q ∈ X) from fun h ↦ hq (h.mp hp))
    · simpa only [h0, h1] using (show ¬ (q ∈ X ↔ p ∈ X) from fun h ↦ hq (h.mpr hp))
  obtain ⟨M, hM, heM, hcross⟩ := hs.exists_perfectMatching_through e
  have hends : ({H.endAt e 0, H.endAt e 1} : Finset V) = {p, q} := by
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [h0, h1]
    · simp only [h0, h1, Finset.pair_comm]
  refine ⟨M.erase e, ?_, ?_⟩
  · simpa only [hends] using hM.erase_edge heM
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hfM := Finset.mem_inter.mp hf
    have heI : e ∈ M ∩ H.dangling X := Finset.mem_inter.mpr ⟨heM, heD⟩
    have hfI : f ∈ M ∩ H.dangling X :=
      Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hfM.1).2, hfM.2⟩
    have hfe : f = e := Finset.card_le_one_iff.mp hcross.le hfI heI
    exact (Finset.mem_erase.mp hfM.1).1 hfe

end GraphPuzzles.LoopMultigraph
