import GraphPuzzles.Petersen.Minors.DeletedPetersenSingleFiber
import GraphPuzzles.Reduction.Wheels.TwoWheelDeletionInduction

/-! The noncubic two-wheel case using an avoided spoke and one expansion fiber. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V} {e : E}

/-- A family bound of one expansion fiber supplies the distinguished
fiber required by the single-fiber matching assembly. -/
theorem PetersenFiberModel.exists_three_crossing_of_at_most_one_fiber
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hsimple : H.IsSimple) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hcard : R.nonsingletonFibers.card ≤ 1) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  by_cases hex : ∃ p, 2 ≤ (R.canonicalFiber p).card
  · obtain ⟨p, hp⟩ := hex
    apply R.exists_three_crossing_of_single_fiber hb hsimple hr hm hbi hs hX p
    intro r hrp
    by_contra hn
    have hr : 2 ≤ (R.canonicalFiber r).card := by omega
    have hpF : R.canonicalFiber p ∈ R.nonsingletonFibers :=
      (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm p, hp, rfl⟩
    have hrF : R.canonicalFiber r ∈ R.nonsingletonFibers :=
      (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm r, hr, rfl⟩
    have heq := Finset.card_le_one.mp hcard _ hrF _ hpF
    obtain ⟨w, hw⟩ := R.canonicalFiber_nonempty r
    exact hrp (((R.mem_canonicalFiber r w).mp hw).symm.trans
      ((R.mem_canonicalFiber p w).mp (heq ▸ hw)))
  · apply R.exists_three_crossing_of_single_fiber hb hsimple hr hm hbi hs hX 0
    intro r _
    have hh : ¬ 2 ≤ (R.canonicalFiber r).card := fun h ↦ hex ⟨r, h⟩
    omega

/-- A high-degree endpoint excludes one side's expansion fibers,
regardless of the orientation of the selected cut. -/
theorem PetersenFiberModel.card_nonsingletonFibers_le_one_of_high_endpoint
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hl : (H.contract X).IsOddWheel none)
    (hrw : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (he : e ∈ H.dangling X) {k : Fin 2}
    (hd : 2 ≤ H.degreeIn (H.dangling X) (H.endAt e k)) :
    R.nonsingletonFibers.card ≤ 1 := by
  by_cases hk : H.endAt e k ∈ X
  · exact R.card_nonsingletonFibers_le_one_of_cut_degree hb hr hm hbi hl he hk hd
  · have he' : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
    have hd' : 2 ≤ H.degreeIn (H.dangling (Finset.univ \ X)) (H.endAt e k) := by
      simpa only [dangling_compl] using hd
    exact R.compl.card_nonsingletonFibers_le_one_of_cut_degree hb hr hm hbi hrw he'
      (by simp [hk]) hd'

/-- The noncubic branch of the final two-wheel case. The deleted spoke
is chosen outside an existing matching, so the avoided-edge deletion
theorem applies and leaves at most one Petersen expansion fiber. -/
theorem IsBrick.three_of_noncubic_oddWheel_contractions (hb : H.IsBrick)
    (hsimple : H.IsSimple)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    (hr : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hc : ¬ ∀ w, H.degree w = 3) {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card) :
    ∃ N, H.IsPerfectMatching N ∧ (N ∩ H.dangling X).card = 3 := by
  obtain ⟨e, he, k, hk, hn, hd⟩ :=
    hr.exists_deleted_nearBrick_of_not_cubic hsl hsr hwl hwr hc hM h5
  have hX := hr.nontrivial hb.matchingCovered
  rcases hb.three_or_deleted_petersenMinor ih hr.isSeparatingCut hX hn hd.isSeparatingCut with h3 | hp
  · exact h3
  · obtain ⟨R, hbi⟩ := hp.exists_bipartite_fiberModel hn
    apply R.exists_three_crossing_of_at_most_one_fiber hb hsimple hn.matchingCovered
      hn.matchingCovered hbi hd.isSeparatingCut hX
    exact R.card_nonsingletonFibers_le_one_of_high_endpoint hb hn.matchingCovered
      hn.matchingCovered hbi hwl hwr he hk

end GraphPuzzles.LoopMultigraph
