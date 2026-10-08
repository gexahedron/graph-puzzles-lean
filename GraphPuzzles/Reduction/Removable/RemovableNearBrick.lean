import GraphPuzzles.Reduction.Removable.RemovableCut

/-! Removable edges of solid near-bricks preserve the near-brick property. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Adding an admissible edge to a bipartite graph with a perfect matching
preserves bipartiteness. -/
theorem IsPerfectMatching.bipartite_of_deleteEdge {e : E}
    {P : Finset (Finset.univ.erase e)} (hP : (H.deleteEdge e).IsPerfectMatching P)
    {M : Finset E} (hM : H.IsPerfectMatching M) (he : e ∈ M)
    (hb : (H.deleteEdge e).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := hb
  let p : V → ℚ := fun v ↦ if c v then 1 else -1
  have hz : (∑ v, p v) = 0 :=
    hP.on_univ.signed_sum_zero c (fun f _ ↦ hc f)
  have hother (f : E) (hf : f ≠ e) : c (H.endAt f 0) ≠ c (H.endAt f 1) :=
    hc ⟨f, Finset.mem_erase.mpr ⟨hf, Finset.mem_univ _⟩⟩
  have hh := sum_vertexWeight_degree (H := H) p (matchingVector M)
  simp only [hM.isFractional.degree, mul_one, hz] at hh
  rw [Finset.sum_eq_single e] at hh
  · simp only [matchingVector, if_pos he, one_mul] at hh
    refine ⟨c, fun f ↦ ?_⟩
    by_cases hf : f = e
    · subst f
      intro hsame
      change 0 = (if c (H.endAt e 0) then (1 : ℚ) else -1) +
        (if c (H.endAt e 1) then 1 else -1) at hh
      rw [hsame] at hh
      cases hc1 : c (H.endAt e 1) <;> norm_num [hc1] at hh
    · exact hother f hf
  · intro f _ hf
    have hn := hother f hf
    have hp : p (H.endAt f 0) + p (H.endAt f 1) = 0 := by
      cases h0 : c (H.endAt f 0) <;> cases h1 : c (H.endAt f 1) <;> simp_all [p]
    rw [hp, mul_zero]
  · simp

/-- A removable edge cannot turn a nonbipartite matching-covered graph bipartite. -/
theorem IsRemovable.notBipartite {e : E} (hr : H.IsRemovable e)
    (hm : H.IsMatchingCovered) (hb : ¬ H.IsBipartite) : ¬ (H.deleteEdge e).IsBipartite := by
  intro h
  obtain ⟨g, _⟩ := hr.1.dangling_nonempty (X := {H.endAt e 0})
    (Finset.singleton_nonempty _) ⟨H.endAt e 1, by simp [Ne.symm (hm.loopless e)]⟩
  obtain ⟨P, hP, _⟩ := hr.2 g
  obtain ⟨M, hM, he⟩ := hm.2 e
  exact hb (hP.bipartite_of_deleteEdge hM he h)

/-- A nonbipartite solid matching-covered graph has exactly one brick in every
tight-cut decomposition. -/
theorem IsSolid.isNearBrick (hs : H.IsSolid) (hm : H.IsMatchingCovered)
    (hb : ¬ H.IsBipartite) : H.IsNearBrick := by
  apply isNearBrick_iff.mpr
  refine ⟨hm, hb, ?_⟩
  intro X ht hn
  by_contra h
  push Not at h
  have hX : X.Nonempty := Finset.card_pos.mp (by have hh := hn.1; omega)
  have hXC : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by have hh := hn.2; omega)
  exact hs X ⟨ht.isSeparatingCut hm hX hXC, h.1, h.2⟩

/-- Campos--Lucchesi Corollary 3.5, in its near-brick form: every removable
edge of a solid near-brick is b-removable. -/
theorem IsNearBrick.deleteEdge_of_solid (hb : H.IsNearBrick) (hs : H.IsSolid)
    {e : E} (hr : H.IsRemovable e) : (H.deleteEdge e).IsNearBrick :=
  (hs.deleteEdge hb.matchingCovered hr).isNearBrick hr
    (hr.notBipartite hb.matchingCovered hb.notBipartite)

end GraphPuzzles.LoopMultigraph
