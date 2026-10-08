import GraphPuzzles.Petersen.Minors.DeletedPetersenFibers
import GraphPuzzles.Petersen.Minors.TightQuotientIso
import GraphPuzzles.Petersen.PetersenMatching

/-! The internal or adjacent restored-edge branch of Proposition 6.4. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V W : Type u} {E F : Type v}
  [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F}

namespace TightVertexQuotient

/-- If all other fibers are singletons, contracting one fiber gives
exactly the target vertex set. -/
noncomputable def singleFiberVertexEquiv (Q : H.TightVertexQuotient K) (p : W)
    (hs : ∀ q, q ≠ p → (Q.fiber q).card ≤ 1) :
    Option ↥((Finset.univ : Finset V) \ Q.fiber p) ≃ W := by
  let f : Option ↥((Finset.univ : Finset V) \ Q.fiber p) → W := fun z ↦
    match z with
    | none => p
    | some z => Q.vertexMap z.1
  have hn (z : ↥((Finset.univ : Finset V) \ Q.fiber p)) : Q.vertexMap z.1 ≠ p := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Q.mem_fiber] using z.2
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (hn b hab.symm).elim
    | some a =>
      cases b with
      | none => exact (hn a hab).elim
      | some b =>
        apply congrArg some
        apply Subtype.ext
        exact Finset.card_le_one.mp (hs (Q.vertexMap b.1) (hn b)) a.1
          ((Q.mem_fiber _ _).mpr hab) b.1 (by simp)
  · intro q
    by_cases hq : q = p
    · exact ⟨none, hq.symm⟩
    obtain ⟨z, hz⟩ := Q.surjective q
    exact ⟨some ⟨z, by simp [hz, hq]⟩, hz⟩

omit [DecidableEq F] in
theorem singleFiberVertexEquiv_contractVertex (Q : H.TightVertexQuotient K) (p : W)
    (hs : ∀ q, q ≠ p → (Q.fiber q).card ≤ 1) (z : V) :
    Q.singleFiberVertexEquiv p hs (contractVertex (Finset.univ \ Q.fiber p) z) =
      Q.vertexMap z := by
  by_cases hz : Q.vertexMap z = p
  · simp [singleFiberVertexEquiv, contractVertex, hz]
  · simp [singleFiberVertexEquiv, contractVertex, hz]

end TightVertexQuotient

namespace PetersenFiberModel

variable {X : Finset V} {e : E} (R : (H.deleteEdge e).PetersenFiberModel X)

/-- With only one nonsingleton fiber, restoring an internal edge or a
parallel edge preserves the Petersen graph after contracting that fiber. -/
theorem exists_parallelReduction_contract_of_single_fiber (p : R.Vertex)
    (hs : ∀ q, q ≠ p → (R.quotient.fiber q).card ≤ 1)
    (hl : ∀ f, H.endAt f 0 ≠ H.endAt f 1)
    (he : (∀ k, H.endAt e k ∈ R.quotient.fiber p) ∨
      ∃ g, R.graph.Joins g (R.quotient.vertexMap (H.endAt e 0))
        (R.quotient.vertexMap (H.endAt e 1))) :
    ∃ f : ParallelReduction (H.contract (Finset.univ \ R.quotient.fiber p)) LoopMultigraph.petersen,
      ∀ z, f.vertexEquiv (contractVertex (Finset.univ \ R.quotient.fiber p) z) =
        R.petersen.some.vertexEquiv (R.quotient.vertexMap z) := by
  classical
  let Q := R.quotient
  let S := Finset.univ \ Q.fiber p
  let P := R.petersen.some
  let ev := (Q.singleFiberVertexEquiv p hs).trans P.vertexEquiv
  have hmap (f : H.meets S) (k : Fin 2) :
      ev ((H.contract S).endAt f k) = P.vertexEquiv (Q.vertexMap (H.endAt f.1 k)) := by
    exact congrArg P.vertexEquiv (Q.singleFiberVertexEquiv_contractVertex p hs
      (H.endAt f.1 k))
  have hex (f : H.meets S) :
      ∃ g, LoopMultigraph.petersen.Joins g (ev ((H.contract S).endAt f 0))
        (ev ((H.contract S).endAt f 1)) := by
    rw [hmap, hmap]
    by_cases hfe : f.1 = e
    · rcases he with hi | ⟨g, hg⟩
      · obtain ⟨k, hk⟩ := mem_meets.mp f.2
        have hk' : H.endAt e k ∉ Q.fiber p := (Finset.mem_sdiff.mp (hfe ▸ hk)).2
        exact (hk' (hi k)).elim
      · exact ⟨P.edgeMap g, (P.joins_iff _ _ _).mp (hfe.symm ▸ hg)⟩
    · let d : Finset.univ.erase e := ⟨f.1, by simp [hfe]⟩
      have hne : Q.vertexMap (H.endAt f.1 0) ≠ Q.vertexMap (H.endAt f.1 1) := by
        intro hh
        apply contract_loopless S hl f
        apply ev.injective
        rw [hmap, hmap, hh]
      obtain ⟨g, hg, hj⟩ := Q.exists_join_of_distinct_images
        (show (H.deleteEdge e).Joins d (H.endAt f.1 0) (H.endAt f.1 1) from
          Or.inl ⟨rfl, rfl⟩) hne
      exact ⟨P.edgeMap g, (P.joins_iff _ _ _).mp hj⟩
  choose edgeMap hedge using hex
  have hsurj : Function.Surjective edgeMap := by
    intro g
    obtain ⟨r, hr⟩ := P.edge_surjective g
    let d := Q.edgeLift r
    have hj : LoopMultigraph.petersen.Joins g (P.vertexEquiv (Q.vertexMap (H.endAt d.1 0)))
        (P.vertexEquiv (Q.vertexMap (H.endAt d.1 1))) := by
      exact hr ▸ (P.joins_iff _ _ _).mp (Q.joins_edgeLift r)
    have hne : Q.vertexMap (H.endAt d.1 0) ≠ Q.vertexMap (H.endAt d.1 1) := by
      intro hh
      rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact petersen_isSimple.loopless g (h0.trans ((congrArg P.vertexEquiv hh).trans h1.symm))
      · exact petersen_isSimple.loopless g (h0.trans ((congrArg P.vertexEquiv hh).symm.trans h1.symm))
    have hd : d.1 ∈ H.meets S := by
      apply mem_meets.mpr
      by_cases h0 : Q.vertexMap (H.endAt d.1 0) = p
      · exact ⟨1, by simp [S, show Q.vertexMap (H.endAt d.1 1) ≠ p from
          fun hh ↦ hne (h0.trans hh.symm)]⟩
      · exact ⟨0, by simp [S, h0]⟩
    let f : H.meets S := ⟨d.1, hd⟩
    refine ⟨f, ?_⟩
    have hf := hedge f
    rw [hmap, hmap] at hf
    apply petersen_isSimple.no_parallel _ _
    rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hj
    · exact (LoopMultigraph.petersen.joins_comm.mp (by simpa only [h0, h1] using hj))
  let F : ParallelReduction (H.contract S) LoopMultigraph.petersen := {
    vertexEquiv := ev
    edgeMap := edgeMap
    edge_surjective := hsurj
    joins_iff := by
      intro f a b
      have hf := hedge f
      rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simp only [Joins, h0, h1, Equiv.apply_eq_iff_eq]
      · simp only [Joins, h0, h1, Equiv.apply_eq_iff_eq]
        tauto }
  exact ⟨F, fun z ↦ congrArg P.vertexEquiv
    (Q.singleFiberVertexEquiv_contractVertex p hs z)⟩

/-- The graph conclusion of the aligned one-fiber contraction. -/
theorem contract_isPetersenUpToParallel_of_single_fiber (p : R.Vertex)
    (hs : ∀ q, q ≠ p → (R.quotient.fiber q).card ≤ 1)
    (hl : ∀ f, H.endAt f 0 ≠ H.endAt f 1)
    (he : (∀ k, H.endAt e k ∈ R.quotient.fiber p) ∨
      ∃ g, R.graph.Joins g (R.quotient.vertexMap (H.endAt e 0))
        (R.quotient.vertexMap (H.endAt e 1))) :
    (H.contract (Finset.univ \ R.quotient.fiber p)).IsPetersenUpToParallel := by
  obtain ⟨f, _⟩ := R.exists_parallelReduction_contract_of_single_fiber p hs hl he
  exact ⟨f⟩

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
