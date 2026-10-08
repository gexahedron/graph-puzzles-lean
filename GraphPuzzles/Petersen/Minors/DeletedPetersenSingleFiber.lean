import GraphPuzzles.Petersen.Minors.OneFiberPetersenContraction
import GraphPuzzles.Petersen.PetersenOneExpansionMatching
import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixOpposite
import GraphPuzzles.Petersen.PetersenExpansion
import GraphPuzzles.Petersen.PetersenAddedEdge

/-! The zero- and one-expansion branches of Sections 6.4 and 6.5. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V} {e : E}

namespace PetersenFiberModel

/-- Reverse only the orientation of the selected cut. -/
def compl (R : H.PetersenFiberModel X) : H.PetersenFiberModel (Finset.univ \ X) where
  Vertex := R.Vertex
  Edge := R.Edge
  graph := R.graph
  quotient := R.quotient
  petersen := R.petersen
  cut := Finset.univ \ R.cut
  strict := R.strict.compl
  selected_eq := by rw [R.quotient.preimage_compl, R.selected_eq]

@[simp] theorem compl_canonicalVertex (R : H.PetersenFiberModel X) (v : V) :
    R.compl.canonicalVertex v = R.canonicalVertex v := rfl

@[simp] theorem compl_canonicalFiber (R : H.PetersenFiberModel X) (p : Fin 10) :
    R.compl.canonicalFiber p = R.canonicalFiber p := rfl

@[simp] theorem compl_canonicalCut (R : H.PetersenFiberModel X) :
    R.compl.canonicalCut = Finset.univ \ R.canonicalCut := R.reduction.mapVertices_compl R.cut

variable (R : (H.deleteEdge e).PetersenFiberModel X)

/-- The same local matching construction also handles an exterior
restored endpoint on the opposite side of the selected cut. -/
theorem exists_three_crossing_one_expansion_opposite {p q : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (hbic : H.IsBicritical)
    (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small)
    (hw : R.canonicalVertex w = q) (hqp : q ≠ p)
    (hp : p ∈ R.canonicalCut) (hq : q ∉ R.canonicalCut)
    (hadj : ∀ f, ¬ LoopMultigraph.petersen.Joins f p q) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  obtain ⟨x, y, z, N, hxy, hxz, hyz, hd, hc, hN, hn⟩ :=
    R.canonical_cut_separating.petersen_opposite_expansion_patch
      R.canonical_cut_nontrivial hp hq hqp.symm hadj
  apply R.assemble_one_expansion P hbic hsingle he hv hw hqp hp hxy hxz hyz hd hc hN
  have hqx : q ≠ x := fun h ↦ Finset.disjoint_left.mp hd
    (by simp [h] : q ∈ ({x, y, z} : Finset (Fin 10))) (by simp)
  have hqy : q ≠ y := fun h ↦ Finset.disjoint_left.mp hd
    (by simp [h] : q ∈ ({x, y, z} : Finset (Fin 10))) (by simp)
  have heq : ({x, y, q} : Finset (Fin 10)) \ R.canonicalCut =
      insert q ({x, y} \ R.canonicalCut) := by
    ext t
    by_cases ht : t = q <;> simp [ht, hq, or_comm]
  rw [heq, Finset.card_insert_of_notMem (by simp [hqx, hqy])]
  omega

/-- Internal restoration or restoration parallel to an existing target
edge is reduced to Lemma 2.7, with its exact selected-cut alignment. -/
theorem exists_three_crossing_one_fiber_internal_or_adjacent
    (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (p : Fin 10) (hcard : 2 ≤ (R.canonicalFiber p).card)
    (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1)
    (hp : p ∈ R.canonicalCut)
    (he : (∀ k, R.canonicalVertex (H.endAt e k) = p) ∨
      ∃ g, LoopMultigraph.petersen.Joins g
        (R.canonicalVertex (H.endAt e 0)) (R.canonicalVertex (H.endAt e 1))) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  let p' := R.reduction.vertexEquiv.symm p
  let Y := R.canonicalFiber p
  let S := Finset.univ \ Y
  have hs' : ∀ q, q ≠ p' → (R.quotient.fiber q).card ≤ 1 := by
    intro q hq
    have hqp : R.reduction.vertexEquiv q ≠ p := fun h ↦ hq
      (by simpa only [p', Equiv.symm_apply_apply] using congrArg R.reduction.vertexEquiv.symm h)
    simpa only [canonicalFiber, Equiv.symm_apply_apply] using hsingle _ hqp
  have he' : (∀ k, H.endAt e k ∈ R.quotient.fiber p') ∨
      ∃ g, R.graph.Joins g (R.quotient.vertexMap (H.endAt e 0))
        (R.quotient.vertexMap (H.endAt e 1)) := by
    rcases he with he | ⟨g, hg⟩
    · exact Or.inl (fun k ↦ (R.mem_canonicalFiber p _).mpr (he k))
    · obtain ⟨g, rfl⟩ := R.reduction.edge_surjective g
      exact Or.inr ⟨g, (R.reduction.joins_iff g _ _).mpr hg⟩
  obtain ⟨f, hf⟩ := R.exists_parallelReduction_contract_of_single_fiber p' hs'
    hb.matchingCovered.loopless he'
  have hmap (z : V) : f.vertexEquiv (contractVertex S z) = R.canonicalVertex z := hf z
  have hYS : Y ⊆ X := by
    intro z hz
    exact (R.mem_canonicalCut z).mp ((R.mem_canonicalFiber p z).mp hz ▸ hp)
  have hXS : Finset.univ \ X ⊆ S := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy ↦ (Finset.mem_sdiff.mp hz).2 (hYS hy)⟩
  let Z := contractShore S (Finset.univ \ X)
  have hZ : f.mapVertices Z = Finset.univ \ R.canonicalCut := by
    ext r
    obtain ⟨z, rfl⟩ := R.canonicalVertex_surjective r
    conv_lhs => rw [← hmap z]
    rw [f.mem_mapVertices]
    by_cases hz : z ∈ S
    · simp only [Z, contractVertex, dif_pos hz,
        Finset.mem_sdiff, Finset.mem_univ, true_and, R.mem_canonicalCut]
      exact (some_mem_contractShore S (Finset.univ \ X) ⟨z, hz⟩).trans (by simp)
    · have hzX : z ∈ X := by
        by_contra hzX
        exact hz (hXS (by simp [hzX]))
      simp only [Z, contractVertex, dif_neg hz,
        Finset.mem_sdiff, Finset.mem_univ, true_and, R.mem_canonicalCut, hzX, not_true_eq_false]
      exact iff_false_intro (none_not_mem_contractShore S (Finset.univ \ X))
  have hsZ : (H.contract S).IsSeparatingCut Z := by
    apply (f.isSeparatingCut_iff_contract Z).mpr
    rw [hZ]
    exact R.canonical_cut_separating.compl
  have hntZ : IsNontrivialCut Z := by
    apply (f.nontrivial_mapVertices Z).mp
    rw [hZ]
    exact R.canonical_cut_nontrivial.compl
  have hYmem : Y ∈ R.nonsingletonFibers :=
    (R.mem_nonsingletonFibers Y).mpr ⟨p', hcard, rfl⟩
  have hYprops := R.deleted_shore_properties hb hr hm hbi hYmem
  obtain ⟨M, hM, heM⟩ := hb.matchingCovered.2 e
  have hM3 : (M ∩ H.dangling S).card = 3 := by
    change (M ∩ H.dangling (Finset.univ \ Y)).card = 3
    rw [dangling_compl]
    exact hb.crossing_three_of_deleted_tight_shore hr hYprops.1 hYprops.2.1 hYprops.2.2.1 hM heM
  obtain ⟨N, hN, hN3⟩ := hM.exists_three_crossing_of_petersen_contraction hM3 ⟨f⟩
    (none_not_mem_contractShore S _) hsZ hntZ
  refine ⟨N, hN, ?_⟩
  simpa only [Z, sourceShore_contractShore, Finset.inter_eq_right.mpr hXS,
    dangling_compl] using hN3

/-- The oriented one-fiber case, including internal, adjacent, and
nonadjacent restored endpoints on either side of the selected cut. -/
theorem exists_three_crossing_one_fiber_oriented
    (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (p : Fin 10) (hcard : 2 ≤ (R.canonicalFiber p).card)
    (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1)
    (hp : p ∈ R.canonicalCut) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  have hmem : R.canonicalFiber p ∈ R.nonsingletonFibers :=
    (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm p, hcard, rfl⟩
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hmem
  obtain ⟨k, hk⟩ := mem_meets.mp P.edge_meets_small
  have hv : R.canonicalVertex (H.endAt e k) = p :=
    (R.mem_canonicalFiber p _).mp (P.union_eq ▸ Finset.mem_union_left _ hk)
  have hej : H.Joins e (H.endAt e k) (H.endAt e (Fin.rev k)) := by
    fin_cases k
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  let q := R.canonicalVertex (H.endAt e (Fin.rev k))
  by_cases hqp : q = p
  · apply R.exists_three_crossing_one_fiber_internal_or_adjacent hb hr hm hbi p hcard hsingle hp
    apply Or.inl
    intro j
    fin_cases k <;> fin_cases j <;> simp_all [q]
  by_cases hadj : ∃ f, LoopMultigraph.petersen.Joins f p q
  · apply R.exists_three_crossing_one_fiber_internal_or_adjacent hb hr hm hbi p hcard hsingle hp
    obtain ⟨f, hf⟩ := hadj
    apply Or.inr
    fin_cases k
    · change R.canonicalVertex (H.endAt e 0) = p at hv
      change LoopMultigraph.petersen.Joins f p (R.canonicalVertex (H.endAt e 1)) at hf
      exact ⟨f, hv.symm ▸ hf⟩
    · change R.canonicalVertex (H.endAt e 1) = p at hv
      change LoopMultigraph.petersen.Joins f p (R.canonicalVertex (H.endAt e 0)) at hf
      exact ⟨f, hv.symm ▸ (LoopMultigraph.petersen.joins_comm.mp hf)⟩
  have hno : ∀ f, ¬ LoopMultigraph.petersen.Joins f p q := by simpa only [not_exists] using hadj
  have hbic := hb.isBicritical hb.matchingCovered.loopless
  by_cases hq : q ∈ R.canonicalCut
  · exact R.exists_three_crossing_one_expansion P hbic hsingle hej hk rfl hqp hp hq hno
  · exact R.exists_three_crossing_one_expansion_opposite P hbic hsingle hej hk rfl hqp hp hq hno

/-- The zero-or-one-fiber branch needed in both the internal-edge and
the cut-edge induction cases. The distinguished fiber may be a singleton. -/
theorem exists_three_crossing_of_single_fiber
    (hb : H.IsBrick) (hsimple : H.IsSimple) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X)
    (p : Fin 10) (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  by_cases hcard : 2 ≤ (R.canonicalFiber p).card
  · by_cases hp : p ∈ R.canonicalCut
    · exact R.exists_three_crossing_one_fiber_oriented hb hr hm hbi p hcard hsingle hp
    · have hh := R.compl.exists_three_crossing_one_fiber_oriented hb hr hm hbi p hcard hsingle
        (by simpa using hp)
      simpa only [dangling_compl] using hh
  have hall (r : Fin 10) : (R.canonicalFiber r).card ≤ 1 := by
    by_cases hrp : r = p
    · subst r
      omega
    · exact hsingle r hrp
  have hsQ (w : R.Vertex) : (R.quotient.fiber w).card ≤ 1 := by
    simpa only [canonicalFiber, Equiv.symm_apply_apply] using hall (R.reduction.vertexEquiv w)
  have hp := R.quotient.isPetersenUpToParallel_of_singleton
    (fun f ↦ hb.matchingCovered.loopless f.1) hsQ R.petersen
  have hds : (H.deleteEdge e).IsSimple := {
    loopless := fun f ↦ hsimple.loopless f.1
    no_parallel := fun f g hg ↦ Subtype.ext (hsimple.no_parallel f.1 g.1 hg) }
  exact hsimple.exists_crossing_three_of_petersen_deleteEdge (hp.isPetersen hds) hs hX

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
