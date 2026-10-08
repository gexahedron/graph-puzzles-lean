import GraphPuzzles.Petersen.PetersenFiberTransport
import GraphPuzzles.Petersen.Minors.DeletedPetersenFibers
import GraphPuzzles.Petersen.PetersenCuts
import GraphPuzzles.Matching.MatchingReachability

/-! Exact boundary incidence in a deleted Petersen expansion. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- Every canonical Petersen edge has an original labelled edge
joining its two fibers. -/
theorem exists_canonical_join (R : H.PetersenFiberModel X)
    {d : Fin 15} {p q : Fin 10} (hd : GraphPuzzles.LoopMultigraph.petersen.Joins d p q) :
    ∃ f a b, H.Joins f a b ∧ R.canonicalVertex a = p ∧ R.canonicalVertex b = q := by
  obtain ⟨f, hf⟩ := R.reduction.edge_surjective d
  let g := R.quotient.edgeLift f
  have hj := (R.reduction.joins_iff f _ _).mp (R.quotient.joins_edgeLift f)
  change GraphPuzzles.LoopMultigraph.petersen.Joins (R.reduction.edgeMap f)
    (R.canonicalVertex (H.endAt g 0)) (R.canonicalVertex (H.endAt g 1)) at hj
  rw [hf] at hj
  obtain ⟨i, hi⟩ := hd.exists_end
  have ho := hd.endAt_rev_of_end hi
  rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases i
  · exact ⟨g, H.endAt g 0, H.endAt g 1, Or.inl ⟨rfl, rfl⟩,
      h0.symm.trans hi, h1.symm.trans ho⟩
  · exact ⟨g, H.endAt g 1, H.endAt g 0, Or.inr ⟨rfl, rfl⟩,
      h1.symm.trans hi, h0.symm.trans ho⟩
  · exact ⟨g, H.endAt g 1, H.endAt g 0, Or.inr ⟨rfl, rfl⟩,
      h0.symm.trans hi, h1.symm.trans ho⟩
  · exact ⟨g, H.endAt g 0, H.endAt g 1, Or.inl ⟨rfl, rfl⟩,
      h1.symm.trans hi, h0.symm.trans ho⟩

/-- A cut edge in the original graph projects to the matching cut of Petersen. -/
theorem canonical_cut_join (R : (H.deleteEdge e).PetersenFiberModel X)
    {f : E} (hfe : f ≠ e) (hf : f ∈ H.dangling X) {a b : V}
    (hj : H.Joins f a b) :
    ∃ d ∈ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut,
      GraphPuzzles.LoopMultigraph.petersen.Joins d (R.canonicalVertex a) (R.canonicalVertex b) := by
  have hab : ¬ (a ∈ X ↔ b ∈ X) := by
    rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [mem_dangling, h0, h1] using hf
    · simpa only [mem_dangling, h0, h1, iff_comm] using hf
  have hne : R.canonicalVertex a ≠ R.canonicalVertex b := by
    intro h
    exact hab (by rw [← R.mem_canonicalCut a, ← R.mem_canonicalCut b, h])
  let f' : Finset.univ.erase e := ⟨f, by simp [hfe]⟩
  have hj' : (H.deleteEdge e).Joins f' a b := hj
  obtain ⟨d, hd⟩ := R.canonical_join_of_distinct_images hj' hne
  refine ⟨d, ?_, hd⟩
  rcases hd with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simpa only [mem_dangling, h0, h1, R.mem_canonicalCut, iff_comm] using hab

/-- The unique canonical cut neighbor is also the fiber containing
the other endpoint of every original boundary edge. -/
theorem canonical_cut_neighbor (R : (H.deleteEdge e).PetersenFiberModel X)
    {d : Fin 15} {p q : Fin 10}
    (hd : d ∈ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut)
    (hdj : GraphPuzzles.LoopMultigraph.petersen.Joins d p q)
    {f : E} (hfe : f ≠ e) (hf : f ∈ H.dangling X) {a b : V}
    (hj : H.Joins f a b) (ha : R.canonicalVertex a = p) : R.canonicalVertex b = q := by
  obtain ⟨g, hg, hgj⟩ := R.canonical_cut_join hfe hf hj
  rw [ha] at hgj
  exact (R.canonical_cut_separating.petersen_dangling_isPerfectMatching
    R.canonical_cut_nontrivial).on_univ.joins_unique hg hd hgj hdj

/-- Every nonsingleton fiber contains an endpoint of the restored edge;
all other canonical vertices have singleton fibers. -/
theorem singleton_away_from_restored_endpoints
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    {p : Fin 10} (hp0 : p ≠ R.canonicalVertex (H.endAt e 0))
    (hp1 : p ≠ R.canonicalVertex (H.endAt e 1)) : (R.canonicalFiber p).card ≤ 1 := by
  by_contra hn
  have hcard : 2 ≤ (R.canonicalFiber p).card := by omega
  have hmem : R.canonicalFiber p ∈ R.nonsingletonFibers :=
    (R.mem_nonsingletonFibers _).mpr ⟨R.reduction.vertexEquiv.symm p, hcard, rfl⟩
  obtain ⟨k, hk⟩ := mem_meets.mp (R.deleted_shore_properties hb hr hm hbi hmem).2.2.2
  have hh := (R.mem_canonicalFiber p _).mp hk
  fin_cases k
  · exact hp0 hh.symm
  · exact hp1 hh.symm

/-- If the original selected cut is a perfect matching, deleting one
of its edges makes both endpoint fibers nonsingleton in any Petersen model. -/
theorem two_le_fiber_of_matching_cut_endpoint
    (R : (H.deleteEdge e).PetersenFiberModel X)
    (hC : H.IsPerfectMatching (H.dangling X)) (he : e ∈ H.dangling X) (k : Fin 2) :
    2 ≤ (R.canonicalFiber (R.canonicalVertex (H.endAt e k))).card := by
  by_contra hn
  have hsmall : (R.canonicalFiber (R.canonicalVertex (H.endAt e k))).card ≤ 1 := by omega
  let p := R.canonicalVertex (H.endAt e k)
  have hPM := R.canonical_cut_separating.petersen_dangling_isPerfectMatching
    R.canonical_cut_nontrivial
  have hpos : 0 < GraphPuzzles.LoopMultigraph.petersen.degreeIn
      (GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut) p := by rw [hPM p]; decide
  obtain ⟨⟨d, i⟩, hdi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hdi, hip⟩ := Finset.mem_filter.mp hdi
  have hd := (Finset.mem_product.mp hdi).1
  let q := GraphPuzzles.LoopMultigraph.petersen.endAt d (Fin.rev i)
  have hj : GraphPuzzles.LoopMultigraph.petersen.Joins d p q := by
    fin_cases i
    · exact Or.inl ⟨hip, rfl⟩
    · exact Or.inr ⟨rfl, hip⟩
  obtain ⟨f, a, b, hf, ha, hb⟩ := R.exists_canonical_join hj
  have haeq : a = H.endAt e k := R.canonicalFiber_subsingleton hsmall ha rfl
  have hfb : f.1 ∈ H.dangling X := by
    have hd' := mem_dangling.mp hd
    have hab : ¬ (a ∈ X ↔ b ∈ X) := by
      rw [← R.mem_canonicalCut a, ← R.mem_canonicalCut b, ha, hb]
      rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
        simpa only [h0, h1, iff_comm] using hd'
    change H.Joins f.1 a b at hf
    rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      simpa only [mem_dangling, h0, h1, iff_comm] using hab
  obtain ⟨j, hj⟩ := hf.exists_end
  have hfe : f.1 = e := congrArg Prod.fst
    (eq_incidence_of_degreeIn_one (hC (H.endAt e k)) hfb he (hj.trans haeq) rfl)
  exact (Finset.mem_erase.mp f.2).1 hfe

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
