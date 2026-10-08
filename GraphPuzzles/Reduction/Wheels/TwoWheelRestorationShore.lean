import GraphPuzzles.Petersen.Minors.DeletedPetersenFibers
import GraphPuzzles.Reduction.Wheels.OddWheelCutDeletion

/-! Expansion shores after deleting a spoke between two odd wheels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X Y : Finset V}

namespace BipartiteRestorationShore

variable (P : H.BipartiteRestorationShore e Y)

/-- At a small-side vertex inside one wheel shore, every selected cut
edge must be the restored edge. -/
theorem cut_edge_eq_restored (hYX : Y ⊆ X) {f : E} (hf : f ∈ H.dangling X)
    {k : Fin 2} (hk : H.endAt f k ∈ P.small) : f = e := by
  by_contra hfe
  have hi : H.endAt f k ∈ X := hYX (P.union_eq ▸ Finset.mem_union_left _ hk)
  have ho : H.endAt f (Fin.rev k) ∈ X :=
    hYX (P.union_eq ▸ Finset.mem_union_right _ (P.other_edges f hfe k hk))
  have hd := mem_dangling.mp hf
  fin_cases k <;> simp_all

omit [DecidableEq E] in
private theorem cut_end_unique {f : E} (hf : f ∈ H.dangling X)
    {i j : Fin 2} (hi : H.endAt f i ∈ X) (hj : H.endAt f j ∈ X) : i = j := by
  have hd := mem_dangling.mp hf
  fin_cases i <;> fin_cases j <;> simp_all

/-- The small bipartition class of an expansion inside a wheel shore
consists of the unique endpoint of the restored spoke on that shore. -/
theorem small_eq_singleton_of_wheel (hw : (H.contract X).IsOddWheel none)
    (hYX : Y ⊆ X) (he : e ∈ H.dangling X) :
    ∃ k, P.small = {H.endAt e k} := by
  obtain ⟨k, hk⟩ := mem_meets.mp P.edge_meets_small
  refine ⟨k, Finset.eq_singleton_iff_unique_mem.mpr ⟨hk, ?_⟩⟩
  intro w hwP
  have hwX : w ∈ X := hYX (P.union_eq ▸ Finset.mem_union_left _ hwP)
  obtain ⟨f, hf, j, hj⟩ := hw.exists_incident_cut_edge hwX
  have hfe := P.cut_edge_eq_restored hYX hf (hj.symm ▸ hwP)
  subst f
  have hjk := cut_end_unique he (hj.symm ▸ hwX)
    (hYX (P.union_eq ▸ Finset.mem_union_left _ hk))
  exact hj.symm.trans (congrArg (H.endAt e) hjk)

include P in
/-- Every nontrivial restoration shore inside a wheel has three vertices. -/
theorem card_eq_three_of_wheel (hw : (H.contract X).IsOddWheel none)
    (hYX : Y ⊆ X) (he : e ∈ H.dangling X) : Y.card = 3 := by
  obtain ⟨k, hk⟩ := P.small_eq_singleton_of_wheel hw hYX he
  rw [← P.union_eq, Finset.card_union_of_disjoint P.disjoint, P.card_large, hk]
  simp

/-- Such an expansion can occur only at a vertex with one selected cut edge. -/
theorem cut_degree_one_of_mem_small (hW : (H.contract X).IsOddWheel none)
    (hYX : Y ⊆ X) (he : e ∈ H.dangling X)
    {w : V} (hw : w ∈ P.small) : H.degreeIn (H.dangling X) w = 1 := by
  obtain ⟨k, hsmall⟩ := P.small_eq_singleton_of_wheel hW hYX he
  have hkw : H.endAt e k = w := (Finset.mem_singleton.mp (hsmall ▸ hw)).symm
  have hk : H.endAt e k ∈ P.small := hkw.symm ▸ hw
  unfold degreeIn
  rw [Finset.card_eq_one]
  refine ⟨(e, k), ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hqw⟩
    have hqe := P.cut_edge_eq_restored hYX hq (hqw.symm ▸ hw)
    have hi : H.endAt e q.2 ∈ X := by
      have hi' : H.endAt q.1 q.2 ∈ X := hqw.symm ▸ hYX (P.union_eq ▸ Finset.mem_union_left _ hw)
      simpa only [hqe] using hi'
    have hqk : q.2 = k := cut_end_unique he hi
      (hYX (P.union_eq ▸ Finset.mem_union_left _ hk))
    exact Prod.ext hqe hqk
  · rintro rfl
    exact ⟨he, hkw⟩

include P in
/-- A spoke endpoint incident to at least two cut edges cannot belong
to a restoration shore contained in its wheel shore. -/
theorem not_subset_of_cut_degree (hW : (H.contract X).IsOddWheel none)
    (he : e ∈ H.dangling X) {k : Fin 2} (hk : H.endAt e k ∈ X)
    (hd : 2 ≤ H.degreeIn (H.dangling X) (H.endAt e k)) : ¬ Y ⊆ X := by
  intro hYX
  obtain ⟨j, hj⟩ := mem_meets.mp P.edge_meets_small
  have hjk := cut_end_unique he (hYX (P.union_eq ▸ Finset.mem_union_left _ hj)) hk
  subst j
  have hh := P.cut_degree_one_of_mem_small hW hYX he hj
  omega

end BipartiteRestorationShore

namespace PetersenFiberModel

variable (R : (H.deleteEdge e).PetersenFiberModel X)

/-- In the two-wheel situation, every genuine expansion fiber has
exactly three vertices. -/
theorem deleted_fiber_card_three (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hl : (H.contract X).IsOddWheel none)
    (hrw : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (he : e ∈ H.dangling X) {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) :
    Y.card = 3 := by
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hY
  obtain ⟨w, _, hw⟩ := (R.mem_nonsingletonFibers Y).mp hY
  have hside : Y ⊆ X ∨ Y ⊆ Finset.univ \ X := by
    simpa only [R.selected_eq, hw] using R.quotient.fiber_side R.cut w
  rcases hside with hside | hside
  · exact P.card_eq_three_of_wheel hl hside he
  · exact P.card_eq_three_of_wheel hrw hside (by simpa only [dangling_compl] using he)

/-- A high-degree spoke endpoint rules out all expansion fibers on its side. -/
theorem deleted_fiber_subset_compl_of_cut_degree (hb : H.IsBrick) (hr : H.IsRemovable e)
    (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hl : (H.contract X).IsOddWheel none) (he : e ∈ H.dangling X)
    {k : Fin 2} (hk : H.endAt e k ∈ X)
    (hd : 2 ≤ H.degreeIn (H.dangling X) (H.endAt e k))
    {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) : Y ⊆ Finset.univ \ X := by
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hY
  obtain ⟨w, _, hw⟩ := (R.mem_nonsingletonFibers Y).mp hY
  have hside : Y ⊆ X ∨ Y ⊆ Finset.univ \ X := by
    simpa only [R.selected_eq, hw] using R.quotient.fiber_side R.cut w
  exact hside.resolve_left (P.not_subset_of_cut_degree hl he hk hd)

/-- Consequently, when one endpoint has at least two cut edges, there
is at most one expansion fiber in a deleted Petersen model. -/
theorem card_nonsingletonFibers_le_one_of_cut_degree (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hl : (H.contract X).IsOddWheel none) (he : e ∈ H.dangling X)
    {k : Fin 2} (hk : H.endAt e k ∈ X)
    (hd : 2 ≤ H.degreeIn (H.dangling X) (H.endAt e k)) :
    R.nonsingletonFibers.card ≤ 1 := by
  have hmem {Y : Finset V} (hY : Y ∈ R.nonsingletonFibers) : H.endAt e (Fin.rev k) ∈ Y := by
    have hside := R.deleted_fiber_subset_compl_of_cut_degree hb hr hm hbi hl he hk hd hY
    obtain ⟨j, hj⟩ := mem_meets.mp (R.deleted_shore_properties hb hr hm hbi hY).2.2.2
    have hjk : j ≠ k := by
      intro hh
      subst j
      exact (Finset.mem_sdiff.mp (hside hj)).2 hk
    have hjr : j = Fin.rev k := by fin_cases j <;> fin_cases k <;> simp_all
    exact hjr ▸ hj
  apply Finset.card_le_one.mpr
  intro Y hY Z hZ
  by_contra hne
  exact Finset.disjoint_left.mp (R.nonsingletonFibers_disjoint hY hZ hne) (hmem hY) (hmem hZ)

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
