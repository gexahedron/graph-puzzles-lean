import GraphPuzzles.Ears.FirstEarRotation
import GraphPuzzles.Ears.ClosedOddEar
import GraphPuzzles.Ears.OddEarAvoidance

/-! Odd wheels with labelled rims, allowing parallel hub edges, and the index-one case. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- An odd wheel, up to parallel edges incident with the hub. The rim is
a closed odd ear of length at least three, covering exactly the non-hub
vertices and all edges between them. Every rim vertex has a spoke, and
loops anywhere in the graph are excluded. -/
structure OddWheel (H : LoopMultigraph V E) (v : V) where
  root : V
  root_ne : root ≠ v
  rim : H.OddEar {root}
  labels : List E
  walk : H.EdgeChain rim.start labels (rim.interior ++ [rim.finish])
  vertices_eq : rim.vertices = Finset.univ.erase v
  edges_eq : labels.toFinset = H.edgesIn (Finset.univ.erase v)
  length_three : 3 ≤ labels.length
  spokes : ∀ w, w ≠ v → ∃ e, H.Joins e v w
  loopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1

/-- The odd-wheel alternative in Campos–Lucchesi Theorem 5.1. -/
def IsOddWheel (H : LoopMultigraph V E) (v : V) : Prop := Nonempty (H.OddWheel v)

namespace OddWheel

variable {v : V} (W : H.OddWheel v)

include W

theorem rim_card_odd : Odd (H.edgesIn (Finset.univ.erase v)).card :=
  W.edges_eq ▸ W.rim.labels_card_odd W.walk

theorem rim_degree_two {w : V} (hw : w ≠ v) :
    H.degreeIn (H.edgesIn (Finset.univ.erase v)) w = 2 := by
  rw [← W.edges_eq]
  exact W.rim.degree_two W.walk (W.vertices_eq.symm ▸ (by simp [hw]))

end OddWheel

/-- A rim vertex of degree two off the hub must have a hub edge in a brick. -/
theorem IsBrick.exists_spoke_of_rim_degree_two (hb : H.IsBrick) {v w : V} (hw : w ≠ v)
    (hd : H.degreeIn (H.edgesIn (Finset.univ.erase v)) w = 2) : ∃ e, H.Joins e v w := by
  have h3 := (hb.isBicritical hb.matchingCovered.loopless).three_le_singleton_cut
    hb.matchingCovered hb.notBipartite w
  have hs := sum_degree_eq_two_mul_add (H := H) {w}
  simp only [Finset.sum_singleton] at hs
  have hdeg : 3 ≤ H.degree w := by omega
  have hc := degreeIn_add_compl (H := H) (H.edgesIn (Finset.univ.erase v)) w
  have hp : 0 < H.degreeIn (Finset.univ \ H.edgesIn (Finset.univ.erase v)) w := by omega
  obtain ⟨e, he, i, hi⟩ := (H.mem_edgeSupport_iff).mp
    ((H.degreeIn_pos_iff_mem_edgeSupport _ w).mp hp)
  have hn := (Finset.mem_sdiff.mp he).2
  have hv : H.endAt e (Fin.rev i) = v := by
    by_contra hv
    apply hn
    apply mem_edgesIn.mpr
    intro k
    fin_cases i <;> fin_cases k
    · exact Finset.mem_erase.mpr ⟨fun hh ↦ hw (hi.symm.trans hh), Finset.mem_univ _⟩
    · simpa using hv
    · simpa using hv
    · exact Finset.mem_erase.mpr ⟨fun hh ↦ hw (hi.symm.trans hh), Finset.mem_univ _⟩
  refine ⟨e, ?_⟩
  fin_cases i
  · exact Or.inr ⟨hi, hv⟩
  · exact Or.inl ⟨hv, hi⟩

/-- Section 5, Case 2: maximum ear index one forces an odd wheel with hub `v`,
and permits multiple edges only among its spokes. -/
theorem IsBrick.isOddWheel_of_index_one (hb : H.IsBrick) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M)
    (hmax : H.IsMaximumOddEarIndex M (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)) 1)
    {r : V} (L : H.LastOutsideOddEar M r 1 (Finset.univ.erase v)
      (H.edgesIn (Finset.univ.erase v))) : H.IsOddWheel v := by
  have hS := (L.first_ear rfl).1
  let A := L.ear.rebase hS
  have hA : A.vertices = Finset.univ.erase v := L.ear.rebase_vertices hS |>.trans L.vertices_eq
  have hd : ∀ w ∈ Finset.univ.erase v, H.degreeIn M w ≤ 1 :=
    fun w hw ↦ (hM w (Finset.mem_erase.mp hw).1).le
  have heq := L.labels_eq_of_index_one hmax (Finset.Subset.refl _) hd
  have hwalk : H.EdgeChain A.start L.labels (A.interior ++ [A.finish]) := L.walk
  have hr : r ∈ Finset.univ.erase v := L.vertices_eq ▸
    Finset.mem_union_left L.ear.interior.toFinset L.earlier.forget.root_mem
  exact ⟨{
    root := r
    root_ne := (Finset.mem_erase.mp hr).1
    rim := A
    labels := L.labels
    walk := hwalk
    vertices_eq := hA
    edges_eq := heq
    length_three := A.three_le_labels_length hwalk hb.matchingCovered.loopless
    spokes := fun w hw ↦ hb.exists_spoke_of_rim_degree_two hw (by
      rw [← heq]
      exact A.degree_two hwalk (hA.symm ▸ (by simp [hw])))
    loopless := hb.matchingCovered.loopless }⟩

/-- The index-one and singleton-ear cases of the odd-wheel theorem are
discharged. Only a nontrivial last ear of index greater than one remains in
the brick case when neither desired alternative has already been obtained. -/
theorem IsBrick.oddWheel_or_removable_or_longEar (hb : H.IsBrick)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    H.IsOddWheel v ∨
    (∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧ H.IsRemovableDoubleton f g)) ∨
    ∃ r q, 1 < q ∧
      H.IsMaximumOddEarIndex M (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)) q ∧
      ∃ L : H.LastOutsideOddEar M r q (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)),
        L.ear.interior ≠ [] := by
  classical
  obtain ⟨r, q, hmax, ⟨L⟩⟩ := hb.exists_maximum_lastOutside hM
  by_cases hq : q = 1
  · subst q
    exact Or.inl (hb.isOddWheel_of_index_one hM hmax L)
  · by_cases hi : L.ear.interior = []
    · exact Or.inr (Or.inl (hb.exists_removable_avoiding_of_singleton_lastEar hM L hi))
    · exact Or.inr (Or.inr ⟨r, q, by have := L.positive; omega, hmax, L, hi⟩)

end GraphPuzzles.LoopMultigraph
