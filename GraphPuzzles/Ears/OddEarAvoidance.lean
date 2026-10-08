import GraphPuzzles.Ears.MaximalOddEar
import GraphPuzzles.Ears.OddEarInduced
import GraphPuzzles.Reduction.Removable.DependentAvoidance

/-! The maximal-index setup and the singleton-ear case of the odd-wheel theorem. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every vertex matching of a brick admits the maximal-index setup used
in the odd-wheel proof. The last nonmatching ear has positive index and its
prefix already spans every vertex other than the hub. -/
theorem IsBrick.exists_maximum_lastOutside (hb : H.IsBrick) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) :
    ∃ r q, H.IsMaximumOddEarIndex M (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)) q ∧
      Nonempty (H.LastOutsideOddEar M r q (Finset.univ.erase v)
        (H.edgesIn (Finset.univ.erase v))) := by
  obtain ⟨r, hrv, _⟩ := exists_vertex_outside_pair_of_not_bipartite
    hb.matchingCovered.loopless hb.notBipartite v v
  have hfc := (hb.isBicritical hb.matchingCovered.loopless).factorCritical_erase v
  have hD := hfc.hasOddEarDecomposition_on (r := r) (by simp [hrv])
  obtain ⟨q, hmax⟩ := hD.exists_maximum_index M
  obtain ⟨s, n, hDs⟩ := hmax.1
  have hd : ∀ w ∈ Finset.univ.erase v, H.degreeIn M w ≤ 1 :=
    fun w hw ↦ (hM w (Finset.mem_erase.mp hw).1).le
  have hq : 0 < q := by
    by_contra hq
    have hz : q = 0 := by omega
    have hs := hDs.vertices_eq_singleton_of_index_zero hz hd
    obtain ⟨w, hwv, hws⟩ := exists_vertex_outside_pair_of_not_bipartite
      hb.matchingCovered.loopless hb.notBipartite v s
    have hw : w ∈ Finset.univ.erase v := by simp [hwv]
    rw [hs] at hw
    exact hws (Finset.mem_singleton.mp hw)
  exact ⟨s, q, hmax, hDs.lastOutside hq hd⟩

/-- Section 5, Case 3: a singleton last nonmatching ear yields a removable
edge or doubleton disjoint from both the specified matching and the hub cut. -/
theorem IsBrick.exists_removable_avoiding_of_singleton_lastEar (hb : H.IsBrick)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) {r : V} {q : ℕ}
    (L : H.LastOutsideOddEar M r q (Finset.univ.erase v)
      (H.edgesIn (Finset.univ.erase v))) (hi : L.ear.interior = []) :
    ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧ H.IsRemovableDoubleton f g) := by
  obtain ⟨e, _, heM, heS, hfc⟩ := L.factorCritical_delete_of_singleton hi
  exact hb.exists_removable_avoiding_of_factorCritical_delete hM heM
    (fun k ↦ (Finset.mem_erase.mp ((mem_edgesIn.mp heS) k)).1) hfc

/-- The singleton-ear case is eliminated from the brick part of the
odd-wheel theorem. Every remaining case has a maximal-index ear with a
nonempty, even interior; the edge labels and preceding prefix are retained. -/
theorem IsBrick.removable_avoiding_or_nontrivial_lastEar (hb : H.IsBrick)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    (∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧ H.IsRemovableDoubleton f g)) ∨
    ∃ r q, H.IsMaximumOddEarIndex M (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)) q ∧
      ∃ L : H.LastOutsideOddEar M r q (Finset.univ.erase v) (H.edgesIn (Finset.univ.erase v)),
        L.ear.interior ≠ [] := by
  classical
  obtain ⟨r, q, hmax, ⟨L⟩⟩ := hb.exists_maximum_lastOutside hM
  by_cases hi : L.ear.interior = []
  · exact Or.inl (hb.exists_removable_avoiding_of_singleton_lastEar hM L hi)
  · exact Or.inr ⟨r, q, hmax, L, hi⟩

end GraphPuzzles.LoopMultigraph
