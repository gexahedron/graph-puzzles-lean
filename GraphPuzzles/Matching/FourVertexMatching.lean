import GraphPuzzles.Reduction.Parallel.ParallelEdges

/-! Matching tools retaining the four original vertex and edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
theorem Joins.ne_of_left_not_end {e f : E} {a b c d : V}
    (he : H.Joins e a b) (hf : H.Joins f c d) (hac : a ≠ c) (had : a ≠ d) : e ≠ f := by
  intro hef
  obtain ⟨k, hk⟩ := he.exists_end
  rcases hf.endAt_mem k with h | h
  · exact hac (hk.symm.trans (hef.symm ▸ h))
  · exact had (hk.symm.trans (hef.symm ▸ h))

theorem isPerfectMatching_pair_of_four_vertices {a b c d : V} {e f : E}
    (hn : [a, b, c, d].Nodup) (hV : [a, b, c, d].toFinset = Finset.univ)
    (he : H.Joins e a b) (hf : H.Joins f c d) : H.IsPerfectMatching {e, f} := by
  have hab : a ≠ b := fun h ↦ (List.nodup_cons.mp hn).1 (by simp [h])
  have hcd : c ≠ d := fun h ↦
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1 (by simp [h])
  have hd : Disjoint ({a, b} : Finset V) {c, d} := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff,
      or_false, not_or, List.nodup_nil, not_false_eq_true, and_true] at hn
    simp_all [Finset.disjoint_left]
  have hM := (he.isPerfectMatchingOn hab).union (hf.isPerfectMatchingOn hcd) hd
  have hS : ({a, b} : Finset V) ∪ {c, d} = Finset.univ := by
    simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
      Finset.insert_union, Finset.singleton_union] using hV
  rw [hS] at hM
  simpa only [Finset.singleton_union] using hM.of_univ

omit [DecidableEq E] in
/-- Covering three of four distinct vertices forces the edge opposite a chosen matching
edge. The degree at the fourth vertex need not be constrained. -/
theorem exists_opposite_edge_of_degree_one {a b c d : V} {e : E} {M : Finset E}
    (hl : ∀ f, H.endAt f 0 ≠ H.endAt f 1)
    (hn : [a, b, c, d].Nodup) (hV : [a, b, c, d].toFinset = Finset.univ)
    (he : H.Joins e a b) (heM : e ∈ M)
    (ha : H.degreeIn M a = 1) (hb : H.degreeIn M b = 1) (hc : H.degreeIn M c = 1) :
    ∃ f ∈ M, H.Joins f c d := by
  have hca : c ≠ a := fun h ↦ (List.nodup_cons.mp hn).1 (by simp [← h])
  have hcb : c ≠ b := fun h ↦ (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [← h])
  obtain ⟨f, hfM, k, hk⟩ := H.mem_edgeSupport_iff.mp
    ((H.degreeIn_pos_iff_mem_edgeSupport M c).mp (by omega))
  have hfe : f ≠ e := by
    intro hfe
    rcases he.endAt_mem k with h | h
    · exact hca (hk.symm.trans (hfe.symm ▸ h))
    · exact hcb (hk.symm.trans (hfe.symm ▸ h))
  have hotherA : H.endAt f (Fin.rev k) ≠ a := by
    intro h
    obtain ⟨j, hj⟩ := he.exists_end
    exact hfe (congrArg Prod.fst (eq_incidence_of_degreeIn_one ha hfM heM h hj))
  have hotherB : H.endAt f (Fin.rev k) ≠ b := by
    intro h
    obtain ⟨j, hj⟩ := (H.joins_comm.mp he).exists_end
    exact hfe (congrArg Prod.fst (eq_incidence_of_degreeIn_one hb hfM heM h hj))
  have hotherC : H.endAt f (Fin.rev k) ≠ c := by
    intro h
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact hl f (hk.trans h.symm)
    · exact hl f (h.trans hk.symm)
  have hother : H.endAt f (Fin.rev k) = d := by
    have hh : H.endAt f (Fin.rev k) ∈ [a, b, c, d].toFinset := hV.symm ▸ Finset.mem_univ _
    simpa only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff,
      hotherA, hotherB, hotherC, false_or, or_false] using hh
  refine ⟨f, hfM, ?_⟩
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact Or.inl ⟨hk, hother⟩
  · exact Or.inr ⟨hother, hk⟩

end GraphPuzzles.LoopMultigraph
