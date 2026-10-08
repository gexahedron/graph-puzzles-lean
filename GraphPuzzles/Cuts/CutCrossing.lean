import GraphPuzzles.Cuts.CutOrder

/-! Crossing cuts and the four nested orientations of noncrossing cuts. -/

namespace GraphPuzzles.LoopMultigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two cuts cross exactly when their four common shores are nonempty. -/
def CutsCross (X Y : Finset V) : Prop :=
  (X ∩ Y).Nonempty ∧ (X \ Y).Nonempty ∧ (Y \ X).Nonempty ∧
    (Finset.univ \ (X ∪ Y)).Nonempty

theorem not_cutsCross_iff (X Y : Finset V) : ¬ CutsCross X Y ↔
    X ⊆ Y ∨ X ⊆ Finset.univ \ Y ∨ Finset.univ \ X ⊆ Y ∨
      Finset.univ \ X ⊆ Finset.univ \ Y := by
  classical
  simp only [CutsCross, Finset.nonempty_iff_ne_empty, not_and_or, not_not]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl (by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy ↦
          (Finset.notMem_empty v) (h ▸ Finset.mem_inter.mpr ⟨hv, hy⟩)⟩))
    · exact Or.inl (Finset.sdiff_eq_empty_iff_subset.mp h)
    · exact Or.inr (Or.inr (Or.inr (by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy ↦
          (Finset.mem_sdiff.mp hv).2 ((Finset.sdiff_eq_empty_iff_subset.mp h) hy)⟩)))
    · exact Or.inr (Or.inr (Or.inl (by
        intro v hv
        by_contra hy
        have hm : v ∈ Finset.univ \ (X ∪ Y) := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
            not_or]
          exact ⟨(Finset.mem_sdiff.mp hv).2, hy⟩
        exact (Finset.notMem_empty v) (h ▸ hm))))
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl (Finset.sdiff_eq_empty_iff_subset.mpr h))
    · exact Or.inl (Finset.eq_empty_iff_forall_notMem.mpr (by
        intro v hv
        exact (Finset.mem_sdiff.mp (h (Finset.mem_inter.mp hv).1)).2
          (Finset.mem_inter.mp hv).2))
    · exact Or.inr (Or.inr (Or.inr (Finset.eq_empty_iff_forall_notMem.mpr (by
        intro v hv
        have hh := Finset.mem_sdiff.mp hv
        have hx : v ∉ X := fun hx ↦ hh.2 (Finset.mem_union_left _ hx)
        exact hh.2 (Finset.mem_union_right _ (h (by simp [hx])))))))
    · exact Or.inr (Or.inr (Or.inl (Finset.eq_empty_iff_forall_notMem.mpr (by
        intro v hv
        have hh := Finset.mem_sdiff.mp hv
        exact (Finset.mem_sdiff.mp (h (by simp [hh.2]))).2 hh.1))))

theorem not_cutsCross_self (X : Finset V) : ¬ CutsCross X X :=
  (not_cutsCross_iff X X).mpr (Or.inl (Finset.Subset.refl _))

end GraphPuzzles.LoopMultigraph
