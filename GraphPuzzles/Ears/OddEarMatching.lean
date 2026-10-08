import GraphPuzzles.Ears.LabeledEar

/-! An odd ear contained in a matching consists of a single edge. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace OddEar

variable {S : Finset V} (A : H.OddEar S)

/-- An ear whose labels all belong to an edge set of degree at most one at
its internal vertices has no internal vertices. -/
theorem interior_nil_of_labels_subset {M : Finset E} {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    (hM : es.toFinset ⊆ M)
    (hd : ∀ w ∈ A.interior, H.degreeIn M w ≤ 1) : A.interior = [] := by
  cases hi : A.interior with
  | nil => rfl
  | cons b l =>
    cases l with
    | nil => have he := A.even; simp [hi] at he
    | cons c l =>
      have hn := A.labels_nodup hw
      rw [hi] at hw
      cases hw with
      | @cons _ _ e es _ he ht =>
        cases ht with
        | @cons _ _ f fs _ hf _ =>
          obtain ⟨i, hi'⟩ := (H.joins_comm.mp he).exists_end
          obtain ⟨j, hj⟩ := hf.exists_end
          have hinc : (e, i) = (f, j) := by
            apply Finset.card_le_one_iff.mp (hd b (by simp [hi]))
            · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨hM (by simp), Finset.mem_univ _⟩, hi'⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨hM (by simp), Finset.mem_univ _⟩, hj⟩
          have hef : e = f := congrArg Prod.fst hinc
          exact ((List.nodup_cons.mp hn).1 (by simp [hef])).elim

/-- In particular, a matching ear has exactly one original edge label. -/
theorem labels_singleton_of_subset {M : Finset E} {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    (hM : es.toFinset ⊆ M)
    (hd : ∀ w ∈ A.interior, H.degreeIn M w ≤ 1) : ∃ e, es = [e] := by
  have hi := A.interior_nil_of_labels_subset hw hM hd
  rw [hi] at hw
  cases hw with
  | cons _ ht => cases ht; exact ⟨_, rfl⟩

omit [DecidableEq V] [DecidableEq E] in
theorem labels_singleton_of_interior_nil {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    (hi : A.interior = []) : ∃ e, es = [e] := by
  rw [hi] at hw
  cases hw with
  | cons _ ht => cases ht; exact ⟨_, rfl⟩

theorem vertices_eq_of_labels_subset {M : Finset E} {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    (hM : es.toFinset ⊆ M)
    (hd : ∀ w ∈ A.interior, H.degreeIn M w ≤ 1) : A.vertices = S := by
  simp [vertices, A.interior_nil_of_labels_subset hw hM hd]

/-- Regard any internal edge of the old shore as a one-edge ear. -/
def single (S : Finset V) (e : E) (he : e ∈ H.edgesIn S) : H.OddEar S where
  start := H.endAt e 0
  finish := H.endAt e 1
  interior := []
  start_mem := (mem_edgesIn.mp he) 0
  finish_mem := (mem_edgesIn.mp he) 1
  nodup := by simp
  avoids := by simp
  even := by simp
  chain := List.isChain_cons_cons.mpr ⟨⟨e, Or.inl ⟨rfl, rfl⟩⟩, .singleton _⟩

omit [DecidableEq E] in
theorem single_walk (S : Finset V) (e : E) (he : e ∈ H.edgesIn S) :
    H.EdgeChain (single S e he).start [e]
      ((single S e he).interior ++ [(single S e he).finish]) :=
  .cons (Or.inl ⟨rfl, rfl⟩) (.nil _)

omit [DecidableEq E] in
@[simp] theorem single_vertices (S : Finset V) (e : E) (he : e ∈ H.edgesIn S) :
    (single S e he).vertices = S := by simp [single, vertices]

end OddEar

end GraphPuzzles.LoopMultigraph
