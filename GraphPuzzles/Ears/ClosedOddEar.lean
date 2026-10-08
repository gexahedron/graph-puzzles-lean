import GraphPuzzles.Ears.EdgeChainOperations
import GraphPuzzles.Ears.OddEarMatching

/-! Degree counting on labelled paths and the odd circuit supplied by a first ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem Joins.degreeIn_singleton_eq {e : E} {a b : V} (he : H.Joins e a b) (w : V) :
    H.degreeIn {e} w = (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
  rw [degreeIn_singleton, Finset.card_filter, Fin.sum_univ_two]
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp only [h0, h1]
  omega

/-- Each traversal contributes one incidence at each endpoint. Distinct
edge labels let us count these incidences in the underlying edge set. -/
theorem EdgeChain.degreeIn_eq_counts {a b : V} {es : List E} {l : List V}
    (hw : H.EdgeChain a es (l ++ [b])) (hn : es.Nodup) (w : V) :
    H.degreeIn es.toFinset w = (a :: l).count w + (l ++ [b]).count w := by
  induction l generalizing a es with
  | nil =>
    cases hw with
    | cons he ht =>
      cases ht
      simpa only [List.nil_append, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
        List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add, Nat.add_zero]
        using he.degreeIn_singleton_eq w
  | cons c l ih =>
    cases hw with
    | @cons _ _ e es _ he ht =>
      have heF : e ∉ es.toFinset := by simpa using (List.nodup_cons.mp hn).1
      rw [List.toFinset_cons, ← Finset.singleton_union,
        degreeIn_union_of_disjoint (by simpa using heF), he.degreeIn_singleton_eq,
        ih ht (List.nodup_cons.mp hn).2]
      simp only [List.count_cons, List.cons_append, beq_iff_eq]
      omega

namespace OddEar

/-- Change an ear's old-shore parameter along equality, preserving all
displayed vertex data definitionally. -/
def rebase {S T : Finset V} (A : H.OddEar S) (h : S = T) : H.OddEar T where
  start := A.start
  finish := A.finish
  interior := A.interior
  start_mem := h ▸ A.start_mem
  finish_mem := h ▸ A.finish_mem
  nodup := A.nodup
  avoids := fun w hw ht ↦ A.avoids w hw (h ▸ ht)
  even := A.even
  chain := A.chain

omit [DecidableEq E] in
@[simp] theorem rebase_vertices {S T : Finset V} (A : H.OddEar S) (h : S = T) :
    (A.rebase h).vertices = A.vertices := by simp [rebase, vertices, h]

variable {r : V} (A : H.OddEar {r})

/-- The labels of a closed odd ear give degree two at every vertex of that
ear. In a loopless graph its odd circuit therefore has length at least three. -/
theorem degree_two {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    {w : V} (hwA : w ∈ A.vertices) : H.degreeIn es.toFinset w = 2 := by
  have hs : A.start = r := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = r := Finset.mem_singleton.mp A.finish_mem
  have hr : r ∉ A.interior := fun hh ↦ A.avoids r hh (Finset.mem_singleton_self _)
  have hn₁ : (r :: A.interior).Nodup := List.nodup_cons.mpr ⟨hr, A.nodup⟩
  have hn₂ : (A.interior ++ [r]).Nodup := List.nodup_append.mpr
    ⟨A.nodup, by simp, fun x hx y hy hxy ↦ hr ((hxy.trans (List.mem_singleton.mp hy)) ▸ hx)⟩
  have hw₁ : w ∈ r :: A.interior := by simpa [vertices] using hwA
  have hw₂ : w ∈ A.interior ++ [r] := by simpa [vertices, or_comm] using hwA
  rw [hw.degreeIn_eq_counts (A.labels_nodup hw), hs, ht,
    List.count_eq_one_of_mem hn₁ hw₁, List.count_eq_one_of_mem hn₂ hw₂]

omit [DecidableEq V] in
theorem labels_card_odd {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish])) : Odd es.toFinset.card := by
  rw [List.toFinset_card_of_nodup (A.labels_nodup hw)]
  exact A.labels_odd_length hw

omit [DecidableEq V] [DecidableEq E] in
/-- A loopless closed odd ear has at least three labelled edges. -/
theorem three_le_labels_length {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : 3 ≤ es.length := by
  have ho := A.labels_odd_length hw
  have hh := hw.length
  have hs : A.start = r := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = r := Finset.mem_singleton.mp A.finish_mem
  by_contra hn
  rw [Nat.odd_iff] at ho
  simp only [List.length_append, List.length_singleton] at hh
  have hi : A.interior = [] := List.length_eq_zero_iff.mp (by omega)
  obtain ⟨e, he⟩ := A.labels_singleton_of_interior_nil hw hi
  have hc : H.EdgeChain r [e] [r] := by simpa only [he, hi, List.nil_append, hs, ht] using hw
  cases hc with
  | cons he _ =>
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> exact hl e (h0.trans h1.symm)

end OddEar

end GraphPuzzles.LoopMultigraph
