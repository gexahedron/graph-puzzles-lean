import GraphPuzzles.Ears.LabeledEar

/-! Splitting, joining and reversing walks with their original edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace EdgeChain

omit [DecidableEq V] [DecidableEq E] in
/-- Concatenate two labelled walks at their shared vertex. -/
theorem append {a b : V} {es fs : List E} {l vs : List V}
    (h : H.EdgeChain a es (l ++ [b])) (g : H.EdgeChain b fs vs) :
    H.EdgeChain a (es ++ fs) (l ++ b :: vs) := by
  induction l generalizing a es with
  | nil =>
    cases h with
    | cons he ht => cases ht; exact .cons he g
  | cons c l ih =>
    cases h with
    | cons he ht => exact .cons he (ih ht)

omit [DecidableEq V] [DecidableEq E] in
/-- Split a labelled walk at any displayed intermediate vertex. -/
theorem split {a b : V} {es : List E} (l vs : List V)
    (h : H.EdgeChain a es (l ++ b :: vs)) :
    ∃ xs ys, es = xs ++ ys ∧ H.EdgeChain a xs (l ++ [b]) ∧ H.EdgeChain b ys vs := by
  induction l generalizing a es with
  | nil =>
    cases h with
    | @cons _ _ e es _ he ht => exact ⟨[e], es, rfl, .cons he (.nil _), ht⟩
  | cons c l ih =>
    cases h with
    | @cons _ _ e es _ he ht =>
      obtain ⟨xs, ys, hxy, hx, hy⟩ := ih ht
      exact ⟨e :: xs, ys, by simp [hxy], .cons he hx, hy⟩

omit [DecidableEq V] [DecidableEq E] in
/-- Reverse both the vertices and original labels of a walk. -/
theorem reverse {a b : V} {es : List E} {l : List V}
    (h : H.EdgeChain a es (l ++ [b])) :
    H.EdgeChain b es.reverse (l.reverse ++ [a]) := by
  induction l generalizing a es with
  | nil =>
    cases h with
    | cons he ht => cases ht; exact .cons (H.joins_comm.mp he) (.nil _)
  | cons c l ih =>
    cases h with
    | @cons _ _ e es _ he ht =>
      have hr := (ih ht).append (EdgeChain.cons (H.joins_comm.mp he) (.nil a))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hr

/-- A matching edge incident with the starting vertex prevents another
nonempty walk avoiding that label from lying entirely in the matching. -/
theorem not_subset_of_matching_at_start {a : V} {es : List E} {vs : List V}
    (h : H.EdgeChain a es vs) (hne : vs ≠ []) {M : Finset E} {e : E}
    (heM : e ∈ M) (he : e ∉ es) (hia : ∃ i, H.endAt e i = a)
    (hd : H.degreeIn M a ≤ 1) : ¬ es.toFinset ⊆ M := by
  intro hs
  cases h with
  | nil => exact hne rfl
  | @cons _ b f fs vs hf _ =>
    obtain ⟨i, hi⟩ := hia
    obtain ⟨j, hj⟩ := hf.exists_end
    have hef : (e, i) = (f, j) := by
      apply Finset.card_le_one_iff.mp hd
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heM, Finset.mem_univ _⟩, hi⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs (by simp), Finset.mem_univ _⟩, hj⟩
    have hef' : e = f := congrArg Prod.fst hef
    exact he (by simp [hef'])

end EdgeChain

namespace OddEar

variable {S : Finset V} (A : H.OddEar S)

omit [DecidableEq V] [DecidableEq E] in
theorem reverse_walk {es : List E}
    (hw : H.EdgeChain A.start es (A.interior ++ [A.finish])) :
    H.EdgeChain A.reverse.start es.reverse (A.reverse.interior ++ [A.reverse.finish]) :=
  hw.reverse

end OddEar

end GraphPuzzles.LoopMultigraph
