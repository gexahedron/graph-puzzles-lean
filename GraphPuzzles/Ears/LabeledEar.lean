import GraphPuzzles.Ears.OddEar

/-! Explicit edge labels for odd ears and their attachment to old edge sets. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A walk recorded by its start, successive labelled edges, and successive
vertices. Each list entry retains the original multigraph edge identity. -/
inductive EdgeChain (H : LoopMultigraph V E) : V → List E → List V → Prop
  | nil (a : V) : EdgeChain H a [] []
  | cons {a b : V} {e : E} {es : List E} {vs : List V}
      (step : H.Joins e a b) (tail : EdgeChain H b es vs) :
      EdgeChain H a (e :: es) (b :: vs)

namespace EdgeChain

omit [DecidableEq V] [DecidableEq E] in
theorem length {a : V} {es : List E} {vs : List V} (h : H.EdgeChain a es vs) :
    es.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

omit [DecidableEq V] [DecidableEq E] in
theorem isChain {a : V} {es : List E} {vs : List V} (h : H.EdgeChain a es vs) :
    (a :: vs).IsChain (fun x y ↦ ∃ e, H.Joins e x y) := by
  induction h with
  | nil => exact .singleton _
  | cons he _ ih => exact List.isChain_cons_cons.mpr ⟨⟨_, he⟩, ih⟩

omit [DecidableEq V] [DecidableEq E] in
theorem ends_mem {a : V} {es : List E} {vs : List V} (h : H.EdgeChain a es vs)
    {e : E} (he : e ∈ es) (k : Fin 2) : H.endAt e k ∈ a :: vs := by
  induction h with
  | nil => simp at he
  | cons hf _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · rcases hf.endAt_mem k with hh | hh <;> simp [hh]
    · exact List.mem_cons_of_mem _ (ih he)

omit [DecidableEq V] [DecidableEq E] in
/-- A walk with distinct vertices has distinct labelled edges. -/
theorem nodup {a : V} {es : List E} {vs : List V} (h : H.EdgeChain a es vs)
    (hn : (a :: vs).Nodup) : es.Nodup := by
  induction h with
  | nil => simp
  | @cons a b e es vs he ht ih =>
    have hs := List.nodup_cons.mp hn
    refine List.nodup_cons.mpr ⟨?_, ih hs.2⟩
    intro hem
    obtain ⟨k, hk⟩ := he.exists_end
    exact hs.1 (hk ▸ ht.ends_mem hem k)

omit [DecidableEq V] [DecidableEq E] in
private theorem not_both_of_joins {S : Finset V} {a b : V} {e : E}
    (he : H.Joins e a b) (ha : a ∉ S) : ¬ (H.endAt e 0 ∈ S ∧ H.endAt e 1 ∈ S) := by
  rintro ⟨h0, h1⟩
  obtain ⟨k, hk⟩ := he.exists_end
  fin_cases k
  · exact ha (hk ▸ h0)
  · exact ha (hk ▸ h1)

omit [DecidableEq V] [DecidableEq E] in
/-- If all vertices except possibly the last avoid a shore, every walk edge
has an end outside that shore. -/
theorem not_both_ends_mem {S : Finset V} {a t : V} {es : List E} (l : List V)
    (h : H.EdgeChain a es (l ++ [t])) (ha : a ∉ S) (hl : ∀ x ∈ l, x ∉ S) :
    ∀ e ∈ es, ¬ (H.endAt e 0 ∈ S ∧ H.endAt e 1 ∈ S) := by
  induction l generalizing a es with
  | nil =>
    cases h with
    | cons he ht =>
      cases ht
      intro e he'
      have hef := List.mem_singleton.mp he'
      subst e
      exact not_both_of_joins he ha
  | cons b l ih =>
    cases h with
    | cons he ht =>
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact not_both_of_joins he ha
      · exact ih ht (hl b (by simp)) (fun x hx ↦ hl x (by simp [hx])) e he'

end EdgeChain

omit [DecidableEq V] in
theorem EdgeChain.isChain_restrictEdges {a : V} {es : List E} {vs : List V}
    (h : H.EdgeChain a es vs) {F : Finset E} (hF : es.toFinset ⊆ F) :
    (a :: vs).IsChain (fun x y ↦ ∃ e, (H.restrictEdges F).Joins e x y) := by
  induction h with
  | nil => exact .singleton _
  | @cons a b e es vs he ht ih =>
    have heF : e ∈ F := hF (by simp)
    refine List.isChain_cons_cons.mpr ⟨⟨⟨e, heF⟩, he⟩, ih ?_⟩
    intro f hf
    exact hF (by simp only [List.toFinset_cons, Finset.mem_insert]; exact Or.inr hf)

omit [DecidableEq V] [DecidableEq E] in
/-- Choose an original edge label for every step of an adjacency chain. -/
theorem exists_edgeChain_of_isChain {a : V} {l : List V}
    (h : (a :: l).IsChain (fun x y ↦ ∃ e, H.Joins e x y)) :
    ∃ es, H.EdgeChain a es l := by
  induction l generalizing a with
  | nil => exact ⟨[], .nil a⟩
  | cons b l ih =>
    obtain ⟨e, he⟩ := h.rel_head
    obtain ⟨es, hes⟩ := ih h.tail
    exact ⟨e :: es, .cons he hes⟩

namespace OddEar

variable {S : Finset V} (A : H.OddEar S)

omit [DecidableEq V] [DecidableEq E] in
theorem exists_labels : ∃ es, H.EdgeChain A.start es (A.interior ++ [A.finish]) :=
  exists_edgeChain_of_isChain A.chain

omit [DecidableEq V] [DecidableEq E] in
theorem labels_odd_length {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) : Odd es.length := by
  have he := A.even
  have hl := h.length
  simp only [List.length_append, List.length_singleton] at hl
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

omit [DecidableEq V] [DecidableEq E] in
/-- Odd-ear labels cannot repeat, including for a closed ear. The only
possible immediate return along one edge would have even length two. -/
theorem labels_nodup {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) : es.Nodup := by
  have hn : (A.interior ++ [A.finish]).Nodup := List.nodup_append.mpr
    ⟨A.nodup, by simp, fun x hx y hy hxy ↦
      A.avoids x hx (hxy.symm ▸ (List.mem_singleton.mp hy).symm ▸ A.finish_mem)⟩
  cases hi : A.interior with
  | nil =>
    rw [hi] at h
    cases h with
    | cons _ ht => cases ht; simp
  | cons b l =>
    cases l with
    | nil => have he := A.even; simp [hi] at he
    | cons c l =>
      rw [hi] at h hn
      cases h with
      | @cons _ _ e es _ he ht =>
        cases ht with
        | @cons _ _ f fs _ hf hu =>
          have htail : (f :: fs).Nodup := (EdgeChain.cons hf hu).nodup hn
          refine List.nodup_cons.mpr ⟨?_, htail⟩
          intro hem
          rcases List.mem_cons.mp hem with hef | hem
          · have hac : A.start = c := by
              rw [← hef] at hf
              rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
                rcases hf with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> simp_all
            exact A.avoids c (by simp [hi]) (hac ▸ A.start_mem)
          · obtain ⟨k, hk⟩ := (H.joins_comm.mp he).exists_end
            exact (List.nodup_cons.mp hn).1 (hk ▸ hu.ends_mem hem k)

theorem labels_edgesIn {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) :
    es.toFinset ⊆ H.edgesIn A.vertices := by
  intro e he
  apply mem_edgesIn.mpr
  intro k
  have hk := h.ends_mem (List.mem_toFinset.mp he) k
  rcases List.mem_cons.mp hk with hk | hk
  · exact Finset.mem_union_left _ (hk.symm ▸ A.start_mem)
  · rcases List.mem_append.mp hk with hk | hk
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hk)
    · exact Finset.mem_union_left _ ((List.mem_singleton.mp hk).symm ▸ A.finish_mem)

/-- A nontrivial ear uses no edge whose two ends were already in the old
shore, hence none of the old labelled edges. -/
theorem labels_disjoint_old {F : Finset E} (hF : F ⊆ H.edgesIn S)
    (hne : A.interior ≠ []) {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) : Disjoint F es.toFinset := by
  have hn : ∀ e ∈ es, ¬ (H.endAt e 0 ∈ S ∧ H.endAt e 1 ∈ S) := by
    cases hi : A.interior with
    | nil => exact (hne hi).elim
    | cons b l =>
      rw [hi] at h
      cases h with
      | cons he ht =>
        intro e he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact EdgeChain.not_both_of_joins (H.joins_comm.mp he)
            (A.avoids b (by simp [hi]))
        · exact ht.not_both_ends_mem l (A.avoids b (by simp [hi]))
            (fun x hx ↦ A.avoids x (by simp [hi, hx])) e he'
  apply Finset.disjoint_left.mpr
  intro e heF heL
  exact hn e (List.mem_toFinset.mp heL) ⟨(mem_edgesIn.mp (hF heF)) 0,
    (mem_edgesIn.mp (hF heF)) 1⟩

/-- Realize the ear inside any spanning edge restriction containing its
chosen edge labels. -/
def restrictEdges (F : Finset E) {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) (hF : es.toFinset ⊆ F) :
    (H.restrictEdges F).OddEar S where
  start := A.start
  finish := A.finish
  interior := A.interior
  start_mem := A.start_mem
  finish_mem := A.finish_mem
  nodup := A.nodup
  avoids := A.avoids
  even := A.even
  chain := h.isChain_restrictEdges hF

@[simp] theorem restrictEdges_vertices (F : Finset E) {es : List E}
    (h : H.EdgeChain A.start es (A.interior ++ [A.finish])) (hF : es.toFinset ⊆ F) :
    (A.restrictEdges F h hF).vertices = A.vertices := rfl

end OddEar

end GraphPuzzles.LoopMultigraph
