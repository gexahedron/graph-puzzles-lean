import GraphPuzzles.Cuts.Shores.DeletedAdjacentShoreMatching
import GraphPuzzles.Bricks.BrickConnectivity
import GraphPuzzles.Matching.MatchingReachability

/-! Selecting the two distinct large-side attachments in Proposition 6.6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Two different vertices of the shore attach to the two prescribed neighbours. -/
def HasDistinctAttachments (H : LoopMultigraph V E) (A : Finset V) (a b : V) : Prop :=
  ∃ s ∈ A, ∃ t ∈ A, s ≠ t ∧ ∃ f g, H.Joins f s a ∧ H.Joins g t b

omit [DecidableEq E] in
private theorem common_attachment_of_not_distinct {A : Finset V} {a b : V}
    (ha : ∃ s ∈ A, ∃ f, H.Joins f s a) (hb : ∃ t ∈ A, ∃ g, H.Joins g t b)
    (hn : ¬ H.HasDistinctAttachments A a b) :
    ∃ s ∈ A, ∀ t ∈ A, ∀ e, H.Joins e t a ∨ H.Joins e t b → t = s := by
  obtain ⟨s, hs, f, hf⟩ := ha
  obtain ⟨t, ht, g, hg⟩ := hb
  have hst : s = t := by
    by_contra hh
    exact hn ⟨s, hs, t, ht, hh, f, g, hf, hg⟩
  subst t
  refine ⟨s, hs, ?_⟩
  intro u hu e he
  rcases he with he | he
  · by_contra hne
    exact hn ⟨u, hu, s, hs, hne, e, g, he, hg⟩
  · by_contra hne
    exact hn ⟨s, hs, u, hu, (fun h ↦ hne h.symm), f, e, hf, he⟩

omit [DecidableEq E] in
/-- If two disjoint shores attach externally through two prescribed
neighbours each, connectivity after deleting two vertices forces one shore
to have distinct attachment vertices. -/
theorem ConnectedAfterDeletingPairs.distinct_attachments
    (hconn : H.ConnectedAfterDeletingPairs) {Y Z A B : Finset V} {a b x y : V}
    (hYZ : Disjoint Y Z) (hAY : A ⊆ Y) (hBZ : B ⊆ Z)
    (hYcard : 2 ≤ Y.card) (hout : (Finset.univ \ (Y ∪ Z)).Nonempty)
    (ha : ∃ s ∈ A, ∃ f, H.Joins f s a) (hb : ∃ t ∈ A, ∃ g, H.Joins g t b)
    (hx : ∃ s ∈ B, ∃ f, H.Joins f s x) (hy : ∃ t ∈ B, ∃ g, H.Joins g t y)
    (hbdY : ∀ e k, H.endAt e k ∈ Y → H.endAt e (Fin.rev k) ∉ Y ∪ Z →
      H.endAt e k ∈ A ∧ H.endAt e (Fin.rev k) ∈ ({a, b} : Finset V))
    (hbdZ : ∀ e k, H.endAt e k ∈ Z → H.endAt e (Fin.rev k) ∉ Y ∪ Z →
      H.endAt e k ∈ B ∧ H.endAt e (Fin.rev k) ∈ ({x, y} : Finset V)) :
    H.HasDistinctAttachments A a b ∨ H.HasDistinctAttachments B x y := by
  by_contra hn
  obtain ⟨hnotA, hnotB⟩ := not_or.mp hn
  obtain ⟨i, hiA, hI⟩ := common_attachment_of_not_distinct ha hb hnotA
  obtain ⟨j, hjB, hJ⟩ := common_attachment_of_not_distinct hx hy hnotB
  have hiY := hAY hiA
  have hjZ := hBZ hjB
  have hij : i ≠ j := fun h ↦ Finset.disjoint_left.mp hYZ hiY (h.symm ▸ hjZ)
  have joins (e : E) (k : Fin 2) : H.Joins e (H.endAt e k) (H.endAt e (Fin.rev k)) := by
    fin_cases k
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have no_cross (e : E) (k : Fin 2) (hin : H.endAt e k ∈ Y ∪ Z)
      (ho : H.endAt e (Fin.rev k) ∉ Y ∪ Z)
      (hk : H.endAt e k ∉ ({i, j} : Finset V)) : False := by
    rcases Finset.mem_union.mp hin with hY | hZ
    · obtain ⟨hA, heab⟩ := hbdY e k hY ho
      have heI : H.endAt e k = i := by
        apply hI _ hA e
        rcases Finset.mem_insert.mp heab with h | h
        · exact Or.inl (h ▸ joins e k)
        · exact Or.inr ((Finset.mem_singleton.mp h) ▸ joins e k)
      exact hk (Finset.mem_insert.mpr (Or.inl heI))
    · obtain ⟨hB, hexy⟩ := hbdZ e k hZ ho
      have heJ : H.endAt e k = j := by
        apply hJ _ hB e
        rcases Finset.mem_insert.mp hexy with h | h
        · exact Or.inl (h ▸ joins e k)
        · exact Or.inr ((Finset.mem_singleton.mp h) ▸ joins e k)
      exact hk (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heJ)))
  let c : V → Bool := fun v ↦ decide (v ∈ Y ∪ Z)
  have hedge (e : E) (h0 : H.endAt e 0 ∉ ({i, j} : Finset V))
      (h1 : H.endAt e 1 ∉ ({i, j} : Finset V)) :
      c (H.endAt e 0) = c (H.endAt e 1) := by
    by_cases he0 : H.endAt e 0 ∈ Y ∪ Z <;> by_cases he1 : H.endAt e 1 ∈ Y ∪ Z
    · simp only [c, he0, he1, decide_true]
    · exact (no_cross e 0 he0 he1 h0).elim
    · exact (no_cross e 1 he1 he0 h1).elim
    · simp only [c, he0, he1, decide_false]
  have hremain : (Y.erase i).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hiY]
    omega)
  obtain ⟨u, hu⟩ := hremain
  obtain ⟨hui, huY⟩ := Finset.mem_erase.mp hu
  have huj : u ≠ j := fun h ↦ Finset.disjoint_left.mp hYZ huY (h.symm ▸ hjZ)
  obtain ⟨v, hv⟩ := hout
  have hvout := (Finset.mem_sdiff.mp hv).2
  have huiJ : u ∉ ({i, j} : Finset V) := by simp [hui, huj]
  have hviJ : v ∉ ({i, j} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ hvout (h.symm ▸ Finset.mem_union_left _ hiY),
      fun h ↦ hvout (h.symm ▸ Finset.mem_union_right _ hjZ)⟩
  have hh := hconn i j hij c hedge u huiJ v hviJ
  have huin := Finset.mem_union_left Z huY
  simp only [c, huin, hvout, decide_true, decide_false, Bool.true_eq_false] at hh

omit [DecidableEq E] in
/-- The attachment vertices selected by connectivity lie in the large
parts of the two restoration shores. -/
theorem BipartiteRestorationShore.distinct_large_attachments
    {e : E} {Y Z : Finset V}
    (P : H.BipartiteRestorationShore e Y) (Q : H.BipartiteRestorationShore e Z)
    (hconn : H.ConnectedAfterDeletingPairs) (hYZ : Disjoint Y Z)
    (hYcard : 2 ≤ Y.card) (hout : (Finset.univ \ (Y ∪ Z)).Nonempty)
    (he : ∀ k, H.endAt e k ∈ Y ∪ Z) {a b x y : V}
    (haout : a ∉ Y ∪ Z) (hbout : b ∉ Y ∪ Z)
    (hxout : x ∉ Y ∪ Z) (hyout : y ∉ Y ∪ Z)
    (ha : ∃ s ∈ Y, ∃ f, H.Joins f s a) (hb : ∃ t ∈ Y, ∃ g, H.Joins g t b)
    (hx : ∃ s ∈ Z, ∃ f, H.Joins f s x) (hy : ∃ t ∈ Z, ∃ g, H.Joins g t y)
    (hbdY : ∀ f k, H.endAt f k ∈ Y → H.endAt f (Fin.rev k) ∉ Y ∪ Z →
      H.endAt f (Fin.rev k) ∈ ({a, b} : Finset V))
    (hbdZ : ∀ f k, H.endAt f k ∈ Z → H.endAt f (Fin.rev k) ∉ Y ∪ Z →
      H.endAt f (Fin.rev k) ∈ ({x, y} : Finset V)) :
    H.HasDistinctAttachments P.large a b ∨ H.HasDistinctAttachments Q.large x y := by
  have large_sub {S : Finset V} (R : H.BipartiteRestorationShore e S) : R.large ⊆ S := by
    intro v hv
    exact R.union_eq ▸ Finset.mem_union_right _ hv
  have large_end {S : Finset V} (R : H.BipartiteRestorationShore e S)
      (hS : S ⊆ Y ∪ Z) (f : E) (k : Fin 2) (hi : H.endAt f k ∈ S)
      (ho : H.endAt f (Fin.rev k) ∉ Y ∪ Z) : H.endAt f k ∈ R.large := by
    have hfe : f ≠ e := fun hh ↦ ho (hh.symm ▸ he (Fin.rev k))
    have hi' : H.endAt f k ∈ R.small ∪ R.large := R.union_eq.symm ▸ hi
    rcases Finset.mem_union.mp hi' with hi' | hi'
    · exact (ho (hS (large_sub R (R.other_edges f hfe k hi')))).elim
    · exact hi'
  have large_neighbor {S : Finset V} (R : H.BipartiteRestorationShore e S)
      (hS : S ⊆ Y ∪ Z) {w : V} (hw : w ∉ Y ∪ Z)
      (h : ∃ s ∈ S, ∃ f, H.Joins f s w) :
      ∃ s ∈ R.large, ∃ f, H.Joins f s w := by
    obtain ⟨s, hs, f, hf⟩ := h
    obtain ⟨k, hk⟩ := hf.exists_end
    refine ⟨s, ?_, f, hf⟩
    have hs' := large_end R hS f k (hk.symm ▸ hs)
      (fun hh ↦ hw (hf.endAt_rev_of_end hk ▸ hh))
    exact hk ▸ hs'
  have hYu : Y ⊆ Y ∪ Z := Finset.subset_union_left
  have hZu : Z ⊆ Y ∪ Z := Finset.subset_union_right
  exact hconn.distinct_attachments hYZ (large_sub P) (large_sub Q) hYcard hout
    (large_neighbor P hYu haout ha) (large_neighbor P hYu hbout hb)
    (large_neighbor Q hZu hxout hx) (large_neighbor Q hZu hyout hy)
    (fun f k hi ho ↦ ⟨large_end P hYu f k hi ho, hbdY f k hi ho⟩)
    (fun f k hi ho ↦ ⟨large_end Q hZu f k hi ho, hbdZ f k hi ho⟩)

end GraphPuzzles.LoopMultigraph
