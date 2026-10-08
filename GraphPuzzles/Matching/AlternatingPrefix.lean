import GraphPuzzles.Matching.MatchingReachability

/-! Pairing an alternating path up to its first return to a closed shore. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A simple path in the union of two matchings, starting with an edge of
`M` and first entering an `M`-closed shore at its last vertex, pairs all
vertices before that last vertex using edges of `M`. The initial exclusion
of `N` also permits recursion after a preceding `N` edge. -/
theorem matchingOn_prefix_of_closed_shore {X Y S : Finset V} {M N : Finset E}
    (hM : H.IsPerfectMatchingOn X M) (hN : H.IsPerfectMatchingOn Y N)
    (hclosed : ∀ a b, (∃ e ∈ M, H.Joins e a b) → (a ∈ S ↔ b ∈ S))
    (l : List V) {t : V} (ht : t ∈ S)
    (hn : (l ++ [t]).Nodup)
    (hc : (l ++ [t]).IsChain (fun a b ↦ ∃ e ∈ M ∪ N, H.Joins e a b))
    (hout : ∀ a ∈ l, a ∉ S)
    (hfirst : ∀ a ∈ (l ++ [t]).head?, ∀ b ∈ (l ++ [t]).tail,
      ¬ ∃ e ∈ N, H.Joins e a b) :
    ∃ P, H.IsPerfectMatchingOn l.toFinset P ∧ P ⊆ M := by
  induction l using List.twoStepInduction with
  | nil => exact ⟨∅, by simp [IsPerfectMatchingOn], Finset.empty_subset _⟩
  | singleton a =>
    obtain ⟨e, he, hea⟩ := hc.rel_head
    have heM : e ∈ M := (Finset.mem_union.mp he).resolve_right fun heN ↦
      hfirst a (by simp) t (by simp) ⟨e, heN, hea⟩
    exact (hout a (by simp) ((hclosed a t ⟨e, heM, hea⟩).mpr ht)).elim
  | cons_cons a b l ih =>
    obtain ⟨e, he, heab⟩ := hc.rel_head
    have heM : e ∈ M := (Finset.mem_union.mp he).resolve_right fun heN ↦
      hfirst a (by simp) b (by simp) ⟨e, heN, heab⟩
    have hna := List.nodup_cons.mp hn
    have hnb := List.nodup_cons.mp hna.2
    have hab : a ≠ b := fun hh ↦ hna.1 (by simp [hh])
    have hfirst' : ∀ x ∈ (l ++ [t]).head?, ∀ y ∈ (l ++ [t]).tail,
        ¬ ∃ f ∈ N, H.Joins f x y := by
      intro x hx y hy hxy
      obtain ⟨f, hf, hfbx⟩ := hc.tail.rel_head? hx
      have hfN : f ∈ N := (Finset.mem_union.mp hf).resolve_left fun hfM ↦ by
        have hax := hM.joins_unique heM hfM (H.joins_comm.mp heab) hfbx
        exact hna.1 (List.mem_cons_of_mem _ (hax.symm ▸ List.mem_of_mem_head? hx))
      obtain ⟨g, hgN, hgxy⟩ := hxy
      have hby := hN.joins_unique hfN hgN (H.joins_comm.mp hfbx) hgxy
      exact hnb.1 (hby.symm ▸ List.mem_of_mem_tail hy)
    obtain ⟨P, hP, hPM⟩ := ih hnb.2 hc.tail.tail
      (fun x hx ↦ hout x (by simp [hx])) hfirst'
    have hd : Disjoint ({a, b} : Finset V) l.toFinset := by
      apply Finset.disjoint_left.mpr
      intro x hx hxl
      have hxl' := List.mem_append_left [t] (List.mem_toFinset.mp hxl)
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hna.1 (List.mem_cons_of_mem _ hxl')
      · exact hnb.1 ((Finset.mem_singleton.mp hx) ▸ hxl')
    refine ⟨{e} ∪ P, ?_, Finset.union_subset (Finset.singleton_subset_iff.mpr heM) hPM⟩
    simpa only [List.toFinset_cons, Finset.insert_union, Finset.singleton_union] using
      (heab.isPerfectMatchingOn hab).union hP hd

end GraphPuzzles.LoopMultigraph
