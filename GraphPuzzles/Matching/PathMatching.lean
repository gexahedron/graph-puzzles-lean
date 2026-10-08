import GraphPuzzles.Matching.MatchingOn
import Mathlib.Data.List.Chain

/-! Pairing consecutive vertices of an even path. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The vertices of a simple path with an even number of vertices have a
perfect matching, obtained by pairing consecutive vertices. -/
theorem exists_matchingOn_of_even_chain (l : List V) (hn : l.Nodup)
    (hc : l.IsChain (fun a b ↦ ∃ e, H.Joins e a b)) (he : Even l.length) :
    ∃ M, H.IsPerfectMatchingOn l.toFinset M := by
  induction l using List.twoStepInduction with
  | nil => exact ⟨∅, by simp [IsPerfectMatchingOn]⟩
  | singleton a => simp at he
  | cons_cons a b l ih =>
    obtain ⟨e, heab⟩ := hc.rel_head
    have hna := List.nodup_cons.mp hn
    have hnb := List.nodup_cons.mp hna.2
    have hab : a ≠ b := fun h ↦ hna.1 (by simp [h])
    have hel : Even l.length := by
      rw [Nat.even_iff] at he ⊢
      simp only [List.length_cons] at he
      omega
    obtain ⟨M, hM⟩ := ih hnb.2 hc.tail.tail hel
    have hd : Disjoint ({a, b} : Finset V) l.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hw hwl
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hna.1 (List.mem_cons_of_mem _ (List.mem_toFinset.mp hwl))
      · exact hnb.1 ((Finset.mem_singleton.mp hw) ▸ List.mem_toFinset.mp hwl)
    refine ⟨{e} ∪ M, ?_⟩
    simpa only [List.toFinset_cons, Finset.insert_union, Finset.singleton_union] using
      (heab.isPerfectMatchingOn hab).union hM hd

/-- A matching covering an external set together with one old vertex can be
glued to a factor-critical old shore, with that vertex omitted there. -/
theorem IsFactorCritical.matchingOn_union_of_matchingOn_insert {S T : Finset V}
    (hfc : H.IsFactorCritical S) {v : V} (hv : v ∈ S) (hd : Disjoint S T)
    {M : Finset E} (hM : H.IsPerfectMatchingOn (insert v T) M) :
    ∃ N, H.IsPerfectMatchingOn (S ∪ T) N := by
  obtain ⟨P, hP⟩ := hfc v hv
  have hdisj : Disjoint (S.erase v) (insert v T) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    rcases Finset.mem_insert.mp hw' with h | h
    · exact (Finset.mem_erase.mp hw).1 h
    · exact Finset.disjoint_left.mp hd (Finset.mem_of_mem_erase hw) h
  have heq : S.erase v ∪ insert v T = S ∪ T := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (⟨_, hw⟩ | (rfl | hw))
      · exact Or.inl hw
      · exact Or.inl hv
      · exact Or.inr hw
    · rintro (hw | hw)
      · by_cases h : w = v
        · exact Or.inr (Or.inl h)
        · exact Or.inl ⟨h, hw⟩
      · exact Or.inr (Or.inr hw)
  exact ⟨P ∪ M, heq ▸ hP.union hM hdisj⟩

end GraphPuzzles.LoopMultigraph
