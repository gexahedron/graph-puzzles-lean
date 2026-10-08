import GraphPuzzles.Matching.MatchingOn
import GraphPuzzles.Matching.Barriers.MaximalBarrier

/-! Barriers containing the ends of an inadmissible edge. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- If deleting two vertices destroys all perfect matchings, a barrier contains
both deleted vertices. This is Tutte's obstruction with equality forced by an
existing perfect matching of the whole graph. -/
theorem IsPerfectMatching.exists_barrier_of_no_pair_matching {M : Finset E}
    (hM : H.IsPerfectMatching M) {u v : V} (huv : u ≠ v)
    (hn : ¬ ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P) :
    ∃ B, u ∈ B ∧ v ∈ B ∧ ∃ F : H.ComponentFamily B, F.IsBarrier := by
  let S : Finset V := (Finset.univ.erase u).erase v
  have hv : v ∈ Finset.univ.erase u := by simp [Ne.symm huv]
  have hSc : S.card + 2 = Fintype.card V := by
    have hu := Finset.card_erase_add_one (s := (Finset.univ : Finset V)) (Finset.mem_univ u)
    have hv' := Finset.card_erase_add_one hv
    change S.card + 1 = (Finset.univ.erase u).card at hv'
    simpa only [Finset.card_univ] using (by omega : S.card + 2 = (Finset.univ : Finset V).card)
  have hSe : Even S.card := by
    have he := hM.isFractional.card_even
    rw [Nat.even_iff] at he ⊢
    omega
  obtain ⟨D, hDS, F, hcount⟩ := exists_componentFamily_of_no_matchingOn_even S hSe hn
  have hScm : Finset.univ \ S = ({u, v} : Finset V) := by
    ext w
    simp only [S, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hd : Disjoint (Finset.univ \ S) D := by
    apply Finset.disjoint_left.mpr
    exact fun w hw hwD ↦ (Finset.mem_sdiff.mp hw).2 (hDS hwD)
  have hc : ((Finset.univ \ S) ∪ D).card = D.card + 2 := by
    rw [Finset.card_union_of_disjoint hd, hScm, Finset.card_pair huv]
    omega
  have hbound := F.odd_card_le_of_fractional hM.isFractional
  have hb : F.IsBarrier := by
    change F.odd.card = ((Finset.univ \ S) ∪ D).card
    omega
  refine ⟨(Finset.univ \ S) ∪ D, ?_, ?_, F, hb⟩
  · exact Finset.mem_union_left _ (hScm.symm ▸ Finset.mem_insert_self _ _)
  · exact Finset.mem_union_left _ (hScm.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- An inadmissible non-loop edge in a matchable graph has both ends in a barrier. -/
theorem IsPerfectMatching.exists_barrier_of_inadmissible_edge {M : Finset E}
    (hM : H.IsPerfectMatching M) {e : E} (hne : H.endAt e 0 ≠ H.endAt e 1)
    (hn : ¬ ∃ N, H.IsPerfectMatching N ∧ e ∈ N) :
    ∃ B, H.endAt e 0 ∈ B ∧ H.endAt e 1 ∈ B ∧ ∃ F : H.ComponentFamily B, F.IsBarrier := by
  apply hM.exists_barrier_of_no_pair_matching hne
  rintro ⟨P, hP⟩
  exact hn ⟨insert e P, hP.insert_perfect (Or.inl ⟨rfl, rfl⟩) hne, Finset.mem_insert_self _ _⟩

/-- No perfect matching can use an edge whose two ends lie in one barrier. -/
theorem ComponentFamily.IsBarrier.edge_not_admissible {B : Finset V}
    {F : H.ComponentFamily B} (hb : F.IsBarrier) {e : E}
    (h0 : H.endAt e 0 ∈ B) (h1 : H.endAt e 1 ∈ B) :
    ¬ ∃ M, H.IsPerfectMatching M ∧ e ∈ M := by
  rintro ⟨M, hM, he⟩
  have hh := hb.endsIn_of_matching F hM he
  have hc : H.endsIn B e = 2 := by
    unfold LoopMultigraph.endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    simp [h0, h1]
  rw [hc] at hh
  split_ifs at hh
  omega

/-- The barrier criterion for admissibility, with the non-loop hypothesis explicit. -/
theorem IsPerfectMatching.admissible_iff_no_barrier {M : Finset E}
    (hM : H.IsPerfectMatching M) {e : E} (hne : H.endAt e 0 ≠ H.endAt e 1) :
    (∃ N, H.IsPerfectMatching N ∧ e ∈ N) ↔
      ¬ ∃ B, H.endAt e 0 ∈ B ∧ H.endAt e 1 ∈ B ∧ ∃ F : H.ComponentFamily B, F.IsBarrier := by
  constructor
  · intro ha hb
    obtain ⟨B, h0, h1, F, hb⟩ := hb
    exact hb.edge_not_admissible h0 h1 ha
  · intro hn
    by_contra ha
    exact hn (hM.exists_barrier_of_inadmissible_edge hne ha)

end GraphPuzzles.LoopMultigraph
