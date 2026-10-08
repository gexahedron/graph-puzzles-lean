import GraphPuzzles.Matching.MatchingInduced
import GraphPuzzles.Matching.Barriers.MatchingBarrier

/-! Refining one component of a separator by a second component family. -/

namespace GraphPuzzles.LoopMultigraph.ComponentFamily

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)
variable {Q T : Finset V} (hQ : Q ∈ F.parts) (hT : T ⊆ Q)
variable (P : H.ComponentFamily ((Finset.univ \ Q) ∪ T))

omit [DecidableEq E] in
theorem inner_subset {R : Finset V} (hR : R ∈ P.parts) : R ⊆ Q := by
  intro v hv
  by_contra hn
  exact P.avoid R hR v hv
    (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))

include hQ in
omit [DecidableEq E] in
theorem outer_avoid {R : Finset V} (hR : R ∈ F.parts.erase Q) : Disjoint R Q := by
  obtain ⟨hne, hR⟩ := Finset.mem_erase.mp hR
  exact F.pairwise R hR Q hQ hne

include hQ in
omit [DecidableEq E] in
theorem refinePart_disjoint : Disjoint (F.parts.erase Q) P.parts := by
  apply Finset.disjoint_left.mpr
  intro R hR hRP
  obtain ⟨v, hv⟩ := P.nonempty R hRP
  exact Finset.disjoint_left.mp (F.outer_avoid hQ hR) hv (inner_subset P hRP hv)

include hQ hT in
omit [DecidableEq E] in
/-- Replace the component `Q` by the components remaining after deleting `T ⊆ Q`. -/
def refinePart : H.ComponentFamily (Z ∪ T) where
  parts := F.parts.erase Q ∪ P.parts
  nonempty := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact F.nonempty R (Finset.mem_of_mem_erase hR)
    · exact P.nonempty R hR
  avoid := by
    intro R hR v hv hz
    rcases Finset.mem_union.mp hR with hR | hR
    · rcases Finset.mem_union.mp hz with hz | ht
      · exact F.avoid R (Finset.mem_of_mem_erase hR) v hv hz
      · exact Finset.disjoint_left.mp (F.outer_avoid hQ hR) hv (hT ht)
    · rcases Finset.mem_union.mp hz with hz | ht
      · exact F.avoid Q hQ v (inner_subset P hR hv) hz
      · exact P.avoid R hR v hv (Finset.mem_union_right _ ht)
  closed := by
    intro R hR e k hk hn
    have hnZ : H.endAt e (Fin.rev k) ∉ Z := fun h ↦ hn (Finset.mem_union_left _ h)
    have hnT : H.endAt e (Fin.rev k) ∉ T := fun h ↦ hn (Finset.mem_union_right _ h)
    rcases Finset.mem_union.mp hR with hR | hR
    · exact F.closed R (Finset.mem_of_mem_erase hR) e k hk hnZ
    · have hQ' := F.closed Q hQ e k (inner_subset P hR hk) hnZ
      apply P.closed R hR e k hk
      intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact (Finset.mem_sdiff.mp hh).2 hQ'
      · exact hnT hh
  pairwise := by
    intro R hR U hU hne
    rcases Finset.mem_union.mp hR with hR | hR <;>
      rcases Finset.mem_union.mp hU with hU | hU
    · exact F.pairwise R (Finset.mem_of_mem_erase hR) U (Finset.mem_of_mem_erase hU) hne
    · apply Finset.disjoint_left.mpr
      intro v hvR hvU
      exact Finset.disjoint_left.mp (F.outer_avoid hQ hR) hvR (inner_subset P hU hvU)
    · apply Finset.disjoint_left.mpr
      intro v hvR hvU
      exact Finset.disjoint_left.mp (F.outer_avoid hQ hU) hvU (inner_subset P hR hvR)
    · exact P.pairwise R hR U hU hne
  cover := by
    intro v hv
    have hnZ : v ∉ Z := fun h ↦ hv (Finset.mem_union_left _ h)
    have hnT : v ∉ T := fun h ↦ hv (Finset.mem_union_right _ h)
    by_cases hvQ : v ∈ Q
    · have hn : v ∉ (Finset.univ \ Q) ∪ T := by simp [hvQ, hnT]
      obtain ⟨R, hR, hvR⟩ := P.cover v hn
      exact ⟨R, Finset.mem_union_right _ hR, hvR⟩
    · obtain ⟨R, hR, hvR⟩ := F.cover v hnZ
      have hne : R ≠ Q := fun hh ↦ hvQ (hh ▸ hvR)
      exact ⟨R, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hR⟩), hvR⟩

omit [DecidableEq E] in
theorem refinePart_parts : (F.refinePart hQ hT P).parts = F.parts.erase Q ∪ P.parts := rfl

omit [DecidableEq E] in
theorem refinePart_odd : (F.refinePart hQ hT P).odd = F.odd.erase Q ∪ P.odd := by
  ext R
  simp only [odd, Finset.mem_filter, refinePart_parts, Finset.mem_union, Finset.mem_erase]
  tauto

omit [DecidableEq E] in
theorem refinePart_odd_card : (F.refinePart hQ hT P).odd.card = (F.odd.erase Q).card + P.odd.card := by
  rw [F.refinePart_odd hQ hT P, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro R hR hRP
  obtain ⟨hne, hR⟩ := Finset.mem_erase.mp hR
  exact Finset.disjoint_left.mp (F.refinePart_disjoint hQ P)
    (Finset.mem_erase.mpr ⟨hne, (F.mem_odd.mp hR).1⟩) (P.mem_odd.mp hRP).1

include hQ hT in
omit [DecidableEq E] in
theorem refinePart_separator_card : (Z ∪ T).card = Z.card + T.card := by
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro v hvZ hvT
  exact F.avoid Q hQ v (hT hvT) hvZ

end GraphPuzzles.LoopMultigraph.ComponentFamily
