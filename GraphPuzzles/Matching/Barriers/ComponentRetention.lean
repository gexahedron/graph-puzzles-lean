import GraphPuzzles.Matching.Barriers.MaximalBarrier

/-! Retain chosen components at a smaller separator, grouping the remainder in one part. -/

namespace GraphPuzzles.LoopMultigraph.ComponentFamily

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)
variable (C : Finset (Finset V)) (B : Finset V)

/-- Vertices outside the retained components and the new separator. -/
def remainder : Finset V := Finset.univ \ (B ∪ C.biUnion id)

omit [Fintype E] [DecidableEq E] in
theorem mem_remainder (v : V) : v ∈ remainder C B ↔ v ∉ B ∧ ∀ Q ∈ C, v ∉ Q := by
  simp [remainder]

variable (hCF : C ⊆ F.parts) (hBZ : B ⊆ Z)
variable (hc : ∀ Q ∈ C, ∀ e : E, ∀ k : Fin 2,
  H.endAt e k ∈ Q → H.endAt e (Fin.rev k) ∉ B → H.endAt e (Fin.rev k) ∈ Q)

omit [Fintype E] [DecidableEq E] in
theorem remainder_disjoint {Q : Finset V} (hQ : Q ∈ C) : Disjoint (remainder C B) Q := by
  apply Finset.disjoint_left.mpr
  intro v hv hvQ
  exact ((mem_remainder C B v).mp hv).2 Q hQ hvQ

include hCF hBZ hc in
omit [DecidableEq E] in
/-- If chosen old parts remain closed after shrinking the separator, keep those
parts and group all remaining vertices in a single part, when nonempty. -/
def retainParts : H.ComponentFamily B where
  parts := C ∪ (({remainder C B} : Finset (Finset V)).filter fun Q ↦ Q.Nonempty)
  nonempty := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact F.nonempty Q (hCF hQ)
    · exact (Finset.mem_filter.mp hQ).2
  avoid := by
    intro Q hQ v hv hz
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact F.avoid Q (hCF hQ) v hv (hBZ hz)
    · have he := Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1
      exact ((mem_remainder C B v).mp (he ▸ hv)).1 hz
  closed := by
    intro Q hQ e k hk hn
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact hc Q hQ e k hk hn
    · have he := Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1
      rw [he] at hk ⊢
      apply (mem_remainder C B _).mpr
      refine ⟨hn, ?_⟩
      intro R hR hr
      have hnB := ((mem_remainder C B _).mp hk).1
      have hh := hc R hR e (Fin.rev k) hr (by simpa using hnB)
      exact ((mem_remainder C B _).mp hk).2 R hR (by simpa using hh)
  pairwise := by
    intro Q hQ R hR hne
    rcases Finset.mem_union.mp hQ with hQ | hQ <;>
      rcases Finset.mem_union.mp hR with hR | hR
    · exact F.pairwise Q (hCF hQ) R (hCF hR) hne
    · have he := Finset.mem_singleton.mp (Finset.mem_filter.mp hR).1
      rw [he]
      exact (remainder_disjoint C B hQ).symm
    · have he := Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1
      rw [he]
      exact remainder_disjoint C B hR
    · exact (hne ((Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1).trans
        (Finset.mem_singleton.mp (Finset.mem_filter.mp hR).1).symm)).elim
  cover := by
    intro v hv
    by_cases hmem : ∃ Q ∈ C, v ∈ Q
    · obtain ⟨Q, hQ, hvQ⟩ := hmem
      exact ⟨Q, Finset.mem_union_left _ hQ, hvQ⟩
    · have hr : v ∈ remainder C B := (mem_remainder C B v).mpr ⟨hv, by
        intro Q hQ hvQ
        exact hmem ⟨Q, hQ, hvQ⟩⟩
      exact ⟨remainder C B, Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, ⟨v, hr⟩⟩), hr⟩

/-- If there are as many retained odd components as new separator vertices,
Tutte's bound forces the remainder to be even and the new family to be a barrier. -/
theorem retainParts_odd {M : Finset E} (hM : H.IsPerfectMatching M)
    (hodd : ∀ Q ∈ C, Odd Q.card) (hcard : C.card = B.card) :
    (F.retainParts C B hCF hBZ hc).odd = C := by
  let P := F.retainParts C B hCF hBZ hc
  have hsub : C ⊆ P.odd := by
    intro Q hQ
    exact P.mem_odd.mpr ⟨Finset.mem_union_left _ hQ, hodd Q hQ⟩
  have hbound := P.odd_card_le_of_fractional hM.isFractional
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem retainParts_isBarrier {M : Finset E} (hM : H.IsPerfectMatching M)
    (hodd : ∀ Q ∈ C, Odd Q.card) (hcard : C.card = B.card) :
    (F.retainParts C B hCF hBZ hc).IsBarrier := by
  change (F.retainParts C B hCF hBZ hc).odd.card = B.card
  rw [F.retainParts_odd C B hCF hBZ hc hM hodd hcard, hcard]

end GraphPuzzles.LoopMultigraph.ComponentFamily
