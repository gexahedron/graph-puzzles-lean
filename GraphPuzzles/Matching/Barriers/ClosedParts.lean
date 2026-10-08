import GraphPuzzles.Matching.Barriers.ComponentRetention
import GraphPuzzles.Matching.Barriers.BarrierBicritical

/-! Complete a disjoint collection of closed vertex sets to a component family. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable (C : Finset (Finset V)) (B : Finset V)
variable (hne : ∀ Q ∈ C, Q.Nonempty)
variable (ha : ∀ Q ∈ C, ∀ v ∈ Q, v ∉ B)
variable (hc : ∀ Q ∈ C, ∀ e : E, ∀ k : Fin 2,
  H.endAt e k ∈ Q → H.endAt e (Fin.rev k) ∉ B → H.endAt e (Fin.rev k) ∈ Q)
variable (hd : ∀ Q ∈ C, ∀ R ∈ C, Q ≠ R → Disjoint Q R)

include hne ha hc hd in
omit [DecidableEq E] in
/-- Keep the specified closed parts and group all remaining vertices in one part. -/
def ofClosedParts : H.ComponentFamily B where
  parts := C ∪ (({remainder C B} : Finset (Finset V)).filter fun Q ↦ Q.Nonempty)
  nonempty := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact hne Q hQ
    · exact (Finset.mem_filter.mp hQ).2
  avoid := by
    intro Q hQ v hv hz
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact ha Q hQ v hv hz
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
      have hh := hc R hR e (Fin.rev k) hr
        (by simpa using ((mem_remainder C B _).mp hk).1)
      exact ((mem_remainder C B _).mp hk).2 R hR (by simpa using hh)
  pairwise := by
    intro Q hQ R hR hQR
    rcases Finset.mem_union.mp hQ with hQ | hQ <;>
      rcases Finset.mem_union.mp hR with hR | hR
    · exact hd Q hQ R hR hQR
    · rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hR).1]
      exact (remainder_disjoint C B hQ).symm
    · rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1]
      exact remainder_disjoint C B hR
    · exact (hQR ((Finset.mem_singleton.mp (Finset.mem_filter.mp hQ).1).trans
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

/-- In a matchable graph, the parity of Tutte's bound rules out a deficit of one. -/
theorem isBarrier_of_odd_card_pred {B : Finset V} (F : H.ComponentFamily B)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hcount : B.card ≤ F.odd.card + 1) :
    F.IsBarrier := by
  have hle := F.odd_card_le_of_fractional hM.isFractional
  have hp := F.odd_card_mod_two
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  rw [Finset.card_univ] at hs
  have he := hM.isFractional.card_even
  rw [Nat.even_iff] at he
  change F.odd.card = B.card
  omega

include hne ha hc hd in
/-- Enough closed odd parts certify a barrier, even if the remainder has
not been separated into individual connected components. -/
theorem exists_barrier_of_closed_odd_parts {M : Finset E} (hM : H.IsPerfectMatching M)
    (ho : ∀ Q ∈ C, Odd Q.card) (hcount : B.card ≤ C.card + 1) :
    ∃ F : H.ComponentFamily B, F.IsBarrier := by
  let F := ofClosedParts C B hne ha hc hd
  have hsub : C ⊆ F.odd := fun Q hQ ↦ F.mem_odd.mpr
    ⟨Finset.mem_union_left _ hQ, ho Q hQ⟩
  exact ⟨F, F.isBarrier_of_odd_card_pred hM
    (hcount.trans (Nat.add_le_add_right (Finset.card_le_card hsub) 1))⟩

end ComponentFamily

end GraphPuzzles.LoopMultigraph
