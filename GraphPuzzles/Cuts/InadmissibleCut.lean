import GraphPuzzles.Matching.Barriers.BarrierObstruction
import GraphPuzzles.Cuts.Shores.ShoreConnectivity

/-! Cuts containing no admissible edge, and barriers meeting their two shores. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- No perfect matching contains an edge of the cut. -/
def IsInadmissibleCut (H : LoopMultigraph V E) (X : Finset V) : Prop :=
  ∀ M, H.IsPerfectMatching M → M ∩ H.dangling X = ∅

variable {X : Finset V}

theorem IsInadmissibleCut.compl (hn : H.IsInadmissibleCut X) :
    H.IsInadmissibleCut (Finset.univ \ X) := by
  intro M hM
  simpa only [dangling_compl] using hn M hM

theorem IsInadmissibleCut.not_mem (hn : H.IsInadmissibleCut X)
    {M : Finset E} (hM : H.IsPerfectMatching M) {e : E} (he : e ∈ M) : e ∉ H.dangling X := by
  intro hd
  have hh : e ∈ M ∩ H.dangling X := Finset.mem_inter.mpr ⟨he, hd⟩
  rw [hn M hM] at hh
  exact Finset.notMem_empty e hh

theorem IsInadmissibleCut.mem_iff (hn : H.IsInadmissibleCut X)
    {M : Finset E} (hM : H.IsPerfectMatching M) {e : E} (he : e ∈ M) :
    H.endAt e 0 ∈ X ↔ H.endAt e 1 ∈ X := by
  by_contra hh
  exact hn.not_mem hM he (mem_dangling.mpr hh)

theorem IsInadmissibleCut.matching_restrict (hn : H.IsInadmissibleCut X)
    {M : Finset E} (hM : H.IsPerfectMatching M) :
    H.IsPerfectMatchingOn X (M ∩ H.edgesIn X) := by
  apply hM.on_univ.restrict (Finset.subset_univ _)
  intro e he k hk
  have hh := hn.mem_iff hM he
  fin_cases k
  · exact hh.mp hk
  · exact hh.mpr hk

/-- A tight component boundary met by a matching inside one shore forces the
intersection with that shore to have odd order. -/
theorem IsInadmissibleCut.odd_inter_of_tight_boundary (hn : H.IsInadmissibleCut X)
    {Q : Finset V} (ht : H.IsTightCut Q) {M : Finset E} (hM : H.IsPerfectMatching M)
    {e : E} (heM : e ∈ M) (heQ : e ∈ H.dangling Q) {k : Fin 2} (hk : H.endAt e k ∈ X) :
    Odd (Q ∩ X).card := by
  have hsub : M ∩ H.dangling (Q ∩ X) ⊆ M ∩ H.dangling Q := by
    intro f hf
    obtain ⟨hfM, hfD⟩ := Finset.mem_inter.mp hf
    refine Finset.mem_inter.mpr ⟨hfM, ?_⟩
    have hX := hn.mem_iff hM hfM
    have hQD := mem_dangling.mp hfD
    simp only [Finset.mem_inter] at hQD
    apply mem_dangling.mpr
    tauto
  have heX := hn.mem_iff hM heM
  have h0X : H.endAt e 0 ∈ X := by
    fin_cases k
    · exact hk
    · exact heX.mpr hk
  have h1X := heX.mp h0X
  have heI : e ∈ M ∩ H.dangling (Q ∩ X) := by
    refine Finset.mem_inter.mpr ⟨heM, mem_dangling.mpr ?_⟩
    simpa only [Finset.mem_inter, h0X, h1X, and_true] using mem_dangling.mp heQ
  have hc := Finset.card_le_card hsub
  rw [ht M hM] at hc
  have hp := Finset.card_pos.mpr ⟨e, heI⟩
  have hpar := hM.crossing_mod_two (Q ∩ X)
  rw [Nat.odd_iff]
  omega

/-- A nonempty proper inadmissible cut has a barrier meeting both shores.
For a nonempty cut, use an inadmissible edge. For an empty cut, deleting one
vertex from each even shore leaves an odd shore with no possible matching. -/
theorem IsInadmissibleCut.exists_barrier_meets_shores (hn : H.IsInadmissibleCut X)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hX : X.Nonempty)
    (hXC : (Finset.univ \ X).Nonempty) :
    ∃ B, (B ∩ X).Nonempty ∧ (B \ X).Nonempty ∧ ∃ F : H.ComponentFamily B, F.IsBarrier := by
  by_cases hd : (H.dangling X).Nonempty
  · obtain ⟨e, he⟩ := hd
    have hmem := mem_dangling.mp he
    have hne : H.endAt e 0 ≠ H.endAt e 1 := by
      intro heq
      exact hmem (heq ▸ Iff.rfl)
    have ha : ¬ ∃ N, H.IsPerfectMatching N ∧ e ∈ N := by
      rintro ⟨N, hN, heN⟩
      exact hn.not_mem hN heN he
    obtain ⟨B, h0, h1, F, hF⟩ := hM.exists_barrier_of_inadmissible_edge hne ha
    refine ⟨B, ?_, ?_, F, hF⟩
    · by_cases h0X : H.endAt e 0 ∈ X
      · exact ⟨_, Finset.mem_inter.mpr ⟨h0, h0X⟩⟩
      · have h1X : H.endAt e 1 ∈ X := by tauto
        exact ⟨_, Finset.mem_inter.mpr ⟨h1, h1X⟩⟩
    · by_cases h0X : H.endAt e 0 ∈ X
      · have h1X : H.endAt e 1 ∉ X := by tauto
        exact ⟨_, Finset.mem_sdiff.mpr ⟨h1, h1X⟩⟩
      · exact ⟨_, Finset.mem_sdiff.mpr ⟨h0, h0X⟩⟩
  · have hde : H.dangling X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
    have hlocal (e : E) : H.endAt e 0 ∈ X ↔ H.endAt e 1 ∈ X := by
      by_contra hh
      have he := mem_dangling.mpr hh
      rw [hde] at he
      exact Finset.notMem_empty e he
    obtain ⟨u, hu⟩ := hX
    obtain ⟨v, hv⟩ := hXC
    have hvX : v ∉ X := (Finset.mem_sdiff.mp hv).2
    have huv : u ≠ v := fun he ↦ hvX (he ▸ hu)
    have hXe := (hn.matching_restrict hM).card_even
    have hno : ¬ ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P := by
      rintro ⟨P, hP⟩
      have hsub : X.erase u ⊆ (Finset.univ.erase u).erase v := by
        intro w hw
        obtain ⟨hwu, hwX⟩ := Finset.mem_erase.mp hw
        exact Finset.mem_erase.mpr ⟨fun he ↦ hvX (he ▸ hwX),
          Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ _⟩⟩
      have hmX := hP.restrict hsub (fun e he k hk ↦ by
        have hnU := (Finset.mem_erase.mp (Finset.mem_erase.mp (hP.1 e he (Fin.rev k))).2).1
        apply Finset.mem_erase.mpr
        refine ⟨hnU, ?_⟩
        have hkX := (Finset.mem_erase.mp hk).2
        fin_cases k
        · exact (hlocal e).mp hkX
        · exact (hlocal e).mpr hkX)
      have he := hmX.card_even
      have hc := Finset.card_erase_add_one hu
      rw [Nat.even_iff] at he hXe
      omega
    obtain ⟨B, huB, hvB, F, hF⟩ := hM.exists_barrier_of_no_pair_matching huv hno
    exact ⟨B, ⟨u, Finset.mem_inter.mpr ⟨huB, hu⟩⟩,
      ⟨v, Finset.mem_sdiff.mpr ⟨hvB, hvX⟩⟩, F, hF⟩

end GraphPuzzles.LoopMultigraph
