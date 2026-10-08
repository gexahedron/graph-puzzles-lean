import GraphPuzzles.Reduction.Removable.EdgeConnectivity
import GraphPuzzles.Bricks.BrickCharacterization

/-! Bricks and their nondegenerate contractions are three-edge-connected. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype E] in
private theorem pair_cover_of_card_le_two {C : Finset E} (hne : C.Nonempty) (hc : C.card ≤ 2) :
    ∃ e ∈ C, ∃ f ∈ C, C ⊆ {e, f} := by
  have hp := Finset.card_pos.mpr hne
  have hcases : C.card = 1 ∨ C.card = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨e, by simp, e, by simp, by simp⟩
  · obtain ⟨e, f, _, rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨e, by simp, f, by simp, Finset.Subset.refl _⟩

omit [DecidableEq E] in
private theorem cut_edge_ends {X : Finset V} {e : E} (he : e ∈ H.dangling X) :
    ∃ k : Fin 2, H.endAt e k ∈ X ∧ H.endAt e (Fin.rev k) ∉ X := by
  have hh := mem_dangling.mp he
  by_cases h0 : H.endAt e 0 ∈ X
  · exact ⟨0, h0, by simpa using (show H.endAt e 1 ∉ X by tauto)⟩
  · exact ⟨1, by tauto, by simpa using h0⟩

omit [DecidableEq E] in
/-- A loopless nonbipartite graph has a vertex outside any prescribed pair. -/
theorem exists_vertex_outside_pair_of_not_bipartite
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (hn : ¬ H.IsBipartite) (u v : V) :
    ∃ w, w ≠ u ∧ w ≠ v := by
  by_contra h
  push Not at h
  apply hn
  refine ⟨fun w ↦ decide (w = u), fun e ↦ ?_⟩
  by_cases h0 : H.endAt e 0 = u
  · have h1 : H.endAt e 1 ≠ u := fun he ↦ hl e (h0.trans he.symm)
    simp [h0, h1]
  · have h1 : H.endAt e 1 = u := by
      by_contra he
      exact hl e ((h _ h0).trans (h _ he).symm)
    simp [h0, h1]

/-- Bicriticality prevents an even shore from having a cut of size at most
two: deleting one boundary endpoint from each shore leaves an unmatched odd shore. -/
theorem IsBicritical.three_le_even_cut (hb : H.IsBicritical) (hc : H.IsConnected)
    {X : Finset V} (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty)
    (heven : Even X.card) : 3 ≤ (H.dangling X).card := by
  by_contra hn
  obtain ⟨e, he, f, hf, hsub⟩ := pair_cover_of_card_le_two (hc.dangling_nonempty hX hXC) (by omega)
  obtain ⟨i, hi, _⟩ := cut_edge_ends he
  obtain ⟨j, _, hj⟩ := cut_edge_ends hf
  let u := H.endAt e i
  let v := H.endAt f (Fin.rev j)
  have huv : u ≠ v := by
    intro h
    apply hj
    change v ∈ X
    rw [← h]
    exact hi
  obtain ⟨P, hP⟩ := hb u v huv
  have hcut : ∀ g ∈ P, g ∉ H.dangling X := by
    intro g hg hgD
    have hp := hsub hgD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hP.1 _ hg i)).2).1 rfl
    · exact (Finset.mem_erase.mp (hP.1 _ hg (Fin.rev j))).1 rfl
  have hS : X.erase u ⊆ (Finset.univ.erase u).erase v := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem (Finset.mem_of_mem_erase hw) hj,
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ _⟩⟩
  have hr := hP.restrict hS (by
    intro g hg k hk
    have hh : H.endAt g 0 ∈ X ↔ H.endAt g 1 ∈ X := by
      by_contra hn
      exact hcut g hg (mem_dangling.mpr hn)
    have hkX := Finset.mem_of_mem_erase hk
    have ho : H.endAt g (Fin.rev k) ∈ X := by
      fin_cases k
      · exact hh.mp hkX
      · exact hh.mpr hkX
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp (hP.1 _ hg (Fin.rev k))).2).1, ho⟩)
  have he := hr.card_even
  rw [Finset.card_erase_of_mem hi, Nat.even_iff] at he
  rw [Nat.even_iff] at heven
  have hp := Finset.card_pos.mpr hX
  omega

/-- In a nonbipartite matching-covered bicritical graph, each vertex is
incident with at least three edges. -/
theorem IsBicritical.three_le_singleton_cut (hb : H.IsBicritical)
    (hm : H.IsMatchingCovered) (hn : ¬ H.IsBipartite) (v : V) :
    3 ≤ (H.dangling {v}).card := by
  by_contra hlt
  obtain ⟨z, hz, _⟩ := exists_vertex_outside_pair_of_not_bipartite hm.loopless hn v v
  have hVC : (Finset.univ \ {v}).Nonempty := ⟨z, by simp [hz]⟩
  obtain ⟨e, he, f, hf, hsub⟩ := pair_cover_of_card_le_two
    (hm.1.dangling_nonempty (Finset.singleton_nonempty v) hVC) (by omega)
  obtain ⟨i, hi, hu⟩ := cut_edge_ends he
  obtain ⟨j, hj, hw⟩ := cut_edge_ends hf
  let u := H.endAt e (Fin.rev i)
  let w := H.endAt f (Fin.rev j)
  have huv : u ≠ v := by simpa only [Finset.mem_singleton] using hu
  have hwv : w ≠ v := by simpa only [Finset.mem_singleton] using hw
  have impossible (a b : V) (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
      (huab : u = a ∨ u = b) (hwab : w = a ∨ w = b) : False := by
    obtain ⟨P, hP⟩ := hb a b hab
    have hnot (g : E) (hg : g ∈ P) (k : Fin 2) :
        H.endAt g k ≠ a ∧ H.endAt g k ≠ b := by
      have hh := hP.1 g hg k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hh
      exact ⟨hh.2, hh.1⟩
    have hz : H.degreeIn P v = 0 := degreeIn_eq_zero_of (by
      intro g hg k hk
      have hgD : g ∈ H.dangling {v} := by
        apply mem_dangling.mpr
        intro h
        have h' : H.endAt g 0 = v ↔ H.endAt g 1 = v := by simpa using h
        fin_cases k
        · exact hm.loopless g (hk.trans (h'.mp hk).symm)
        · exact hm.loopless g ((h'.mpr hk).trans hk.symm)
      have hgf := hsub hgD
      simp only [Finset.mem_insert, Finset.mem_singleton] at hgf
      rcases hgf with rfl | rfl
      · rcases huab with h | h
        · exact (hnot _ hg (Fin.rev i)).1 h
        · exact (hnot _ hg (Fin.rev i)).2 h
      · rcases hwab with h | h
        · exact (hnot _ hg (Fin.rev j)).1 h
        · exact (hnot _ hg (Fin.rev j)).2 h)
    have ho := hP.2 v (by simp [hva, hvb])
    omega
  by_cases huw : u = w
  · obtain ⟨a, hav, hau⟩ := exists_vertex_outside_pair_of_not_bipartite hm.loopless hn v u
    exact impossible u a hau.symm huv.symm hav.symm (Or.inl rfl) (Or.inl huw.symm)
  · exact impossible u w huw huv.symm hwv.symm (Or.inl rfl) (Or.inr rfl)

/-- Every brick is three-edge-connected. Odd cuts of size at most two would
be tight; even cuts and trivial cuts are excluded by bicriticality. -/
theorem IsBrick.isThreeEdgeConnected (hb : H.IsBrick) : H.IsThreeEdgeConnected := by
  have hbi := hb.isBicritical hb.matchingCovered.loopless
  intro X hX hXC
  rcases Nat.even_or_odd X.card with heven | hodd
  · exact hbi.three_le_even_cut hb.matchingCovered.1 hX hXC heven
  · by_contra hn
    have hsmall : (H.dangling X).card ≤ 2 := by omega
    have ht : H.IsTightCut X := by
      intro M hM
      have hle := (Finset.card_le_card (Finset.inter_subset_right (s₁ := M) (s₂ := H.dangling X))).trans hsmall
      have hp := hM.crossing_mod_two X
      rw [Nat.odd_iff] at hodd
      omega
    have hnt := hb.tight_trivial X ht
    have hXpos := Finset.card_pos.mpr hX
    have hXCpos := Finset.card_pos.mpr hXC
    have hcases : X.card = 1 ∨ (Finset.univ \ X).card = 1 := by
      by_contra h
      push Not at h
      exact hnt ⟨by omega, by omega⟩
    rcases hcases with h1 | h1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
      have hh := hbi.three_le_singleton_cut hb.matchingCovered hb.notBipartite v
      omega
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
      have hh := hbi.three_le_singleton_cut hb.matchingCovered hb.notBipartite v
      rw [← hv, dangling_compl] at hh
      omega

end GraphPuzzles.LoopMultigraph
