import GraphPuzzles.Reduction.Parallel.ParallelEdges
import GraphPuzzles.Cuts.TightCutDecomposition

/-! The four-vertex brace case of Campos–Lucchesi Lemma 2.12. -/

namespace GraphPuzzles.LoopMultigraph

open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
private theorem exists_joins_of_mem_meets_singleton {e : E} {v : V}
    (he : e ∈ H.meets {v}) : ∃ w, H.Joins e v w := by
  obtain ⟨k, hk⟩ := mem_meets.mp he
  have hk' := Finset.mem_singleton.mp hk
  fin_cases k
  · exact ⟨H.endAt e 1, Or.inl ⟨hk', rfl⟩⟩
  · exact ⟨H.endAt e 0, Or.inr ⟨rfl, hk'⟩⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem color_ne_of_joins {c : V → Bool}
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    {e : E} {u v : V} (he : H.Joins e u v) : c u ≠ c v := by
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simpa only [h0, h1] using hc e
  · simpa only [h0, h1] using (hc e).symm

/-- In a bipartite matching-covered multigraph on four vertices, a vertex whose degree is
not two is incident with at most one nonremovable edge. Parallel edge labels are counted
separately. -/
theorem IsMatchingCovered.card_nonremovable_incident_le_one_of_card_four
    (hm : H.IsMatchingCovered) (hb : H.IsBipartite) (h4 : Fintype.card V = 4)
    (v : V) (hdeg : H.degree v ≠ 2) :
    ((H.meets {v}).filter fun e ↦ ¬ H.IsRemovable e).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heI, heN⟩ := Finset.mem_filter.mp he
  obtain ⟨hfI, hfN⟩ := Finset.mem_filter.mp hf
  by_contra hef
  obtain ⟨a, hea⟩ := exists_joins_of_mem_meets_singleton heI
  obtain ⟨b, hfb⟩ := exists_joins_of_mem_meets_singleton hfI
  have hab : a ≠ b := by
    intro hab
    subst b
    exact heN (hm.isRemovable_of_parallel hef (hea.parallel hfb))
  obtain ⟨c, hc⟩ := hb
  have hva := color_ne_of_joins hc hea
  have hvb := color_ne_of_joins hc hfb
  let S := Finset.univ.filter fun w ↦ c w ≠ c v
  have hS_card : S.card = 2 := by
    obtain ⟨M, hM, _⟩ := hm.2 e
    have heq := card_sides_eq hc hM (by decide : 0 < 1)
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (fun w ↦ c w = true)
    have hsum' : (Finset.univ.filter fun w ↦ c w = true).card +
        (Finset.univ.filter fun w ↦ c w = false).card = 4 := by
      simpa only [Bool.not_eq_true, Finset.card_univ, h4] using hsum
    dsimp [S]
    cases c v <;> simp only [Bool.not_eq_false, Bool.not_eq_true] <;> omega
  have hS_pair : ({a, b} : Finset V) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hva.symm⟩
      · rw [Finset.mem_singleton.mp hw]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvb.symm⟩
    · simp [hS_card, hab]
  have hinc : ∀ g ∈ H.meets {v}, g = e ∨ g = f := by
    intro g hg
    obtain ⟨w, hgw⟩ := exists_joins_of_mem_meets_singleton hg
    have hwS : w ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (color_ne_of_joins hc hgw).symm⟩
    rw [← hS_pair] at hwS
    rcases Finset.mem_insert.mp hwS with hwa | hwb
    · have hga : H.Joins g v a := hwa ▸ hgw
      by_cases hge : g = e
      · exact Or.inl hge
      · exact False.elim (heN (hm.isRemovable_of_parallel (Ne.symm hge) (hea.parallel hga)))
    · have hgb : H.Joins g v b := (Finset.mem_singleton.mp hwb) ▸ hgw
      by_cases hgf : g = f
      · exact Or.inr hgf
      · exact False.elim (hfN (hm.isRemovable_of_parallel (Ne.symm hgf) (hfb.parallel hgb)))
  have hd0 : H.degreeIn (Finset.univ \ {e, f}) v = 0 := by
    apply degreeIn_eq_zero_of
    intro g hg k hkv
    have hgi : g ∈ H.meets {v} := mem_meets.mpr ⟨k, by simp [hkv]⟩
    exact (Finset.mem_sdiff.mp hg).2 (by simpa using hinc g hgi)
  have hde : H.degreeIn {e} v = 1 :=
    degreeIn_singleton_of_joins hea (fun h ↦ hva (congrArg c h))
  have hdf : H.degreeIn {f} v = 1 :=
    degreeIn_singleton_of_joins hfb (fun h ↦ hvb (congrArg c h))
  have hdp : H.degreeIn {e, f} v = 2 := by
    have hd : Disjoint ({e} : Finset E) {f} := by simp [hef]
    have hh := degreeIn_union_of_disjoint (H := H) hd v
    simpa only [Finset.singleton_union, hde, hdf] using hh
  have htotal := degreeIn_add_compl (H := H) {e, f} v
  exact hdeg (by omega)

/-- Campos–Lucchesi Lemma 2.12 on four vertices. -/
theorem IsBrace.card_nonremovable_incident_le_one
    (hb : H.IsBrace) (h4 : Fintype.card V = 4) (hdeg : ∀ v, H.degree v ≠ 2) (v : V) :
    ((H.meets {v}).filter fun e ↦ ¬ H.IsRemovable e).card ≤ 1 :=
  hb.matchingCovered.card_nonremovable_incident_le_one_of_card_four hb.bipartite h4 v (hdeg v)

end GraphPuzzles.LoopMultigraph
