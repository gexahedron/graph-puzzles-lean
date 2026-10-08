import GraphPuzzles.Matching.Bipartite.BipartiteHall
import GraphPuzzles.Bricks.BraceRemovability

/-! Every edge of a brace on at least six vertices is removable (Campos–Lucchesi 2.12). -/

namespace GraphPuzzles.LoopMultigraph

open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {c : V → Bool}

omit [DecidableEq E] in
theorem IsPerfectMatching.card_eq_twice_bipartite_side {M : Finset E}
    (hM : H.IsPerfectMatching M)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) :
    Fintype.card V = 2 * Fintype.card {v // c v = true} := by
  have heq := card_sides_eq hc hM (by decide : 0 < 1)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun w ↦ c w = true)
  simp only [Bool.not_eq_true, Finset.card_univ] at hsum
  rw [Fintype.card_subtype]
  omega

/-- A brace has two surplus neighbours for every nonempty left set missing at least
two vertices of the left colour class. Otherwise its neighbour shore is a nontrivial tight cut. -/
theorem IsBrace.two_hall_condition (hb : H.IsBrace)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    (S : Finset {v // c v = true}) (hS : S.Nonempty)
    (hsize : S.card + 2 ≤ Fintype.card {v // c v = true}) :
    S.card + 2 ≤ (S.biUnion (nbr H c Finset.univ)).card := by
  have hSU : S ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at hsize
    omega
  have hs := hb.matchingCovered.strictHall hc S hS hSU
  by_contra hn
  have hN : (S.biUnion (nbr H c Finset.univ)).card = S.card + 1 := by omega
  let X := bipartiteShore c S (S.biUnion (nbr H c Finset.univ))
  have ht : H.IsTightCut X := by
    intro M hM
    have hh := hM.neighbor_shore_count hc S
    change (M ∩ H.dangling (bipartiteShore c S (S.biUnion (nbr H c Finset.univ)))).card = 1
    omega
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hbS⟩ : ∃ b, b ∉ S := by
    by_contra h
    push Not at h
    exact hSU (Finset.eq_univ_of_forall h)
  have hab : a.1 ≠ b.1 := by
    intro h
    exact hbS ((Subtype.ext h : a = b) ▸ ha)
  obtain ⟨M, hM⟩ := hb.matchingCovered.exists_perfectMatching_of_ne hab
  have hV := hM.card_eq_twice_bipartite_side hc
  have hX : X.card = S.card + (S.biUnion (nbr H c Finset.univ)).card := card_bipartiteShore _ _
  have hXC := Finset.card_sdiff_of_subset (Finset.subset_univ X)
  rw [Finset.card_univ] at hXC
  have hpos := Finset.card_pos.mpr ⟨a, ha⟩
  exact hb.tight_trivial X ht ⟨by omega, by omega⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem bipartite_joins_unique {e : E}
    {a x : {v // c v = true}} {b y : {v // c v = false}}
    (he : H.Joins e a.1 b.1) (hf : H.Joins e x.1 y.1) : a = x ∧ b = y := by
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rcases hf with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact ⟨Subtype.ext (ha.symm.trans hx), Subtype.ext (hb.symm.trans hy)⟩
  · have hh := congrArg c (ha.symm.trans hy)
    simp only [a.2, y.2] at hh
    cases hh
  · have hh := congrArg c (hb.symm.trans hx)
    simp only [b.2, x.2] at hh
    cases hh
  · exact ⟨Subtype.ext (ha.symm.trans hx), Subtype.ext (hb.symm.trans hy)⟩

/-- Removing one edge from a brace with at least three vertices of each colour leaves
the strict Hall inequalities intact. -/
theorem IsBrace.strictHall_erase (hb : H.IsBrace)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    (h3 : 3 ≤ Fintype.card {v // c v = true}) (e : E) :
    HallCore.StrictHall (nbr H c (Finset.univ.erase e)) := by
  obtain ⟨a, b, he⟩ := exists_bipartite_ends hc e
  have havoid (T : Finset {v // c v = true}) (ha : a ∉ T) :
      T.biUnion (nbr H c Finset.univ) ⊆ T.biUnion (nbr H c (Finset.univ.erase e)) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨g, _, hg⟩ := mem_nbr.mp hxy
    have hge : g ≠ e := by
      intro hge
      subst g
      exact ha ((bipartite_joins_unique he hg).1.symm ▸ hx)
    exact Finset.mem_biUnion.mpr ⟨x, hx, mem_nbr.mpr
      ⟨g, Finset.mem_erase.mpr ⟨hge, Finset.mem_univ _⟩, hg⟩⟩
  intro S hS hSU
  have hlt : S.card < Fintype.card {v // c v = true} := by
    have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, hSU⟩)
    simpa only [Finset.card_univ] using hh
  by_cases ha : a ∈ S
  · by_cases hsize : S.card + 2 ≤ Fintype.card {v // c v = true}
    · have htwo := hb.two_hall_condition hc S hS hsize
      have hsub : S.biUnion (nbr H c Finset.univ) ⊆
          insert b (S.biUnion (nbr H c (Finset.univ.erase e))) := by
        intro y hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hy
        obtain ⟨g, _, hg⟩ := mem_nbr.mp hxy
        by_cases hge : g = e
        · subst g
          exact Finset.mem_insert.mpr (Or.inl (bipartite_joins_unique he hg).2.symm)
        · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hx,
            mem_nbr.mpr ⟨g, Finset.mem_erase.mpr ⟨hge, Finset.mem_univ _⟩, hg⟩⟩)
      have hh := Finset.card_le_card hsub
      have hh' := Finset.card_insert_le b (S.biUnion (nbr H c (Finset.univ.erase e)))
      omega
    · have hcT := Finset.card_erase_add_one ha
      have hT : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
      have htwo := hb.two_hall_condition hc (S.erase a) hT (by omega)
      have hsub : (S.erase a).biUnion (nbr H c Finset.univ) ⊆
          S.biUnion (nbr H c (Finset.univ.erase e)) := by
        intro y hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp
          (havoid (S.erase a) (Finset.notMem_erase _ _) hy)
        exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_erase.mp hx).2, hxy⟩
      have hh := Finset.card_le_card hsub
      omega
  · have hs := hb.matchingCovered.strictHall hc S hS hSU
    exact lt_of_lt_of_le hs (Finset.card_le_card (havoid S ha))

omit [DecidableEq V] in
theorem nbr_deleteEdge (e : E) (a : {v // c v = true}) :
    nbr (H.deleteEdge e) c Finset.univ a = nbr H c (Finset.univ.erase e) a := by
  ext b
  simp only [mem_nbr]
  constructor
  · rintro ⟨g, _, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, hj⟩
    exact ⟨⟨g, hg⟩, Finset.mem_univ _, hj⟩

/-- Campos–Lucchesi Lemma 2.12 for braces on at least six vertices. -/
theorem IsBrace.isRemovable_of_six_le_card (hb : H.IsBrace)
    (h6 : 6 ≤ Fintype.card V) (e : E) : H.IsRemovable e := by
  obtain ⟨c, hc⟩ := hb.bipartite
  obtain ⟨M, hM, _⟩ := hb.matchingCovered.2 e
  have hV := hM.card_eq_twice_bipartite_side hc
  have h3 : 3 ≤ Fintype.card {v // c v = true} := by omega
  have hbal : Fintype.card {v // c v = true} = Fintype.card {v // c v = false} := by
    simp only [Fintype.card_subtype]
    exact card_sides_eq hc hM (by decide : 0 < 1)
  have hs := hb.strictHall_erase hc h3 e
  have hstrict : HallCore.StrictHall (nbr (H.deleteEdge e) c Finset.univ) := by
    simpa only [funext (nbr_deleteEdge (H := H) (c := c) e)] using hs
  have hne : Nonempty (Finset.univ.erase e : Finset E) := by
    obtain ⟨a, _, _⟩ := exists_bipartite_ends hc e
    have hproper : ({a} : Finset {v // c v = true}) ≠ Finset.univ := by
      intro heq
      have hh := congrArg Finset.card heq
      simp only [Finset.card_singleton, Finset.card_univ] at hh
      omega
    have hpos := hs {a} (Finset.singleton_nonempty a) hproper
    obtain ⟨b, hbN⟩ := Finset.card_pos.mp (by omega :
      0 < (({a} : Finset {v // c v = true}).biUnion (nbr H c (Finset.univ.erase e))).card)
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hbN
    obtain ⟨g, hg, _⟩ := mem_nbr.mp hx
    exact ⟨⟨g, hg⟩⟩
  exact isMatchingCovered_of_strictHall (H := H.deleteEdge e) (fun g ↦ hc g.1)
    hstrict hbal hne

end GraphPuzzles.LoopMultigraph
