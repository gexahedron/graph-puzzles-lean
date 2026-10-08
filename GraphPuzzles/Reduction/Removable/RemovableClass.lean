import GraphPuzzles.Reduction.Removable.DependenceClass
import GraphPuzzles.Bricks.BrickEdgeConnectivity

/-! Source classes in the dependence order give removable edges or doubletons. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem EdgeDepends.refl (e : E) : H.EdgeDepends e e := fun _ _ he ↦ he

omit [DecidableEq E] in
theorem EdgeDepends.trans {e f g : E} (h : H.EdgeDepends e f) (h' : H.EdgeDepends f g) :
    H.EdgeDepends e g := fun M hM he ↦ h' M hM (h M hM he)

omit [DecidableEq E] in
/-- Below any prescribed edge in the finite dependence order there is a
source class. Every edge depending on its representative belongs to it. -/
theorem exists_source_dependence_of_edge (H : LoopMultigraph V E) (g : E) :
    ∃ e, H.EdgeDepends e g ∧ ∀ f, H.EdgeDepends f e → H.EdgeDepends e f := by
  classical
  let S : E → Finset E := fun e ↦ Finset.univ.filter fun f ↦ H.EdgeDepends f e
  have hg : g ∈ S g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, EdgeDepends.refl g⟩
  obtain ⟨e, heg, he⟩ := (S g).exists_min_image (fun e ↦ (S e).card) ⟨g, hg⟩
  have hd : H.EdgeDepends e g := (Finset.mem_filter.mp heg).2
  refine ⟨e, hd, fun f hf ↦ ?_⟩
  have hsub : S f ⊆ S e := by
    intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hg).2).trans hf⟩
  have hfS : f ∈ S g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.trans hd⟩
  have hEq : S f = S e := Finset.eq_of_subset_of_card_le hsub (he f hfS)
  have heS : e ∈ S e := Finset.mem_filter.mpr ⟨Finset.mem_univ _, EdgeDepends.refl e⟩
  have hm : e ∈ S f := hEq.symm ▸ heS
  simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hm

omit [DecidableEq E] in
/-- A finite nonempty dependence order has a source equivalence class. -/
theorem exists_source_dependence [Nonempty E] (H : LoopMultigraph V E) :
    ∃ e, ∀ f, H.EdgeDepends f e → H.EdgeDepends e f := by
  obtain ⟨e, _, hs⟩ := exists_source_dependence_of_edge H (Classical.arbitrary E)
  exact ⟨e, hs⟩

/-- Every edge outside a source class has a perfect matching avoiding the
whole class. -/
theorem exists_matching_avoiding_source_class {e : E}
    (hs : ∀ f, H.EdgeDepends f e → H.EdgeDepends e f)
    {g : E} (hg : g ∉ H.dependenceClass e) :
    ∃ M, H.IsPerfectMatching M ∧ g ∈ M ∧ M ⊆ Finset.univ \ H.dependenceClass e := by
  have hnd : ¬ H.EdgeDepends g e := by
    intro h
    exact hg ((mem_dependenceClass e g).mpr (fun M hM ↦ ⟨hs g h M hM, h M hM⟩))
  change ¬ ∀ M, H.IsPerfectMatching M → g ∈ M → e ∈ M at hnd
  push Not at hnd
  obtain ⟨M, hM, hgM, heM⟩ := hnd
  refine ⟨M, hM, hgM, ?_⟩
  intro f hfM
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hf ↦ ?_⟩
  exact heM (((mem_dependenceClass e f).mp hf M hM).mpr hfM)

/-- A connected source-class deletion is matching covered. -/
theorem isMatchingCovered_delete_source_class {e : E}
    (hs : ∀ f, H.EdgeDepends f e → H.EdgeDepends e f)
    (hc : (H.restrictEdges (Finset.univ \ H.dependenceClass e)).IsConnected) :
    (H.restrictEdges (Finset.univ \ H.dependenceClass e)).IsMatchingCovered := by
  apply isMatchingCovered_restrictEdges_of_cover hc
  intro g hg
  obtain ⟨M, hM, hgM, hMS⟩ := exists_matching_avoiding_source_class hs (Finset.mem_sdiff.mp hg).2
  exact ⟨M, hM, hMS, hgM⟩

/-- Deleting one of two distinct mutually dependent edges cannot leave a
matching-covered graph, because the other edge becomes inadmissible. -/
theorem MutuallyDependent.not_removable_left {e f : E} (hd : H.MutuallyDependent e f)
    (hef : e ≠ f) : ¬ H.IsRemovable e := by
  intro hr
  let a : Finset.univ.erase e := ⟨f, by simp [hef.symm]⟩
  obtain ⟨M, hM, haM⟩ := hr.2 a
  have hfM : f ∈ M.image Subtype.val := Finset.mem_image.mpr ⟨a, haM, rfl⟩
  have heM := (hd _ hM.of_restrictEdges).mpr hfM
  obtain ⟨g, _, hge⟩ := Finset.mem_image.mp heM
  exact (Finset.mem_erase.mp g.2).1 hge

/-- A removable edge or doubleton can be chosen with every member depending
on any prescribed edge. -/
theorem IsNearBrick.exists_removable_or_doubleton_dependingOn (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) (g₀ : E) :
    ∃ e, H.EdgeDepends e g₀ ∧
      (H.IsRemovable e ∨ ∃ f, H.EdgeDepends f g₀ ∧ H.IsRemovableDoubleton e f) := by
  classical
  obtain ⟨e, he, hs⟩ := exists_source_dependence_of_edge H g₀
  have hdep {f : E} (hf : f ∈ H.dependenceClass e) : H.EdgeDepends f g₀ :=
    (show H.EdgeDepends f e from fun M hM hfM ↦
      ((mem_dependenceClass e f).mp hf M hM).mpr hfM).trans he
  have heQ : e ∈ H.dependenceClass e := (mem_dependenceClass e e).mpr (MutuallyDependent.refl e)
  have hpos := Finset.card_pos.mpr ⟨e, heQ⟩
  have hle := hn.dependenceClass_card_le_two h3 e
  have hcases : (H.dependenceClass e).card = 1 ∨ (H.dependenceClass e).card = 2 := by omega
  rcases hcases with h1 | h2
  · have hQ : H.dependenceClass e = {e} := by
      obtain ⟨f, hf⟩ := Finset.card_eq_one.mp h1
      have hef : e = f := Finset.mem_singleton.mp (hf ▸ heQ)
      simpa only [hef] using hf
    have hc : (H.restrictEdges (Finset.univ \ H.dependenceClass e)).IsConnected := by
      rw [hQ]
      have hc2 := h3.connected_deletePair e e
      change (H.restrictEdges (Finset.univ \ {e, e})).IsConnected at hc2
      rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self e)] at hc2
      exact hc2
    have hm := isMatchingCovered_delete_source_class hs hc
    rw [hQ] at hm
    refine ⟨e, he, Or.inl ?_⟩
    rw [Finset.sdiff_singleton_eq_erase] at hm
    exact hm
  · obtain ⟨f, g, hfg, hQ⟩ := Finset.card_eq_two.mp h2
    have hc : (H.restrictEdges (Finset.univ \ H.dependenceClass e)).IsConnected := by
      rw [hQ]
      exact h3.connected_deletePair f g
    have hm := isMatchingCovered_delete_source_class hs hc
    rw [hQ] at hm
    have hf : H.MutuallyDependent e f := (mem_dependenceClass e f).mp (by rw [hQ]; simp)
    have hg : H.MutuallyDependent e g := (mem_dependenceClass e g).mp (by rw [hQ]; simp)
    have hd := hf.symm.trans hg
    refine ⟨f, hdep (by rw [hQ]; simp), Or.inr ⟨g, hdep (by rw [hQ]; simp),
      hfg, ?_, hd.not_removable_left hfg, hd.symm.not_removable_left hfg.symm⟩⟩
    change (H.restrictEdges (Finset.univ \ {f, g})).IsMatchingCovered
    exact hm

/-- A three-edge-connected near-brick has a removable edge or a removable
doubleton. The choice is a source class in its finite dependence order. -/
theorem IsNearBrick.exists_removable_or_doubleton (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) :
    ∃ e, H.IsRemovable e ∨ ∃ f, H.IsRemovableDoubleton e f := by
  classical
  have he : Nonempty E := by
    by_contra h
    exact hn.notBipartite ⟨fun _ ↦ false, fun e ↦ (h ⟨e⟩).elim⟩
  obtain ⟨e, _, hr | ⟨f, _, hr⟩⟩ :=
    hn.exists_removable_or_doubleton_dependingOn h3 (Classical.choice he)
  · exact ⟨e, Or.inl hr⟩
  · exact ⟨e, Or.inr ⟨f, hr⟩⟩

theorem IsBrick.exists_removable_or_doubleton (hb : H.IsBrick) :
    ∃ e, H.IsRemovable e ∨ ∃ f, H.IsRemovableDoubleton e f :=
  hb.isNearBrick.exists_removable_or_doubleton hb.isThreeEdgeConnected

/-- A robust-cut contraction of a brick has a removable edge or doubleton. -/
theorem IsRobustCut.exists_removable_or_doubleton_left {X : Finset V}
    (hr : H.IsRobustCut X) (hb : H.IsBrick) :
    ∃ e, (H.contract X).IsRemovable e ∨ ∃ f, (H.contract X).IsRemovableDoubleton e f := by
  have hn := hr.nontrivial hb.matchingCovered
  exact hr.leftNear.exists_removable_or_doubleton (hb.isThreeEdgeConnected.contract X
    (Finset.card_pos.mp (by have hh := hn.2; omega)))

end GraphPuzzles.LoopMultigraph
