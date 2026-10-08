import GraphPuzzles.Reduction.Removable.DependentBipartite

/-! Campos--Lucchesi Lemma 2.10: mutual-dependence classes in a
three-edge-connected near-brick contain at most two edges. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem MutuallyDependent.refl (e : E) : H.MutuallyDependent e e := fun _ _ ↦ Iff.rfl

omit [DecidableEq E] in
theorem MutuallyDependent.symm {e f : E} (h : H.MutuallyDependent e f) :
    H.MutuallyDependent f e := fun M hM ↦ (h M hM).symm

omit [DecidableEq E] in
theorem MutuallyDependent.trans {e f g : E} (h : H.MutuallyDependent e f)
    (h' : H.MutuallyDependent f g) : H.MutuallyDependent e g :=
  fun M hM ↦ (h M hM).trans (h' M hM)

/-- All edges occurring in exactly the same perfect matchings as `e`. -/
noncomputable def dependenceClass (H : LoopMultigraph V E) (e : E) : Finset E := by
  classical
  exact Finset.univ.filter fun f ↦ H.MutuallyDependent e f

omit [DecidableEq E] in
@[simp] theorem mem_dependenceClass (e f : E) : f ∈ H.dependenceClass e ↔ H.MutuallyDependent e f := by
  classical
  simp [dependenceClass]

/-- Three mutually dependent edges would give two bipartitions whose
exclusive-or separates the ends of an edge after deleting two edges. -/
theorem MutuallyDependent.eq_or_eq_of_threeEdgeConnected {e f g : E}
    (hef : H.MutuallyDependent e f) (heg : H.MutuallyDependent e g) (hne : e ≠ f)
    (hn : H.IsNearBrick) (h3 : H.IsThreeEdgeConnected) : g = e ∨ g = f := by
  by_contra h
  push Not at h
  obtain ⟨hge, hgf⟩ := h
  obtain ⟨c, he0, he1, hf0, hf1, hc⟩ :=
    hef.exists_bipartition_of_connected_deletePair hne hn (h3.connected_deletePair e f)
  obtain ⟨d, he0', he1', _, _, hd⟩ :=
    heg.exists_bipartition_of_connected_deletePair hge.symm hn (h3.connected_deletePair e g)
  have hh (a : ↥(Finset.univ \ {f, g})) :
      Bool.xor (c (H.endAt a.1 0)) (d (H.endAt a.1 0)) =
        Bool.xor (c (H.endAt a.1 1)) (d (H.endAt a.1 1)) := by
    have ha := a.2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at ha
    by_cases hae : a.1 = e
    · simp [hae, he0, he1, he0', he1']
    · exact bool_xor_eq_of_ne (hc a.1 hae ha.1) (hd a.1 hae ha.2)
  have hx := h3.connected_deletePair f g (fun v ↦ Bool.xor (c v) (d v)) hh
    (H.endAt f 0) (H.endAt f 1)
  have hfd := hd f hne.symm hgf.symm
  exact hfd (by simpa only [hf0, hf1, Bool.false_xor] using hx)

/-- Campos--Lucchesi Lemma 2.10, cardinality assertion. -/
theorem IsNearBrick.dependenceClass_card_le_two (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) (e : E) : (H.dependenceClass e).card ≤ 2 := by
  classical
  by_cases hex : ∃ f, f ∈ H.dependenceClass e ∧ f ≠ e
  · obtain ⟨f, hf, hfe⟩ := hex
    have hd := (mem_dependenceClass e f).mp hf
    have hsub : H.dependenceClass e ⊆ {e, f} := by
      intro g hg
      have hg' := hd.eq_or_eq_of_threeEdgeConnected
        ((mem_dependenceClass e g).mp hg) hfe.symm hn h3
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hg'
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hsub : H.dependenceClass e ⊆ {e} := by
      intro f hf
      exact Finset.mem_singleton.mpr (by by_contra hne; exact hex ⟨f, hf, hne⟩)
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega

/-- Campos--Lucchesi Lemma 2.10, equality case: deleting a two-edge
mutual-dependence class leaves a bipartite graph. -/
theorem IsNearBrick.bipartite_delete_dependenceClass (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) {e : E} (he : (H.dependenceClass e).card = 2) :
    (H.restrictEdges (Finset.univ \ H.dependenceClass e)).IsBipartite := by
  classical
  obtain ⟨f, g, hfg, hclass⟩ := Finset.card_eq_two.mp he
  have hf : H.MutuallyDependent e f := (mem_dependenceClass e f).mp (by rw [hclass]; simp)
  have hg : H.MutuallyDependent e g := (mem_dependenceClass e g).mp (by rw [hclass]; simp)
  rw [hclass]
  exact (hf.symm.trans hg).bipartite_deletePair hfg hn h3

end GraphPuzzles.LoopMultigraph
