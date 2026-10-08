import GraphPuzzles.Cuts.Contraction.ContractionCommute

/-!
# Near-bricks and strictly separating tight cuts

A near-brick is matching covered and every complete tight-cut decomposition has
exactly one brick leaf. The proofs below establish the characterization by absence
of strictly separating tight cuts without assuming general decomposition invariance.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- No nontrivial tight cut has two nonbipartite contractions. -/
def NoStrictTightCut (H : LoopMultigraph V E) : Prop :=
  ∀ X, H.IsTightCut X → IsNontrivialCut X →
    (H.contract X).IsBipartite ∨ (H.contract (Finset.univ \ X)).IsBipartite

/-- A matching-covered graph with precisely one brick in each complete decomposition. -/
structure IsNearBrick (H : LoopMultigraph V E) : Prop where
  matchingCovered : H.IsMatchingCovered
  brickCount_one : ∀ D : TightCutDecomposition H, D.brickCount = 1

theorem IsBrick.isNearBrick (hb : H.IsBrick) : H.IsNearBrick :=
  ⟨hb.matchingCovered, fun D ↦ D.brickCount_of_brick hb⟩

theorem IsNearBrick.notBipartite (hn : H.IsNearBrick) : ¬ H.IsBipartite := by
  intro hb
  obtain ⟨D⟩ := hn.matchingCovered.exists_tightCutDecomposition
  have h0 := D.brickCount_eq_zero_iff.mpr hb
  have h1 := hn.brickCount_one D
  omega

theorem IsNearBrick.noStrictTightCut (hn : H.IsNearBrick) : H.NoStrictTightCut := by
  intro X ht hX
  have hs := ht.isSeparatingCut hn.matchingCovered
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  obtain ⟨L⟩ := hs.1.exists_tightCutDecomposition
  obtain ⟨R⟩ := hs.2.exists_tightCutDecomposition
  have hh := hn.brickCount_one (.split hn.matchingCovered X ht hX L R)
  change L.brickCount + R.brickCount = 1 at hh
  by_cases h0 : L.brickCount = 0
  · exact Or.inl (L.brickCount_eq_zero_iff.mp h0)
  · exact Or.inr (R.brickCount_eq_zero_iff.mp (by omega))

/-- A nontrivial pole-free shore stays nontrivial on lifting through a nontrivial cut. -/
theorem IsNontrivialCut.sourceShore {X : Finset V} (hX : IsNontrivialCut X)
    {Y : Finset (Option X)} (hY : IsNontrivialCut Y) (hn : none ∉ Y) :
    IsNontrivialCut (sourceShore X Y) := by
  refine ⟨by rw [card_sourceShore X Y hn]; exact hY.1, ?_⟩
  apply hX.2.trans (Finset.card_le_card ?_)
  intro v hv
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
    fun hz ↦ (Finset.mem_sdiff.mp hv).2 (sourceShore_subset X Y hz)⟩

/-- The complementary side of a nested cut remains bipartite after the outer contraction. -/
theorem bipartite_complement_of_nested {X Z : Finset V} (hZX : Z ⊆ X)
    (htX : H.IsTightCut X) (hsZ : H.IsSeparatingCut Z)
    (hXC : (Finset.univ \ X).Nonempty)
    (hb : (H.contract (Finset.univ \ Z)).IsBipartite) :
    ((H.contract X).contract (Finset.univ \ contractShore X Z)).IsBipartite := by
  have hsource : sourceShore (Finset.univ \ Z)
      (contractShore (Finset.univ \ Z) (Finset.univ \ X)) = Finset.univ \ X := by
    rw [sourceShore_contractShore]
    apply Finset.inter_eq_right.mpr
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hz ↦ (Finset.mem_sdiff.mp hv).2 (hZX hz)⟩
  have ht : (H.contract (Finset.univ \ Z)).IsTightCut
      (contractShore (Finset.univ \ Z) (Finset.univ \ X)) := by
    apply IsTightCut.descend_contract ?_ (none_not_mem_contractShore _ _) hsZ.compl.2
    rw [hsource]
    exact htX.compl
  have ht' : (H.contract (Finset.univ \ Z)).IsTightCut (poleShore (Finset.univ \ Z) X) := by
    simpa only [compl_contractShore, Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using ht.compl
  have hcomp : (Finset.univ \ poleShore (Finset.univ \ Z) X).Nonempty := by
    obtain ⟨v, hv⟩ := hXC
    have hz : v ∈ Finset.univ \ Z := Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun h ↦ (Finset.mem_sdiff.mp hv).2 (hZX h)⟩
    refine ⟨some ⟨v, hz⟩, ?_⟩
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, some_mem_poleShore] using
      (Finset.mem_sdiff.mp hv).2
  have hb' := hb.contract_of_separating (ht'.isSeparatingCut hsZ.2
    ⟨none, none_mem_poleShore _ _⟩ hcomp)
  have hu : X ∪ (Finset.univ \ Z) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hx : v ∈ X
    · exact Or.inl hx
    · exact Or.inr (fun hz ↦ hx (hZX hz))
  rw [compl_contractShore]
  exact (contractCommuteIso (H := H) hu).symm.isBipartite hb'

/-- Absence of strictly separating tight cuts is inherited by tight-cut contractions. -/
theorem NoStrictTightCut.contract (hN : H.NoStrictTightCut) (hm : H.IsMatchingCovered)
    {X : Finset V} (htX : H.IsTightCut X) (hX : IsNontrivialCut X) :
    (H.contract X).NoStrictTightCut := by
  have key (Y : Finset (Option X)) (htY : (H.contract X).IsTightCut Y)
      (hY : IsNontrivialCut Y) (hn : none ∉ Y) :
      ((H.contract X).contract Y).IsBipartite ∨
        ((H.contract X).contract (Finset.univ \ Y)).IsBipartite := by
    let Z := sourceShore X Y
    have hZX : Z ⊆ X := sourceShore_subset X Y
    have he : contractShore X Z = Y := contractShore_sourceShore X Y hn
    have htZ : H.IsTightCut Z := htX.lift_contract htY hn
    have hZ : IsNontrivialCut Z := hX.sourceShore hY hn
    rcases hN Z htZ hZ with hb | hb
    · have hh := (contractNestedIso (H := H) hZX).symm.isBipartite hb
      exact Or.inl (he ▸ hh)
    · have hsZ := htZ.isSeparatingCut hm
        (Finset.card_pos.mp (by have hh := hZ.1; omega))
        (Finset.card_pos.mp (by have hh := hZ.2; omega))
      have hh := bipartite_complement_of_nested hZX htX hsZ
        (Finset.card_pos.mp (by have hh := hX.2; omega)) hb
      exact Or.inr (he ▸ hh)
  intro Y htY hY
  by_cases hn : none ∈ Y
  · have hh := key (Finset.univ \ Y) htY.compl hY.compl (by simp [hn])
    rcases hh with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y) ▸ h)
  · exact key Y htY hY hn

/-- With no strictly separating tight cuts, every nonbipartite decomposition has one brick. -/
theorem TightCutDecomposition.brickCount_one_of_noStrictTightCut (D : TightCutDecomposition H)
    (hN : H.NoStrictTightCut) (hb : ¬ H.IsBipartite) : D.brickCount = 1 := by
  revert hN hb
  induction D with
  | leaf hm ht =>
    intro hN hb
    classical
    simp only [TightCutDecomposition.brickCount, if_neg hb]
  | split hm X ht hX L R ihL ihR =>
    intro hN hb
    have hNL := hN.contract hm ht hX
    have hNR := hN.contract hm ht.compl hX.compl
    rcases hN X ht hX with hbL | hbR
    · have hnR := fun h ↦ hb (hbL.of_contracts h)
      rw [TightCutDecomposition.brickCount, L.brickCount_eq_zero_iff.mpr hbL, ihR hNR hnR,
        zero_add]
    · have hnL := fun h ↦ hb (IsBipartite.of_contracts h hbR)
      rw [TightCutDecomposition.brickCount, R.brickCount_eq_zero_iff.mpr hbR, ihL hNL hnL,
        add_zero]

/-- Campos--Lucchesi Lemma 2.5, with matching-coveredness and nonbipartiteness explicit. -/
theorem isNearBrick_iff :
    H.IsNearBrick ↔ H.IsMatchingCovered ∧ ¬ H.IsBipartite ∧ H.NoStrictTightCut := by
  constructor
  · exact fun h ↦ ⟨h.matchingCovered, h.notBipartite, h.noStrictTightCut⟩
  · rintro ⟨hm, hb, hN⟩
    exact ⟨hm, fun D ↦ D.brickCount_one_of_noStrictTightCut hN hb⟩

/-- Each nontrivial tight cut of a near-brick has one bipartite contraction and one near-brick. -/
theorem IsNearBrick.tight_contractions (hb : H.IsNearBrick) {X : Finset V}
    (ht : H.IsTightCut X) (hX : IsNontrivialCut X) :
    ((H.contract X).IsBipartite ∧ (H.contract (Finset.univ \ X)).IsNearBrick) ∨
      ((H.contract X).IsNearBrick ∧ (H.contract (Finset.univ \ X)).IsBipartite) := by
  have hs := ht.isSeparatingCut hb.matchingCovered
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  rcases hb.noStrictTightCut X ht hX with hbL | hbR
  · refine Or.inl ⟨hbL, isNearBrick_iff.mpr ⟨hs.2, ?_, ?_⟩⟩
    · exact fun h ↦ hb.notBipartite (hbL.of_contracts h)
    · exact hb.noStrictTightCut.contract hb.matchingCovered ht.compl hX.compl
  · refine Or.inr ⟨isNearBrick_iff.mpr ⟨hs.1, ?_, ?_⟩, hbR⟩
    · exact fun h ↦ hb.notBipartite (h.of_contracts hbR)
    · exact hb.noStrictTightCut.contract hb.matchingCovered ht hX

section Relabelling

variable {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
variable {K : LoopMultigraph W F}

/-- Near-brickness is invariant under an endpoint graph isomorphism. -/
theorem EndpointIso.isNearBrick (f : EndpointIso H K) (hb : H.IsNearBrick) : K.IsNearBrick := by
  have hm := f.isMatchingCovered hb.matchingCovered
  refine isNearBrick_iff.mpr ⟨hm, fun h ↦ hb.notBipartite (f.symm.isBipartite h), ?_⟩
  intro Y htY hY
  have hsY := htY.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  rcases hb.noStrictTightCut (f.symm.mapVertices Y) (f.symm.isTightCut htY)
      ((f.symm.nontrivial_mapVertices Y).mpr hY) with h | h
  · have hh : K.IsBipartiteOn Y := by
      simpa only [EndpointIso.mapVertices_symm_mapVertices] using
        f.isBipartiteOn h.induced_of_contract
    exact Or.inl (hh.contract_of_separating hsY)
  · have hh : K.IsBipartiteOn (Finset.univ \ Y) := by
      simpa only [EndpointIso.mapVertices_compl, EndpointIso.mapVertices_symm_mapVertices] using
        f.isBipartiteOn h.induced_of_contract
    exact Or.inr (hh.contract_of_separating hsY.compl)

end Relabelling

end GraphPuzzles.LoopMultigraph
