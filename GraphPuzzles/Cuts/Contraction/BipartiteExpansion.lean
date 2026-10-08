import GraphPuzzles.Bricks.NearBrick
import GraphPuzzles.Cuts.CohesiveUncrossing

/-! Expanding the bipartite side of a tight cut preserves the near-brick property. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsMatchingCovered.loopless (hm : H.IsMatchingCovered) (e : E) :
    H.endAt e 0 ≠ H.endAt e 1 := by
  intro he
  obtain ⟨M, hM, heM⟩ := hm.2 e
  have hh := H.two_le_degreeIn_of_ne (M := M)
    ⟨(e, 0), rfl⟩ ⟨(e, 1), he.symm⟩ (by
      intro h
      have hh := congrArg (fun x : H.halfEdgesAt (H.endAt e 0) ↦ x.1.2) h
      norm_num at hh) heM heM
  rw [hM] at hh
  omega

omit [DecidableEq E] in
theorem bipartite_contract_of_card_le_one (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    {X : Finset V} (hX : X.card ≤ 1) : (H.contract X).IsBipartite := by
  refine ⟨Option.isSome, ?_⟩
  intro e
  by_cases h0 : H.endAt e.1 0 ∈ X <;> by_cases h1 : H.endAt e.1 1 ∈ X
  · exact (hl e.1 (Finset.card_le_one.mp hX _ h0 _ h1)).elim
  · simp [contract_endAt, h0, h1]
  · simp [contract_endAt, h0, h1]
  · obtain ⟨k, hk⟩ := mem_meets.mp e.2
    fin_cases k <;> contradiction

/-- The near-brick cut criterion also holds for trivial cuts. -/
theorem NoStrictTightCut.all (hN : H.NoStrictTightCut) (hm : H.IsMatchingCovered)
    {X : Finset V} (ht : H.IsTightCut X) :
    (H.contract X).IsBipartite ∨ (H.contract (Finset.univ \ X)).IsBipartite := by
  by_cases hX : 2 ≤ X.card
  · by_cases hXC : 2 ≤ (Finset.univ \ X).card
    · exact hN X ht ⟨hX, hXC⟩
    · exact Or.inr (bipartite_contract_of_card_le_one hm.loopless (by omega))
  · exact Or.inl (bipartite_contract_of_card_le_one hm.loopless (by omega))

omit [DecidableEq V] [DecidableEq E] in
theorem IsBipartiteOn.mono {X Y : Finset V} (hb : H.IsBipartiteOn X) (hYX : Y ⊆ X) :
    H.IsBipartiteOn Y := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun e h0 h1 ↦ hc e (hYX h0) (hYX h1)⟩

omit [DecidableEq E] in
/-- Bipartitions of contractions on disjoint shores can be phased consistently on their union. -/
theorem IsBipartiteOn.union_of_disjoint_contracts {X Z : Finset V} (hXZ : Disjoint X Z)
    (hX : (H.contract X).IsBipartite) (hZ : (H.contract Z).IsBipartite) :
    H.IsBipartiteOn (X ∪ Z) := by
  obtain ⟨c, hc⟩ := hX
  obtain ⟨d, hd⟩ := hZ
  let f : Bool → Bool := fun b ↦ if b = d none then !c none else c none
  have hinj (a b : Bool) (hne : a ≠ b) : f a ≠ f b := by
    cases a <;> cases b <;> cases hcn : c none <;> cases hdn : d none <;> simp_all [f]
  let g : V → Bool := fun v ↦ if h : v ∈ X then c (some ⟨v, h⟩)
    else f (d (contractVertex Z v))
  refine ⟨g, ?_⟩
  intro e he0 he1
  by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X
  · have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    simpa only [contract_endAt, dif_pos h0, dif_pos h1, g] using hh
  · have h0' : H.endAt e 0 ∉ Z := fun h ↦ Finset.disjoint_left.mp hXZ h0 h
    have h1' : H.endAt e 1 ∈ Z := (Finset.mem_union.mp he1).resolve_left h1
    have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    have hh' := hd ⟨e, mem_meets.mpr ⟨1, h1'⟩⟩
    simp only [contract_endAt, dif_pos h0, dif_neg h1] at hh
    simp only [contract_endAt, dif_neg h0', dif_pos h1'] at hh'
    simpa only [g, dif_pos h0, dif_neg h1, contractVertex, dif_pos h1', f,
      if_neg (Ne.symm hh')] using hh
  · have h0' : H.endAt e 0 ∈ Z := (Finset.mem_union.mp he0).resolve_left h0
    have h1' : H.endAt e 1 ∉ Z := fun h ↦ Finset.disjoint_left.mp hXZ h1 h
    have hh := hc ⟨e, mem_meets.mpr ⟨1, h1⟩⟩
    have hh' := hd ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩
    simp only [contract_endAt, dif_neg h0, dif_pos h1] at hh
    simp only [contract_endAt, dif_pos h0', dif_neg h1'] at hh'
    simpa only [g, dif_neg h0, dif_pos h1, contractVertex, dif_pos h0', f,
      if_neg hh'] using hh
  · have h0' : H.endAt e 0 ∈ Z := (Finset.mem_union.mp he0).resolve_left h0
    have h1' : H.endAt e 1 ∈ Z := (Finset.mem_union.mp he1).resolve_left h1
    have hh := hd ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩
    simp only [contract_endAt, dif_pos h0', dif_pos h1'] at hh
    simpa only [g, dif_neg h0, dif_neg h1, contractVertex, dif_pos h0', dif_pos h1'] using
      hinj _ _ hh

private theorem bipartite_side_of_odd_inter (hm : H.IsMatchingCovered)
    {X Y : Finset V} (htX : H.IsTightCut X) (hX : IsNontrivialCut X)
    (hbX : (H.contract X).IsBipartite)
    (hN : (H.contract (Finset.univ \ X)).NoStrictTightCut)
    (htY : H.IsTightCut Y) (hY : IsNontrivialCut Y) (hI : Odd (X ∩ Y).card) :
    (H.contract Y).IsBipartite ∨ (H.contract (Finset.univ \ Y)).IsBipartite := by
  let R := Finset.univ \ X
  let U := X ∪ Y
  let D := Finset.univ \ U
  have hDR : D ⊆ R := by
    intro v hv
    simp only [D, R, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
    tauto
  have hsX := htX.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  have hsY := htY.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  have htD : H.IsTightCut D := (htX.uncross htY hI).2.compl
  have htS : (H.contract R).IsTightCut (contractShore R D) := by
    apply IsTightCut.descend_contract ?_ (none_not_mem_contractShore _ _) hsX.compl.2
    rwa [sourceShore_contractShore, Finset.inter_eq_right.mpr hDR]
  rcases hN.all hsX.2 htS with hbD | hbU
  · have hbD' := (contractNestedIso (H := H) hDR).isBipartite hbD
    have hXD : Disjoint X D := by
      apply Finset.disjoint_left.mpr
      intro v hx hd
      exact (Finset.mem_sdiff.mp hd).2 (Finset.mem_union_left Y hx)
    have hsub : Finset.univ \ Y ⊆ X ∪ D := by
      intro v hv
      simp only [D, U, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
      tauto
    have hb := (IsBipartiteOn.union_of_disjoint_contracts hXD hbX hbD').mono hsub
    exact Or.inr (hb.contract_of_separating hsY.compl)
  · have hu : R ∪ U = Finset.univ := by
      ext v
      simp [R, U]
      tauto
    have he : Finset.univ \ contractShore R D = poleShore R U := by
      rw [compl_contractShore]
      congr 1
      exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ U)
    have hbMiddle : ((H.contract R).contract (poleShore R U)).IsBipartite := he ▸ hbU
    have hbMiddle' := (contractCommuteIso (H := H) hu).isBipartite hbMiddle
    have hbLeft : ((H.contract U).contract (contractShore U X)).IsBipartite :=
      (contractNestedIso (H := H) (show X ⊆ U from Finset.subset_union_left)).symm.isBipartite hbX
    have hbRight : ((H.contract U).contract (Finset.univ \ contractShore U X)).IsBipartite := by
      rw [compl_contractShore]
      exact hbMiddle'
    have hbU' : (H.contract U).IsBipartite := hbLeft.of_contracts hbRight
    have hb := hbU'.induced_of_contract.mono (show Y ⊆ U from Finset.subset_union_right)
    exact Or.inl (hb.contract_of_separating hsY)

/-- Expanding a bipartite tight-cut side cannot create a strictly separating tight cut. -/
theorem NoStrictTightCut.of_bipartite_contraction (hm : H.IsMatchingCovered)
    {X : Finset V} (htX : H.IsTightCut X) (hX : IsNontrivialCut X)
    (hbX : (H.contract X).IsBipartite)
    (hN : (H.contract (Finset.univ \ X)).NoStrictTightCut) : H.NoStrictTightCut := by
  have hsX := htX.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  have hoX := hsX.odd_shore hm.1 hX
  intro Y htY hY
  by_cases hI : Odd (X ∩ Y).card
  · exact bipartite_side_of_odd_inter hm htX hX hbX hN htY hY hI
  · have ho : Odd (X ∩ (Finset.univ \ Y)).card := by
      have he : X ∩ (Finset.univ \ Y) = X \ Y := by ext v; simp
      rw [he, Nat.odd_iff]
      rw [Nat.odd_iff] at hoX hI
      have hh := Finset.card_sdiff_add_card_inter X Y
      omega
    rcases bipartite_side_of_odd_inter hm htX hX hbX hN htY.compl hY.compl ho with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y) ▸ h)

/-- A bipartite tight-cut contraction and a near-brick contraction assemble to a near-brick. -/
theorem IsNearBrick.of_tight_contractions (hm : H.IsMatchingCovered)
    {X : Finset V} (htX : H.IsTightCut X) (hX : IsNontrivialCut X)
    (hbX : (H.contract X).IsBipartite)
    (hn : (H.contract (Finset.univ \ X)).IsNearBrick) : H.IsNearBrick := by
  have hsX := htX.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  refine isNearBrick_iff.mpr ⟨hm, ?_, ?_⟩
  · exact fun h ↦ hn.notBipartite (h.contract_of_separating hsX.compl)
  · exact NoStrictTightCut.of_bipartite_contraction hm htX hX hbX hn.noStrictTightCut

/-- The symmetric form of assembling a near-brick through a tight cut. -/
theorem IsNearBrick.of_tight_contractions_left (hm : H.IsMatchingCovered)
    {X : Finset V} (htX : H.IsTightCut X) (hX : IsNontrivialCut X)
    (hn : (H.contract X).IsNearBrick)
    (hb : (H.contract (Finset.univ \ X)).IsBipartite) : H.IsNearBrick := by
  apply IsNearBrick.of_tight_contractions hm htX.compl hX.compl hb
  exact (Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)).symm ▸ hn

/-- A single complete decomposition with one brick forces all complete decompositions
to have one brick. This proves decomposition invariance in the near-brick case. -/
theorem TightCutDecomposition.isNearBrick_of_brickCount_eq_one (D : TightCutDecomposition H)
    (hD : D.brickCount = 1) : H.IsNearBrick := by
  induction D with
  | leaf hm ht =>
    apply IsBrick.isNearBrick
    refine ⟨?_, hm, ht⟩
    intro hb
    have hh := (TightCutDecomposition.leaf hm ht).brickCount_eq_zero_iff.mpr hb
    omega
  | split hm X ht hX L R ihL ihR =>
    change L.brickCount + R.brickCount = 1 at hD
    by_cases hL : L.brickCount = 0
    · exact IsNearBrick.of_tight_contractions hm ht hX (L.brickCount_eq_zero_iff.mp hL)
        (ihR (by omega))
    · exact IsNearBrick.of_tight_contractions_left hm ht hX (ihL (by omega))
        (R.brickCount_eq_zero_iff.mp (by omega))

theorem TightCutDecomposition.brickCount_eq_one_iff (D : TightCutDecomposition H) :
    D.brickCount = 1 ↔ H.IsNearBrick :=
  ⟨D.isNearBrick_of_brickCount_eq_one, fun h ↦ h.brickCount_one D⟩

theorem isNearBrick_iff_exists_decomposition :
    H.IsNearBrick ↔ ∃ D : TightCutDecomposition H, D.brickCount = 1 := by
  constructor
  · intro h
    obtain ⟨D⟩ := h.matchingCovered.exists_tightCutDecomposition
    exact ⟨D, h.brickCount_one D⟩
  · rintro ⟨D, hD⟩
    exact D.isNearBrick_of_brickCount_eq_one hD

end GraphPuzzles.LoopMultigraph
