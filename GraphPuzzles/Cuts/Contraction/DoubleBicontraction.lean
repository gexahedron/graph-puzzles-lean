import GraphPuzzles.Cuts.Contraction.EndpointIsoContraction
import GraphPuzzles.Cuts.Contraction.ContractionCommute
import GraphPuzzles.Cuts.Contraction.BipartiteExpansion
import GraphPuzzles.Cuts.CutDegreeBound
import GraphPuzzles.Matching.Bipartite.VertexMatchingBipartite

/-! Contracting two disjoint bipartite tight shores and reconstructing a near-brick. -/

namespace GraphPuzzles.LoopMultigraph


variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The second retained shore when the two collapsed sets are disjoint. -/
noncomputable def doubleRetained (A B : Finset V) :=
  poleShore (Finset.univ \ A) (Finset.univ \ B)

/-- Collapse `A`, then collapse the surviving copy of `B`. -/
noncomputable def doubleContract (H : LoopMultigraph V E) (A B : Finset V) :=
  (H.contract (Finset.univ \ A)).contract (doubleRetained A B)

/-- A cut separating the two collapsed sets, represented in the final graph. -/
noncomputable def doubleShore (A B X : Finset V) :=
  contractShore (doubleRetained A B) (poleShore (Finset.univ \ A) X)

theorem poleShore_subset_doubleRetained {A B X : Finset V}
    (hB : B ⊆ Finset.univ \ X) :
    poleShore (Finset.univ \ A) X ⊆ doubleRetained A B := by
  intro v hv
  cases v with
  | none => exact none_mem_poleShore _ _
  | some v =>
    simp only [doubleRetained, some_mem_poleShore, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at *
    exact fun hb ↦ (Finset.mem_sdiff.mp (hB hb)).2 hv

/-- The left contraction of the double contraction is the bicontracted left side. -/
noncomputable def doubleContractLeftIso {A B X : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ Finset.univ \ X) :
    EndpointIso ((H.doubleContract A B).contract (doubleShore A B X))
      ((H.contract X).contract (poleShore X (Finset.univ \ A))) :=
  (contractNestedIso (H := H.contract (Finset.univ \ A))
    (poleShore_subset_doubleRetained hB)).trans
    (contractCommuteIso (H := H) (by
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
      exact (em (v ∈ A)).elim (fun h ↦ Or.inr (hA h)) Or.inl))

omit [DecidableEq E] in
private theorem map_nested_poleShore {S Z T : Finset V} (hs : Z ⊆ S) :
    (contractNestedIso (H := H) hs).mapVertices
        (poleShore (contractShore S Z) (poleShore S T)) = poleShore Z T := by
  ext v
  obtain ⟨v, rfl⟩ := (contractNestedIso (H := H) hs).vertexEquiv.surjective v
  rw [EndpointIso.mem_mapVertices]
  cases v with
  | none => simp [contractNestedIso]
  | some v =>
    obtain ⟨v, hv⟩ := v
    cases v with
    | none => exact ((none_not_mem_contractShore S Z) hv).elim
    | some v => simp [contractNestedIso, contractShoreEquiv]

/-- The right contraction of the double contraction is the bicontracted right side. -/
noncomputable def doubleContractRightIso {A B X : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ Finset.univ \ X) :
    EndpointIso ((H.doubleContract A B).contract (Finset.univ \ doubleShore A B X))
      ((H.contract (Finset.univ \ X)).contract
        (poleShore (Finset.univ \ X) (Finset.univ \ B))) := by
  have hz : Finset.univ \ X ⊆ Finset.univ \ A := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ha ↦ (Finset.mem_sdiff.mp hv).2 (hA ha)⟩
  have hu : doubleRetained A B ∪
      contractShore (Finset.univ \ A) (Finset.univ \ X) = Finset.univ := by
    ext v
    cases v with
    | none => simp [doubleRetained]
    | some v =>
      simp only [Finset.mem_union, doubleRetained, some_mem_poleShore,
        some_mem_contractShore, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
      exact (em (v.1 ∈ B)).elim
        (fun hb ↦ Or.inr (Finset.mem_sdiff.mp (hB hb)).2) Or.inl
  unfold doubleContract doubleShore
  rw [compl_contractShore, compl_poleShore]
  let f := contractNestedIso (H := H) hz
  have hf := f.contract (poleShore (contractShore (Finset.univ \ A) (Finset.univ \ X))
    (doubleRetained A B))
  rw [show f.mapVertices (poleShore (contractShore (Finset.univ \ A) (Finset.univ \ X))
      (doubleRetained A B)) = poleShore (Finset.univ \ X) (Finset.univ \ B) from
    map_nested_poleShore hz] at hf
  exact (contractCommuteIso (H := H.contract (Finset.univ \ A)) hu).trans hf

/-- Two disjoint bipartite tight-cut expansions preserve near-brickness. -/
theorem IsNearBrick.of_doubleContract (hm : H.IsMatchingCovered)
    {A B : Finset V} (hd : Disjoint A B)
    (htA : H.IsTightCut A) (hnA : IsNontrivialCut A)
    (htB : H.IsTightCut B)
    (hnB : IsNontrivialCut (contractShore (Finset.univ \ A) B))
    (hbA : (H.contract A).IsBipartite) (hbB : (H.contract B).IsBipartite)
    (hn : (H.doubleContract A B).IsNearBrick) : H.IsNearBrick := by
  have hBA : B ⊆ Finset.univ \ A := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ha ↦ Finset.disjoint_left.mp hd ha hv⟩
  have hsA := htA.isSeparatingCut hm
    (Finset.card_pos.mp (by have := hnA.1; omega))
    (Finset.card_pos.mp (by have := hnA.2; omega))
  have hsource : sourceShore (Finset.univ \ A) (contractShore (Finset.univ \ A) B) = B := by
    rw [sourceShore_contractShore, Finset.inter_eq_right.mpr hBA]
  have htB' : (H.contract (Finset.univ \ A)).IsTightCut
      (contractShore (Finset.univ \ A) B) := by
    apply IsTightCut.descend_contract (hsource.symm ▸ htB) (none_not_mem_contractShore _ _)
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ A)]
    exact hsA.1
  apply IsNearBrick.of_tight_contractions hm htA hnA hbA
  apply IsNearBrick.of_tight_contractions hsA.2 htB' hnB
    ((contractNestedIso hBA).symm.isBipartite hbB)
  rw [compl_contractShore]
  exact hn

theorem contractMatching_card_of_subset_meets {S : Finset V} {F : Finset E}
    (hF : F ⊆ H.meets S) : (H.contractMatching S F).card = F.card := by
  apply Finset.card_bij (fun e _ ↦ e.1)
  · intro e he
    exact (mem_contractMatching S F e).mp he
  · intro e _ g _ he
    exact Subtype.ext he
  · intro e he
    exact ⟨⟨e, hF he⟩, (mem_contractMatching S F _).mpr he, rfl⟩

/-- Restrict a boundary edge set through both contractions. -/
noncomputable def doubleLabels (H : LoopMultigraph V E) (A B : Finset V) (F : Finset E) :=
  (H.contract (Finset.univ \ A)).contractMatching (doubleRetained A B)
    (H.contractMatching (Finset.univ \ A) F)

omit [DecidableEq E] in
private theorem boundary_meets_complement {A X : Finset V} (hA : A ⊆ X)
    {e : E} (he : e ∈ H.dangling X) : e ∈ H.meets (Finset.univ \ A) := by
  have hx := mem_dangling.mp he
  by_cases h0 : H.endAt e 0 ∈ X
  · exact mem_meets.mpr ⟨1, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro ha
      exact hx (by simp [h0, hA ha])⟩
  · exact mem_meets.mpr ⟨0, by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun ha ↦ h0 (hA ha)⟩

theorem doubleLabels_card {A B X : Finset V} (hA : A ⊆ X)
    (hB : B ⊆ Finset.univ \ X) {F : Finset E} (hF : F ⊆ H.dangling X) :
    (H.doubleLabels A B F).card = F.card := by
  have hu : (Finset.univ \ A) ∪ (Finset.univ \ B) = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases ha : v ∈ A
    · exact Or.inr (fun hb ↦ (Finset.mem_sdiff.mp (hB hb)).2 (hA ha))
    · exact Or.inl ha
  unfold doubleLabels
  rw [contractMatching_card_of_subset_meets, contractMatching_card_of_subset_meets]
  · exact fun e he ↦ boundary_meets_complement hA (hF he)
  · intro e he
    apply (contract_mem_meets_poleShore hu e).mpr
    apply boundary_meets_complement hB
    simpa only [dangling_compl] using hF ((mem_contractMatching _ _ e).mp he)

theorem doubleLabels_subset_dangling {A B X : Finset V} (hA : A ⊆ X)
    (hB : B ⊆ Finset.univ \ X) {F : Finset E} (hF : F ⊆ H.dangling X) :
    H.doubleLabels A B F ⊆ (H.doubleContract A B).dangling (doubleShore A B X) := by
  have hu : (Finset.univ \ A) ∪ X = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    exact (em (v ∈ A)).elim (fun h ↦ Or.inr (hA h)) Or.inl
  intro e he
  have heF : e.1.1 ∈ F := (mem_contractMatching _ _ _).mp ((mem_contractMatching _ _ _).mp he)
  have heX := mem_dangling.mp (hF heF)
  have hend (k : Fin 2) :
      (H.doubleContract A B).endAt e k ∈ doubleShore A B X ↔ H.endAt e.1.1 k ∈ X := by
    rw [doubleContract, doubleShore, contract_end_mem_contractShore]
    rw [← contract_end_mem_poleShore hu e.1 k]
    exact and_iff_right_of_imp (fun hv ↦ poleShore_subset_doubleRetained (A := A) hB hv)
  simpa only [mem_dangling, hend] using heX

theorem doubleLabels_degree_le_two {A B X : Finset V} (hA : A ⊆ X)
    (hB : B ⊆ Finset.univ \ X) {F : Finset E}
    (hd : ∀ v, H.degreeIn F v ≤ 2)
    (hFA : (F ∩ H.dangling A).card ≤ 2) (hFB : (F ∩ H.dangling B).card ≤ 2) :
    ∀ v, (H.doubleContract A B).degreeIn (H.doubleLabels A B F) v ≤ 2 := by
  have hBA : B ⊆ Finset.univ \ A := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ha ↦ (Finset.mem_sdiff.mp (hB hv)).2 (hA ha)⟩
  intro v
  cases v with
  | none =>
    change ((H.contract (Finset.univ \ A)).contract (doubleRetained A B)).degreeIn
      ((H.contract (Finset.univ \ A)).contractMatching (doubleRetained A B)
        (H.contractMatching (Finset.univ \ A) F)) none ≤ 2
    rw [contractMatching_degreeIn_none]
    have he : doubleRetained A B = Finset.univ \ contractShore (Finset.univ \ A) B :=
      (compl_contractShore _ _).symm
    rw [he, dangling_compl, contractMatching_crossing _ _ (none_not_mem_contractShore _ _),
      sourceShore_contractShore, Finset.inter_eq_right.mpr hBA]
    exact hFB
  | some v =>
    change ((H.contract (Finset.univ \ A)).contract (doubleRetained A B)).degreeIn
      ((H.contract (Finset.univ \ A)).contractMatching (doubleRetained A B)
        (H.contractMatching (Finset.univ \ A) F)) (some v) ≤ 2
    rw [contractMatching, contract_degreeIn_some]
    cases hv : v.1 with
    | none => rw [contractMatching_degreeIn_none, dangling_compl]; exact hFA
    | some w => rw [contractMatching, contract_degreeIn_some]; exact hd w.1

/-- Two brick shore contractions and five surviving boundary labels yield a brick
after contracting the two disjoint expansion shores. -/
theorem doubleContract_isBrick {A B X : Finset V} (hA : A ⊆ X)
    (hB : B ⊆ Finset.univ \ X)
    (hl : ((H.contract X).contract (poleShore X (Finset.univ \ A))).IsBrick)
    (hr : ((H.contract (Finset.univ \ X)).contract
      (poleShore (Finset.univ \ X) (Finset.univ \ B))).IsBrick)
    {F : Finset E} (hF : F ⊆ H.dangling X) (hcard : 5 ≤ F.card)
    (hd : ∀ v, H.degreeIn F v ≤ 2)
    (hFA : (F ∩ H.dangling A).card ≤ 2) (hFB : (F ∩ H.dangling B).card ≤ 2) :
    (H.doubleContract A B).IsBrick := by
  have hl' := (doubleContractLeftIso hA hB).symm.isBrick hl
  have hr' := (doubleContractRightIso hA hB).symm.isBrick hr
  have hs : (H.doubleContract A B).IsSeparatingCut (doubleShore A B X) :=
    ⟨hl'.matchingCovered, hr'.matchingCovered⟩
  have hm := hs.isMatchingCovered (by
    exact ⟨none, by simp [doubleShore]⟩)
  exact hm.isBrick_of_brick_contractions_cut_degree_two hl' hr'
    (doubleLabels_subset_dangling hA hB hF)
    (doubleLabels_degree_le_two hA hB hd hFA hFB)
    (by rw [doubleLabels_card hA hB hF]; exact hcard)

/-- Local bipartite triple expansions on opposite shores reconstruct a near-brick
once their double contraction has the brick splicing boundary bound. -/
theorem IsMatchingCovered.isNearBrick_of_double_bicontraction
    (hm : H.IsMatchingCovered) {A B X : Finset V}
    (hA : A ⊆ X) (hB : B ⊆ Finset.univ \ X)
    (htA : H.IsTightCut A) (hnA : IsNontrivialCut A)
    (htB : H.IsTightCut B)
    (hnB : IsNontrivialCut (contractShore (Finset.univ \ A) B))
    (hbA : (H.contract A).IsBipartite) (hbB : (H.contract B).IsBipartite)
    (hl : ((H.contract X).contract (poleShore X (Finset.univ \ A))).IsBrick)
    (hr : ((H.contract (Finset.univ \ X)).contract
      (poleShore (Finset.univ \ X) (Finset.univ \ B))).IsBrick)
    {F : Finset E} (hF : F ⊆ H.dangling X) (hcard : 5 ≤ F.card)
    (hd : ∀ v, H.degreeIn F v ≤ 2)
    (hFA : (F ∩ H.dangling A).card ≤ 2) (hFB : (F ∩ H.dangling B).card ≤ 2) :
    H.IsNearBrick := by
  apply IsNearBrick.of_doubleContract hm (Finset.disjoint_left.mpr ?_)
    htA hnA htB hnB hbA hbB
    (doubleContract_isBrick hA hB hl hr hF hcard hd hFA hFB).isNearBrick
  intro v hvA hvB
  exact (Finset.mem_sdiff.mp (hB hvB)).2 (hA hvA)

end GraphPuzzles.LoopMultigraph
