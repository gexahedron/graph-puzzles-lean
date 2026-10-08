import GraphPuzzles.Petersen.PetersenMatching
import GraphPuzzles.Cuts.CutWitness

namespace GraphPuzzles.LoopMultigraph

private def petersenSplitShore (A B : Finset (Fin 5)) : Finset (Fin 10) :=
  A.image (Fin.castAdd 5) ∪ B.image (Fin.natAdd 5)

private theorem petersenSplitShore_surjective (X : Finset (Fin 10)) :
    ∃ A B : Finset (Fin 5), X = petersenSplitShore A B := by
  refine ⟨Finset.univ.filter (fun v ↦ v.castAdd 5 ∈ X),
    Finset.univ.filter (fun v ↦ v.natAdd 5 ∈ X), ?_⟩
  ext v
  constructor
  · intro hv
    cases v using Fin.addCases (m := 5) (n := 5) with
    | left i =>
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)
    | right i =>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hw).2
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hw).2

private def petersenFirstHalfShore : Fin 32 → Finset (Fin 5) :=
  ![∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {2, 4}, {0, 2, 4}, {1, 2, 4}, {0, 1, 2, 4}, {3, 4}, {0, 3, 4}, {1, 3, 4}, {0, 1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}]

set_option maxRecDepth 4000 in
private theorem petersenFirstHalfShore_surjective :
    Function.Surjective petersenFirstHalfShore := by
  unfold Function.Surjective
  decide

private def PetersenCutCertificate (X : Finset (Fin 10)) : Prop :=
  (2 ≤ X.card ∧ 2 ≤ (Finset.univ \ X).card) →
    (∀ e : Fin 15, ∃ i : Fin 6, e ∈ petersenMatching i ∧
      (petersenMatching i ∩ petersen.dangling X).card = 1) →
    ∃ i : Fin 6, X = petersenMatchingShore i ∨ X = Finset.univ \ petersenMatchingShore i

-- Each row has its own declaration so kernel reduction does not accumulate
-- the proof state of all 1024 shores in a single declaration.
private theorem finite_cut_row_0 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 0) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_1 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 1) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_2 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 2) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_3 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 3) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_4 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 4) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_5 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 5) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_6 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 6) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_7 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 7) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_8 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 8) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_9 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 9) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_10 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 10) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_11 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 11) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_12 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 12) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_13 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 13) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_14 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 14) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_15 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 15) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_16 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 16) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_17 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 17) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_18 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 18) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_19 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 19) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_20 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 20) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_21 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 21) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_22 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 22) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_23 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 23) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_24 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 24) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_25 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 25) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_26 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 26) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_27 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 27) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_28 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 28) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_29 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 29) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_30 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 30) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_cut_row_31 (B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore (petersenFirstHalfShore 31) B) := by
  unfold PetersenCutCertificate
  fin_cases B <;> decide

private theorem finite_split_cut_certificate (A B : Finset (Fin 5)) :
    PetersenCutCertificate (petersenSplitShore A B) := by
  obtain ⟨i, rfl⟩ := petersenFirstHalfShore_surjective A
  fin_cases i
  · exact finite_cut_row_0 B
  · exact finite_cut_row_1 B
  · exact finite_cut_row_2 B
  · exact finite_cut_row_3 B
  · exact finite_cut_row_4 B
  · exact finite_cut_row_5 B
  · exact finite_cut_row_6 B
  · exact finite_cut_row_7 B
  · exact finite_cut_row_8 B
  · exact finite_cut_row_9 B
  · exact finite_cut_row_10 B
  · exact finite_cut_row_11 B
  · exact finite_cut_row_12 B
  · exact finite_cut_row_13 B
  · exact finite_cut_row_14 B
  · exact finite_cut_row_15 B
  · exact finite_cut_row_16 B
  · exact finite_cut_row_17 B
  · exact finite_cut_row_18 B
  · exact finite_cut_row_19 B
  · exact finite_cut_row_20 B
  · exact finite_cut_row_21 B
  · exact finite_cut_row_22 B
  · exact finite_cut_row_23 B
  · exact finite_cut_row_24 B
  · exact finite_cut_row_25 B
  · exact finite_cut_row_26 B
  · exact finite_cut_row_27 B
  · exact finite_cut_row_28 B
  · exact finite_cut_row_29 B
  · exact finite_cut_row_30 B
  · exact finite_cut_row_31 B

private theorem finite_cut_certificate (X : Finset (Fin 10)) :
    (2 ≤ X.card ∧ 2 ≤ (Finset.univ \ X).card) →
      (∀ e : Fin 15, ∃ i : Fin 6, e ∈ petersenMatching i ∧
        (petersenMatching i ∩ petersen.dangling X).card = 1) →
      ∃ i : Fin 6, X = petersenMatchingShore i ∨
        X = Finset.univ \ petersenMatchingShore i := by
  obtain ⟨A, B, rfl⟩ := petersenSplitShore_surjective X
  exact finite_split_cut_certificate A B

/-- A nontrivial separating cut is one of the twelve displayed pentagonal shores. -/
theorem IsSeparatingCut.eq_petersenMatchingShore {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ i : Fin 6, X = petersenMatchingShore i ∨ X = Finset.univ \ petersenMatchingShore i := by
  apply finite_cut_certificate X hX
  intro e
  obtain ⟨M, hM, he, hcross⟩ := hs.exists_perfectMatching_through e
  obtain ⟨i, rfl⟩ := hM.eq_petersenMatching
  exact ⟨i, he, hcross⟩

theorem IsSeparatingCut.petersen_shore_card {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) : X.card = 5 := by
  obtain ⟨i, rfl | rfl⟩ := hs.eq_petersenMatchingShore hX
  · exact petersenMatchingShore_card i
  · fin_cases i <;> decide

theorem IsStrictlySeparatingCut.petersen_shore_card {X : Finset (Fin 10)}
    (hs : petersen.IsStrictlySeparatingCut X) : X.card = 5 :=
  hs.separating.petersen_shore_card (hs.nontrivial petersen_isMatchingCovered)

theorem IsSeparatingCut.petersen_dangling_isPerfectMatching {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    petersen.IsPerfectMatching (petersen.dangling X) := by
  obtain ⟨i, rfl | rfl⟩ := hs.eq_petersenMatchingShore hX
  · rw [petersenMatchingShore_dangling]
    exact petersenMatching_isPerfectMatching i
  · rw [dangling_compl, petersenMatchingShore_dangling]
    exact petersenMatching_isPerfectMatching i

theorem IsStrictlySeparatingCut.petersen_dangling_isPerfectMatching {X : Finset (Fin 10)}
    (hs : petersen.IsStrictlySeparatingCut X) :
    petersen.IsPerfectMatching (petersen.dangling X) :=
  hs.separating.petersen_dangling_isPerfectMatching (hs.nontrivial petersen_isMatchingCovered)

theorem petersen_separatingCut_cutCharacteristic {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    petersen.cutCharacteristic X = 5 := by
  obtain ⟨i, h | h⟩ := hs.eq_petersenMatchingShore hX
  · subst X
    exact petersenMatchingShore_cutCharacteristic i
  · subst X
    rw [cutCharacteristic_compl]
    exact petersenMatchingShore_cutCharacteristic i

theorem petersen_notBipartite : ¬ petersen.IsBipartite := by
  rintro ⟨c, hc⟩
  have h0 : c 0 ≠ c 1 := hc 0
  have h1 : c 1 ≠ c 2 := hc 1
  have h2 : c 2 ≠ c 3 := hc 2
  have h3 : c 3 ≠ c 4 := hc 3
  have h4 : c 4 ≠ c 0 := hc 4
  cases hc0 : c 0 <;> cases hc1 : c 1 <;> cases hc2 : c 2 <;>
    cases hc3 : c 3 <;> cases hc4 : c 4 <;> simp_all

theorem petersen_isBrick : petersen.IsBrick := by
  refine ⟨petersen_notBipartite, petersen_isMatchingCovered, ?_⟩
  intro X ht hX
  have hs := ht.isSeparatingCut petersen_isMatchingCovered
    (Finset.card_pos.mp (by have h := hX.1; omega))
    (Finset.card_pos.mp (by have h := hX.2; omega))
  have ho := hs.odd_shore petersen_isConnected hX
  have htop := (cutCharacteristic_eq_top_iff_tight ho).mpr ht
  have hfive := petersen_separatingCut_cutCharacteristic hs hX
  rw [hfive] at htop
  exact (by decide : (5 : WithTop ℕ) ≠ ⊤) htop

theorem petersenMatchingShore_isStrictlySeparatingCut (i : Fin 6) :
    petersen.IsStrictlySeparatingCut (petersenMatchingShore i) := by
  have hs := petersenMatchingShore_isSeparatingCut i
  have hn := petersen_isBrick.nonbipartite_contractions hs (petersenMatchingShore_nontrivial i)
  exact ⟨hs, hn.1, hn.2⟩

end GraphPuzzles.LoopMultigraph
