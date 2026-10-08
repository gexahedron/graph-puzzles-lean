import GraphPuzzles.Bricks.Brick
import GraphPuzzles.Cuts.CutCharacteristic

/-!
# The six perfect matchings of the labelled Petersen graph

The first matching consists of all five spokes. Each other matching has a single
spoke, two edges of the outer pentagon, and two edges of the inner pentagram.
The classification uses the ten vertex incidence equations, not a powerset search.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

theorem petersen_isSimple : petersen.IsSimple := by
  constructor
  · decide
  · unfold Joins
    decide

theorem petersen_degree (v : Fin 10) : petersen.degree v = 3 := by
  fin_cases v <;> decide

/-- The complete list of Petersen perfect matchings, in the labels of `petersen`. -/
def petersenMatching : Fin 6 → Finset (Fin 15) :=
  ![{5, 6, 7, 8, 9}, {1, 3, 5, 11, 12}, {2, 4, 6, 12, 13},
    {0, 3, 7, 13, 14}, {1, 4, 8, 10, 14}, {0, 2, 9, 10, 11}]

theorem petersenMatching_isPerfectMatching (i : Fin 6) :
    petersen.IsPerfectMatching (petersenMatching i) := by
  unfold IsPerfectMatching
  fin_cases i <;> decide

theorem petersenMatching_card (i : Fin 6) : (petersenMatching i).card = 5 := by
  fin_cases i <;> decide

theorem petersenMatching_injective : Function.Injective petersenMatching := by
  decide

private theorem degreeIn_indicator_sum (M : Finset (Fin 15)) (v : Fin 10) :
    petersen.degreeIn M v =
      ∑ e : Fin 15, if e ∈ M then
        (∑ k : Fin 2, if petersen.endAt e k = v then 1 else 0) else 0 := by
  simp only [degreeIn, Finset.card_filter, Finset.sum_product]
  simp

/-- The ten degree equations expressed in edge membership indicators. -/
theorem petersen_degreeIn (M : Finset (Fin 15)) (v : Fin 10) :
    let b : Fin 15 → ℕ := fun e ↦ if e ∈ M then 1 else 0
    petersen.degreeIn M v =
      ![b 0 + b 4 + b 5, b 0 + b 1 + b 6, b 1 + b 2 + b 7,
        b 2 + b 3 + b 8, b 3 + b 4 + b 9, b 5 + b 10 + b 13,
        b 6 + b 11 + b 14, b 7 + b 10 + b 12, b 8 + b 11 + b 13,
        b 9 + b 12 + b 14] v := by
  rw [degreeIn_indicator_sum]
  simp only [Fin.sum_univ_succ]
  fin_cases v <;> simp [petersen, Nat.add_assoc]

private theorem eq_of_mem_indicators {M N : Finset (Fin 15)}
    (h : ∀ e, (if e ∈ M then 1 else 0 : ℕ) = if e ∈ N then 1 else 0) : M = N := by
  ext e
  have he := h e
  by_cases hm : e ∈ M <;> by_cases hn : e ∈ N <;> simp_all

set_option maxHeartbeats 400000 in
/-- Every perfect matching of the Petersen graph is one of the six displayed matchings. -/
theorem IsPerfectMatching.eq_petersenMatching {M : Finset (Fin 15)}
    (hM : petersen.IsPerfectMatching M) : ∃ i, M = petersenMatching i := by
  let b : ℕ → ℕ := fun e ↦ if h : e < 15 then
    if (⟨e, h⟩ : Fin 15) ∈ M then 1 else 0 else 0
  have hbval (e : Fin 15) : b e.val = (if e ∈ M then 1 else 0 : ℕ) := by
    simp [b, e.isLt]
  have hv (v : Fin 10) := (petersen_degreeIn M v).symm.trans (hM v)
  have h0 : b 0 + b 4 + b 5 = 1 := hv 0
  have h1 : b 0 + b 1 + b 6 = 1 := hv 1
  have h2 : b 1 + b 2 + b 7 = 1 := hv 2
  have h3 : b 2 + b 3 + b 8 = 1 := hv 3
  have h4 : b 3 + b 4 + b 9 = 1 := hv 4
  have h5 : b 5 + b 10 + b 13 = 1 := hv 5
  have h6 : b 6 + b 11 + b 14 = 1 := hv 6
  have h7 : b 7 + b 10 + b 12 = 1 := hv 7
  have h8 : b 8 + b 11 + b 13 = 1 := hv 8
  have h9 : b 9 + b 12 + b 14 = 1 := hv 9
  generalize hb : b = c at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hc :
      (c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 0) ∨
      (c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 0 ∧ c 3 = 1 ∧ c 4 = 0) ∨
      (c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 1 ∧ c 3 = 0 ∧ c 4 = 1) ∨
      (c 0 = 1 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 1 ∧ c 4 = 0) ∨
      (c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 1) ∨
      (c 0 = 1 ∧ c 1 = 0 ∧ c 2 = 1 ∧ c 3 = 0 ∧ c 4 = 0) := by
    clear hb hbval hv b hM M
    have hc0 : c 0 = 0 ∨ c 0 = 1 := by omega
    have hc1 : c 1 = 0 ∨ c 1 = 1 := by omega
    have hc2 : c 2 = 0 ∨ c 2 = 1 := by omega
    have hc3 : c 3 = 0 ∨ c 3 = 1 := by omega
    have hc4 : c 4 = 0 ∨ c 4 = 1 := by omega
    rcases hc0 with hc0 | hc0 <;> rcases hc1 with hc1 | hc1 <;>
      rcases hc2 with hc2 | hc2 <;> rcases hc3 with hc3 | hc3 <;>
      rcases hc4 with hc4 | hc4 <;> simp_all <;> omega
  rcases hc with hc | hc | hc | hc | hc | hc
  · refine ⟨0, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({5, 6, 7, 8, 9} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega
  · refine ⟨1, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({1, 3, 5, 11, 12} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega
  · refine ⟨2, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({2, 4, 6, 12, 13} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega
  · refine ⟨3, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({0, 3, 7, 13, 14} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega
  · refine ⟨4, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({1, 4, 8, 10, 14} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega
  · refine ⟨5, eq_of_mem_indicators ?_⟩
    intro e
    rw [← hbval e, hb]
    clear hb hbval hv b hM M
    change c e.val = if e ∈ ({0, 2, 9, 10, 11} : Finset (Fin 15)) then 1 else 0
    rcases hc with ⟨hc0, hc1, hc2, hc3, hc4⟩
    simp only [hc0, hc1, hc2, hc3, hc4, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    fin_cases e <;> simp_all [Fin.ext_iff] <;> omega

theorem petersen_isPerfectMatching_iff (M : Finset (Fin 15)) :
    petersen.IsPerfectMatching M ↔ ∃ i, M = petersenMatching i := by
  constructor
  · exact IsPerfectMatching.eq_petersenMatching
  · rintro ⟨i, rfl⟩
    exact petersenMatching_isPerfectMatching i

/-- Distinct Petersen perfect matchings meet in a single labelled edge. -/
theorem petersenMatching_inter_card (i j : Fin 6) (hne : i ≠ j) :
    (petersenMatching i ∩ petersenMatching j).card = 1 := by
  revert i j
  decide

/-- Each Petersen edge belongs to exactly two of the six perfect matchings. -/
theorem petersenMatching_count (e : Fin 15) :
    (Finset.univ.filter fun i : Fin 6 ↦ e ∈ petersenMatching i).card = 2 := by
  fin_cases e <;> decide

/-- The intersection assertion for arbitrary, rather than indexed, perfect matchings. -/
theorem petersen_perfectMatchings_inter_card {M N : Finset (Fin 15)}
    (hM : petersen.IsPerfectMatching M) (hN : petersen.IsPerfectMatching N)
    (hne : M ≠ N) : (M ∩ N).card = 1 := by
  obtain ⟨i, rfl⟩ := hM.eq_petersenMatching
  obtain ⟨j, rfl⟩ := hN.eq_petersenMatching
  exact petersenMatching_inter_card i j (fun h ↦ hne (congrArg petersenMatching h))

/-- One pentagonal shore for each of the six complementary pairs of pentagons. -/
def petersenMatchingShore : Fin 6 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4}, {0, 1, 4, 6, 9}, {0, 1, 2, 5, 7},
    {0, 4, 5, 7, 9}, {0, 1, 5, 6, 8}, {0, 3, 4, 5, 8}]

theorem petersenMatchingShore_card (i : Fin 6) : (petersenMatchingShore i).card = 5 := by
  fin_cases i <;> decide

/-- The cut of each listed pentagonal shore is its corresponding perfect matching. -/
theorem petersenMatchingShore_dangling (i : Fin 6) :
    petersen.dangling (petersenMatchingShore i) = petersenMatching i := by
  fin_cases i <;> decide

/-- Every perfect matching crosses a listed Petersen cut either once or five times. -/
theorem petersen_matching_crossing_one_or_five {M : Finset (Fin 15)}
    (hM : petersen.IsPerfectMatching M) (i : Fin 6) :
    (M ∩ petersen.dangling (petersenMatchingShore i)).card = 1 ∨
      (M ∩ petersen.dangling (petersenMatchingShore i)).card = 5 := by
  obtain ⟨j, rfl⟩ := hM.eq_petersenMatching
  rw [petersenMatchingShore_dangling]
  by_cases hji : j = i
  · subst j
    right
    simpa using petersenMatching_card i
  · exact Or.inl (petersenMatching_inter_card j i hji)

theorem petersen_matching_crossing_ne_three {M : Finset (Fin 15)}
    (hM : petersen.IsPerfectMatching M) (i : Fin 6) :
    (M ∩ petersen.dangling (petersenMatchingShore i)).card ≠ 3 := by
  rcases petersen_matching_crossing_one_or_five hM i with h | h <;> omega

/-- Connectivity follows already from the outer circuit and the five spokes. -/
theorem petersen_isConnected : petersen.IsConnected := by
  intro c hc u v
  have h0 : c 0 = c 1 := hc 0
  have h1 : c 1 = c 2 := hc 1
  have h2 : c 2 = c 3 := hc 2
  have h3 : c 3 = c 4 := hc 3
  have h5 : c 0 = c 5 := hc 5
  have h6 : c 1 = c 6 := hc 6
  have h7 : c 2 = c 7 := hc 7
  have h8 : c 3 = c 8 := hc 8
  have h9 : c 4 = c 9 := hc 9
  have h (w : Fin 10) : c w = c 0 := by
    fin_cases w
    · rfl
    · exact h0.symm
    · exact h1.symm.trans h0.symm
    · exact h2.symm.trans (h1.symm.trans h0.symm)
    · exact h3.symm.trans (h2.symm.trans (h1.symm.trans h0.symm))
    · exact h5.symm
    · exact h6.symm.trans h0.symm
    · exact h7.symm.trans (h1.symm.trans h0.symm)
    · exact h8.symm.trans (h2.symm.trans (h1.symm.trans h0.symm))
    · exact h9.symm.trans (h3.symm.trans (h2.symm.trans (h1.symm.trans h0.symm)))
  exact (h u).trans (h v).symm

theorem petersen_isMatchingCovered : petersen.IsMatchingCovered := by
  refine ⟨petersen_isConnected, ?_⟩
  intro e
  have hpos : 0 < (Finset.univ.filter fun i : Fin 6 ↦ e ∈ petersenMatching i).card := by
    rw [petersenMatching_count]
    decide
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨_, petersenMatching_isPerfectMatching i, (Finset.mem_filter.mp hi).2⟩

/-- Each edge is covered by a listed matching other than any specified matching. -/
theorem petersenMatching_cover_avoiding_index (i : Fin 6) (e : Fin 15) :
    ∃ j : Fin 6, j ≠ i ∧ e ∈ petersenMatching j := by
  revert i e
  decide

theorem petersenMatchingShore_nontrivial (i : Fin 6) :
    IsNontrivialCut (petersenMatchingShore i) := by
  unfold IsNontrivialCut
  fin_cases i <;> decide

/-- The canonical pentagonal cuts are separating: crossing-one matchings cover every edge. -/
theorem petersenMatchingShore_isSeparatingCut (i : Fin 6) :
    petersen.IsSeparatingCut (petersenMatchingShore i) := by
  have hX : (petersenMatchingShore i).Nonempty :=
    Finset.card_pos.mp (by rw [petersenMatchingShore_card]; decide)
  have hXC : (Finset.univ \ petersenMatchingShore i).Nonempty :=
    Finset.card_pos.mp (by have h := (petersenMatchingShore_nontrivial i).2; omega)
  apply isSeparatingCut_of_crossing_one petersen_isConnected hX hXC
  intro e
  obtain ⟨j, hji, he⟩ := petersenMatching_cover_avoiding_index i e
  refine ⟨_, petersenMatching_isPerfectMatching j, he, ?_⟩
  rw [petersenMatchingShore_dangling]
  exact petersenMatching_inter_card j i hji

/-- Every canonical Petersen cut has characteristic five. -/
theorem petersenMatchingShore_cutCharacteristic (i : Fin 6) :
    petersen.cutCharacteristic (petersenMatchingShore i) = 5 := by
  apply (cutCharacteristic_eq_coe_iff (n := 5)).mpr
  refine ⟨by decide, ⟨petersenMatching i, petersenMatching_isPerfectMatching i, ?_⟩, ?_⟩
  · rw [petersenMatchingShore_dangling, Finset.inter_self]
    exact petersenMatching_card i
  · intro M hM hc
    rcases petersen_matching_crossing_one_or_five hM i with h | h <;> omega

end GraphPuzzles.LoopMultigraph
