import GraphPuzzles.Cuts.TightCutTransport
import GraphPuzzles.Cuts.CohesiveUncrossing

/-!
# The characteristic of a separating cut

Following Campos--Lucchesi, the characteristic is the smallest perfect-matching
crossing count greater than one, or infinity if there is no such matching. The
definition makes sense for arbitrary shores; for odd shores infinity is exactly
tightness. Contraction preserves the characteristic along a tight cut.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- All crossing counts realized by perfect matchings. -/
noncomputable def matchingCrossings (H : LoopMultigraph V E) (X : Finset V) : Finset ℕ := by
  classical
  exact (Finset.univ.filter H.IsPerfectMatching).image fun M ↦ (M ∩ H.dangling X).card

theorem mem_matchingCrossings {X : Finset V} {n : ℕ} :
    n ∈ H.matchingCrossings X ↔ ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = n := by
  classical
  simp only [matchingCrossings, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The minimum crossing count greater than one; infinity for tight odd cuts. -/
noncomputable def cutCharacteristic (H : LoopMultigraph V E) (X : Finset V) : WithTop ℕ :=
  ((H.matchingCrossings X).filter (1 < ·)).min

theorem cutCharacteristic_compl (X : Finset V) :
    H.cutCharacteristic (Finset.univ \ X) = H.cutCharacteristic X := by
  simp only [cutCharacteristic, matchingCrossings, dangling_compl]

theorem cutCharacteristic_le {X : Finset V} {M : Finset E} (hM : H.IsPerfectMatching M)
    (hc : 1 < (M ∩ H.dangling X).card) :
    H.cutCharacteristic X ≤ ((M ∩ H.dangling X).card : WithTop ℕ) :=
  Finset.min_le (Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr ⟨M, hM, rfl⟩, hc⟩)

theorem cutCharacteristic_eq_coe_iff {X : Finset V} {n : ℕ} :
    H.cutCharacteristic X = (n : WithTop ℕ) ↔ 1 < n ∧
      (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = n) ∧
      ∀ M, H.IsPerfectMatching M → 1 < (M ∩ H.dangling X).card →
        n ≤ (M ∩ H.dangling X).card := by
  constructor
  · intro h
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp (Finset.mem_of_min h)
    exact ⟨hn, mem_matchingCrossings.mp hm, fun M hM hc ↦
      WithTop.coe_le_coe.mp (h.symm.le.trans (cutCharacteristic_le hM hc))⟩
  · rintro ⟨hn, ⟨M, hM, hm⟩, hmin⟩
    apply le_antisymm
    · have hc : 1 < (M ∩ H.dangling X).card := by omega
      have hh := cutCharacteristic_le (X := X) hM hc
      rw [hm] at hh
      exact hh
    · apply Finset.le_min
      intro m hm
      obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
      obtain ⟨P, hP, hp⟩ := mem_matchingCrossings.mp hm
      exact WithTop.coe_le_coe.mpr (hp ▸ hmin P hP (hp.symm ▸ hc))

theorem cutCharacteristic_eq_top_iff {X : Finset V} :
    H.cutCharacteristic X = ⊤ ↔
      ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card ≤ 1 := by
  rw [cutCharacteristic, Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h M hM
    by_contra hn
    exact h _ (Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr ⟨M, hM, rfl⟩,
      Nat.lt_of_not_ge hn⟩)
  · intro h n hn
    obtain ⟨hn, hgt⟩ := Finset.mem_filter.mp hn
    obtain ⟨M, hM, hm⟩ := mem_matchingCrossings.mp hn
    have hh := h M hM
    omega

theorem cutCharacteristic_eq_top_iff_tight {X : Finset V} (ho : Odd X.card) :
    H.cutCharacteristic X = ⊤ ↔ H.IsTightCut X := by
  rw [cutCharacteristic_eq_top_iff]
  constructor
  · intro h M hM
    have hh := h M hM
    have hp := hM.crossing_mod_two X
    rw [Nat.odd_iff] at ho
    omega
  · exact fun h M hM ↦ (h M hM).le

/-- For odd shores, characteristic three is exactly the requested three-crossing matching. -/
theorem cutCharacteristic_eq_three_iff {X : Finset V} (ho : Odd X.card) :
    H.cutCharacteristic X = 3 ↔ ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  rw [show (3 : WithTop ℕ) = ((3 : ℕ) : WithTop ℕ) from rfl, cutCharacteristic_eq_coe_iff]
  constructor
  · exact fun h ↦ h.2.1
  · intro h
    refine ⟨by omega, h, ?_⟩
    intro M hM hc
    have hp := hM.crossing_mod_two X
    rw [Nat.odd_iff] at ho
    omega

theorem MatchingEquivalentCuts.characteristic_eq {X Y : Finset V}
    (h : H.MatchingEquivalentCuts X Y) : H.cutCharacteristic X = H.cutCharacteristic Y := by
  have he : H.matchingCrossings X = H.matchingCrossings Y := by
    ext n
    simp only [mem_matchingCrossings]
    exact ⟨fun ⟨M, hM, hm⟩ ↦ ⟨M, hM, (h M hM).symm.trans hm⟩,
      fun ⟨M, hM, hm⟩ ↦ ⟨M, hM, (h M hM).trans hm⟩⟩
  simp only [cutCharacteristic, he]

/-- The characteristic cannot decrease on a contraction across a separating cut. -/
theorem cutCharacteristic_le_contract {X : Finset V} (hs : H.IsSeparatingCut X)
    (Y : Finset (Option X)) (hn : none ∉ Y) :
    H.cutCharacteristic (sourceShore X Y) ≤ (H.contract X).cutCharacteristic Y := by
  apply Finset.min_mono
  intro n hn'
  obtain ⟨hm, hgt⟩ := Finset.mem_filter.mp hn'
  exact Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr
    (exists_matching_crossing_of_contract hn hs.2 (mem_matchingCrossings.mp hm)), hgt⟩

/-- The equality assertion of Campos--Lucchesi Lemma 4.5: a tight contraction preserves
the characteristic of each cut carried by the retained shore. -/
theorem IsTightCut.characteristic_contract {X : Finset V} (ht : H.IsTightCut X)
    (hs : H.IsSeparatingCut X) (Y : Finset (Option X)) (hn : none ∉ Y) :
    (H.contract X).cutCharacteristic Y = H.cutCharacteristic (sourceShore X Y) := by
  have he : (H.contract X).matchingCrossings Y = H.matchingCrossings (sourceShore X Y) := by
    ext n
    simp only [mem_matchingCrossings, ht.exists_matching_crossing_iff hs Y hn n]
  simp only [cutCharacteristic, he]

/-- Nontrivial separating cuts of bricks have a finite odd characteristic at least three. -/
theorem IsBrick.exists_finite_characteristic (hb : H.IsBrick) {X : Finset V}
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ n : ℕ, H.cutCharacteristic X = (n : WithTop ℕ) ∧ Odd n ∧ 3 ≤ n := by
  obtain ⟨M, hM, _, hle⟩ := hb.exists_crossing_at_least_three hs hX
  have hm : (M ∩ H.dangling X).card ∈ (H.matchingCrossings X).filter (1 < ·) :=
    Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr ⟨M, hM, rfl⟩, by omega⟩
  obtain ⟨n, hn⟩ := Finset.min_of_mem hm
  have hspec := cutCharacteristic_eq_coe_iff.mp hn
  obtain ⟨P, hP, hp⟩ := hspec.2.1
  have ho := hs.odd_shore hb.matchingCovered.1 hX
  have hpar := hP.crossing_mod_two X
  rw [hp] at hpar
  rw [Nat.odd_iff] at ho
  exact ⟨n, hn, Nat.odd_iff.mpr (hpar.trans ho), by have hh := hspec.1; omega⟩

end GraphPuzzles.LoopMultigraph
