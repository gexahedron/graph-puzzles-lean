import GraphPuzzles.Cuts.Contraction.DoubleBicontraction
import GraphPuzzles.Reduction.Wheels.OddWheelShoreBicontraction

/-! A matching cut with two wheel shores has a b-removable spoke when it has
at least six labels. Consequently the final non-removable case has five labels. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem deleted_cut_image (X : Finset V) (e : E) :
    ((H.deleteEdge e).dangling X).image Subtype.val = (H.dangling X).erase e := by
  ext f
  constructor
  · rintro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp g.2).1,
      (restrictEdges_mem_dangling _ g X).mp hg⟩
  · intro hf
    obtain ⟨hne, hf⟩ := Finset.mem_erase.mp hf
    exact Finset.mem_image.mpr ⟨⟨f, by simp [hne]⟩,
      (restrictEdges_mem_dangling _ _ X).mpr hf, rfl⟩

theorem deleted_cut_card {X : Finset V} {e : E} (he : e ∈ H.dangling X) :
    ((H.deleteEdge e).dangling X).card + 1 = (H.dangling X).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,
    deleted_cut_image, Finset.card_erase_add_one he]

theorem IsPerfectMatching.deleted_cut_degree {X : Finset V}
    (hC : H.IsPerfectMatching (H.dangling X)) {e : E} (he : e ∈ H.dangling X) (v : V) :
    (H.deleteEdge e).degreeIn ((H.deleteEdge e).dangling X) v ≤ 1 := by
  have hd : H.degreeIn (((H.deleteEdge e).dangling X).image Subtype.val) v =
      (H.deleteEdge e).degreeIn ((H.deleteEdge e).dangling X) v :=
    restrictEdges_degreeIn (H := H) (Finset.univ.erase e) ((H.deleteEdge e).dangling X) v
  rw [← hd, deleted_cut_image]
  have hP := hC.erase_edge he
  by_cases hv : v ∈ Finset.univ \ {H.endAt e 0, H.endAt e 1}
  · exact (hP.2 v hv).le
  · exact (hP.degree_zero hv).le.trans (by omega)

/-- A deleted matching edge consumes one of the three vertices in an expansion
triple, leaving at most two boundary incidences in that triple. -/
theorem IsPerfectMatching.deleted_cut_triple_bound {X : Finset V}
    (hC : H.IsPerfectMatching (H.dangling X)) {e : E} (he : e ∈ H.dangling X)
    {A : Finset V} (hA : A.card = 3)
    (hAe : H.endAt e 0 ∈ A ∨ H.endAt e 1 ∈ A) :
    ((H.deleteEdge e).dangling X ∩ (H.deleteEdge e).dangling A).card ≤ 2 := by
  obtain ⟨z, hzA, hze⟩ : ∃ z ∈ A, z = H.endAt e 0 ∨ z = H.endAt e 1 := by
    rcases hAe with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  have hz : (H.deleteEdge e).degreeIn ((H.deleteEdge e).dangling X) z = 0 := by
    have hd : H.degreeIn (((H.deleteEdge e).dangling X).image Subtype.val) z =
        (H.deleteEdge e).degreeIn ((H.deleteEdge e).dangling X) z :=
      restrictEdges_degreeIn (H := H) (Finset.univ.erase e) ((H.deleteEdge e).dangling X) z
    rw [← hd, deleted_cut_image]
    apply (hC.erase_edge he).degree_zero
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_not]
    exact hze
  have hsum : (∑ v ∈ A, (H.deleteEdge e).degreeIn ((H.deleteEdge e).dangling X) v) ≤ 2 := by
    rw [← Finset.sum_erase_add _ _ hzA, hz, add_zero]
    calc
      _ ≤ ∑ _v ∈ A.erase z, 1 := Finset.sum_le_sum (fun v _ ↦ hC.deleted_cut_degree he v)
      _ = 2 := by simp [Finset.card_erase_of_mem hzA, hA]
  have hh := sum_degreeIn_eq_two_mul_add (H := H.deleteEdge e) A ((H.deleteEdge e).dangling X)
  omega

/-- Local wheel spoke removability makes the original deleted graph matching covered. -/
theorem isMatchingCovered_deleteEdge_of_two_wheels {X : Finset V}
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hX : 5 ≤ X.card) (hXC : 5 ≤ (Finset.univ \ X).card)
    {e : E} (he : e ∈ H.dangling X) : (H.deleteEdge e).IsMatchingCovered := by
  obtain ⟨Wl⟩ := hl
  obtain ⟨Wr⟩ := hr
  have hec : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
  have hs : (H.deleteEdge e).IsSeparatingCut X :=
    ⟨(deleteContractIso X ⟨e, dangling_subset_meets X he⟩).symm.isMatchingCovered
        (Wl.isRemovable_cut_label hX he),
      (deleteContractIso (Finset.univ \ X) ⟨e, dangling_subset_meets _ hec⟩).symm.isMatchingCovered
        (Wr.isRemovable_cut_label hXC hec)⟩
  exact hs.isMatchingCovered (Finset.card_pos.mp (by omega))

/-- In the cubic two-wheel case, every selected spoke is b-removable if the
matching cut has at least six labels. -/
theorem IsPerfectMatching.deleteEdge_nearBrick_of_two_wheels {X : Finset V}
    (hC : H.IsPerfectMatching (H.dangling X))
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (h6 : 6 ≤ (H.dangling X).card) {e : E} (he : e ∈ H.dangling X) :
    (H.deleteEdge e).IsNearBrick := by
  have hX : 6 ≤ X.card := by
    have hh := hC.crossing_le_card X
    simp only [Finset.inter_self] at hh
    omega
  have hXC : 6 ≤ (Finset.univ \ X).card := by
    have hh := hC.crossing_le_card (Finset.univ \ X)
    simp only [dangling_compl, Finset.inter_self] at hh
    omega
  obtain ⟨A, hAX, hA, heA, htA, hbA, hbrA⟩ := hl.exists_deleted_spoke_shore hC (by omega) he
  have hC' : H.IsPerfectMatching (H.dangling (Finset.univ \ X)) := by
    simpa only [dangling_compl] using hC
  have he' : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
  obtain ⟨B, hBX, hB, heB, htB, hbB, hbrB⟩ := hr.exists_deleted_spoke_shore hC' (by omega) he'
  have hBA : B ⊆ Finset.univ \ A := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ha ↦ (Finset.mem_sdiff.mp (hBX hv)).2 (hAX ha)⟩
  have hnA : IsNontrivialCut A := by
    refine ⟨by omega, ?_⟩
    have hh : Finset.univ \ X ⊆ Finset.univ \ A := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun ha ↦ (Finset.mem_sdiff.mp hv).2 (hAX ha)⟩
    have hc := Finset.card_le_card hh
    omega
  have hnB : IsNontrivialCut (contractShore (Finset.univ \ A) B) := by
    have hc := card_contractShore_of_subset hBA
    have htotal : 12 ≤ Fintype.card V := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
      simp only [Finset.card_univ] at hh
      omega
    have hfirst : (Finset.univ \ A).card = Fintype.card V - 3 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hA]
    refine ⟨by omega, ?_⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe, hc, hB, hfirst]
    omega
  have hm := isMatchingCovered_deleteEdge_of_two_wheels hl hr (by omega) (by omega) he
  apply hm.isNearBrick_of_double_bicontraction hAX hBX htA hnA htB hnB hbA hbB hbrA hbrB
    (Finset.Subset.refl ((H.deleteEdge e).dangling X))
  · have hc := deleted_cut_card he
    omega
  · exact fun v ↦ (hC.deleted_cut_degree he v).trans (by omega)
  · exact hC.deleted_cut_triple_bound he hA heA
  · exact hC.deleted_cut_triple_bound he hB heB

/-- The final non-removable two-wheel case has exactly five cut labels. -/
theorem IsPerfectMatching.cut_card_five_of_no_deleted_nearBrick {X : Finset V}
    (hC : H.IsPerfectMatching (H.dangling X))
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (h5 : 5 ≤ (H.dangling X).card)
    (hn : ∀ e ∈ H.dangling X, ¬ (H.deleteEdge e).IsNearBrick) :
    (H.dangling X).card = 5 := by
  by_contra hc
  have h6 : 6 ≤ (H.dangling X).card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (H.dangling X).card by omega)
  exact hn e he (hC.deleteEdge_nearBrick_of_two_wheels hl hr h6 he)

end GraphPuzzles.LoopMultigraph
