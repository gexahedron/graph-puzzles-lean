import GraphPuzzles.Bricks.NearBrickCuts
import GraphPuzzles.Cuts.CohesiveCrossingTransport

/-! A matching-covered graph with a robust cut is a near-brick. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- Glue a bipartite intersection to a bipartite region containing the opposite contraction pole. -/
theorem IsBipartiteOn.glue_contract_region {X Y : Finset V}
    (hI : (H.contract (X ∩ Y)).IsBipartite)
    (hR : (H.contract (Finset.univ \ X)).IsBipartiteOn (poleShore (Finset.univ \ X) Y)) :
    H.IsBipartiteOn Y := by
  let I := X ∩ Y
  let R := Finset.univ \ X
  change (H.contract I).IsBipartite at hI
  change (H.contract R).IsBipartiteOn (poleShore R Y) at hR
  obtain ⟨c, hc⟩ := hI
  obtain ⟨d, hd⟩ := hR
  let f : Bool → Bool := fun b ↦ if b = d none then !c none else c none
  have hinj (a b : Bool) (hne : a ≠ b) : f a ≠ f b := by
    cases a <;> cases b <;> cases hcn : c none <;> cases hdn : d none <;> simp_all [f]
  have hret (v : V) (hv : v ∈ Y) : contractVertex R v ∈ poleShore R Y := by
    unfold contractVertex
    split_ifs <;> simp [hv]
  have he (e : H.meets R) (h0 : H.endAt e.1 0 ∈ Y) (h1 : H.endAt e.1 1 ∈ Y) :
      d ((H.contract R).endAt e 0) ≠ d ((H.contract R).endAt e 1) :=
    hd e (hret _ h0) (hret _ h1)
  let g : V → Bool := fun v ↦ if h : v ∈ I then c (some ⟨v, h⟩)
    else f (d (contractVertex R v))
  refine ⟨g, ?_⟩
  intro e hy0 hy1
  by_cases h0 : H.endAt e 0 ∈ I <;> by_cases h1 : H.endAt e 1 ∈ I
  · have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    simpa only [contract_endAt, dif_pos h0, dif_pos h1, g] using hh
  · have h0' : H.endAt e 0 ∉ R := by
      simpa only [R, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using
        (Finset.mem_inter.mp h0).1
    have h1' : H.endAt e 1 ∈ R := by
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hx ↦ h1 (Finset.mem_inter.mpr ⟨hx, hy1⟩)
    have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    have hh' := he ⟨e, mem_meets.mpr ⟨1, h1'⟩⟩ hy0 hy1
    simp only [contract_endAt, dif_pos h0, dif_neg h1] at hh
    simp only [contract_endAt, dif_neg h0', dif_pos h1'] at hh'
    simpa only [g, dif_pos h0, dif_neg h1, contractVertex, dif_pos h1', f,
      if_neg (Ne.symm hh')] using hh
  · have h0' : H.endAt e 0 ∈ R := by
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hx ↦ h0 (Finset.mem_inter.mpr ⟨hx, hy0⟩)
    have h1' : H.endAt e 1 ∉ R := by
      simpa only [R, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using
        (Finset.mem_inter.mp h1).1
    have hh := hc ⟨e, mem_meets.mpr ⟨1, h1⟩⟩
    have hh' := he ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩ hy0 hy1
    simp only [contract_endAt, dif_neg h0, dif_pos h1] at hh
    simp only [contract_endAt, dif_pos h0', dif_neg h1'] at hh'
    simpa only [g, dif_neg h0, dif_pos h1, contractVertex, dif_pos h0', f,
      if_neg hh'] using hh
  · have h0' : H.endAt e 0 ∈ R := by
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hx ↦ h0 (Finset.mem_inter.mpr ⟨hx, hy0⟩)
    have h1' : H.endAt e 1 ∈ R := by
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hx ↦ h1 (Finset.mem_inter.mpr ⟨hx, hy1⟩)
    have hh := he ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩ hy0 hy1
    simp only [contract_endAt, dif_pos h0', dif_pos h1'] at hh
    simpa only [g, dif_neg h0, dif_neg h1, contractVertex, dif_pos h0', dif_pos h1'] using
      hinj _ _ hh

omit [DecidableEq E] in
private theorem bipartite_of_inner_and_opposite_middle {X Y : Finset V}
    (hI : (H.contract (X ∩ Y)).IsBipartite)
    (hK : ((H.contract (Finset.univ \ X)).contract
      (poleShore (Finset.univ \ X)
        (Finset.univ \ ((Finset.univ \ X) ∩ (Finset.univ \ Y))))).IsBipartite) :
    H.IsBipartiteOn Y := by
  apply IsBipartiteOn.glue_contract_region hI
  apply hK.induced_of_contract.mono
  intro v hv
  cases v with
  | none => simp
  | some v =>
    simp only [some_mem_poleShore] at hv ⊢
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_inter]
    exact fun h ↦ h.2 hv

/-- Uncrossing against a tight cut gives a tight cut in a near-brick contraction;
one of its two contractions is bipartite, including when the uncrossed cut is trivial. -/
theorem IsNearBrick.bipartite_uncrossing {X Y : Finset V}
    (hb : (H.contract X).IsNearBrick) (hc : H.IsCohesiveCuts {X, Y})
    (htY : H.IsTightCut Y) (ho : Odd (X ∩ Y).card) :
    (H.contract (X ∩ Y)).IsBipartite ∨
      ((H.contract X).contract (poleShore X (Finset.univ \ (X ∩ Y)))).IsBipartite := by
  have hc' : H.IsCohesiveCuts {Y, X} := by simpa only [Finset.pair_comm] using hc
  have ho' : Odd (Y ∩ X).card := by simpa only [Finset.inter_comm] using ho
  have htS : (H.contract X).IsTightCut (contractShore X Y) := by
    intro M hM
    obtain ⟨P, hP, hp⟩ := hc'.extend_intersection_matching ho' hM
    exact hp.symm.trans (htY P hP)
  have he : contractShore X (X ∩ Y) = contractShore X Y := by
    ext v
    cases v with
    | none => simp
    | some v => simp [v.2]
  have htI : (H.contract X).IsTightCut (contractShore X (X ∩ Y)) := he.symm ▸ htS
  rcases hb.noStrictTightCut.all hb.matchingCovered htI with h | h
  · exact Or.inl ((contractNestedIso (H := H) Finset.inter_subset_left).isBipartite h)
  · exact Or.inr (compl_contractShore X (X ∩ Y) ▸ h)

theorem IsRobustCut.nontrivial (hm : H.IsMatchingCovered) {X : Finset V}
    (hr : H.IsRobustCut X) : IsNontrivialCut X := by
  constructor
  · by_contra h
    exact hr.leftNear.notBipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))
  · by_contra h
    exact hr.rightNear.notBipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))

private theorem robust_bipartite_side_of_odd_inter (hm : H.IsMatchingCovered)
    {X Y : Finset V} (hr : H.IsRobustCut X) (htY : H.IsTightCut Y)
    (hY : IsNontrivialCut Y) (ho : Odd (X ∩ Y).card) :
    (H.contract Y).IsBipartite ∨ (H.contract (Finset.univ \ Y)).IsBipartite := by
  let I := X ∩ Y
  let D := (Finset.univ \ X) ∩ (Finset.univ \ Y)
  have heD : D = Finset.univ \ (X ∪ Y) := by
    ext v
    simp [D]
  have hX := hr.nontrivial hm
  have hsY := htY.isSeparatingCut hm
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  have hc := hr.isSeparatingCut.cohesive_pair_tight htY
  have hc' : H.IsCohesiveCuts {Finset.univ \ X, Finset.univ \ Y} := by
    simpa only [Finset.image_insert, Finset.image_singleton] using hc.compls
  have hoD := hc.odd_complement_intersection hm.1 hY ho
  have hl := hr.leftNear.bipartite_uncrossing hc htY ho
  have hr' := hr.rightNear.bipartite_uncrossing hc' htY.compl hoD
  have hcu := hc.uncross (X := X) (Y := Y) (by simp) (by simp) ho
  obtain ⟨e, _⟩ := hm.1.dangling_nonempty (X := X)
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  obtain ⟨N, hN, _, hn⟩ := hcu e
  have hNX : (N ∩ H.dangling X).card = 1 := hn X (by simp)
  have hNI : (N ∩ H.dangling I).card = 1 := hn I (by simp [I])
  have hND : (N ∩ H.dangling D).card = 1 := by
    rw [heD, dangling_compl]
    exact hn (X ∪ Y) (by simp)
  rcases hl with hI | hB <;> rcases hr' with hD | hC
  · exfalso
    apply hr.notTight
    intro M hM
    have hi := (hI.contract_cut_count hM hN).trans hNI
    have hd := (hD.contract_cut_count hM hN).trans hND
    have hd' : (M ∩ H.dangling (X ∪ Y)).card = 1 := by
      change (M ∩ H.dangling D).card = 1 at hd
      simpa only [heD, dangling_compl] using hd
    have hy := htY M hM
    have hh := hc.crossing_modular (X := X) (Y := Y) (by simp) (by simp) ho M
    omega
  · exact Or.inl ((bipartite_of_inner_and_opposite_middle hI hC).contract_of_separating hsY)
  · have hb : H.IsBipartiteOn (Finset.univ \ Y) := by
      apply bipartite_of_inner_and_opposite_middle hD
      rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X),
        Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y)]
      exact hB
    exact Or.inr (hb.contract_of_separating hsY.compl)
  · have hNX' : (N ∩ H.dangling (Finset.univ \ X)).card = 1 := by
      simpa only [dangling_compl] using hNX
    have hntX' : ¬ H.IsTightCut (Finset.univ \ X) := by
      intro h
      apply hr.notTight
      simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using h.compl
    have heI := hB.middle_matchingEquivalent_of_not_tight Finset.inter_subset_left hN hNX hNI
      hr.notTight
    have heD' := hC.middle_matchingEquivalent_of_not_tight Finset.inter_subset_left hN hNX' hND
      hntX'
    exfalso
    apply hr.notTight
    intro M hM
    have hi := heI M hM
    have hd := heD' M hM
    have hd' : (M ∩ H.dangling (X ∪ Y)).card = (M ∩ H.dangling X).card := by
      change (M ∩ H.dangling D).card = (M ∩ H.dangling (Finset.univ \ X)).card at hd
      simpa only [heD, dangling_compl] using hd
    have hy := htY M hM
    have hh := hc.crossing_modular (X := X) (Y := Y) (by simp) (by simp) ho M
    omega

/-- Campos--Lucchesi Lemma 3.2: a matching-covered graph with a robust cut is a near-brick. -/
theorem IsRobustCut.isNearBrick (hm : H.IsMatchingCovered) {X : Finset V}
    (hr : H.IsRobustCut X) : H.IsNearBrick := by
  have hX := hr.nontrivial hm
  have hoX := hr.isSeparatingCut.odd_shore hm.1 hX
  refine isNearBrick_iff.mpr ⟨hm, ?_, ?_⟩
  · exact fun h ↦ hr.leftNear.notBipartite (h.contract_of_separating hr.isSeparatingCut)
  · intro Y htY hY
    by_cases ho : Odd (X ∩ Y).card
    · exact robust_bipartite_side_of_odd_inter hm hr htY hY ho
    · have ho' : Odd (X ∩ (Finset.univ \ Y)).card := by
        have he : X ∩ (Finset.univ \ Y) = X \ Y := by ext v; simp
        rw [he, Nat.odd_iff]
        rw [Nat.odd_iff] at ho hoX
        have hh := Finset.card_sdiff_add_card_inter X Y
        omega
      rcases robust_bipartite_side_of_odd_inter hm hr htY.compl hY.compl ho' with h | h
      · exact Or.inr h
      · exact Or.inl (Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y) ▸ h)

end GraphPuzzles.LoopMultigraph
