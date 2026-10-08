import GraphPuzzles.Reduction.Wheels.OddWheelTheorem
import GraphPuzzles.Reduction.Wheels.OddWheelTriangle
import GraphPuzzles.Bricks.BraceContraction
import GraphPuzzles.Bricks.BraceRemovabilityLarge
import GraphPuzzles.Matching.Bipartite.VertexMatchingBipartite
import GraphPuzzles.Reduction.Removable.RemovableClassContraction

/-! The tight-cut induction for the near-brick odd-wheel theorem. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

open scoped Classical

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A nonsolid near-brick contraction makes the original graph nonsolid. -/
theorem IsSeparatingCut.not_solid_of_contract {X : Finset V}
    (hs : H.IsSeparatingCut X) (hm : H.IsMatchingCovered) (hX : IsNontrivialCut X)
    (hn : (H.contract X).IsNearBrick) (hns : ¬ (H.contract X).IsSolid) :
    ¬ H.IsSolid := by
  classical
  change ¬ ∀ Y, ¬ (H.contract X).IsStrictlySeparatingCut Y at hns
  push Not at hns
  obtain ⟨Y₀, hY₀⟩ := hns
  have hh : ∃ Y, (H.contract X).IsStrictlySeparatingCut Y ∧ none ∉ Y := by
    by_cases hp : none ∈ Y₀
    · exact ⟨Finset.univ \ Y₀, hY₀.compl, by simp [hp]⟩
    · exact ⟨Y₀, hY₀, hp⟩
  obtain ⟨Y, hY, hp⟩ := hh
  have hnt := hY.nontrivial hn.matchingCovered
  have hD := hX.sourceShore hnt hp
  have hd := hs.lift_contract hY.separating hp hm.1
    (Finset.card_pos.mp (by have := hD.1; omega))
    (Finset.card_pos.mp (by have := hD.2; omega))
  obtain ⟨N, hN, hNY⟩ := hY.separating.exists_crossing_gt_one hn.matchingCovered.1 hnt
    (hY.not_tight hn)
  obtain ⟨M, hM, _, heM⟩ := hN.extend_contract_exact hs.2
  have hMD : 1 < (M ∩ H.dangling (sourceShore X Y)).card := by
    rw [← contractMatching_crossing X Y hp, heM]
    exact hNY
  have hnot : ¬ H.IsTightCut (sourceShore X Y) := fun ht ↦ by
    have := ht M hM
    omega
  intro hsolid
  apply hsolid (sourceShore X Y)
  refine ⟨hd, fun hb ↦ hnot (hd.tight_of_bipartite hm.1 hD hb), ?_⟩
  intro hb
  apply hnot
  simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using
    (hd.compl.tight_of_bipartite hm.1 hD.compl hb).compl

/-- The degree bound needed when choosing edges at a brace vertex. -/
theorem IsThreeEdgeConnected.three_le_degree (h3 : H.IsThreeEdgeConnected)
    {w : V} (hw : ∃ z, z ≠ w) : 3 ≤ H.degree w := by
  obtain ⟨z, hz⟩ := hw
  have hcut := h3 {w} (Finset.singleton_nonempty w) ⟨z, by simp [hz]⟩
  have hh := sum_degree_eq_two_mul_add (H := H) {w}
  simp only [Finset.sum_singleton] at hh
  omega

/-- A brace with at least four vertices and no degree-two vertices has
at most one nonremovable edge at each vertex. -/
theorem IsBrace.card_nonremovable_incident_le_one_of_four_le
    (hb : H.IsBrace) (h4 : 4 ≤ Fintype.card V) (hdeg : ∀ w, H.degree w ≠ 2) (w : V) :
    ((H.meets {w}).filter fun e ↦ ¬ H.IsRemovable e).card ≤ 1 := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : V, z ≠ w := by
    by_contra hn
    push Not at hn
    have hcard : (Finset.univ : Finset V) = {w} := by ext z; simp [hn z]
    have hh := congrArg Finset.card hcard
    simp only [Finset.card_univ, Finset.card_singleton] at hh
    omega
  obtain ⟨M, hM⟩ := hb.matchingCovered.exists_perfectMatching_of_ne hz
  have heven := hM.isFractional.card_even
  by_cases heq : Fintype.card V = 4
  · exact hb.card_nonremovable_incident_le_one heq hdeg w
  have h6 : 6 ≤ Fintype.card V := by rw [Nat.even_iff] at heven; omega
  have hempty : (H.meets {w}).filter (fun e ↦ ¬ H.IsRemovable e) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e _ hn
    exact hn (hb.isRemovable_of_six_le_card h6 e)
  simp [hempty]

/-- At a degree-at-least-three brace vertex, a degree-one edge set and
the unique possible nonremovable edge cannot cover all incident edges. -/
theorem IsBrace.exists_removable_incident_avoiding (hb : H.IsBrace)
    (h4 : 4 ≤ Fintype.card V) (h3 : H.IsThreeEdgeConnected)
    {M : Finset E} {w : V} (hM : H.degreeIn M w = 1) :
    ∃ e, e ∈ H.meets {w} ∧ e ∉ M ∧ H.IsRemovable e := by
  classical
  have hother (w : V) : ∃ z, z ≠ w := by
    by_contra hn
    push Not at hn
    have hcard : (Finset.univ : Finset V) = {w} := by ext z; simp [hn z]
    have hh := congrArg Finset.card hcard
    simp only [Finset.card_univ, Finset.card_singleton] at hh
    omega
  have hbad := hb.card_nonremovable_incident_le_one_of_four_le h4
    (fun z ↦ by have := h3.three_le_degree (hother z); omega) w
  have hmatch : ((H.meets {w}) ∩ M).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨hei, heM⟩ := Finset.mem_inter.mp he
    obtain ⟨hfi, hfM⟩ := Finset.mem_inter.mp hf
    obtain ⟨i, hi⟩ := mem_meets.mp hei
    obtain ⟨j, hj⟩ := mem_meets.mp hfi
    exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hM heM hfM
      (Finset.mem_singleton.mp hi) (Finset.mem_singleton.mp hj))
  by_contra hn
  push Not at hn
  have hsub : H.dangling {w} ⊆ ((H.meets {w}) ∩ M) ∪
      ((H.meets {w}).filter fun e ↦ ¬ H.IsRemovable e) := by
    intro e he
    have hi := dangling_subset_meets {w} he
    by_cases heM : e ∈ M
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, heM⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hn e hi heM⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  obtain ⟨z, hz⟩ := hother w
  have hc := h3 {w} (Finset.singleton_nonempty _) ⟨z, by simp [hz]⟩
  omega

omit [DecidableEq E] in
/-- Each side of a bipartite graph with a perfect matching and at least
four vertices contains a second vertex. -/
theorem IsPerfectMatching.exists_same_color_ne {M : Finset E}
    (hM : H.IsPerfectMatching M) {c : V → Bool}
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    (h4 : 4 ≤ Fintype.card V) (w : V) : ∃ z, z ≠ w ∧ c z = c w := by
  classical
  have hbal := card_sides_eq hc hM (by decide : 0 < 1)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun z ↦ c z = true)
  simp only [Bool.not_eq_true, Finset.card_univ] at hsum
  have hsize : 2 ≤ ((Finset.univ : Finset V).filter fun z ↦ c z = c w).card := by
    cases hw : c w <;> omega
  by_contra hn
  push Not at hn
  have hsub : ((Finset.univ : Finset V).filter fun z ↦ c z = c w) ⊆ {w} := by
    intro z hz
    have hzc := (Finset.mem_filter.mp hz).2
    by_cases hzw : z = w
    · simp [hzw]
    · exact (hn z hzw hzc).elim
  have hh := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hh
  omega

omit [DecidableEq E] in
private theorem incident_avoids_same_color {c : V → Bool}
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) {w z : V}
    (hwz : w ≠ z) (hcolor : c w = c z) {e : E} (he : e ∈ H.meets {w}) :
    ∀ k, H.endAt e k ≠ z := by
  obtain ⟨i, hi⟩ := mem_meets.mp he
  have hiw := Finset.mem_singleton.mp hi
  intro k hk
  fin_cases i <;> fin_cases k <;> dsimp at hiw hk
  · exact hwz (hiw.symm.trans hk)
  · exact hc e (by rw [hiw, hk, hcolor])
  · exact hc e (by rw [hiw, hk, hcolor])
  · exact hwz (hiw.symm.trans hk)

omit [DecidableEq E] in
private theorem internal_of_avoids_pole {X : Finset V} {e : H.meets X}
    (he : ∀ k, (H.contract X).endAt e k ≠ none) : ∀ k, H.endAt e.1 k ∈ X := by
  intro k
  by_contra h
  exact he k ((contract_endAt_eq_none_iff X e k).mpr h)

omit [DecidableEq E] in
private theorem cut_of_incident_pole {X : Finset V} {e : H.meets X}
    (he : e ∈ (H.contract X).meets {none}) : e.1 ∈ H.dangling X := by
  obtain ⟨k, hk⟩ := mem_meets.mp he
  have hout := (contract_endAt_eq_none_iff X e k).mp (Finset.mem_singleton.mp hk)
  obtain ⟨j, hj⟩ := mem_meets.mp e.2
  apply mem_dangling.mpr
  intro hh
  fin_cases k <;> fin_cases j
  · exact hout hj
  · exact hout (hh.mpr hj)
  · exact hout (hh.mp hj)
  · exact hout hj

private theorem brace_shore_card (hs : H.IsSeparatingCut X)
    (hm : H.IsMatchingCovered) (hX : IsNontrivialCut X) : 4 ≤ Fintype.card (Option X) := by
  have ho := hs.odd_shore hm.1 hX
  rw [Nat.odd_iff] at ho
  simp only [Fintype.card_option, Fintype.card_coe]
  have := hX.1
  omega

/-- Case 1(a): a brace shore omitting the prescribed hub directly
provides an internal removable edge. -/
private theorem avoiding_class_of_hub_outside_brace {X : Finset V}
    (hs : H.IsSeparatingCut X) (hm : H.IsMatchingCovered) (hX : IsNontrivialCut X)
    (hb : (H.contract X).IsBrace) (h3 : H.IsThreeEdgeConnected)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) (hv : v ∉ X) :
    H.HasAvoidingRemovableClass v M := by
  have hXC : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by have := hX.2; omega)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := hX.1; omega : 0 < X.card)
  obtain ⟨P, hP⟩ := hb.matchingCovered.exists_perfectMatching_of_ne
    (show (some ⟨x, hx⟩ : Option X) ≠ none by simp)
  have hN := hM.contract_perfect_of_bipartite hv hb.bipartite hP
  obtain ⟨c, hc⟩ := hb.bipartite
  have h4 := brace_shore_card hs hm hX
  obtain ⟨w, hw, hwc⟩ := hP.exists_same_color_ne hc h4 none
  obtain ⟨e, hei, heM, heR⟩ := hb.exists_removable_incident_avoiding h4
    (h3.contract X hXC) (hN w)
  have hei' := internal_of_avoids_pole (incident_avoids_same_color hc hw hwc hei)
  refine ⟨e.1, ?_, fun k h ↦ hv (h ▸ hei' k), Or.inl (hs.removable_of_internal hXC hei' heR)⟩
  exact fun h ↦ heM ((mem_contractMatching X M e).mpr h)

/-- Case 1(b): when the hub and brace pole have the same colour, parity
makes the prescribed matching perfect and a boundary dependency class lifts. -/
private theorem avoiding_class_of_hub_same_color {X : Finset V}
    (hs : H.IsSeparatingCut X) (hm : H.IsMatchingCovered) (hX : IsNontrivialCut X)
    (hb : (H.contract X).IsBrace) (hn : (H.contract (Finset.univ \ X)).IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (hv : v ∈ X) {c : Option X → Bool}
    (hc : ∀ e, c ((H.contract X).endAt e 0) ≠ c ((H.contract X).endAt e 1))
    (hcolor : c (some ⟨v, hv⟩) = c none) : H.HasAvoidingRemovableClass v M := by
  have hXN : X.Nonempty := Finset.card_pos.mp (by have := hX.1; omega)
  have hXC : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by have := hX.2; omega)
  obtain ⟨P, hP⟩ := hb.matchingCovered.exists_perfectMatching_of_ne
    (show (some ⟨v, hv⟩ : Option X) ≠ none by simp)
  obtain ⟨Q, hQ⟩ := hm.exists_perfectMatching_of_ne
    (ne_of_mem_of_not_mem hv (Finset.mem_sdiff.mp hXC.choose_spec).2)
  obtain ⟨hPM, hcross⟩ := hM.perfect_of_contract_same_color hQ.isFractional.card_even hv
    (hs.odd_shore hm.1 hX) hc hP hcolor
  have hN := hPM.contract_of_crossing_one X hcross
  obtain ⟨e, hei, heM, heR⟩ := hb.exists_removable_incident_avoiding
    (brace_shore_card hs hm hX) (h3.contract X hXC) (hN none)
  have hecut := cut_of_incident_pole hei
  have hev : ∀ k, H.endAt e.1 k ≠ v := by
    have hh := incident_avoids_same_color hc (show none ≠ some ⟨v, hv⟩ by simp) hcolor.symm hei
    exact fun k hk ↦ hh k ((contract_endAt_eq_some_iff X e k ⟨v, hv⟩).mpr hk)
  have hcomp : Finset.univ \ (Finset.univ \ X) = X := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  apply hs.compl.avoiding_class_of_removable_boundary (by rwa [hcomp]) hn
    (h3.contract (Finset.univ \ X) (by rwa [hcomp])) (by simp [hv])
    (hPM.contract_of_crossing_one _ (by simpa only [dangling_compl] using hcross))
    (by simpa only [dangling_compl] using hecut)
    (fun h ↦ heM ((mem_contractMatching X M e).mpr h)) hev
  have transfer (Y : Finset V) (hY : Y = X) (a : H.meets Y) (ha : a.1 = e.1) :
      (H.contract Y).IsRemovable a := by
    subst Y
    have ha' : a = e := Subtype.ext ha
    exact ha'.symm ▸ heR
  exact transfer _ hcomp _ rfl

omit [DecidableEq E] in
private theorem joins_of_incident {e : E} {w : V} (he : e ∈ H.meets {w}) :
    ∃ z, H.Joins e w z := by
  obtain ⟨k, hk⟩ := mem_meets.mp he
  have hh := Finset.mem_singleton.mp hk
  fin_cases k
  · exact ⟨H.endAt e 1, Or.inl ⟨hh, rfl⟩⟩
  · exact ⟨H.endAt e 0, Or.inr ⟨rfl, hh⟩⟩

/-- The odd-wheel branch of Case 1(c): a brace edge is removable on
both sides, or belongs to the exceptional triangle-wheel doubleton. -/
private theorem avoiding_class_of_opposite_wheel {X : Finset V}
    (hs : H.IsSeparatingCut X) (hm : H.IsMatchingCovered) (hX : IsNontrivialCut X)
    (hb : (H.contract X).IsBrace) (h3 : H.IsThreeEdgeConnected)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) (hv : v ∈ X)
    {c : Option X → Bool}
    (hc : ∀ e, c ((H.contract X).endAt e 0) ≠ c ((H.contract X).endAt e 1))
    (hcolor : c (some ⟨v, hv⟩) ≠ c none)
    (W : (H.contract (Finset.univ \ X)).OddWheel none) :
    H.HasAvoidingRemovableClass v M := by
  have hXN : X.Nonempty := Finset.card_pos.mp (by have := hX.1; omega)
  have hXC : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by have := hX.2; omega)
  have hcomp : Finset.univ \ (Finset.univ \ X) = X := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
  obtain ⟨P, hP⟩ := hb.matchingCovered.exists_perfectMatching_of_ne
    (show (some ⟨v, hv⟩ : Option X) ≠ none by simp)
  obtain ⟨w, hw, hwc⟩ := hP.exists_same_color_ne hc (brace_shore_card hs hm hX) (some ⟨v, hv⟩)
  have hwn : w ≠ none := fun hn ↦ hcolor (hwc.symm.trans (congrArg c hn))
  cases w with
  | none => exact (hwn rfl).elim
  | some w =>
    have hwv : w.1 ≠ v := fun h ↦ hw (congrArg some (Subtype.ext h))
    have hMw : (H.contract X).degreeIn (H.contractMatching X M) (some w) = 1 := by
      rw [contractMatching, contract_degreeIn_some]
      exact hM w.1 hwv
    obtain ⟨e, hei, heM, heR⟩ := hb.exists_removable_incident_avoiding
      (brace_shore_card hs hm hX) (h3.contract X hXC) hMw
    have heM' : e.1 ∉ M := fun h ↦ heM ((mem_contractMatching X M e).mpr h)
    have hev : ∀ k, H.endAt e.1 k ≠ v := by
      have hh := incident_avoids_same_color hc hw hwc hei
      exact fun k hk ↦ hh k ((contract_endAt_eq_some_iff X e k ⟨v, hv⟩).mpr hk)
    by_cases hint : ∀ k, H.endAt e.1 k ∈ X
    · exact ⟨e.1, heM', hev, Or.inl (hs.removable_of_internal hXC hint heR)⟩
    push Not at hint
    obtain ⟨k, hk⟩ := hint
    have heC : e.1 ∈ H.meets (Finset.univ \ X) := mem_meets.mpr ⟨k, by simp [hk]⟩
    let a : H.meets (Finset.univ \ X) := ⟨e.1, heC⟩
    have hai : a ∈ (H.contract (Finset.univ \ X)).meets {none} := by
      obtain ⟨j, hj⟩ := mem_meets.mp e.2
      exact mem_meets.mpr ⟨j, Finset.mem_singleton.mpr
        ((contract_endAt_eq_none_iff _ a j).mpr (by
          intro h
          exact (Finset.mem_sdiff.mp h).2 hj))⟩
    obtain ⟨z, haz⟩ := joins_of_incident hai
    have finish (haR : (H.contract (Finset.univ \ X)).IsRemovable a) :
        H.HasAvoidingRemovableClass v M :=
      ⟨e.1, heM', hev, Or.inl (removable_of_both_contractions hXC e.2 heC heR haR)⟩
    by_cases h5 : 5 ≤ W.labels.length
    · exact finish (W.isRemovable_spoke h5 haz)
    by_cases huniq : ∀ b, (H.contract (Finset.univ \ X)).Joins b none z → b = a
    · have hlen : W.labels.length = 3 := by
        have ho := W.rim.labels_odd_length W.walk
        rw [Nat.odd_iff] at ho
        have := W.length_three
        omega
      have hNM := hM.contract_of_notMem (X := Finset.univ \ X) (by simp [hv])
      obtain ⟨b, hbI, hbM, hab⟩ := W.exists_removableDoubleton_of_triangle_spoke hlen haz huniq hNM
        (fun h ↦ heM' ((mem_contractMatching _ M a).mp h))
      have hbi : ∀ j, H.endAt b.1 j ∈ Finset.univ \ X :=
        internal_of_avoids_pole (fun j ↦ (Finset.mem_erase.mp ((mem_edgesIn.mp hbI) j)).1)
      have hbM' : b.1 ∉ M := fun h ↦ hbM ((mem_contractMatching _ M b).mpr h)
      have hbv : ∀ j, H.endAt b.1 j ≠ v := fun j h ↦
        (Finset.mem_sdiff.mp (hbi j)).2 (h.symm ▸ hv)
      have hpair : (H.deletePair a.1 b.1).IsMatchingCovered := by
        apply deletePair_of_one_boundary (X := Finset.univ \ X) (by rwa [hcomp]) (by simpa only [hcomp] using e.2)
          hbi hab.matchingCovered
        have transfer (Y : Finset V) (hY : Y = X) (f : H.meets Y) (hf : f.1 = e.1) :
            (H.contract Y).IsRemovable f := by
          subst Y
          have hf' : f = e := Subtype.ext hf
          exact hf'.symm ▸ heR
        exact transfer _ hcomp _ rfl
      obtain ⟨f, ⟨hfM, hfv⟩, hfr⟩ := removable_or_doubleton_of_deletePair
        (P := fun f ↦ f ∉ M ∧ ∀ j, H.endAt f j ≠ v)
        (fun h ↦ hab.ne (Subtype.ext h)) ⟨heM', hev⟩ ⟨hbM', hbv⟩ hpair
      rcases hfr with hfr | ⟨g, ⟨hgM, hgv⟩, hfg⟩
      · exact ⟨f, hfM, hfv, Or.inl hfr⟩
      · exact ⟨f, hfM, hfv, Or.inr ⟨g, hgM, hgv, hfg⟩⟩
    · push Not at huniq
      obtain ⟨b, hb, hba⟩ := huniq
      exact finish (hs.2.isRemovable_of_parallel hba.symm (haz.parallel hb))

private theorem oddWheel_nearBrick_aux (n : ℕ) :
    ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (H : LoopMultigraph V E), Fintype.card V = n → H.IsNearBrick →
      H.IsThreeEdgeConnected → ∀ v M, H.IsVertexMatching v M →
      H.IsOddWheel v ∨ ¬ H.IsSolid ∨ H.HasAvoidingRemovableClass v M := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ H hcard hn h3 v M hM
    by_cases hbrick : H.IsBrick
    · exact hbrick.oddWheel_or_not_solid_or_removable hM
    obtain ⟨X, hX, ht, hb, hnC⟩ := hn.exists_brace_contraction hbrick
    have hXN : X.Nonempty := Finset.card_pos.mp (by have := hX.1; omega)
    have hXC : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by have := hX.2; omega)
    have hs := ht.isSeparatingCut hn.matchingCovered hXN hXC
    by_cases hv : v ∈ X
    · obtain ⟨c, hc⟩ := hb.bipartite
      by_cases hcolor : c (some ⟨v, hv⟩) = c none
      · exact Or.inr (Or.inr (avoiding_class_of_hub_same_color hs hn.matchingCovered hX hb hnC h3 hM hv hc hcolor))
      have hcomp : Finset.univ \ (Finset.univ \ X) = X := Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)
      have h3C := h3.contract (Finset.univ \ X) (by rwa [hcomp])
      have hsmall : Fintype.card (Option ↥(Finset.univ \ X)) < n := by
        have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
        rw [Finset.card_univ, hcard] at hh
        simp only [Fintype.card_option, Fintype.card_coe]
        have := hX.1
        omega
      rcases ih _ hsmall (H.contract (Finset.univ \ X)) rfl hnC h3C none
        (H.contractMatching (Finset.univ \ X) M) (hM.contract_of_notMem (by simp [hv])) with hW | hns | hR
      · obtain ⟨W⟩ := hW
        exact Or.inr (Or.inr (avoiding_class_of_opposite_wheel hs hn.matchingCovered hX hb h3 hM hv hc hcolor W))
      · exact Or.inr (Or.inl (hs.compl.not_solid_of_contract hn.matchingCovered hX.compl hnC hns))
      · exact Or.inr (Or.inr (HasAvoidingRemovableClass.of_internal_contract hs.compl (by rwa [hcomp]) (by simp [hv]) hR))
    · exact Or.inr (Or.inr (avoiding_class_of_hub_outside_brace hs hn.matchingCovered hX hb h3 hM hv))

/-- Campos–Lucchesi Theorem 5.1: a three-edge-connected near-brick with a
prescribed vertex matching is an odd wheel, is nonsolid, or has an
avoiding removable edge or removable doubleton. -/
theorem IsNearBrick.oddWheel_or_not_solid_or_removable (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    H.IsOddWheel v ∨ ¬ H.IsSolid ∨
      ∃ e, e ∉ M ∧ (∀ k, H.endAt e k ≠ v) ∧
        (H.IsRemovable e ∨ ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
          H.IsRemovableDoubleton e f) :=
  oddWheel_nearBrick_aux _ H rfl hn h3 v M hM

/-- The solid near-brick form used in the characteristic-three proof. -/
theorem IsNearBrick.oddWheel_or_removable_of_solid (hn : H.IsNearBrick)
    (h3 : H.IsThreeEdgeConnected) (hs : H.IsSolid)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    H.IsOddWheel v ∨ H.HasAvoidingRemovableClass v M := by
  rcases hn.oddWheel_or_not_solid_or_removable h3 hM with hw | hns | hr
  · exact Or.inl hw
  · exact (hns hs).elim
  · exact Or.inr hr

end GraphPuzzles.LoopMultigraph
