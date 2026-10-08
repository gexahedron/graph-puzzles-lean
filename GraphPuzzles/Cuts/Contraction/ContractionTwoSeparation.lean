import GraphPuzzles.Cuts.Contraction.ContractionBarrierStructure
import GraphPuzzles.Bricks.BrickConnectivity

/-! Two-vertex separations in contractions of minimal separating cuts. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Splitting the excess crossing count between two nontrivial odd cuts in a
brick produces a strict predecessor retaining a chosen matching's excess. -/
theorem IsSeparatingCut.exists_strict_predecessor_of_crossing_sum {X Y Z : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick)
    (hYo : Odd Y.card) (hZo : Odd Z.card)
    (hY : IsNontrivialCut Y) (hZ : IsNontrivialCut Z)
    (hsum : ∀ N, H.IsPerfectMatching N →
      (N ∩ H.dangling Y).card + (N ∩ H.dangling Z).card =
        (N ∩ H.dangling X).card + 1)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card) :
    ∃ W, H.IsSeparatingCut W ∧ 1 < (M ∩ H.dangling W).card ∧ H.CutStrictlyPrecedes W X := by
  have pos {W : Finset V} (ho : Odd W.card) {N : Finset E} (hN : H.IsPerfectMatching N) :
      1 ≤ (N ∩ H.dangling W).card := by
    have hh := hN.isFractional.odd_cut W ho
    rw [cutWeight_matchingVector] at hh
    exact_mod_cast hh
  have step {A B : Finset V} (hoA : Odd A.card) (hoB : Odd B.card)
      (hntA : IsNontrivialCut A) (hntB : IsNontrivialCut B)
      (heq : ∀ N, H.IsPerfectMatching N →
        (N ∩ H.dangling A).card + (N ∩ H.dangling B).card =
          (N ∩ H.dangling X).card + 1)
      (hMA : 1 < (M ∩ H.dangling A).card) :
      H.IsSeparatingCut A ∧ 1 < (M ∩ H.dangling A).card ∧ H.CutStrictlyPrecedes A X := by
    have hp : H.CutPrecedes A X := by
      intro N hN
      have hh := heq N hN
      have hlo := pos hoB hN
      omega
    have hsep := hp.isSeparatingCut hs hg.matchingCovered.1 hoA
      (Finset.card_pos.mp (by have hh := hntA.1; omega))
      (Finset.card_pos.mp (by have hh := hntA.2; omega))
    have hnt : ¬ H.IsTightCut B := fun ht ↦ hg.tight_trivial B ht hntB
    simp only [IsTightCut, not_forall] at hnt
    obtain ⟨N, hN, hn⟩ := hnt
    have hh := heq N hN
    have hlo := pos hoB hN
    exact ⟨hsep, hMA, hp, N, hN, by omega⟩
  by_cases hMY : 1 < (M ∩ H.dangling Y).card
  · exact ⟨Y, step hYo hZo hY hZ hsum hMY⟩
  · have hh := hsum M hM
    refine ⟨Z, step hZo hYo hZ hY ?_ (by omega)⟩
    intro N hN
    simpa only [Nat.add_comm] using hsum N hN

namespace ContractionTwoSeparation

variable {X : Finset V} (v : X)
variable (F : (H.contract X).ComponentFamily {none, some v})

omit [DecidableEq E] in
theorem none_not_mem {Q : Finset (Option X)} (hQ : Q ∈ F.parts) : none ∉ Q :=
  fun h ↦ F.avoid Q hQ none h (by simp)

omit [DecidableEq E] in
theorem vertex_not_mem_source {Q : Finset (Option X)} (hQ : Q ∈ F.parts) :
    v.1 ∉ sourceShore X Q := by
  intro hv
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
  have hw' : some w ∈ Q := (Finset.mem_filter.mp hw).2
  have heq : w = v := Subtype.ext he
  exact F.avoid Q hQ (some v) (heq ▸ hw') (by simp)

omit [DecidableEq E] in
/-- The only exits from a lifted component inside the shore go to the retained separator vertex. -/
theorem source_closed {Q : Finset (Option X)} (hQ : Q ∈ F.parts) (e : E) (k : Fin 2)
    (hk : H.endAt e k ∈ sourceShore X Q) (hx : H.endAt e (Fin.rev k) ∈ X)
    (hv : H.endAt e (Fin.rev k) ≠ v.1) :
    H.endAt e (Fin.rev k) ∈ sourceShore X Q := by
  let f : H.meets X := ⟨e, mem_meets.mpr ⟨k, sourceShore_subset X Q hk⟩⟩
  have hk' : (H.contract X).endAt f k ∈ Q :=
    (contract_mem_sourceShore X Q (none_not_mem v F hQ) f k).mp hk
  have hn : (H.contract X).endAt f (Fin.rev k) ∉ ({none, some v} : Finset (Option X)) := by
    rw [contract_endAt, dif_pos hx]
    simp only [Finset.mem_insert, Finset.mem_singleton, Option.some_ne_none, false_or,
      Option.some.injEq]
    intro hh
    exact hv (congrArg Subtype.val hh)
  exact (contract_mem_sourceShore X Q (none_not_mem v F hQ) f (Fin.rev k)).mpr
    (F.closed Q hQ f k hk' hn)

/-- Components after deleting two vertices of a bicritical contraction are even. -/
theorem source_even (hb : (H.contract X).IsBicritical)
    {Q : Finset (Option X)} (hQ : Q ∈ F.parts) : Even (sourceShore X Q).card := by
  obtain ⟨P, hP⟩ := hb none (some v) (by simp)
  have hP' : (H.contract X).IsPerfectMatchingOn (Finset.univ \ {none, some v}) P := by
    have he : (Finset.univ.erase (none : Option X)).erase (some v) =
        Finset.univ \ {none, some v} := by ext w; simp; tauto
    rwa [he] at hP
  rw [card_sourceShore X Q (none_not_mem v F hQ)]
  exact F.even_parts_of_matching hP' hQ

theorem source_card_ge_two (hb : (H.contract X).IsBicritical)
    {Q : Finset (Option X)} (hQ : Q ∈ F.parts) : 2 ≤ (sourceShore X Q).card := by
  have he := source_even v F hb hQ
  have hp := Finset.card_pos.mpr (F.nonempty Q hQ)
  have hc := card_sourceShore X Q (none_not_mem v F hQ)
  rw [Nat.even_iff] at he
  omega

/-- The two lifted odd shores share only the retained separator vertex. -/
theorem crossing_sum {Q : Finset (Option X)} (hQ : Q ∈ F.parts)
    {M : Finset E} (hM : H.IsPerfectMatching M) :
    (M ∩ H.dangling (insert v.1 (sourceShore X Q))).card +
      (M ∩ H.dangling (X \ sourceShore X Q)).card = (M ∩ H.dangling X).card + 1 := by
  let R := sourceShore X Q
  have hRX : R ⊆ X := sourceShore_subset X Q
  have hvR : v.1 ∉ R := vertex_not_mem_source v F hQ
  have hI : insert v.1 R ∩ (X \ R) = {v.1} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hw | hw, _, hn⟩
      · exact hw
      · exact (hn hw).elim
    · rintro rfl
      exact ⟨Or.inl rfl, v.2, hvR⟩
  have hU : insert v.1 R ∪ (X \ R) = X := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro ((rfl | hr) | ⟨hx, _⟩)
      · exact v.2
      · exact hRX hr
      · exact hx
    · intro hx
      by_cases hr : w ∈ R
      · exact Or.inl (Or.inr hr)
      · exact Or.inr ⟨hx, hr⟩
  have hD : insert v.1 R \ (X \ R) = R := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hn⟩
      · subst w
        exact (hn ⟨v.2, hvR⟩).elim
      · exact hw
    · intro hw
      exact ⟨Or.inr hw, fun h ↦ h.2 hw⟩
  have hD' : (X \ R) \ insert v.1 R = X \ insert v.1 R := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    tauto
  have hempty : H.edgesBetween R (X \ insert v.1 R) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp h1
      have hv : H.endAt e 1 ≠ v.1 := fun hh ↦ hn (Finset.mem_insert.mpr (Or.inl hh))
      have hh := source_closed v F hQ e 0 h0 hx hv
      exact hn (Finset.mem_insert_of_mem hh)
    · obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp h0
      have hv : H.endAt e 0 ≠ v.1 := fun hh ↦ hn (Finset.mem_insert.mpr (Or.inl hh))
      have hh := source_closed v F hQ e 1 h1 hx hv
      exact hn (Finset.mem_insert_of_mem hh)
  have hsingle : H.cutWeight (matchingVector M) {v.1} = 1 := by
    have hlo := hM.isFractional.odd_cut {v.1} (by simp)
    have hhi := cutWeight_le_sum_weightedDegree (H := H) hM.isFractional.nonneg {v.1}
    simp only [Finset.sum_singleton, hM.isFractional.degree] at hhi
    exact le_antisymm hhi hlo
  have hh := cutWeight_modular (H := H) (matchingVector M) (insert v.1 R) (X \ R)
  rw [hI, hU, hD, hD', hempty, Finset.sum_empty, mul_zero, add_zero, hsingle] at hh
  simp only [cutWeight_matchingVector] at hh
  exact_mod_cast (hh.trans (add_comm _ _))

/-- A two-vertex separation through the contraction vertex would contradict
minimality: the two odd shores split the excess crossing count. -/
theorem parts_card_le_one_of_minimal (hb : (H.contract X).IsBicritical)
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) : F.parts.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro Q hQ R hR
  by_contra hne
  let A := insert v.1 (sourceShore X Q)
  let B := X \ sourceShore X Q
  have hvQ := vertex_not_mem_source v F hQ
  have hQeven := source_even v F hb hQ
  have hQ2 := source_card_ge_two v F hb hQ
  have hR2 := source_card_ge_two v F hb hR
  have hX := hM.nontrivial_of_crossing_gt_one hcross
  have hXodd := hs.odd_shore hg.matchingCovered.1 hX
  have hAo : Odd A.card := by
    rw [Finset.card_insert_of_notMem hvQ, Nat.odd_add_one]
    exact Nat.not_odd_iff_even.mpr hQeven
  have hBo : Odd B.card := by
    rw [Finset.card_sdiff_of_subset (sourceShore_subset X Q)]
    have hle := Finset.card_le_card (sourceShore_subset X Q)
    rw [Nat.odd_iff] at hXodd ⊢
    rw [Nat.even_iff] at hQeven
    omega
  have hAX : A ⊆ X := Finset.insert_subset v.2 (sourceShore_subset X Q)
  have hBX : B ⊆ X := Finset.sdiff_subset
  have compl_large {Y : Finset V} (hYX : Y ⊆ X) : 2 ≤ (Finset.univ \ Y).card := by
    apply hX.2.trans
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy ↦ (Finset.mem_sdiff.mp hw).2 (hYX hy)⟩
  have hAnt : IsNontrivialCut A :=
    ⟨hQ2.trans (Finset.card_le_card (Finset.subset_insert _ _)), compl_large hAX⟩
  have hBnt : IsNontrivialCut B := by
    refine ⟨hR2.trans (Finset.card_le_card ?_), compl_large hBX⟩
    intro w hw
    refine Finset.mem_sdiff.mpr ⟨sourceShore_subset X R hw, ?_⟩
    exact Finset.disjoint_left.mp
      (ContractionBarrier.source_disjoint F hR hQ (Ne.symm hne)) hw
  obtain ⟨Y, hsY, hMY, hpY⟩ := hs.exists_strict_predecessor_of_crossing_sum hg
    hAo hBo hAnt hBnt (fun _ hN ↦ crossing_sum v F hQ hN) hM hcross
  exact hmin Y hsY hMY hpY.1 hpY

end ContractionTwoSeparation

/-- Deleting the contraction vertex and one other vertex leaves a connected
graph when the contraction is bicritical and the separating cut is minimal. -/
theorem IsSeparatingCut.connected_delete_pole_of_minimal {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) (hb : (H.contract X).IsBicritical)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X)
    (v : X) (c : Option X → Bool)
    (hc : ∀ e, (H.contract X).endAt e 0 ∉ ({none, some v} : Finset (Option X)) →
      (H.contract X).endAt e 1 ∉ ({none, some v} : Finset (Option X)) →
      c ((H.contract X).endAt e 0) = c ((H.contract X).endAt e 1)) :
    ∀ a, a ∉ ({none, some v} : Finset (Option X)) →
      ∀ b, b ∉ ({none, some v} : Finset (Option X)) → c a = c b := by
  obtain ⟨F, hF⟩ := exists_componentFamily_of_coloring (H := H.contract X) {none, some v} c hc
  have hcard := ContractionTwoSeparation.parts_card_le_one_of_minimal v F hb hs hg hM hcross hmin
  intro a ha b hb
  obtain ⟨Q, hQ, haQ⟩ := F.cover a ha
  obtain ⟨R, hR, hbR⟩ := F.cover b hb
  have heq := Finset.card_le_one.mp hcard Q hQ R hR
  subst R
  exact hF Q hQ a haQ b hbR

/-- Two retained vertices cannot separate a contraction of a brick: lift a
locally constant colouring and use connectivity after deleting the original pair. -/
theorem IsBrick.contract_connected_delete_pair_away (hg : H.IsBrick)
    {X : Finset V} (hXC : (Finset.univ \ X).Nonempty) (u v : X) (huv : u ≠ v)
    (c : Option X → Bool)
    (hc : ∀ e, (H.contract X).endAt e 0 ∉ ({some u, some v} : Finset (Option X)) →
      (H.contract X).endAt e 1 ∉ ({some u, some v} : Finset (Option X)) →
      c ((H.contract X).endAt e 0) = c ((H.contract X).endAt e 1)) :
    ∀ a, a ∉ ({some u, some v} : Finset (Option X)) →
      ∀ b, b ∉ ({some u, some v} : Finset (Option X)) → c a = c b := by
  let d : V → Bool := c ∘ contractVertex X
  have hd : ∀ e, H.endAt e 0 ∉ ({u.1, v.1} : Finset V) →
      H.endAt e 1 ∉ ({u.1, v.1} : Finset V) → d (H.endAt e 0) = d (H.endAt e 1) := by
    intro e h0 h1
    by_cases he : e ∈ H.meets X
    · have h0' : (H.contract X).endAt ⟨e, he⟩ 0 ∉
          ({some u, some v} : Finset (Option X)) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton,
          contract_endAt_eq_some_iff] using h0
      have h1' : (H.contract X).endAt ⟨e, he⟩ 1 ∉
          ({some u, some v} : Finset (Option X)) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton,
          contract_endAt_eq_some_iff] using h1
      simpa only [d, Function.comp_apply, contractVertex, contract_endAt] using hc ⟨e, he⟩ h0' h1'
    · have hn (k : Fin 2) : H.endAt e k ∉ X := fun h ↦ he (mem_meets.mpr ⟨k, h⟩)
      simp [d, contractVertex, hn]
  have hval : u.1 ≠ v.1 := fun he ↦ huv (Subtype.ext he)
  have hdall := hg.connected_delete_pair hg.matchingCovered.loopless u.1 v.1 hval d hd
  have lift (a : Option X) (ha : a ∉ ({some u, some v} : Finset (Option X))) :
      ∃ w : V, w ∉ ({u.1, v.1} : Finset V) ∧ contractVertex X w = a := by
    cases a with
    | none =>
      obtain ⟨w, hw⟩ := hXC
      have hn : w ∉ X := (Finset.mem_sdiff.mp hw).2
      have hwu : w ≠ u.1 := fun he ↦ hn (he.symm ▸ u.2)
      have hwv : w ≠ v.1 := fun he ↦ hn (he.symm ▸ v.2)
      exact ⟨w, by simp [hwu, hwv], by simp [contractVertex, hn]⟩
    | some w =>
      refine ⟨w.1, ?_, by simp [contractVertex, w.2]⟩
      intro hw
      rcases Finset.mem_insert.mp hw with hu | hv
      · exact ha (Finset.mem_insert.mpr (Or.inl (congrArg some (Subtype.ext hu))))
      · exact ha (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_singleton.mpr (congrArg some (Subtype.ext (Finset.mem_singleton.mp hv))))))
  intro a ha b hb
  obtain ⟨w, hw, hwa⟩ := lift a ha
  obtain ⟨z, hz, hzb⟩ := lift b hb
  simpa only [d, Function.comp_apply, hwa, hzb] using hdall w hw z hz

/-- Every pair deletion is connected in a bicritical contraction of a minimal
separating cut. The remaining step to call it a brick is the tight-cut characterization. -/
theorem IsSeparatingCut.connected_delete_pair_of_minimal_bicritical {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) (hb : (H.contract X).IsBicritical)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X)
    (u v : Option X) (huv : u ≠ v) (c : Option X → Bool)
    (hc : ∀ e, (H.contract X).endAt e 0 ∉ ({u, v} : Finset (Option X)) →
      (H.contract X).endAt e 1 ∉ ({u, v} : Finset (Option X)) →
      c ((H.contract X).endAt e 0) = c ((H.contract X).endAt e 1)) :
    ∀ a, a ∉ ({u, v} : Finset (Option X)) →
      ∀ b, b ∉ ({u, v} : Finset (Option X)) → c a = c b := by
  cases u with
  | none =>
    cases v with
    | none => exact (huv rfl).elim
    | some v => exact hs.connected_delete_pole_of_minimal hg hb hM hcross hmin v c hc
  | some u =>
    cases v with
    | none =>
      have hc' : ∀ e, (H.contract X).endAt e 0 ∉ ({none, some u} : Finset (Option X)) →
          (H.contract X).endAt e 1 ∉ ({none, some u} : Finset (Option X)) →
          c ((H.contract X).endAt e 0) = c ((H.contract X).endAt e 1) := by
        simpa only [Finset.pair_comm] using hc
      simpa only [Finset.pair_comm] using
        hs.connected_delete_pole_of_minimal hg hb hM hcross hmin u c hc'
    | some v =>
      have hX := hM.nontrivial_of_crossing_gt_one hcross
      exact hg.contract_connected_delete_pair_away
        (Finset.card_pos.mp (by have hh := hX.2; omega)) u v
        (fun he ↦ huv (congrArg some he)) c hc

theorem IsSeparatingCut.connectedAfterDeletingPairs_of_minimal_bicritical {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) (hb : (H.contract X).IsBicritical)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    (H.contract X).ConnectedAfterDeletingPairs :=
  hs.connected_delete_pair_of_minimal_bicritical hg hb hM hcross hmin

end GraphPuzzles.LoopMultigraph
