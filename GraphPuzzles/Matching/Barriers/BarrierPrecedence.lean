import GraphPuzzles.Matching.Barriers.MatchingBarrier
import GraphPuzzles.Cuts.CutOrder
import GraphPuzzles.Cuts.SeparatingCutLift
import GraphPuzzles.Cuts.Contraction.BipartiteExpansion

/-!
# Barriers at a contraction vertex and cut precedence

For a barrier containing the contraction vertex, the sum of the excess crossing
counts of its odd components equals the excess crossing count of the original
cut. In particular, every lifted component cut precedes the original cut.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- Barrier incidence equality also applies to weights that are not fractional matchings. -/
theorem IsBarrier.sum_cutWeight_eq_sum_degree (hb : F.IsBarrier)
    (hm : H.IsMatchingCovered) (x : E → ℚ) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) = ∑ v ∈ Z, H.weightedDegree x v := by
  rw [sum_weightedDegree]
  simp only [hb.endsIn F hm, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  symm
  apply Finset.sum_biUnion
  intro Q hQ R hR hne
  exact F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne

/-- A nonempty barrier in a matching-covered graph has no even components. -/
theorem IsBarrier.mem_odd_of_mem (hb : F.IsBarrier) (hm : H.IsMatchingCovered)
    (hZ : Z.Nonempty) {Q : Finset V} (hQ : Q ∈ F.parts) : Q ∈ F.odd := by
  by_contra hnQ
  have hQC : (Finset.univ \ Q).Nonempty := by
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q hQ z h hz⟩⟩
  obtain ⟨e, he⟩ := hm.1.dangling_nonempty (F.nonempty Q hQ) hQC
  obtain ⟨k, _, _, hkZ⟩ := F.exists_end_of_mem_dangling hQ he
  have hp : 0 < H.endsIn Z e := Finset.card_pos.mpr
    ⟨Fin.rev k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkZ⟩⟩
  have hh := hb.endsIn F hm e
  have hu : e ∈ F.odd.biUnion H.dangling := by
    by_contra hn
    rw [if_neg hn] at hh
    omega
  obtain ⟨R, hR, heR⟩ := Finset.mem_biUnion.mp hu
  have hne : Q ≠ R := fun heq ↦ hnQ (heq.symm ▸ hR)
  exact Finset.disjoint_left.mp (F.disjoint_dangling hQ (F.mem_odd.mp hR).1 hne) he heR

/-- If all other barrier components are singletons, the complement of one component
is bipartite. The barrier itself is one colour class. -/
theorem IsBarrier.bipartiteOn_compl (hb : F.IsBarrier) (hm : H.IsMatchingCovered)
    (hZ : Z.Nonempty) {Q : Finset V}
    (hsingle : ∀ R ∈ F.odd, R ≠ Q → R.card = 1) :
    H.IsBipartiteOn (Finset.univ \ Q) := by
  refine ⟨fun v ↦ decide (v ∈ Z), ?_⟩
  intro e h0 h1
  by_cases hz0 : H.endAt e 0 ∈ Z
  · have hn1 : H.endAt e 1 ∉ Z := by
      intro hz1
      have hh := hb.endsIn F hm e
      have hall : ∀ k : Fin 2, H.endAt e k ∈ Z := by
        intro k
        fin_cases k <;> assumption
      have ht : H.endsIn Z e = 2 := by
        simp [LoopMultigraph.endsIn, hall]
      rw [ht] at hh
      split_ifs at hh; omega
    simp [hz0, hn1]
  · have hz1 : H.endAt e 1 ∈ Z := by
      by_contra hn1
      obtain ⟨R, hR, hvR⟩ := F.cover _ hz0
      have hrQ : R ≠ Q := fun heq ↦ (Finset.mem_sdiff.mp h0).2 (heq ▸ hvR)
      have hcard := hsingle R (hb.mem_odd_of_mem F hm hZ hR) hrQ
      have hvR' : H.endAt e 1 ∈ R := F.closed R hR e 0 hvR hn1
      exact hm.loopless e (Finset.card_le_one_iff.mp hcard.le hvR hvR')
    simp [hz0, hz1]

/-- The bipartite middle graph is obtained by contracting the exceptional component. -/
theorem IsBarrier.bipartite_contract_compl (hb : F.IsBarrier) (hm : H.IsMatchingCovered)
    (hZ : Z.Nonempty) {Q : Finset V} (hQ : Q ∈ F.odd)
    (hsingle : ∀ R ∈ F.odd, R ≠ Q → R.card = 1) :
    (H.contract (Finset.univ \ Q)).IsBipartite := by
  have hQC : (Finset.univ \ Q).Nonempty := by
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦
      F.avoid Q (F.mem_odd.mp hQ).1 z h hz⟩⟩
  have hsep := (hb.isTightCut F hQ).isSeparatingCut hm
    (F.nonempty Q (F.mem_odd.mp hQ).1) hQC
  exact (hb.bipartiteOn_compl F hm hZ hsingle).contract_of_separating hsep.compl

end ComponentFamily

namespace ContractionBarrier

variable {X : Finset V} {B : Finset (Option X)}
variable (F : (H.contract X).ComponentFamily B)

omit [DecidableEq E] in
theorem none_not_mem {Q : Finset (Option X)} (hn : none ∈ B) (hQ : Q ∈ F.parts) :
    none ∉ Q := fun h ↦ F.avoid Q hQ none h hn

omit [DecidableEq E] in
theorem source_odd {Q : Finset (Option X)} (hn : none ∈ B) (hQ : Q ∈ F.odd) :
    Odd (sourceShore X Q).card := by
  rw [card_sourceShore X Q (none_not_mem F hn (F.mem_odd.mp hQ).1)]
  exact (F.mem_odd.mp hQ).2

/-- A perfect matching can have arbitrary degree at the contracted vertex.
Barrier equality accounts exactly for the excess at that vertex. -/
theorem sum_crossing (hb : F.IsBarrier) (hm : (H.contract X).IsMatchingCovered)
    (hn : none ∈ B) {M : Finset E} (hM : H.IsPerfectMatching M) :
    (∑ Q ∈ F.odd, (M ∩ H.dangling (sourceShore X Q)).card) + 1 =
      B.card + (M ∩ H.dangling X).card := by
  have hs := hb.sum_cutWeight_eq_sum_degree F hm (fun e ↦ matchingVector M e.1)
  have hleft : (∑ Q ∈ F.odd,
      (H.contract X).cutWeight (fun e ↦ matchingVector M e.1) Q) =
      ∑ Q ∈ F.odd, ((M ∩ H.dangling (sourceShore X Q)).card : ℚ) := by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [contract_cutWeight_sourceShore X Q
      (none_not_mem F hn (F.mem_odd.mp hQ).1), cutWeight_matchingVector]
  have hright : (∑ v ∈ B,
      (H.contract X).weightedDegree (fun e ↦ matchingVector M e.1) v) =
      ((B.erase none).card : ℚ) + (M ∩ H.dangling X).card := by
    rw [← Finset.sum_erase_add B
      (fun v ↦ (H.contract X).weightedDegree (fun e ↦ matchingVector M e.1) v) hn,
      contract_weightedDegree_none,
      cutWeight_matchingVector]
    congr 1
    calc
      (∑ v ∈ B.erase none,
          (H.contract X).weightedDegree (fun e ↦ matchingVector M e.1) v) =
          ∑ _v ∈ B.erase none, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro v hv
        cases v with
        | none => simp at hv
        | some v =>
          exact (contract_weightedDegree_some X (matchingVector M) v).trans
            (hM.isFractional.degree v.1)
      _ = _ := by simp
  rw [hleft, hright] at hs
  have hcard := Finset.card_erase_add_one hn
  have hnat : (∑ Q ∈ F.odd, (M ∩ H.dangling (sourceShore X Q)).card) =
      (B.erase none).card + (M ∩ H.dangling X).card := by
    exact_mod_cast hs
  omega

/-- Every odd component contributes at least one crossing to any original matching. -/
theorem crossing_pos (hn : none ∈ B) {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    {M : Finset E} (hM : H.IsPerfectMatching M) :
    1 ≤ (M ∩ H.dangling (sourceShore X Q)).card := by
  have hh := hM.isFractional.odd_cut _ (source_odd F hn hQ)
  rw [cutWeight_matchingVector] at hh
  exact_mod_cast hh

/-- A component cut precedes the outer cut for every perfect matching. -/
theorem precedes (hb : F.IsBarrier) (hm : (H.contract X).IsMatchingCovered)
    (hn : none ∈ B) {Q : Finset (Option X)} (hQ : Q ∈ F.odd) :
    H.CutPrecedes (sourceShore X Q) X := by
  intro M hM
  have hs := sum_crossing F hb hm hn hM
  have hrest : (F.odd.erase Q).card ≤
      ∑ R ∈ F.odd.erase Q, (M ∩ H.dangling (sourceShore X R)).card := by
    calc
      _ = ∑ _R ∈ F.odd.erase Q, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun R hR ↦ crossing_pos F hn (Finset.mem_of_mem_erase hR) hM
  have he := Finset.sum_erase_add F.odd
    (fun R ↦ (M ∩ H.dangling (sourceShore X R)).card) hQ
  have hc := Finset.card_erase_add_one hQ
  have hcard : F.odd.card = B.card := hb
  omega

/-- If the outer cut is crossed more than once, some odd component retains that property. -/
theorem exists_crossing_gt_one (hb : F.IsBarrier) (hm : (H.contract X).IsMatchingCovered)
    (hn : none ∈ B) {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcross : 1 < (M ∩ H.dangling X).card) :
    ∃ Q ∈ F.odd, 1 < (M ∩ H.dangling (sourceShore X Q)).card := by
  by_contra hnQ
  push Not at hnQ
  have hsum : (∑ Q ∈ F.odd, (M ∩ H.dangling (sourceShore X Q)).card) ≤ F.odd.card := by
    calc
      _ ≤ ∑ _Q ∈ F.odd, 1 := Finset.sum_le_sum hnQ
      _ = _ := by simp
  have hs := sum_crossing F hb hm hn hM
  have hcard : F.odd.card = B.card := hb
  omega

/-- A second component with excess crossings makes precedence strict. -/
theorem crossing_lt_of_other (hb : F.IsBarrier) (hm : (H.contract X).IsMatchingCovered)
    (hn : none ∈ B) {Q R : Finset (Option X)} (hQ : Q ∈ F.odd) (hR : R ∈ F.odd)
    (hne : R ≠ Q) {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcross : 1 < (M ∩ H.dangling (sourceShore X R)).card) :
    (M ∩ H.dangling (sourceShore X Q)).card < (M ∩ H.dangling X).card := by
  have hrest : (F.odd.erase Q).card <
      ∑ T ∈ F.odd.erase Q, (M ∩ H.dangling (sourceShore X T)).card := by
    calc
      _ = ∑ _T ∈ F.odd.erase Q, 1 := by simp
      _ < _ := Finset.sum_lt_sum
        (fun T hT ↦ crossing_pos F hn (Finset.mem_of_mem_erase hT) hM)
        ⟨R, Finset.mem_erase.mpr ⟨hne, hR⟩, hcross⟩
  have hs := sum_crossing F hb hm hn hM
  have he := Finset.sum_erase_add F.odd
    (fun T ↦ (M ∩ H.dangling (sourceShore X T)).card) hQ
  have hc := Finset.card_erase_add_one hQ
  have hcard : F.odd.card = B.card := hb
  omega

/-- Unless every other lifted component is tight, the component strictly precedes the cut. -/
theorem strictlyPrecedes_of_other_not_tight (hb : F.IsBarrier)
    (hm : (H.contract X).IsMatchingCovered) (hn : none ∈ B)
    {Q R : Finset (Option X)} (hQ : Q ∈ F.odd) (hR : R ∈ F.odd) (hne : R ≠ Q)
    (hnt : ¬ H.IsTightCut (sourceShore X R)) :
    H.CutStrictlyPrecedes (sourceShore X Q) X := by
  refine ⟨precedes F hb hm hn hQ, ?_⟩
  simp only [IsTightCut, not_forall] at hnt
  obtain ⟨M, hM, hneM⟩ := hnt
  have hp := crossing_pos F hn hR hM
  exact ⟨M, hM, crossing_lt_of_other F hb hm hn hQ hR hne hM (by omega)⟩

/-- When all other components are tight, the selected cut is matching-equivalent to the outer cut. -/
theorem matchingEquivalent_of_others_tight (hb : F.IsBarrier)
    (hm : (H.contract X).IsMatchingCovered) (hn : none ∈ B)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    (ht : ∀ R ∈ F.odd, R ≠ Q → H.IsTightCut (sourceShore X R)) :
    H.MatchingEquivalentCuts (sourceShore X Q) X := by
  intro M hM
  have hrest : (∑ R ∈ F.odd.erase Q, (M ∩ H.dangling (sourceShore X R)).card) =
      (F.odd.erase Q).card := by
    calc
      _ = ∑ _R ∈ F.odd.erase Q, 1 := by
        apply Finset.sum_congr rfl
        intro R hR
        obtain ⟨hne, hR⟩ := Finset.mem_erase.mp hR
        exact ht R hR hne M hM
      _ = _ := by simp
  have hs := sum_crossing F hb hm hn hM
  have he := Finset.sum_erase_add F.odd
    (fun R ↦ (M ∩ H.dangling (sourceShore X R)).card) hQ
  have hc := Finset.card_erase_add_one hQ
  have hcard : F.odd.card = B.card := hb
  omega

/-- The component cuts are separating whenever the outer cut is separating. -/
theorem separating (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hn : none ∈ B) (hXC : (Finset.univ \ X).Nonempty)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd) :
    H.IsSeparatingCut (sourceShore X Q) := by
  apply (precedes F hb hs.1 hn hQ).isSeparatingCut hs hc (source_odd F hn hQ)
  · apply Finset.card_pos.mp
    rw [card_sourceShore X Q (none_not_mem F hn (F.mem_odd.mp hQ).1)]
    exact Finset.card_pos.mpr (F.nonempty Q (F.mem_odd.mp hQ).1)
  · obtain ⟨v, hv⟩ := hXC
    exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦
      (Finset.mem_sdiff.mp hv).2 (sourceShore_subset X Q h)⟩⟩

/-- A separating predecessor retains a specified matching's multiple crossings. -/
theorem exists_separating_predecessor (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hn : none ∈ B) {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcross : 1 < (M ∩ H.dangling X).card) :
    ∃ Q ∈ F.odd, H.IsSeparatingCut (sourceShore X Q) ∧
      H.CutPrecedes (sourceShore X Q) X ∧
      1 < (M ∩ H.dangling (sourceShore X Q)).card := by
  obtain ⟨Q, hQ, hMQ⟩ := exists_crossing_gt_one F hb hs.1 hn hM hcross
  have hX := hM.nontrivial_of_crossing_gt_one hcross
  exact ⟨Q, hQ, separating F hb hs hc hn
    (Finset.card_pos.mp (by have hh := hX.2; omega)) hQ,
    precedes F hb hs.1 hn hQ, hMQ⟩

/-- Minimality in the crossing-count order forces the other component cuts to be tight. -/
theorem others_tight_of_minimal (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hn : none ∈ B) {M : Finset E} (hM : H.IsPerfectMatching M)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    (hcross : 1 < (M ∩ H.dangling (sourceShore X Q)).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    ∀ R ∈ F.odd, R ≠ Q → H.IsTightCut (sourceShore X R) := by
  intro R hR hne
  by_contra hnt
  have hcrossX : 1 < (M ∩ H.dangling X).card :=
    lt_of_lt_of_le hcross (precedes F hb hs.1 hn hQ M hM)
  have hX := hM.nontrivial_of_crossing_gt_one hcrossX
  have hsep := separating F hb hs hc hn
    (Finset.card_pos.mp (by have hh := hX.2; omega)) hQ
  exact hmin _ hsep hcross (precedes F hb hs.1 hn hQ)
    (strictlyPrecedes_of_other_not_tight F hb hs.1 hn hQ hR hne hnt)

omit [DecidableEq E] in
theorem source_disjoint {Q R : Finset (Option X)} (hQ : Q ∈ F.parts) (hR : R ∈ F.parts)
    (hne : Q ≠ R) : Disjoint (sourceShore X Q) (sourceShore X R) := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hvR
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hvQ
  obtain ⟨r, hr, her⟩ := Finset.mem_image.mp hvR
  have hqr : q = r := Subtype.ext (heq.trans her.symm)
  have hqQ : some q ∈ Q := (Finset.mem_filter.mp hq).2
  have hqR : some q ∈ R := hqr.symm ▸ (Finset.mem_filter.mp hr).2
  exact Finset.disjoint_left.mp (F.pairwise Q hQ R hR hne) hqQ hqR

/-- In a brick, the other components of a minimal-cut barrier are singletons. -/
theorem other_card_one_of_minimal (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hg : H.IsBrick) (hn : none ∈ B) {M : Finset E} (hM : H.IsPerfectMatching M)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    (hcross : 1 < (M ∩ H.dangling (sourceShore X Q)).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X)
    {R : Finset (Option X)} (hR : R ∈ F.odd) (hne : R ≠ Q) : R.card = 1 := by
  have ht := others_tight_of_minimal F hb hs hg.matchingCovered.1 hn hM hQ hcross hmin R hR hne
  have htriv := hg.tight_trivial _ ht
  have hQcard := (hM.nontrivial_of_crossing_gt_one hcross).1
  have hdis := source_disjoint F (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne.symm
  have hsub : sourceShore X Q ⊆ Finset.univ \ sourceShore X R := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hdis hv⟩
  have hc := Finset.card_le_card hsub
  have he := card_sourceShore X R (none_not_mem F hn (F.mem_odd.mp hR).1)
  have hp := Finset.card_pos.mpr (F.nonempty R (F.mem_odd.mp hR).1)
  by_contra hnR
  apply htriv
  exact ⟨by omega, by omega⟩

/-- The barrier case of minimal-cut reduction: a proper smaller shore retains the
matching counts, and the discarded middle contraction is bipartite. -/
theorem exists_reduction_of_minimal (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hg : H.IsBrick) (hn : none ∈ B) (hB : 2 ≤ B.card)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    ∃ Q ∈ F.odd, IsNontrivialCut Q ∧
      (H.contract X).IsTightCut Q ∧
      H.IsSeparatingCut (sourceShore X Q) ∧
      H.MatchingEquivalentCuts (sourceShore X Q) X ∧
      ((H.contract X).contract (Finset.univ \ Q)).IsBipartite ∧
      (sourceShore X Q).card < X.card := by
  obtain ⟨Q, hQ, hsep, _, hMQ⟩ :=
    exists_separating_predecessor F hb hs hg.matchingCovered.1 hn hM hcross
  have hnQ := none_not_mem F hn (F.mem_odd.mp hQ).1
  have hecard := card_sourceShore X Q hnQ
  have hsub : B ⊆ Finset.univ \ Q := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q (F.mem_odd.mp hQ).1 v h hv⟩
  have hBcard := Finset.card_le_card hsub
  have hQcard := (hM.nontrivial_of_crossing_gt_one hMQ).1
  have hQnt : IsNontrivialCut Q := ⟨by omega, by omega⟩
  have hsingle : ∀ R ∈ F.odd, R ≠ Q → R.card = 1 :=
    fun R hR hne ↦ other_card_one_of_minimal F hb hs hg hn hM hQ hMQ hmin hR hne
  refine ⟨Q, hQ, hQnt, hb.isTightCut F hQ, hsep,
    matchingEquivalent_of_others_tight F hb hs.1 hn hQ
      (others_tight_of_minimal F hb hs hg.matchingCovered.1 hn hM hQ hMQ hmin),
    hb.bipartite_contract_compl F hs.1 ⟨none, hn⟩ hQ hsingle, ?_⟩
  have hsum : Q.card + (Finset.univ \ Q).card = X.card + 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Q), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe]
    have hle := Finset.card_le_univ Q
    rw [Fintype.card_option, Fintype.card_coe] at hle
    omega
  have hc := hQnt.2
  omega

end ContractionBarrier

end GraphPuzzles.LoopMultigraph
