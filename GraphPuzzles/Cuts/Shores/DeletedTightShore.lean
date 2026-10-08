import GraphPuzzles.Reduction.Removable.RemovableContractionBasics
import GraphPuzzles.Matching.Bipartite.VertexMatchingBipartite
import GraphPuzzles.Cuts.CutCharacteristic
import GraphPuzzles.Reduction.Removable.EdgeDependence

/-! Tight shores created by deleting one edge of a brick, as used in
Campos–Lucchesi Proposition 6.3. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

private theorem vertexMatching_exceptional_edge_balance {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {e : E} (he : e ∈ M)
    {P : Finset (Finset.univ.erase e)} (hP : (H.deleteEdge e).IsPerfectMatching P)
    {c : V → Bool}
    (hc : ∀ f : Finset.univ.erase e,
      c ((H.deleteEdge e).endAt f 0) ≠ c ((H.deleteEdge e).endAt f 1)) :
    bipartiteSign c v * ((H.degreeIn M v : ℚ) - 1) =
      bipartiteSign c (H.endAt e 0) + bipartiteSign c (H.endAt e 1) := by
  let p := bipartiteSign c
  have hz : (∑ w, p w) = 0 := hP.on_univ.signed_sum_zero c (fun f _ ↦ hc f)
  have hsum : (∑ w, p w * H.weightedDegree (matchingVector M) w) =
      p v * ((H.degreeIn M v : ℚ) - 1) := by
    have hexpand : (∑ w, p w * H.weightedDegree (matchingVector M) w) =
        (∑ w, p w * ((H.degreeIn M w : ℚ) - 1)) + ∑ w, p w := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rw [weightedDegree_matchingVector]
      ring
    rw [hexpand, hz, add_zero, Finset.sum_eq_single v]
    · intro w _ hw
      rw [hM w hw]
      norm_num
    · simp
  have hh := sum_vertexWeight_degree (H := H) p (matchingVector M)
  rw [hsum, Finset.sum_eq_single e] at hh
  · simpa only [matchingVector, if_pos he, one_mul] using hh
  · intro f _ hfe
    have hfc := hc ⟨f, Finset.mem_erase.mpr ⟨hfe, Finset.mem_univ _⟩⟩
    have hp : p (H.endAt f 0) + p (H.endAt f 1) = 0 := by
      change c (H.endAt f 0) ≠ c (H.endAt f 1) at hfc
      cases h0 : c (H.endAt f 0) <;> cases h1 : c (H.endAt f 1) <;> simp_all [p, bipartiteSign]
    rw [hp, mul_zero]
  · simp

/-- Restoring an edge to a bipartite graph can make a vertex matching
use at most three edges at its exceptional vertex. -/
theorem IsVertexMatching.degree_le_three_of_bipartite_deleteEdge {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {e : E} (he : e ∈ M)
    {P : Finset (Finset.univ.erase e)} (hP : (H.deleteEdge e).IsPerfectMatching P)
    (hb : (H.deleteEdge e).IsBipartite) : H.degreeIn M v ≤ 3 := by
  obtain ⟨c, hc⟩ := hb
  have hh := vertexMatching_exceptional_edge_balance hM he hP hc
  by_contra hle
  have hd : (4 : ℚ) ≤ H.degreeIn M v := by exact_mod_cast (by omega : 4 ≤ H.degreeIn M v)
  cases hv : c v <;> cases h0 : c (H.endAt e 0) <;> cases h1 : c (H.endAt e 1) <;>
    simp only [bipartiteSign, hv, h0, h1, Bool.false_eq_true, ite_false, ite_true] at hh <;> linarith

/-- A restored edge supporting exceptional degree three has both ends
in the colour class of the exceptional vertex. -/
theorem IsVertexMatching.restored_edge_same_color_of_degree_three {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {e : E} (he : e ∈ M)
    {P : Finset (Finset.univ.erase e)} (hP : (H.deleteEdge e).IsPerfectMatching P)
    {c : V → Bool}
    (hc : ∀ f : Finset.univ.erase e,
      c ((H.deleteEdge e).endAt f 0) ≠ c ((H.deleteEdge e).endAt f 1))
    (h3 : H.degreeIn M v = 3) :
    c (H.endAt e 0) = c v ∧ c (H.endAt e 1) = c v := by
  have hh := vertexMatching_exceptional_edge_balance hM he hP hc
  rw [h3] at hh
  cases hv : c v <;> cases h0 : c (H.endAt e 0) <;> cases h1 : c (H.endAt e 1) <;>
    norm_num [bipartiteSign, hv, h0, h1] at hh
  all_goals exact ⟨rfl, rfl⟩

/-- If the restored graph is nonbipartite, the exceptional degree must
be three: degree one would itself supply a perfect matching making the
restored edge compatible with the old bipartition. -/
theorem IsVertexMatching.degree_three_of_bipartite_deleteEdge {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {e : E} (he : e ∈ M)
    {P : Finset (Finset.univ.erase e)} (hP : (H.deleteEdge e).IsPerfectMatching P)
    (hb : (H.deleteEdge e).IsBipartite) (hnb : ¬ H.IsBipartite) :
    H.degreeIn M v = 3 := by
  have hle := hM.degree_le_three_of_bipartite_deleteEdge he hP hb
  have heven : Even (Fintype.card V) := hP.isFractional.card_even
  have ho := hM.odd_hub_degree heven
  have hne : H.degreeIn M v ≠ 1 := by
    intro hv
    have hPM : H.IsPerfectMatching M := by
      intro w
      by_cases hw : w = v
      · simpa only [hw] using hv
      · exact hM w hw
    exact hnb (hP.bipartite_of_deleteEdge hPM he hb)
  rw [Nat.odd_iff] at ho
  omega

/-- A matching of an edge restriction keeps its exact crossing count
when its original edge labels are restored. -/
theorem exists_matching_crossing_of_restrictEdges {S : Finset E} {X : Finset V} {n : ℕ}
    (h : ∃ M, (H.restrictEdges S).IsPerfectMatching M ∧
      (M ∩ (H.restrictEdges S).dangling X).card = n) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = n := by
  obtain ⟨M, hM, hc⟩ := h
  exact ⟨M.image Subtype.val, hM.of_restrictEdges, (restrictEdges_crossing S M X).trans hc⟩

/-- Deleting edges can only increase the characteristic of a fixed cut. -/
theorem cutCharacteristic_le_restrictEdges (S : Finset E) (X : Finset V) :
    H.cutCharacteristic X ≤ (H.restrictEdges S).cutCharacteristic X := by
  apply Finset.min_mono
  intro n hn
  obtain ⟨hn, hgt⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr
    (exists_matching_crossing_of_restrictEdges (mem_matchingCrossings.mp hn)), hgt⟩

/-- Characteristic three in an edge-deleted graph proves characteristic
three in the original graph whenever the selected shore is odd. -/
theorem cutCharacteristic_eq_three_of_restrictEdges {S : Finset E} {X : Finset V}
    (ho : Odd X.card) (h : (H.restrictEdges S).cutCharacteristic X = 3) :
    H.cutCharacteristic X = 3 :=
  (cutCharacteristic_eq_three_iff ho).mpr
    (exists_matching_crossing_of_restrictEdges ((cutCharacteristic_eq_three_iff ho).mp h))

private theorem deleted_matching_crosses_once {e : E} (hr : H.IsRemovable e)
    {Y : Finset V} (hY : IsNontrivialCut Y) (ht : (H.deleteEdge e).IsTightCut Y) :
    ∃ P, (H.deleteEdge e).IsPerfectMatching P ∧
      (P ∩ (H.deleteEdge e).dangling Y).card = 1 := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := hY.1; omega : 0 < Y.card)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by have := hY.2; omega : 0 < (Finset.univ \ Y).card)
  obtain ⟨P, hP⟩ := (show (H.deleteEdge e).IsMatchingCovered from hr).exists_perfectMatching_of_ne
    (ne_of_mem_of_not_mem hx (Finset.mem_sdiff.mp hy).2)
  exact ⟨P, hP, ht P hP⟩

/-- A nontrivial tight shore newly created by deleting an edge of a
brick has a nonbipartite contraction before the edge is deleted. -/
theorem IsBrick.notBipartite_contract_of_deleted_tight (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {Y : Finset V} (hY : IsNontrivialCut Y)
    (ht : (H.deleteEdge e).IsTightCut Y) : ¬ (H.contract Y).IsBipartite := by
  obtain ⟨P, hP, hc⟩ := deleted_matching_crosses_once hr hY ht
  have hPc : ((P.image Subtype.val) ∩ H.dangling Y).card = 1 :=
    (restrictEdges_crossing _ P Y).trans hc
  intro hbi
  apply hb.tight_trivial Y ?_ hY
  intro M hM
  exact (hbi.contract_cut_count hM hP.of_restrictEdges).trans hPc

/-- Each bipartite expansion shore of a deleted-edge Petersen minor
contains an endpoint of the restored edge. -/
theorem IsBrick.edge_meets_deleted_tight_shore (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {Y : Finset V} (hY : IsNontrivialCut Y)
    (ht : (H.deleteEdge e).IsTightCut Y)
    (hbi : ((H.deleteEdge e).contract Y).IsBipartite) : e ∈ H.meets Y := by
  by_contra he
  exact hb.notBipartite_contract_of_deleted_tight hr hY ht
    ((deleteAwayContractIso Y e he).isBipartite hbi)

/-- The matching-count part of Campos–Lucchesi Proposition 6.3: every
perfect matching using the restored edge crosses each bipartite expansion
shore in precisely three edges. -/
theorem IsBrick.crossing_three_of_deleted_tight_shore (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {Y : Finset V} (hY : IsNontrivialCut Y)
    (ht : (H.deleteEdge e).IsTightCut Y)
    (hbi : ((H.deleteEdge e).contract Y).IsBipartite)
    {M : Finset E} (hM : H.IsPerfectMatching M) (he : e ∈ M) :
    (M ∩ H.dangling Y).card = 3 := by
  have hem := hb.edge_meets_deleted_tight_shore hr hY ht hbi
  let a : H.meets Y := ⟨e, hem⟩
  have hnb := hb.notBipartite_contract_of_deleted_tight hr hY ht
  have hdelete : ((H.contract Y).deleteEdge a).IsBipartite :=
    (deleteContractIso Y a).isBipartite hbi
  obtain ⟨P, hP, hPc⟩ := deleted_matching_crosses_once hr hY ht
  have hCP := hP.contract_of_crossing_one Y hPc
  have hCP' := (deleteContractIso Y a).isPerfectMatching hCP
  have hN : (H.contract Y).IsVertexMatching none (H.contractMatching Y M) := by
    intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some w => rw [contractMatching, contract_degreeIn_some]; exact hM w.1
  have hh := hN.degree_three_of_bipartite_deleteEdge
    ((mem_contractMatching Y M a).mpr he) hCP' hdelete hnb
  rwa [contractMatching_degreeIn_none] at hh

omit [DecidableEq E] in
/-- A fixed edge meets at most two pairwise disjoint vertex sets. -/
theorem card_disjoint_shores_met_by_edge_le_two {D : Finset (Finset V)}
    (hd : ∀ Y ∈ D, ∀ Z ∈ D, Y ≠ Z → Disjoint Y Z) (e : E) (he : ∀ Y ∈ D, e ∈ H.meets Y) : D.card ≤ 2 := by
  classical
  have hex (Y : D) : ∃ k : Fin 2, H.endAt e k ∈ Y.1 := mem_meets.mp (he Y.1 Y.2)
  choose k hk using hex
  have hinj : Function.Injective k := by
    intro Y Z heq
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hd Y.1 Y.2 Z.1 Z.2 hne) (hk Y) (heq.symm ▸ hk Z)
  have hh := Fintype.card_le_of_injective k hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hh

/-- The cardinality part of Proposition 6.3: there can be at most two
disjoint bipartite expansion shores created by deleting a single brick edge. -/
theorem IsBrick.card_deleted_tight_shores_le_two (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {D : Finset (Finset V)} (hd : ∀ Y ∈ D, ∀ Z ∈ D, Y ≠ Z → Disjoint Y Z)
    (hD : ∀ Y ∈ D, IsNontrivialCut Y ∧ (H.deleteEdge e).IsTightCut Y ∧
      ((H.deleteEdge e).contract Y).IsBipartite) : D.card ≤ 2 := by
  apply card_disjoint_shores_met_by_edge_le_two hd e
  intro Y hY
  obtain ⟨hnt, ht, hbi⟩ := hD Y hY
  exact hb.edge_meets_deleted_tight_shore hr hnt ht hbi

/-- If the restored edge is internal to the selected shore, every
disjoint expansion shore lying on one side of the selected cut lies on
that same side. -/
theorem IsBrick.deleted_tight_shore_subset (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {X Y : Finset V}
    (heX : ∀ k, H.endAt e k ∈ X) (hY : IsNontrivialCut Y)
    (ht : (H.deleteEdge e).IsTightCut Y)
    (hbi : ((H.deleteEdge e).contract Y).IsBipartite)
    (hside : Y ⊆ X ∨ Y ⊆ Finset.univ \ X) : Y ⊆ X := by
  rcases hside with h | h
  · exact h
  · obtain ⟨k, hk⟩ := mem_meets.mp (hb.edge_meets_deleted_tight_shore hr hY ht hbi)
    exact ((Finset.mem_sdiff.mp (h hk)).2 (heX k)).elim

/-- The bipartition of a tight shore created by deleting one edge. The
smaller side can reach outside the larger side only through that edge. -/
structure BipartiteRestorationShore (H : LoopMultigraph V E) (e : E) (Y : Finset V) where
  small : Finset V
  large : Finset V
  disjoint : Disjoint small large
  union_eq : small ∪ large = Y
  card_large : large.card = small.card + 1
  large_independent : ∀ f, ¬ (H.endAt f 0 ∈ large ∧ H.endAt f 1 ∈ large)
  other_edges : ∀ f, f ≠ e → ∀ k, H.endAt f k ∈ small → H.endAt f (Fin.rev k) ∈ large
  edge_meets_small : e ∈ H.meets small
  edge_avoids_large : ∀ k, H.endAt e k ∉ large

/-- The full local bipartition assertion of Campos–Lucchesi Proposition 6.3. -/
theorem IsBrick.bipartiteRestorationShore (hb : H.IsBrick)
    {e : E} (hr : H.IsRemovable e) {Y : Finset V} (hY : IsNontrivialCut Y)
    (ht : (H.deleteEdge e).IsTightCut Y)
    (hbi : ((H.deleteEdge e).contract Y).IsBipartite) :
    Nonempty (H.BipartiteRestorationShore e Y) := by
  classical
  have hem := hb.edge_meets_deleted_tight_shore hr hY ht hbi
  let a : H.meets Y := ⟨e, hem⟩
  have hdelete : ((H.contract Y).deleteEdge a).IsBipartite :=
    (deleteContractIso Y a).isBipartite hbi
  obtain ⟨c, hc⟩ := hdelete
  obtain ⟨P, hP, hPc⟩ := deleted_matching_crosses_once hr hY ht
  have hCP := (deleteContractIso Y a).isPerfectMatching (hP.contract_of_crossing_one Y hPc)
  obtain ⟨M, hM, heM⟩ := hb.matchingCovered.2 e
  have hN : (H.contract Y).IsVertexMatching none (H.contractMatching Y M) := by
    intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some w => rw [contractMatching, contract_degreeIn_some]; exact hM w.1
  have hthree : (H.contract Y).degreeIn (H.contractMatching Y M) none = 3 := by
    rw [contractMatching_degreeIn_none]
    exact hb.crossing_three_of_deleted_tight_shore hr hY ht hbi hM heM
  have hea := hN.restored_edge_same_color_of_degree_three
    ((mem_contractMatching Y M a).mpr heM) hCP hc hthree
  have hecolor (k : Fin 2) : c ((H.contract Y).endAt a k) = c none := by
    fin_cases k
    · exact hea.1
    · exact hea.2
  let A' : Finset Y := Finset.univ.filter fun w ↦ c (some w) = c none
  let B' : Finset Y := Finset.univ \ A'
  let A := A'.image Subtype.val
  let B := B'.image Subtype.val
  have hAY : A ⊆ Y := by
    intro w hw
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hw
    exact w.2
  have hBY : B ⊆ Y := by
    intro w hw
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hw
    exact w.2
  have hmemA (w : Y) : w.1 ∈ A ↔ c (some w) = c none := by
    simp [A, A']
  have hmemB (w : Y) : w.1 ∈ B ↔ c (some w) ≠ c none := by
    simp [B, B', A']
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    exact (hmemB ⟨w, hAY hwA⟩).mp hwB ((hmemA ⟨w, hAY hwA⟩).mp hwA)
  have hu : A ∪ B = Y := by
    apply Finset.Subset.antisymm (Finset.union_subset hAY hBY)
    intro w hw
    by_cases hcol : c (some ⟨w, hw⟩) = c none
    · exact Finset.mem_union_left _ ((hmemA ⟨w, hw⟩).mpr hcol)
    · exact Finset.mem_union_right _ ((hmemB ⟨w, hw⟩).mpr hcol)
  have hcard : B.card = A.card + 1 := by
    let S : Finset (Option Y) := Finset.univ.filter fun w ↦ c w = c none
    let T : Finset (Option Y) := Finset.univ.filter fun w ↦ c w ≠ c none
    have hS : S = insert none (A'.image some) := by
      ext w
      cases w <;> simp [S, A']
    have hT : T = B'.image some := by
      ext w
      cases w <;> simp [T, B', A']
    have hbal := card_sides_eq hc hCP (by decide : 0 < 1)
    have heq : S.card = T.card := by
      dsimp [S, T]
      cases hn : c none <;> simp only [Bool.not_eq_false, Bool.not_eq_true] <;> omega
    rw [hS, hT, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _),
      Finset.card_image_of_injective _ (Option.some_injective _)] at heq
    simpa only [A, B, Finset.card_image_of_injective _ Subtype.val_injective] using heq.symm
  refine ⟨⟨A, B, hd, hu, hcard, ?_, ?_, ?_, ?_⟩⟩
  · intro f hf
    have h0 := (hmemB ⟨_, hBY hf.1⟩).mp hf.1
    have h1 := (hmemB ⟨_, hBY hf.2⟩).mp hf.2
    by_cases hfe : f = e
    · subst f
      rw [← (contract_endAt_eq_some_iff Y a 0 ⟨_, hBY hf.1⟩).mpr rfl] at h0
      exact h0 (hecolor 0)
    let b : H.meets Y := ⟨f, mem_meets.mpr ⟨0, hBY hf.1⟩⟩
    have hba : b ≠ a := fun h ↦ hfe (congrArg Subtype.val h)
    have hh := hc ⟨b, Finset.mem_erase.mpr ⟨hba, Finset.mem_univ _⟩⟩
    change c ((H.contract Y).endAt b 0) ≠ c ((H.contract Y).endAt b 1) at hh
    rw [(contract_endAt_eq_some_iff Y b 0 ⟨_, hBY hf.1⟩).mpr rfl,
      (contract_endAt_eq_some_iff Y b 1 ⟨_, hBY hf.2⟩).mpr rfl] at hh
    have same {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
      cases x <;> cases y <;> cases z <;> simp_all
    exact hh (same h0 h1)
  · intro f hfe k hk
    have hkY := hAY hk
    let b : H.meets Y := ⟨f, mem_meets.mpr ⟨k, hkY⟩⟩
    have hba : b ≠ a := fun h ↦ hfe (congrArg Subtype.val h)
    have hbc := hc ⟨b, Finset.mem_erase.mpr ⟨hba, Finset.mem_univ _⟩⟩
    change c ((H.contract Y).endAt b 0) ≠ c ((H.contract Y).endAt b 1) at hbc
    have hkcol : c ((H.contract Y).endAt b k) = c none := by
      rw [(contract_endAt_eq_some_iff Y b k ⟨_, hkY⟩).mpr rfl]
      exact (hmemA ⟨_, hkY⟩).mp hk
    have hncol : c ((H.contract Y).endAt b (Fin.rev k)) ≠ c none := by
      intro hh
      fin_cases k
      · exact hbc (hkcol.trans hh.symm)
      · exact hbc (hh.trans hkcol.symm)
    have hoY : H.endAt f (Fin.rev k) ∈ Y := by
      by_contra hh
      exact hncol (congrArg c ((contract_endAt_eq_none_iff Y b _).mpr hh))
    apply (hmemB ⟨_, hoY⟩).mpr
    rw [← (contract_endAt_eq_some_iff Y b (Fin.rev k) ⟨_, hoY⟩).mpr rfl]
    exact hncol
  · obtain ⟨k, hk⟩ := mem_meets.mp hem
    apply mem_meets.mpr
    refine ⟨k, (hmemA ⟨_, hk⟩).mpr ?_⟩
    rw [← (contract_endAt_eq_some_iff Y a k ⟨_, hk⟩).mpr rfl]
    exact hecolor k
  · intro k hk
    have hkY := hBY hk
    have hh := (hmemB ⟨_, hkY⟩).mp hk
    rw [← (contract_endAt_eq_some_iff Y a k ⟨_, hkY⟩).mpr rfl] at hh
    exact hh (hecolor k)

end GraphPuzzles.LoopMultigraph
