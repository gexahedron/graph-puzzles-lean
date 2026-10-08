import GraphPuzzles.Bricks.BicriticalSplicing
import GraphPuzzles.Cuts.Contraction.BipartiteExpansion

/-! Connectivity and brickness when splicing brick contractions. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- The pair-deletion colouring criterion also gives connectivity of its shore. -/
theorem ConnectedAfterDeletingPairs.connectedOn_erase_pair
    (hc : H.ConnectedAfterDeletingPairs) (u v : V) (huv : u ≠ v) :
    H.IsConnectedOn ((Finset.univ.erase u).erase v) := by
  intro c he a ha b hb
  apply hc u v huv c
  · intro e h0 h1
    apply he e
    · simpa only [Finset.mem_erase, Finset.mem_univ, and_true, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using h0
    · simpa only [Finset.mem_erase, Finset.mem_univ, and_true, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using h1
  · simpa only [Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using ha
  · simpa only [Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using hb

omit [Fintype V] in
private theorem contractVertex_eq_some (X : Finset V) (w : V) (u : X) :
    contractVertex X w = some u ↔ w = u.1 := by
  by_cases hw : w ∈ X
  · simp only [contractVertex, dif_pos hw, Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [contractVertex, dif_neg hw, reduceCtorEq, false_iff]
    exact fun h ↦ hw (h ▸ u.2)

private theorem connected_pair_same_shore {X : Finset V}
    (hs : H.IsSeparatingCut X) (hl : (H.contract X).ConnectedAfterDeletingPairs)
    (hXC : (Finset.univ \ X).Nonempty) {u v : V} (hu : u ∈ X) (hv : v ∈ X)
    (huv : u ≠ v) (c : V → Bool)
    (he : ∀ e, H.endAt e 0 ∉ ({u, v} : Finset V) → H.endAt e 1 ∉ ({u, v} : Finset V) →
      c (H.endAt e 0) = c (H.endAt e 1)) :
    ∀ a, a ∉ ({u, v} : Finset V) → ∀ b, b ∉ ({u, v} : Finset V) → c a = c b := by
  obtain ⟨w, hw⟩ := hXC
  have hout : ∀ a ∈ Finset.univ \ X, a ∉ ({u, v} : Finset V) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ (Finset.mem_sdiff.mp ha).2 (h ▸ hu),
      fun h ↦ (Finset.mem_sdiff.mp ha).2 (h ▸ hv)⟩
  have hconst (a : V) (ha : a ∉ X) : c a = c w :=
    hs.compl.connectedOn c (fun e h0 h1 ↦ he e (hout _ h0) (hout _ h1))
      a (by simp [ha]) w hw
  let d : Option X → Bool := fun z ↦ z.elim (c w) (fun z ↦ c z.1)
  have hd (a : V) : d (contractVertex X a) = c a := by
    by_cases ha : a ∈ X
    · simp [d, contractVertex, ha]
    · simpa only [d, contractVertex, dif_neg ha, Option.elim_none] using (hconst a ha).symm
  have hdel (a : V) : contractVertex X a ∉ ({some ⟨u, hu⟩, some ⟨v, hv⟩} : Finset (Option X)) ↔
      a ∉ ({u, v} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, contractVertex_eq_some]
  have hed (e : H.meets X)
      (h0 : (H.contract X).endAt e 0 ∉ ({some ⟨u, hu⟩, some ⟨v, hv⟩} : Finset (Option X)))
      (h1 : (H.contract X).endAt e 1 ∉ ({some ⟨u, hu⟩, some ⟨v, hv⟩} : Finset (Option X))) :
      d ((H.contract X).endAt e 0) = d ((H.contract X).endAt e 1) := by
    change d (contractVertex X (H.endAt e.1 0)) = d (contractVertex X (H.endAt e.1 1))
    rw [hd, hd]
    exact he e.1 ((hdel _).mp h0) ((hdel _).mp h1)
  intro a ha b hb
  have hh := hl (some ⟨u, hu⟩) (some ⟨v, hv⟩)
    (fun h ↦ huv (congrArg Subtype.val (Option.some.inj h))) d hed
    (contractVertex X a) ((hdel a).mpr ha) (contractVertex X b) ((hdel b).mpr hb)
  simpa only [hd] using hh

/-- A surviving cut edge joins the connected remnants of the two shores. -/
theorem IsSeparatingCut.connectedAfterDeletingPairs_of_contractions {X : Finset V}
    (hs : H.IsSeparatingCut X) (hl : (H.contract X).ConnectedAfterDeletingPairs)
    (hr : (H.contract (Finset.univ \ X)).ConnectedAfterDeletingPairs)
    (hcut : ∀ u v : V, u ≠ v → ∃ e ∈ H.dangling X,
      ∀ k, H.endAt e k ∉ ({u, v} : Finset V)) : H.ConnectedAfterDeletingPairs := by
  have hside (Y : Finset V) (hc : (H.contract Y).ConnectedAfterDeletingPairs)
      (u : V) (hu : u ∈ Y) : H.IsConnectedOn (Y.erase u) := by
    exact (contract_connectedOn_delete_iff Y ⟨u, hu⟩).mp
      (hc.connectedOn_erase_pair none (some ⟨u, hu⟩) (by simp))
  intro u v huv c he a ha b hb
  obtain ⟨e, heX, heuv⟩ := hcut u v huv
  have hX : X.Nonempty := by
    obtain ⟨k, hk⟩ := mem_meets.mp (dangling_subset_meets X heX)
    exact ⟨_, hk⟩
  have hXC : (Finset.univ \ X).Nonempty := by
    have heXC : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using heX
    obtain ⟨k, hk⟩ := mem_meets.mp (dangling_subset_meets _ heXC)
    exact ⟨_, hk⟩
  have opposite (u v : V) (hu : u ∈ X) (hv : v ∉ X)
      (he : ∀ f, H.endAt f 0 ∉ ({u, v} : Finset V) → H.endAt f 1 ∉ ({u, v} : Finset V) →
        c (H.endAt f 0) = c (H.endAt f 1))
      (heuv : ∀ k, H.endAt e k ∉ ({u, v} : Finset V)) :
      ∀ a, a ∉ ({u, v} : Finset V) → ∀ b, b ∉ ({u, v} : Finset V) → c a = c b := by
    have hleft := hside X hl u hu
    have hright := hside (Finset.univ \ X) hr v (by simp [hv])
    have hleftmem : ∀ w ∈ X.erase u, w ∉ ({u, v} : Finset V) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(Finset.mem_erase.mp hw).1, fun h ↦ hv (h ▸ (Finset.mem_erase.mp hw).2)⟩
    have hrightmem : ∀ w ∈ (Finset.univ \ X).erase v, w ∉ ({u, v} : Finset V) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h ↦ (Finset.mem_sdiff.mp (Finset.mem_erase.mp hw).2).2 (h ▸ hu),
        (Finset.mem_erase.mp hw).1⟩
    have cl := hleft c (fun f h0 h1 ↦ he f (hleftmem _ h0) (hleftmem _ h1))
    have cr := hright c (fun f h0 h1 ↦ he f (hrightmem _ h0) (hrightmem _ h1))
    have hcross := mem_dangling.mp heX
    have link := he e (heuv 0) (heuv 1)
    have ends (w : V) (hw : w ∉ ({u, v} : Finset V)) : c w = c (H.endAt e 0) := by
      have hwu : w ≠ u := fun h ↦ hw (by simp [h])
      have hwv : w ≠ v := fun h ↦ hw (by simp [h])
      have he0u : H.endAt e 0 ≠ u := fun h ↦ heuv 0 (by simp [h])
      have he0v : H.endAt e 0 ≠ v := fun h ↦ heuv 0 (by simp [h])
      have he1u : H.endAt e 1 ≠ u := fun h ↦ heuv 1 (by simp [h])
      have he1v : H.endAt e 1 ≠ v := fun h ↦ heuv 1 (by simp [h])
      by_cases hwX : w ∈ X
      · by_cases h0X : H.endAt e 0 ∈ X
        · exact cl w (by simp [hwu, hwX]) _ (by simp [he0u, h0X])
        · have h1X : H.endAt e 1 ∈ X := by tauto
          exact (cl w (by simp [hwu, hwX]) _ (by simp [he1u, h1X])).trans link.symm
      · by_cases h0X : H.endAt e 0 ∈ X
        · have h1X : H.endAt e 1 ∉ X := by tauto
          exact (cr w (by simp [hwv, hwX]) _ (by simp [he1v, h1X])).trans link.symm
        · exact cr w (by simp [hwv, hwX]) _ (by simp [he0v, h0X])
    exact fun a ha b hb ↦ (ends a ha).trans (ends b hb).symm
  by_cases hu : u ∈ X
  · by_cases hv : v ∈ X
    · exact connected_pair_same_shore hs hl hXC hu hv huv c he a ha b hb
    · exact opposite u v hu hv he heuv a ha b hb
  · by_cases hv : v ∈ X
    · have he' : ∀ f, H.endAt f 0 ∉ ({v, u} : Finset V) → H.endAt f 1 ∉ ({v, u} : Finset V) →
          c (H.endAt f 0) = c (H.endAt f 1) := by simpa only [Finset.pair_comm v u] using he
      have hev : ∀ k, H.endAt e k ∉ ({v, u} : Finset V) := by
        simpa only [Finset.pair_comm v u] using heuv
      exact opposite v u hv hu he' hev a (by simpa only [Finset.pair_comm v u] using ha)
        b (by simpa only [Finset.pair_comm v u] using hb)
    · apply connected_pair_same_shore hs.compl hr
      · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
        exact hX
      · simpa using hu
      · simpa using hv
      · exact huv
      · exact he
      · exact ha
      · exact hb

/-- Splicing brick contractions produces a brick if every vertex pair leaves
at least one cut edge. -/
theorem IsMatchingCovered.isBrick_of_brick_contractions {X : Finset V}
    (hm : H.IsMatchingCovered) (hl : (H.contract X).IsBrick)
    (hr : (H.contract (Finset.univ \ X)).IsBrick)
    (hcut : ∀ u v : V, u ≠ v → ∃ e ∈ H.dangling X,
      ∀ k, H.endAt e k ∉ ({u, v} : Finset V)) : H.IsBrick := by
  have hs : H.IsSeparatingCut X := ⟨hl.matchingCovered, hr.matchingCovered⟩
  exact hm.isBrick_of_bicritical
    (fun hb ↦ hl.notBipartite (hb.contract_of_separating hs))
    (hs.isBicritical_of_contractions
      (hl.isBicritical hl.matchingCovered.loopless) (hr.isBicritical hr.matchingCovered.loopless))
    (hs.connectedAfterDeletingPairs_of_contractions
      (hl.connectedAfterDeletingPairs hl.matchingCovered.loopless)
      (hr.connectedAfterDeletingPairs hr.matchingCovered.loopless) hcut)

omit [DecidableEq E] in
/-- Three matching edges cannot all be incident with just two vertices. -/
theorem exists_edge_avoiding_pair_of_degree_le_one {F : Finset E}
    (hd : ∀ w, H.degreeIn F w ≤ 1) (hF : 3 ≤ F.card) (u v : V) (huv : u ≠ v) :
    ∃ e ∈ F, ∀ k, H.endAt e k ∉ ({u, v} : Finset V) := by
  by_contra hn
  push Not at hn
  have hends : ∀ e ∈ F, 1 ≤ H.endsIn {u, v} e := by
    intro e he
    obtain ⟨k, hk⟩ := hn e he
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hsum : F.card ≤ H.degreeIn F u + H.degreeIn F v := by
    calc
      F.card = ∑ _e ∈ F, 1 := by simp
      _ ≤ ∑ e ∈ F, H.endsIn {u, v} e := Finset.sum_le_sum hends
      _ = ∑ w ∈ ({u, v} : Finset V), H.degreeIn F w := (H.sum_degreeIn_eq _ _).symm
      _ = H.degreeIn F u + H.degreeIn F v := Finset.sum_pair huv
  have hu := hd u
  have hv := hd v
  omega

/-- The brick assertion of Campos--Lucchesi Lemma 2.11: two brick contractions
splice to a brick exactly when their cut contains three independent edges. -/
theorem IsMatchingCovered.isBrick_iff_cut_matching_of_brick_contractions {X : Finset V}
    (hm : H.IsMatchingCovered) (hl : (H.contract X).IsBrick)
    (hr : (H.contract (Finset.univ \ X)).IsBrick) :
    H.IsBrick ↔ ∃ F : Finset E, F ⊆ H.dangling X ∧
      (∀ w, H.degreeIn F w ≤ 1) ∧ 3 ≤ F.card := by
  constructor
  · intro hb
    have hX : IsNontrivialCut X := by
      constructor
      · by_contra hn
        exact hl.notBipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))
      · by_contra hn
        exact hr.notBipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))
    obtain ⟨M, hM, _, hc⟩ := hb.exists_crossing_at_least_three
      ⟨hl.matchingCovered, hr.matchingCovered⟩ hX
    refine ⟨M ∩ H.dangling X, Finset.inter_subset_right, ?_, hc⟩
    intro w
    calc
      H.degreeIn (M ∩ H.dangling X) w ≤ H.degreeIn M w := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpM, hpk⟩ := Finset.mem_product.mp hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hpM).1, hpk⟩, he⟩
      _ = 1 := hM w
  · rintro ⟨F, hFX, hd, hF⟩
    apply hm.isBrick_of_brick_contractions hl hr
    intro u v huv
    obtain ⟨e, he, huv⟩ := exists_edge_avoiding_pair_of_degree_le_one hd hF u v huv
    exact ⟨e, hFX he, huv⟩

end GraphPuzzles.LoopMultigraph
