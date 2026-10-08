import GraphPuzzles.Petersen.PetersenNeighborhood
import GraphPuzzles.Reduction.Parallel.ParallelCutTransport
import GraphPuzzles.Cuts.TrivialCutCharacteristic
import GraphPuzzles.Matching.VertexMatchingExtension

/-! Matching replacement outside an expanded Petersen pole. -/

namespace GraphPuzzles.LoopMultigraph

/-- A degree-three pole matching uses every Petersen edge incident with the pole. -/
theorem IsVertexMatching.petersen_pole_edges_subset {p : Fin 10}
    {M : Finset (Fin 15)} (_hM : petersen.IsVertexMatching p M)
    (hd : petersen.degreeIn M p = 3) : petersen.meets {p} ⊆ M := by
  have hc := degreeIn_add_compl (H := petersen) M p
  rw [hd, petersen_degree] at hc
  have hz : petersen.degreeIn (Finset.univ \ M) p = 0 := by omega
  intro e he
  obtain ⟨k, hk⟩ := mem_meets.mp he
  have hk' : petersen.endAt e k = p := Finset.mem_singleton.mp hk
  by_contra hem
  have hinc : (e, k) ∈ ((Finset.univ \ M) ×ˢ Finset.univ).filter
      (fun ek : Fin 15 × Fin 2 ↦ petersen.endAt ek.1 ek.2 = p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hem⟩, Finset.mem_univ _⟩, hk'⟩
  have hh := Finset.card_eq_zero.mp hz
  rw [hh] at hinc
  exact Finset.notMem_empty _ hinc

/-- Both endpoints of a pole edge belong to its closed neighborhood. -/
theorem petersen_pole_edge_end_mem_closed {p : Fin 10} {e : Fin 15}
    (he : e ∈ petersen.meets {p}) (k : Fin 2) :
    petersen.endAt e k ∈ petersenClosedNeighborhood p := by
  apply (petersen_mem_closedNeighborhood p _).mpr
  obtain ⟨j, hj⟩ := mem_meets.mp he
  have hj' := Finset.mem_singleton.mp hj
  fin_cases j <;> fin_cases k
  · exact Or.inl hj'
  · exact Or.inr ⟨e, Or.inl ⟨hj', rfl⟩⟩
  · exact Or.inr ⟨e, Or.inr ⟨rfl, hj'⟩⟩
  · exact Or.inl hj'

/-- All matching edges meeting the closed neighborhood are pole edges. -/
theorem IsVertexMatching.petersen_pole_edge_of_neighborhood {p : Fin 10}
    {M : Finset (Fin 15)} (hM : petersen.IsVertexMatching p M)
    (hd : petersen.degreeIn M p = 3) {e : Fin 15} (he : e ∈ M) {k : Fin 2}
    (hk : petersen.endAt e k ∈ petersenClosedNeighborhood p) :
    e ∈ petersen.meets {p} := by
  by_cases hp : petersen.endAt e k = p
  · exact mem_meets.mpr ⟨k, Finset.mem_singleton.mpr hp⟩
  obtain h | ⟨g, hg⟩ := (petersen_mem_closedNeighborhood p _).mp hk
  · exact (hp h).elim
  have hgp : g ∈ petersen.meets {p} := by
    rcases hg with ⟨h0, _⟩ | ⟨_, h1⟩
    · exact mem_meets.mpr ⟨0, Finset.mem_singleton.mpr h0⟩
    · exact mem_meets.mpr ⟨1, Finset.mem_singleton.mpr h1⟩
  have hgM := hM.petersen_pole_edges_subset hd hgp
  have hdeg := hM _ hp
  have heq : e = g := by
    rcases hg with ⟨_, h1⟩ | ⟨h0, _⟩
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hdeg he hgM rfl h1)
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hdeg he hgM rfl h0)
  exact heq.symm ▸ hgp

/-- The far six vertices are closed under a degree-three pole matching. -/
theorem IsVertexMatching.petersen_far_closed {p : Fin 10}
    {M : Finset (Fin 15)} (hM : petersen.IsVertexMatching p M)
    (hd : petersen.degreeIn M p = 3) {e : Fin 15} (he : e ∈ M) {k : Fin 2}
    (hk : petersen.endAt e k ∈ Finset.univ \ petersenClosedNeighborhood p) :
    petersen.endAt e (Fin.rev k) ∈ Finset.univ \ petersenClosedNeighborhood p := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hr
  have hpole := hM.petersen_pole_edge_of_neighborhood hd he hr
  exact (Finset.mem_sdiff.mp hk).2 (petersen_pole_edge_end_mem_closed hpole k)

/-- Restriction to the closed neighborhood leaves exactly the three pole edges. -/
theorem IsVertexMatching.petersen_neighborhood_edges {p : Fin 10}
    {M : Finset (Fin 15)} (hM : petersen.IsVertexMatching p M)
    (hd : petersen.degreeIn M p = 3) :
    M ∩ petersen.edgesIn (petersenClosedNeighborhood p) = petersen.meets {p} := by
  apply Finset.Subset.antisymm
  · intro e he
    exact hM.petersen_pole_edge_of_neighborhood hd (Finset.mem_inter.mp he).1
      ((mem_edgesIn.mp (Finset.mem_inter.mp he).2) 0)
  · intro e he
    exact Finset.mem_inter.mpr ⟨hM.petersen_pole_edges_subset hd he,
      mem_edgesIn.mpr (petersen_pole_edge_end_mem_closed he)⟩

private theorem petersen_meets_singleton (p : Fin 10) :
    petersen.meets {p} = petersen.dangling {p} := by
  fin_cases p <;> decide

/-- Exactly one of the pole edges crosses a nontrivial separating Petersen cut. -/
theorem IsSeparatingCut.petersen_pole_crossing_one {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) (p : Fin 10) :
    (petersen.meets {p} ∩ petersen.dangling X).card = 1 := by
  rw [petersen_meets_singleton, Finset.inter_comm]
  exact petersen.isTightCut_singleton p _ (hs.petersen_dangling_isPerfectMatching hX)

private theorem petersen_pole_edges_degree (p w : Fin 10) :
    petersen.degreeIn (petersen.meets {p}) w =
      if w = p then 3 else if w ∈ petersenClosedNeighborhood p then 1 else 0 := by
  fin_cases p <;> fin_cases w <;> decide

section Replacement

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Replace the six vertices far from the Petersen pole, preserving all
original labels incident with that pole and obtaining three selected crossings. -/
theorem ParallelReduction.replace_petersen_far (f : ParallelReduction H petersen)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (hd : H.degreeIn M v = 3)
    {X : Finset V} (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ N, H.IsVertexMatching v N ∧
      (∀ e ∈ H.meets {v}, e ∈ N ↔ e ∈ M) ∧ (N ∩ H.dangling X).card = 3 := by
  let p := f.vertexEquiv v
  let B := M ∩ H.meets {v}
  have hi := f.edgeMap_injOn_vertexMatching hM hl
  have hPM := f.isVertexMatching_image hM hl
  have hdP : petersen.degreeIn (M.image f.edgeMap) p = 3 :=
    (f.degreeIn_image hi v).trans hd
  have hm (e : E) : f.edgeMap e ∈ petersen.meets {p} ↔ e ∈ H.meets {v} := by
    simpa [p, ParallelReduction.mapVertices] using
      f.mem_meets_mapVertices {v} e
  have hBi : B.image f.edgeMap = petersen.meets {p} := by
    ext g
    constructor
    · intro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
      exact (hm e).mpr (Finset.mem_inter.mp he).2
    · intro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hPM.petersen_pole_edges_subset hdP hg)
      exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr ⟨he, (hm e).mp hg⟩, rfl⟩
  have hiB : Set.InjOn f.edgeMap B := fun a ha b hb he ↦
    hi (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 he
  have hsP := (f.isSeparatingCut_iff_contract X).mp hs
  have hXP := (f.nontrivial_mapVertices X).mpr hX
  obtain ⟨_, L, _, hL, _, hL2⟩ := hsP.petersen_neighborhood_patch hXP p
  let S := (Finset.univ \ petersenClosedNeighborhood p).map f.vertexEquiv.symm.toEmbedding
  have hS (w : V) : w ∈ S ↔ f.vertexEquiv w ∉ petersenClosedNeighborhood p := by
    simp [S, Finset.mem_map_equiv]
  have hv : v ∉ S := by
    rw [hS]
    exact not_not.mpr ((petersen_mem_closedNeighborhood p p).mpr (Or.inl rfl))
  have hL' : H.IsPerfectMatchingOn S (f.liftMatching L) := f.isPerfectMatchingOn_lift hL
  have hdis : Disjoint B (f.liftMatching L) := by
    apply Finset.disjoint_left.mpr
    intro e he hle
    obtain ⟨k, hk⟩ := mem_meets.mp (Finset.mem_inter.mp he).2
    exact hv ((Finset.mem_singleton.mp hk) ▸ hL'.1 e hle k)
  refine ⟨B ∪ f.liftMatching L, ?_, ?_, ?_⟩
  · intro w hw
    rw [degreeIn_union_of_disjoint hdis]
    have hb : H.degreeIn B w = if f.vertexEquiv w ∈ petersenClosedNeighborhood p then 1 else 0 := by
      rw [← f.degreeIn_image hiB w, hBi, petersen_pole_edges_degree, if_neg]
      exact fun he ↦ hw (f.vertexEquiv.injective he)
    rw [hb]
    by_cases hwS : w ∈ S
    · rw [if_neg ((hS w).mp hwS), hL'.2 w hwS]
    · rw [if_pos (not_not.mp (fun h ↦ hwS ((hS w).mpr h))), hL'.degree_zero hwS]
  · intro e he
    have hn : e ∉ f.liftMatching L := by
      intro hle
      obtain ⟨k, hk⟩ := mem_meets.mp he
      exact hv ((Finset.mem_singleton.mp hk) ▸ hL'.1 e hle k)
    simp only [Finset.mem_union, B, Finset.mem_inter, he, and_true, hn, or_false]
  · have hB1 : (B ∩ H.dangling X).card = 1 := by
      have hh := f.crossing_image_of_injOn hiB X
      rw [hBi] at hh
      exact hh.symm.trans (hsP.petersen_pole_crossing_one hXP p)
    have hL2' := (f.liftMatching_crossing L X).trans hL2
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint
      (hdis.mono Finset.inter_subset_left Finset.inter_subset_left), hB1, hL2']

/-- Lemma 2.7 needs only an original matching crossing the expanded pole
three times. The expansion cut itself need not be separating. -/
theorem IsPerfectMatching.exists_three_crossing_of_petersen_contraction
    {R : Finset V} {M : Finset E} (hM : H.IsPerfectMatching M)
    (hM3 : (M ∩ H.dangling R).card = 3)
    (hp : (H.contract R).IsPetersenUpToParallel)
    {Y : Finset (Option R)} (hn : none ∉ Y)
    (hsY : (H.contract R).IsSeparatingCut Y) (hY : IsNontrivialCut Y) :
    ∃ N, H.IsPerfectMatching N ∧ (N ∩ H.dangling (sourceShore R Y)).card = 3 := by
  obtain ⟨f⟩ := hp
  have hmc := f.isMatchingCovered_iff.mpr petersen_isMatchingCovered
  have hvm : (H.contract R).IsVertexMatching none (H.contractMatching R M) := by
    intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some w => rw [contractMatching, contract_degreeIn_some]; exact hM w.1
  have hd : (H.contract R).degreeIn (H.contractMatching R M) none = 3 := by
    rw [contractMatching_degreeIn_none, hM3]
  obtain ⟨N, hN, hag, hN3⟩ := f.replace_petersen_far hmc.loopless hvm hd hsY hY
  obtain ⟨P, hP, hPN⟩ := hN.extend_preserving_boundary hM (by
    intro e he
    rw [← mem_contractMatching R M ⟨e, dangling_subset_meets R he⟩]
    apply hag
    apply mem_meets.mpr
    by_cases h0 : H.endAt e 0 ∈ R
    · refine ⟨1, Finset.mem_singleton.mpr ((contract_endAt_eq_none_iff _ _ _).mpr ?_)⟩
      have hh := mem_dangling.mp he
      tauto
    · exact ⟨0, Finset.mem_singleton.mpr ((contract_endAt_eq_none_iff _ _ _).mpr h0)⟩)
  refine ⟨P, hP, ?_⟩
  rw [← contractMatching_crossing R Y hn, hPN]
  exact hN3


/-- Campos–Lucchesi Lemma 2.7 for a separating nontight expansion of a
Petersen pole. The prescribed cut avoids the pole and is preserved exactly. -/
theorem IsSeparatingCut.exists_three_crossing_of_petersen_expansion
    {R : Finset V} (hsR : H.IsSeparatingCut R)
    (hp : (H.contract R).IsPetersenUpToParallel) (hnt : ¬ H.IsTightCut R)
    {Y : Finset (Option R)} (hn : none ∉ Y)
    (hsY : (H.contract R).IsSeparatingCut Y) (hY : IsNontrivialCut Y) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling (sourceShore R Y)).card = 3 := by
  obtain ⟨M, hM, hM3⟩ := hsR.exists_crossing_three_of_petersen_contraction_nontight hp hnt
  exact hM.exists_three_crossing_of_petersen_contraction hM3 hp hn hsY hY

end Replacement

end GraphPuzzles.LoopMultigraph
