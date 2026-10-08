import GraphPuzzles.Matching.Bipartite.Konig
import GraphPuzzles.Graph.LoopMultigraphIso
import GraphPuzzles.Matching.Fractional.MatchingPolytope

/-!
# Proper snarks are bricks

The note's Lemma (brick): every proper snark is a simple brick.  A brick is a nonbipartite
matching-covered graph without nontrivial tight cuts.  Matching-coveredness of a connected
bridgeless cubic graph is proved directly by the Tutte counting of the hub lemma
(`isMatchingCovered_of_bridgeless`).  For tight cuts the note argues through Edmonds' perfect
matching polytope theorem: the vector `1/3` lies in the polytope of a bridgeless cubic graph, so a
tight cut has exactly three edges. This consequence is proved as `edmondsTightCut`, using
the rational decomposition in `MatchingPolytope`. A `3`-cut of a cyclically `4`-edge-connected cubic graph is
trivial, because a shore without a circuit spans at most `|X| − 1` edges, hence has boundary at
least `|X| + 2`.  Non-bipartiteness follows from König's theorem: a cubic bipartite multigraph
is `3`-edge-colourable.

The Campos–Lucchesi theorem is then stated in its published form, `CamposLucchesi`, for simple
bricks other than the Petersen graph, which is defined explicitly.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped Fin.NatCast

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

section Defs

variable (H : LoopMultigraph V E)

/-- Simple: no loops and no parallel edges. -/
structure IsSimple : Prop where
  loopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1
  no_parallel : ∀ e f, H.Joins f (H.endAt e 0) (H.endAt e 1) → e = f

/-- A cut is tight when every perfect matching meets it in exactly one edge. -/
def IsTightCut (X : Finset V) : Prop :=
  ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1

/-- A brick: nonbipartite, matching covered, without nontrivial tight cuts. -/
structure IsBrick : Prop where
  notBipartite : ¬ H.IsBipartite
  matchingCovered : H.IsMatchingCovered
  tight_trivial : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X

/-- The edges with both ends in `X`. -/
def edgesIn (X : Finset V) : Finset E := Finset.univ.filter fun e ↦ ∀ k, H.endAt e k ∈ X

/-- A vertex set spans a circuit. -/
def HasCircuitIn (X : Finset V) : Prop := ∃ C : H.OrdinaryCircuit, C.edges ⊆ H.edgesIn X

/-- Cyclically `4`-edge-connected: no cut with fewer than four edges separates two subgraphs each
containing a circuit. -/
def IsCyclicallyFourEdgeConnected : Prop :=
  ∀ X : Finset V, H.HasCircuitIn X → H.HasCircuitIn (Finset.univ \ X) → 4 ≤ (H.dangling X).card

/-- A proper snark: connected, bridgeless, simple, cubic, of girth at least five, cyclically
`4`-edge-connected, and not `3`-edge-colourable. -/
structure IsProperSnark : Prop where
  connected : H.IsConnected
  bridgeless : H.IsBridgeless
  simple : H.IsSimple
  cubic : ∀ v, H.degree v = 3
  girth : ∀ C : H.OrdinaryCircuit, 5 ≤ C.edges.card
  cyclic : H.IsCyclicallyFourEdgeConnected
  notColourable : ¬ ∃ g : E → Color, H.ProperOff ∅ g

end Defs

/-- The Petersen graph: the outer circuit `0 … 4`, the spokes `i — 5 + i`, and the inner pentagram
`5 + i — 5 + (i + 2 mod 5)`. -/
def petersen : LoopMultigraph (Fin 10) (Fin 15) :=
  ⟨![![0, 1], ![1, 2], ![2, 3], ![3, 4], ![4, 0],
     ![0, 5], ![1, 6], ![2, 7], ![3, 8], ![4, 9],
     ![5, 7], ![6, 8], ![7, 9], ![8, 5], ![9, 6]]⟩

/-- Being the Petersen graph, up to endpoint-multigraph isomorphism. -/
def IsPetersen (H : LoopMultigraph V E) : Prop := Nonempty (EndpointIso H petersen)

/-- **Edmonds' theorem, in the form used by the note**: in a bridgeless
cubic loopless graph the vector `1/3` lies in the perfect matching polytope, so every tight cut has
exactly three edges. Proved below as `edmondsTightCut`. -/
def EdmondsTightCut : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (G : LoopMultigraph V' E'), (∀ v, G.degree v = 3) → G.IsBridgeless →
    (∀ e, G.endAt e 0 ≠ G.endAt e 1) → ∀ X : Finset V', G.IsTightCut X → (G.dangling X).card = 3

/-- Edmonds' tight-cut consequence, with the matching-polytope input discharged. -/
theorem edmondsTightCut : EdmondsTightCut.{u, v} := by
  intro V' E' _ _ _ _ G hc hb _ X ht
  obtain ⟨C⟩ := exists_matchingCombination_third hc hb
  exact C.card_tight_cut X ht

/-- **The Campos–Lucchesi statement** (brick case of their Theorem 1.1):
every nontrivial separating cut of a simple brick other than the Petersen graph is met by some
perfect matching in exactly three edges. Proved in `Bricks/CamposLucchesi.lean`. -/
def CamposLucchesi : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (G : LoopMultigraph V' E'), G.IsSimple → G.IsBrick → ¬ G.IsPetersen →
    ∀ X : Finset V', G.IsSeparatingCut X → IsNontrivialCut X →
      ∃ N, G.IsPerfectMatching N ∧ (N ∩ G.dangling X).card = 3

section Acyclic

variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem mem_edgesIn {X : Finset V} {e : E} : e ∈ H.edgesIn X ↔ ∀ k, H.endAt e k ∈ X := by
  simp [edgesIn]

/-- A nonempty even edge set contains a circuit. -/
theorem exists_circuit_of_even {J : Finset E} (hJ : H.IsEvenEdgeSet J) (hne : J.Nonempty) :
    ∃ C : H.OrdinaryCircuit, C.edges ⊆ J := by
  obtain ⟨L, hL⟩ := H.decompose_even_edge_set_ordinary J hJ
  obtain ⟨e, he⟩ := hne
  have h1 := hL e
  rw [if_pos he] at h1
  obtain ⟨C, hCL, heC⟩ : ∃ C ∈ L, e ∈ C.edges := by
    by_contra hcon
    push Not at hcon
    have hnil : (L.filter fun C ↦ e ∈ C.edges) = [] := by
      rw [List.filter_eq_nil_iff]
      intro C hC
      simpa using hcon C hC
    rw [hnil] at h1
    simp at h1
  refine ⟨C, fun f hf ↦ ?_⟩
  by_contra hfJ
  have h2 := hL f
  rw [if_neg hfJ] at h2
  have hmem : C ∈ L.filter fun C ↦ f ∈ C.edges := List.mem_filter.mpr ⟨hCL, by simpa using hf⟩
  have := List.length_pos_of_mem hmem
  omega

/-- The boundary of the edges inside `X`, as a linear map over `F₂`. -/
noncomputable def boundaryMap (X : Finset V) : (H.edgesIn X → F₂) →ₗ[F₂] (X → F₂) where
  toFun x v := ∑ e : H.edgesIn X, x e * H.edgeIncidence v.1 e.1
  map_add' x y := by
    funext v
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext v
    simp [Finset.mul_sum, mul_assoc]

/-- The sum of the values of a vertex function on `X`. -/
noncomputable def sumMap (X : Finset V) : (X → F₂) →ₗ[F₂] F₂ where
  toFun y := ∑ v, y v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private theorem F₂_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [DecidableEq E] in
/-- Every value of the boundary map has zero sum: each inside edge has two ends in `X`. -/
theorem sumMap_boundaryMap (X : Finset V) (x : H.edgesIn X → F₂) :
    sumMap X (H.boundaryMap X x) = 0 := by
  change ∑ v : X, ∑ e : H.edgesIn X, x e * H.edgeIncidence v.1 e.1 = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have hmem := mem_edgesIn.mp e.2
  have : ∑ v : X, H.edgeIncidence v.1 e.1 = 0 := by
    rw [Finset.sum_coe_sort X (fun v ↦ H.edgeIncidence v e.1)]
    simp only [edgeIncidence_eq, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (hmem 0), if_pos (hmem 1)]
    decide
  rw [this, mul_zero]

omit [Fintype V] in
theorem sumMap_surjective {X : Finset V} (hX : X.Nonempty) : Function.Surjective (sumMap X) := by
  obtain ⟨v₀, hv₀⟩ := hX
  intro c
  refine ⟨fun v ↦ if v = ⟨v₀, hv₀⟩ then c else 0, ?_⟩
  change ∑ v : X, (if v = ⟨v₀, hv₀⟩ then c else 0) = c
  simp

omit [DecidableEq E] in
/-- A kernel vector of the boundary map selects an even edge set inside `X`. -/
theorem even_of_mem_ker (X : Finset V) {x : H.edgesIn X → F₂}
    (hx : x ∈ LinearMap.ker (H.boundaryMap X)) :
    H.IsEvenEdgeSet
      ((Finset.univ.filter fun e : H.edgesIn X ↦ x e = 1).map (Function.Embedding.subtype _)) := by
  intro v
  rw [Finset.sum_map]
  simp only [Function.Embedding.coe_subtype]
  rw [Finset.sum_filter]
  have hsum : ∑ e : H.edgesIn X, (if x e = 1 then H.edgeIncidence v e.1 else 0) =
      ∑ e : H.edgesIn X, x e * H.edgeIncidence v e.1 := by
    apply Finset.sum_congr rfl
    intro e _
    rcases F₂_eq_zero_or_one (x e) with h | h
    · rw [h, if_neg (by decide), zero_mul]
    · rw [h, if_pos rfl, one_mul]
  rw [hsum]
  by_cases hv : v ∈ X
  · have h0 : H.boundaryMap X x = 0 := LinearMap.mem_ker.mp hx
    exact congr_fun h0 ⟨v, hv⟩
  · apply Finset.sum_eq_zero
    intro e _
    have hmem := mem_edgesIn.mp e.2
    have h0 : H.endAt e.1 0 ≠ v := fun h ↦ hv (h ▸ hmem 0)
    have h1 : H.endAt e.1 1 ≠ v := fun h ↦ hv (h ▸ hmem 1)
    rw [edgeIncidence_eq, if_neg h0, if_neg h1]
    simp

/-- A set of vertices spanning no circuit spans fewer edges than it has vertices. -/
theorem card_edgesIn_lt (X : Finset V) (hX : X.Nonempty) (hno : ¬ H.HasCircuitIn X) :
    (H.edgesIn X).card < X.card := by
  by_contra hle
  push Not at hle
  have hrange : LinearMap.range (H.boundaryMap X) ≤ LinearMap.ker (sumMap X) := by
    rintro y ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (sumMap_boundaryMap X x)
  have hS : Module.finrank F₂ (LinearMap.ker (sumMap X)) + 1 = X.card := by
    have h := LinearMap.finrank_range_add_finrank_ker (sumMap X)
    rw [LinearMap.range_eq_top.mpr (sumMap_surjective hX), finrank_top, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (H.boundaryMap X)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  have hle' := Submodule.finrank_mono hrange
  have hker : 0 < Module.finrank F₂ (LinearMap.ker (H.boundaryMap X)) := by omega
  have hne : LinearMap.ker (H.boundaryMap X) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    exact absurd hker (lt_irrefl 0)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have heven := even_of_mem_ker X hx
  have hnonempty : ((Finset.univ.filter fun e : H.edgesIn X ↦ x e = 1).map
      (Function.Embedding.subtype _)).Nonempty := by
    obtain ⟨e, he⟩ : ∃ e, x e ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    refine ⟨e.1, Finset.mem_map.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩⟩
    rcases F₂_eq_zero_or_one (x e) with h | h
    · exact absurd h he
    · exact h
  obtain ⟨C, hC⟩ := exists_circuit_of_even heven hnonempty
  apply hno
  refine ⟨C, fun f hf ↦ ?_⟩
  obtain ⟨e, -, rfl⟩ := Finset.mem_map.mp (hC hf)
  exact e.2

end Acyclic

section Cuts

variable {H : LoopMultigraph V E}

/-- Handshake: the degrees on `X` count the inside edges twice and the dangling edges once. -/
theorem sum_degree_eq_two_mul_add (X : Finset V) :
    ∑ w ∈ X, H.degree w = 2 * (H.edgesIn X).card + (H.dangling X).card := by
  rw [sum_degree_eq]
  have h : ∀ e, H.endsIn X e = (if e ∈ H.edgesIn X then 2 else 0) +
      (if e ∈ H.dangling X then 1 else 0) := by
    intro e
    unfold endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    have hi := (mem_edgesIn (H := H) (X := X) (e := e))
    have hd := (mem_dangling (K := H) (X := X) (e := e))
    rcases Classical.em (H.endAt e 0 ∈ X) with h0 | h0 <;>
      rcases Classical.em (H.endAt e 1 ∈ X) with h1 | h1
    · rw [if_pos h0, if_pos h1, if_pos (hi.mpr fun k ↦ by
        rcases fin2_cases k with rfl | rfl
        · exact h0
        · exact h1), if_neg (fun h ↦ (hd.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩)]
    · rw [if_pos h0, if_neg h1, if_neg (fun h ↦ h1 (hi.mp h 1)),
        if_pos (hd.mpr fun h ↦ h1 (h.mp h0))]
    · rw [if_neg h0, if_pos h1, if_neg (fun h ↦ h0 (hi.mp h 0)),
        if_pos (hd.mpr fun h ↦ h0 (h.mpr h1))]
    · rw [if_neg h0, if_neg h1, if_neg (fun h ↦ h0 (hi.mp h 0)),
        if_neg (fun h ↦ (hd.mp h) ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩)]
  rw [Finset.sum_congr rfl (fun e _ ↦ h e), Finset.sum_add_distrib, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  congr 1
  have h2 : ∀ e, (if e ∈ H.edgesIn X then 2 else 0) = 2 * (if e ∈ H.edgesIn X then 1 else 0) := by
    intro e
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun e _ ↦ h2 e), ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]

/-- A shore spanning no circuit has at least `|X| + 2` dangling edges in a cubic graph. -/
theorem card_dangling_ge (hCubic : ∀ v, H.degree v = 3) {X : Finset V} (hX : X.Nonempty)
    (hno : ¬ H.HasCircuitIn X) : X.card + 2 ≤ (H.dangling X).card := by
  have h1 := sum_degree_eq_two_mul_add (H := H) X
  rw [Finset.sum_congr rfl (fun w _ ↦ hCubic w), Finset.sum_const, smul_eq_mul] at h1
  have h2 := card_edgesIn_lt X hX hno
  omega

/-- A three-edge cut of a cyclically `4`-edge-connected cubic graph is trivial. -/
theorem not_nontrivial_of_card_dangling_eq_three (hCubic : ∀ v, H.degree v = 3)
    (hcyc : H.IsCyclicallyFourEdgeConnected) (X : Finset V) (h3 : (H.dangling X).card = 3) :
    ¬ IsNontrivialCut X := by
  rintro ⟨hX, hXc⟩
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hXcne : (Finset.univ \ X).Nonempty := Finset.card_pos.mp (by omega)
  by_cases hA : H.HasCircuitIn X
  · by_cases hB : H.HasCircuitIn (Finset.univ \ X)
    · have := hcyc X hA hB
      omega
    · have := card_dangling_ge hCubic hXcne hB
      rw [dangling_compl] at this
      omega
  · have := card_dangling_ge hCubic hXne hA
    omega

end Cuts

section Bipartite

variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- Along a circuit of a bipartite graph the colours alternate, so the circuit is even. -/
theorem even_card_of_bipartite (hbip : H.IsBipartite) (C : H.TraversedCircuit) :
    Even C.edges.card := by
  obtain ⟨c, hc⟩ := hbip
  have hstep : ∀ p : C.tour.Pos, c (C.tour.vertexAt (p + 1)) = !c (C.tour.vertexAt p) := by
    intro p
    have h := hc (C.tour.edge p).1
    rcases C.endAt_edge_eq p 0 with h0 | h0 <;> rcases C.endAt_edge_eq p 1 with h1 | h1
    · exact absurd (congrArg c (h0.trans h1.symm)) h
    · rw [h0, h1] at h
      exact Bool.eq_not_iff.mpr h.symm
    · rw [h0, h1] at h
      exact Bool.eq_not_iff.mpr h
    · exact absurd (congrArg c (h0.trans h1.symm)) h
  have key : ∀ m : ℕ, c (C.tour.vertexAt (m : C.tour.Pos)) =
      (if Even m then c (C.tour.vertexAt 0) else !c (C.tour.vertexAt 0)) := by
    intro m
    induction m with
    | zero => rw [C.posCast_zero, if_pos Even.zero]
    | succ m ih =>
      rw [C.posCast_add, C.posCast_one, hstep, ih]
      by_cases hm : Even m
      · rw [if_pos hm, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm))]
      · rw [if_neg hm, if_pos (Nat.even_add_one.mpr hm), Bool.not_not]
  rw [C.card_edges_eq]
  by_contra hodd
  have h := key (C.tour.n + 1)
  rw [Fin.natCast_self, if_neg hodd] at h
  exact (Bool.eq_not_self _).mp h

end Bipartite

/-- **Lemma (brick)**: every proper snark is a brick. -/
theorem isBrick_of_properSnark {H : LoopMultigraph V E} (hs : H.IsProperSnark) : H.IsBrick := by
  refine ⟨?_, isMatchingCovered_of_bridgeless hs.connected hs.cubic hs.bridgeless
    hs.simple.loopless, ?_⟩
  · intro hbip
    exact hs.notColourable (exists_properOff_of_bipartite hs.cubic hbip)
  · intro X htight
    exact not_nontrivial_of_card_dangling_eq_three hs.cubic hs.cyclic X
      (edmondsTightCut H hs.cubic hs.bridgeless hs.simple.loopless X htight)

/-- **Four perfect matchings covering a two-circuit factor of a proper snark other than the
Petersen graph**, with the note's Lemmas (hub), (separating), and (brick) formalized.  The
hypotheses are Campos–Lucchesi and Karabáš–Máčajová's Theorem 3.1 in ambient form. -/
theorem TwoCircuitFactor.exists_fourCover_of_properSnark_of_camposLucchesi {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen)
    (hCL : CamposLucchesi.{u, v}) (hKM : KMThreePole.{u, v}) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover_of_snark hs.cubic hs.simple.loopless hs.bridgeless hs.notColourable
    (fun X hsep hnt ↦ hCL H hs.simple (isBrick_of_properSnark hs) hnotP X hsep hnt) hKM

end LoopMultigraph
end GraphPuzzles
