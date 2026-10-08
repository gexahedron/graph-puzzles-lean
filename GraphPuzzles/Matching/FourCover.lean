import GraphPuzzles.Circuits.CircuitArcs
import GraphPuzzles.CycleCovers.TwoCircuitFactor
import GraphPuzzles.Graph.CubicDegrees
import GraphPuzzles.Core.FiniteCounts

/-!
# Four perfect matchings covering a two-circuit snark

The paper `two_circuit_four_perfect_matchings.tex` proves that a proper snark other than the Petersen graph
with a perfect matching `M` whose complement is two circuits has three further perfect
matchings covering, together with `M`, every edge.  Its proof has two external ingredients:
the Campos–Lucchesi theorem on bricks, which (through the note's matching-theoretic lemmas)
supplies a perfect matching `N` meeting the cross-spokes in exactly three edges, and the
Karabáš–Máčajová theorem on Hamiltonian `3`-poles, which (through the note's gluing corollary)
gives a four-cover of a loopless cubic multigraph whose complement of a perfect matching is two
odd circuits joined by three matching edges.

This module formalizes the note's own contribution with both ingredients as hypotheses: the
reduction of `G` along `N` to a cubic multigraph on the vertices covered by `S = M ∩ N`, the
parity argument showing that the reduced circuits are odd, and the alternating lifting of the
four-cover of the reduced graph back to `G`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped Fin.NatCast

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

section Degrees

theorem degreeIn_union_of_disjoint {F G : Finset E} (h : Disjoint F G) (v : V) :
    H.degreeIn (F ∪ G) v = H.degreeIn F v + H.degreeIn G v := by
  unfold degreeIn
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl h))

omit [DecidableEq E] in
theorem degreeIn_univ' (v : V) : H.degreeIn Finset.univ v = H.degree v := by
  simp only [degreeIn, degree, halfEdgesAt, vertex]
  rw [Fintype.card_subtype]
  congr 1

omit [DecidableEq E] in
theorem degreeIn_eq_zero_of {F : Finset E} {v : V} (h : ∀ e ∈ F, ∀ k, H.endAt e k ≠ v) :
    H.degreeIn F v = 0 := by
  unfold degreeIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  exact h x.1 (Finset.mem_product.mp hx).1 x.2

theorem degreeIn_add_compl (F : Finset E) (v : V) :
    H.degreeIn F v + H.degreeIn (Finset.univ \ F) v = H.degree v := by
  rw [← degreeIn_union_of_disjoint Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (Finset.subset_univ _), degreeIn_univ']

/-- A cubic vertex has degree one in an edge set containing exactly one of its half-edges. -/
theorem degreeIn_eq_one_of_halfEdges {G : LoopMultigraph V E}
    {F : Finset E} {w : V} (x₁ x₂ x₃ : G.halfEdgesAt w) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (hcases : ∀ x : G.halfEdgesAt w, x = x₁ ∨ x = x₂ ∨ x = x₃)
    (h₁ : x₁.1.1 ∈ F) (h₂ : x₂.1.1 ∉ F) (h₃ : x₃.1.1 ∉ F) : G.degreeIn F w = 1 := by
  rw [G.degreeIn_eq_card_halfEdges, card_filter_of_three x₁ x₂ x₃ h12 h13 h23 hcases,
    if_pos h₁, if_neg h₂, if_neg h₃]

/-- In a cubic graph covered by a perfect matching `S` and three further perfect matchings,
every edge misses one of the three. -/
theorem exists_not_mem_of_cover {G : LoopMultigraph V E} (hCubic : ∀ v : V, G.degree v = 3)
    {S L₁ L₂ L₃ : Finset E} (hS : G.IsPerfectMatching S) (h₁ : G.IsPerfectMatching L₁)
    (h₂ : G.IsPerfectMatching L₂) (h₃ : G.IsPerfectMatching L₃)
    (hcov : S ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ) (f : E) :
    f ∉ L₁ ∨ f ∉ L₂ ∨ f ∉ L₃ := by
  by_contra h
  push Not at h
  have h2 : G.degreeIn (Finset.univ \ S) (G.endAt f 0) = 2 := by
    have := G.degreeIn_add_compl S (G.endAt f 0)
    rw [hS, hCubic] at this
    omega
  rw [G.degreeIn_eq_card_halfEdges] at h2
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (lt_of_lt_of_eq Nat.one_lt_two h2.symm)
  have key : ∀ x : G.halfEdgesAt (G.endAt f 0), x ≠ ⟨(f, 0), rfl⟩ → x.1.1 ∉ S → False := by
    intro x hx hxS
    have hx' : x.1.1 ∈ S ∪ L₁ ∪ L₂ ∪ L₃ := by
      rw [hcov]
      exact Finset.mem_univ _
    simp only [Finset.mem_union] at hx'
    rcases hx' with ((hx' | hx') | hx') | hx'
    · exact hxS hx'
    · have := G.two_le_degreeIn_of_ne ⟨(f, 0), rfl⟩ x hx.symm h.1 hx'
      rw [h₁] at this
      omega
    · have := G.two_le_degreeIn_of_ne ⟨(f, 0), rfl⟩ x hx.symm h.2.1 hx'
      rw [h₂] at this
      omega
    · have := G.two_le_degreeIn_of_ne ⟨(f, 0), rfl⟩ x hx.symm h.2.2 hx'
      rw [h₃] at this
      omega
  by_cases hfa : a = ⟨(f, 0), rfl⟩
  · exact key b (fun hb' ↦ hab (hfa.trans hb'.symm)) (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).2
  · exact key a hfa (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).2).2

end Degrees

/-- **The Karabáš–Máčajová corollary**, taken as a hypothesis.  A loopless cubic multigraph
with a perfect matching `S` whose complement consists of two odd circuits joined by exactly three
edges of `S` has a cover by `S` and three further perfect matchings.  This is the
prescribed-matching form of Corollary 3.7 of Karabáš–Máčajová, obtained in the note by cutting the
three joining edges and gluing proper four-covers of the two Hamiltonian `3`-poles; it is not
formalized here. -/
def KMThreeSpokes : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (K : LoopMultigraph V' E'), (∀ v, K.degree v = 3) → (∀ e, K.endAt e 0 ≠ K.endAt e 1) →
    ∀ S : Finset E', K.IsPerfectMatching S →
    ∀ A B : K.OrdinaryCircuit, Disjoint A.edges B.edges →
      A.edges ∪ B.edges = Finset.univ \ S → Odd A.edges.card → Odd B.edges.card →
      (S.filter fun e ↦ ¬ (K.endAt e 0 ∈ K.edgeSupport A.edges ↔
        K.endAt e 1 ∈ K.edgeSupport A.edges)).card = 3 →
      ∃ L₁ L₂ L₃ : Finset E', K.IsPerfectMatching L₁ ∧ K.IsPerfectMatching L₂ ∧
        K.IsPerfectMatching L₃ ∧ S ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ

namespace TwoCircuitFactor

variable (F : H.TwoCircuitFactor)

/-- The complementary matching of the two-circuit factor. -/
def compl : Finset E := Finset.univ \ (F.A.edges ∪ F.B.edges)

theorem mem_compl_iff {e : E} : e ∈ F.compl ↔ e ∉ F.A.edges ∧ e ∉ F.B.edges := by
  simp [compl]

omit [DecidableEq E] in
theorem disjoint_edges : Disjoint F.A.edges F.B.edges :=
  Finset.disjoint_left.mpr fun _ hA hB ↦ F.not_mem_A_of_mem_B hB hA

/-- The complement of a two-circuit factor of a cubic graph is a perfect matching. -/
theorem compl_perfect (hCubic : ∀ v : V, H.degree v = 3) : H.IsPerfectMatching F.compl := by
  intro v
  have h := degreeIn_add_compl (H := H) (F.A.edges ∪ F.B.edges) v
  rw [hCubic v, degreeIn_union_of_disjoint F.disjoint_edges] at h
  rcases F.cover v with hv | hv
  · rw [F.A.twoRegular v hv, degreeIn_eq_zero_of (F := F.B.edges)
      (fun e he k h' ↦ F.disjoint v hv (by rw [← h']; exact F.endAt_mem_B he k))] at h
    change H.degreeIn (Finset.univ \ (F.A.edges ∪ F.B.edges)) v = 1
    omega
  · rw [F.B.twoRegular v hv, degreeIn_eq_zero_of (F := F.A.edges)
      (fun e he k h' ↦ F.disjoint _ (by rw [← h']; exact F.endAt_mem_A he k) hv)] at h
    change H.degreeIn (Finset.univ \ (F.A.edges ∪ F.B.edges)) v = 1
    omega

/-- The cross-spokes: matching edges joining the two circuits. -/
def cross : Finset E :=
  F.compl.filter fun e ↦ ¬ ((H.endAt e 0 ∈ F.A.vertices) ↔ (H.endAt e 1 ∈ F.A.vertices))

theorem mem_cross_iff_A {e : E} (he : e ∈ F.compl) :
    e ∈ F.cross ↔ ¬ (H.endAt e 0 ∈ F.A.vertices ↔ H.endAt e 1 ∈ F.A.vertices) := by
  simp only [cross, Finset.mem_filter, he, true_and]

omit [DecidableEq E] in
theorem mem_B_iff_not_mem_A (v : V) : v ∈ F.B.vertices ↔ v ∉ F.A.vertices :=
  ⟨fun hB hA ↦ F.disjoint v hA hB, fun hA ↦ (F.cover v).resolve_left hA⟩

theorem mem_cross_iff_B {e : E} (he : e ∈ F.compl) :
    e ∈ F.cross ↔ ¬ (H.endAt e 0 ∈ F.B.vertices ↔ H.endAt e 1 ∈ F.B.vertices) := by
  rw [F.mem_cross_iff_A he, F.mem_B_iff_not_mem_A, F.mem_B_iff_not_mem_A, not_iff_not]
  exact not_iff_not.symm

section Reduction

variable (N : Finset E)

/-- The matching `S = M ∩ N` retained by the reduction. -/
def sat : Finset E := F.compl ∩ N

/-- The vertices covered by `S`. -/
def W : Finset V := H.edgeSupport (F.sat N)

theorem sat_subset_compl : F.sat N ⊆ F.compl := Finset.inter_subset_left

theorem sat_subset_N : F.sat N ⊆ N := Finset.inter_subset_right

variable (hCubic : ∀ v : V, H.degree v = 3) (hN : H.IsPerfectMatching N)

section OneCircuit

variable (C : H.TraversedCircuit) (hbd : ∀ p, (C.boundaryHalfEdge hCubic p).1 ∈ F.compl)
  (hCe : ∀ e ∈ C.edges, e ∉ F.compl)

/-- The degree of a circuit vertex in an edge set, in terms of its three half-edges. -/
theorem degreeIn_at_position (X : Finset E) (p : C.tour.Pos) :
    H.degreeIn X (C.tour.vertexAt p) =
      (if (C.tour.edge p).1 ∈ X then 1 else 0) +
        ((if (C.tour.edge (C.tour.prev p)).1 ∈ X then 1 else 0) +
          (if (C.boundaryHalfEdge hCubic p).1 ∈ X then 1 else 0)) := by
  rw [H.degreeIn_eq_card_halfEdges]
  let eq := C.positionHalfEdgeEquiv hCubic p
  rw [card_filter_of_three (eq 0) (eq 1) (eq 2) (eq.injective.ne (by decide))
    (eq.injective.ne (by decide)) (eq.injective.ne (by decide)) (fun x ↦ by
      obtain ⟨j, hj⟩ := eq.surjective x
      fin_cases j
      · exact Or.inl hj.symm
      · exact Or.inr (Or.inl hj.symm)
      · exact Or.inr (Or.inr hj.symm))]
  rfl

include hbd hCe in
/-- A position is marked exactly when its boundary edge lies in `N`. -/
theorem marked_iff (p : C.tour.Pos) :
    C.Marked (F.W N) p ↔ (C.boundaryHalfEdge hCubic p).1 ∈ N := by
  constructor
  · intro hp
    obtain ⟨e, he, k, hk⟩ := H.mem_edgeSupport_iff.mp hp
    obtain ⟨j, hj⟩ := C.positionHalfEdge_surjective hCubic p ⟨(e, k), hk⟩
    have heS : e ∈ F.sat N := he
    have hmem : (C.positionHalfEdge hCubic p j).1 ∈ C.edges ∨
        C.positionHalfEdge hCubic p j = C.boundaryHalfEdge hCubic p := by
      fin_cases j
      · exact Or.inl (C.tour.edge p).2
      · exact Or.inl (C.tour.edge (C.tour.prev p)).2
      · exact Or.inr rfl
    rw [hj] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (F.sat_subset_compl N heS) (hCe _ hmem)
    · have : (C.boundaryHalfEdge hCubic p).1 = e := (congrArg Prod.fst hmem).symm
      rw [this]
      exact F.sat_subset_N N heS
  · intro h
    apply H.mem_edgeSupport_iff.mpr
    exact ⟨_, Finset.mem_inter.mpr ⟨hbd p, h⟩, _, C.boundaryHalfEdge_endpoint hCubic p⟩

include hN in
theorem N_at_position (p : C.tour.Pos) :
    (if (C.tour.edge p).1 ∈ N then 1 else 0) +
      ((if (C.tour.edge (C.tour.prev p)).1 ∈ N then 1 else 0) +
        (if (C.boundaryHalfEdge hCubic p).1 ∈ N then 1 else 0)) = 1 := by
  rw [← degreeIn_at_position hCubic C N p]
  exact hN _

include hN hbd hCe in
theorem not_mem_N_of_marked {p : C.tour.Pos} (hp : C.Marked (F.W N) p) :
    (C.tour.edge p).1 ∉ N ∧ (C.tour.edge (C.tour.prev p)).1 ∉ N := by
  have h := N_at_position N hCubic hN C p
  rw [if_pos ((F.marked_iff N hCubic C hbd hCe p).mp hp)] at h
  constructor
  · intro h'
    rw [if_pos h'] at h
    omega
  · intro h'
    rw [if_pos h'] at h
    omega

include hN hbd hCe in
theorem mem_N_iff_of_not_marked {p : C.tour.Pos} (hp : ¬ C.Marked (F.W N) p) :
    (C.tour.edge p).1 ∈ N ↔ (C.tour.edge (C.tour.prev p)).1 ∉ N := by
  have h := N_at_position N hCubic hN C p
  rw [if_neg (fun h' ↦ hp ((F.marked_iff N hCubic C hbd hCe p).mpr h'))] at h
  by_cases h1 : (C.tour.edge p).1 ∈ N
  · rw [if_pos h1] at h
    refine iff_of_true h1 (fun h2 ↦ ?_)
    rw [if_pos h2] at h
    omega
  · rw [if_neg h1] at h
    refine iff_of_false h1 (fun h2 ↦ ?_)
    rw [if_neg h2] at h
    omega

omit [DecidableEq E] in
theorem prev_add_succ (p : C.tour.Pos) (m : ℕ) :
    C.tour.prev (p + ((m + 1 : ℕ) : C.tour.Pos)) = p + (m : C.tour.Pos) := by
  rw [EulerTour.prev_eq_sub_one, C.posCast_add, C.posCast_one]
  abel

include hN hbd hCe in
/-- Along an arc from a marked position, the edges of `N` are those at odd distance. -/
theorem mem_N_iff_odd {p : C.tour.Pos} (hp : C.Marked (F.W N) p) :
    ∀ m : ℕ, m < C.forward (F.W N) hp → ((C.tour.edge (p + (m : C.tour.Pos))).1 ∈ N ↔ Odd m) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [C.posCast_zero, add_zero]
    exact iff_of_false (F.not_mem_N_of_marked N hCubic hN C hbd hCe hp).1 (by decide)
  | succ m ih =>
    intro hm
    have hnot : ¬ C.Marked (F.W N) (p + ((m + 1 : ℕ) : C.tour.Pos)) :=
      C.not_marked_of_lt_forward (F.W N) hp (Nat.succ_pos m) hm
    rw [F.mem_N_iff_of_not_marked N hCubic hN C hbd hCe hnot, prev_add_succ C, ih (by omega),
      Nat.odd_add_one]

include hN hbd hCe in
/-- Every arc between consecutive marked positions has odd length. -/
theorem forward_odd {p : C.tour.Pos} (hp : C.Marked (F.W N) p) :
    Odd (C.forward (F.W N) hp) := by
  have hpos := C.forward_pos (F.W N) hp
  have hnext := C.marked_nextM (F.W N) hp
  have h := (F.not_mem_N_of_marked N hCubic hN C hbd hCe hnext).2
  unfold TraversedCircuit.nextM at h
  obtain ⟨f, hf⟩ : ∃ f, C.forward (F.W N) hp = f + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hf, prev_add_succ C] at h
  have := F.mem_N_iff_odd N hCubic hN C hbd hCe hp f (by omega)
  rw [hf]
  rw [Nat.odd_add_one]
  exact fun hodd ↦ h (this.mpr hodd)

end OneCircuit

/-- The boundary edge at a vertex of `A` is a matching edge. -/
theorem boundary_A_mem_compl (p : F.A.tour.Pos) : (F.A.boundaryHalfEdge hCubic p).1 ∈ F.compl := by
  rw [F.mem_compl_iff]
  refine ⟨F.A.boundaryHalfEdge_not_mem hCubic p, ?_⟩
  apply F.not_mem_B_of_endAt_mem_A (i := (F.A.boundaryHalfEdge hCubic p).2)
  rw [F.A.boundaryHalfEdge_endpoint hCubic p]
  exact F.A.vertexAt_mem_vertices p

theorem boundary_B_mem_compl (p : F.B.tour.Pos) : (F.B.boundaryHalfEdge hCubic p).1 ∈ F.compl := by
  rw [F.mem_compl_iff]
  refine ⟨?_, F.B.boundaryHalfEdge_not_mem hCubic p⟩
  apply F.not_mem_A_of_endAt_mem_B (i := (F.B.boundaryHalfEdge hCubic p).2)
  rw [F.B.boundaryHalfEdge_endpoint hCubic p]
  exact F.B.vertexAt_mem_vertices p

theorem A_edge_notin_compl (e : E) (he : e ∈ F.A.edges) : e ∉ F.compl :=
  fun h ↦ ((F.mem_compl_iff).mp h).1 he

theorem B_edge_notin_compl (e : E) (he : e ∈ F.B.edges) : e ∉ F.compl :=
  fun h ↦ ((F.mem_compl_iff).mp h).2 he

/-! ### The reduced graph -/

/-- Representative edges of `A`: the tour edge leaving each marked position. -/
def repsA : Finset E :=
  Finset.univ.filter fun f ↦ ∃ p, F.A.Marked (F.W N) p ∧ f = (F.A.tour.edge p).1

/-- Representative edges of `B`. -/
def repsB : Finset E :=
  Finset.univ.filter fun f ↦ ∃ p, F.B.Marked (F.W N) p ∧ f = (F.B.tour.edge p).1

theorem mem_repsA {f : E} : f ∈ F.repsA N ↔ ∃ p, F.A.Marked (F.W N) p ∧ f = (F.A.tour.edge p).1 := by
  simp [repsA]

theorem mem_repsB {f : E} : f ∈ F.repsB N ↔ ∃ p, F.B.Marked (F.W N) p ∧ f = (F.B.tour.edge p).1 := by
  simp [repsB]

theorem repsA_subset : F.repsA N ⊆ F.A.edges := by
  intro f hf
  obtain ⟨p, -, rfl⟩ := (F.mem_repsA N).mp hf
  exact (F.A.tour.edge p).2

theorem repsB_subset : F.repsB N ⊆ F.B.edges := by
  intro f hf
  obtain ⟨p, -, rfl⟩ := (F.mem_repsB N).mp hf
  exact (F.B.tour.edge p).2

theorem edge_mem_repsA {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    (F.A.tour.edge p).1 ∈ F.repsA N := (F.mem_repsA N).mpr ⟨p, hp, rfl⟩

theorem edge_mem_repsB {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    (F.B.tour.edge p).1 ∈ F.repsB N := (F.mem_repsB N).mpr ⟨p, hp, rfl⟩

theorem repsA_notin_sat {f : E} (hf : f ∈ F.repsA N) : f ∉ F.sat N :=
  fun h ↦ F.A_edge_notin_compl f (F.repsA_subset N hf) (F.sat_subset_compl N h)

theorem repsB_notin_sat {f : E} (hf : f ∈ F.repsB N) : f ∉ F.sat N :=
  fun h ↦ F.B_edge_notin_compl f (F.repsB_subset N hf) (F.sat_subset_compl N h)

theorem repsA_notin_repsB {f : E} (hf : f ∈ F.repsA N) : f ∉ F.repsB N :=
  fun h ↦ F.not_mem_A_of_mem_B (F.repsB_subset N h) (F.repsA_subset N hf)

/-- The position of an edge of `A`. -/
def posA {f : E} (hf : f ∈ F.A.edges) : F.A.tour.Pos := F.A.tour.edge.symm ⟨f, hf⟩

/-- The position of an edge of `B`. -/
def posB {f : E} (hf : f ∈ F.B.edges) : F.B.tour.Pos := F.B.tour.edge.symm ⟨f, hf⟩

omit [DecidableEq E] in
theorem edge_posA {f : E} (hf : f ∈ F.A.edges) : (F.A.tour.edge (F.posA hf)).1 = f := by
  simp [posA]

omit [DecidableEq E] in
theorem edge_posB {f : E} (hf : f ∈ F.B.edges) : (F.B.tour.edge (F.posB hf)).1 = f := by
  simp [posB]

omit [DecidableEq E] in
theorem posA_edge (p : F.A.tour.Pos) : F.posA (F.A.tour.edge p).2 = p := by
  simp [posA]

omit [DecidableEq E] in
theorem posB_edge (p : F.B.tour.Pos) : F.posB (F.B.tour.edge p).2 = p := by
  simp [posB]

theorem posA_marked {f : E} (hf : f ∈ F.repsA N) :
    F.A.Marked (F.W N) (F.posA (F.repsA_subset N hf)) := by
  obtain ⟨p, hp, rfl⟩ := (F.mem_repsA N).mp hf
  rw [F.posA_edge]
  exact hp

theorem posB_marked {f : E} (hf : f ∈ F.repsB N) :
    F.B.Marked (F.W N) (F.posB (F.repsB_subset N hf)) := by
  obtain ⟨p, hp, rfl⟩ := (F.mem_repsB N).mp hf
  rw [F.posB_edge]
  exact hp

/-- The vertices of the reduced graph: the vertices covered by `S`. -/
abbrev RedV := {w : V // w ∈ F.W N}

/-- The edges of the reduced graph: the edges of `S` and the representatives. -/
abbrev RedE := {f : E // f ∈ F.sat N ∨ f ∈ F.repsA N ∨ f ∈ F.repsB N}

/-- The endpoints of the reduced graph: `S`-edges keep their ends, a representative of an arc
runs from the arc's marked position to the next marked position. -/
noncomputable def redEnd (f : F.RedE N) (k : Fin 2) : F.RedV N :=
  if hS : f.1 ∈ F.sat N then ⟨H.endAt f.1 k, H.mem_edgeSupport_iff.mpr ⟨f.1, hS, k, rfl⟩⟩
  else if hA : f.1 ∈ F.repsA N then
    (if k = 0 then ⟨F.A.tour.vertexAt (F.posA (F.repsA_subset N hA)), F.posA_marked N hA⟩
      else ⟨F.A.tour.vertexAt (F.A.nextM (F.W N) (F.posA_marked N hA)),
        F.A.marked_nextM (F.W N) (F.posA_marked N hA)⟩)
  else
    (if k = 0 then ⟨F.B.tour.vertexAt (F.posB (F.repsB_subset N
        ((f.2.resolve_left hS).resolve_left hA))),
        F.posB_marked N ((f.2.resolve_left hS).resolve_left hA)⟩
      else ⟨F.B.tour.vertexAt (F.B.nextM (F.W N)
        (F.posB_marked N ((f.2.resolve_left hS).resolve_left hA))),
        F.B.marked_nextM (F.W N) (F.posB_marked N ((f.2.resolve_left hS).resolve_left hA))⟩)

/-- The reduced graph. -/
noncomputable def red : LoopMultigraph (F.RedV N) (F.RedE N) where
  endAt := F.redEnd N

theorem red_endAt (f : F.RedE N) (k : Fin 2) : (F.red N).endAt f k = F.redEnd N f k := rfl

theorem redEnd_sat {f : F.RedE N} (hS : f.1 ∈ F.sat N) (k : Fin 2) :
    (F.redEnd N f k).1 = H.endAt f.1 k := by
  unfold redEnd
  rw [dif_pos hS]

theorem redEnd_repA_zero {f : F.RedE N} (hA : f.1 ∈ F.repsA N) :
    (F.redEnd N f 0).1 = F.A.tour.vertexAt (F.posA (F.repsA_subset N hA)) := by
  unfold redEnd
  rw [dif_neg (F.repsA_notin_sat N hA), dif_pos hA, if_pos rfl]

theorem redEnd_repA_one {f : F.RedE N} (hA : f.1 ∈ F.repsA N) :
    (F.redEnd N f 1).1 = F.A.tour.vertexAt (F.A.nextM (F.W N) (F.posA_marked N hA)) := by
  unfold redEnd
  rw [dif_neg (F.repsA_notin_sat N hA), dif_pos hA, if_neg (by decide)]

theorem redEnd_repB_zero {f : F.RedE N} (hB : f.1 ∈ F.repsB N) :
    (F.redEnd N f 0).1 = F.B.tour.vertexAt (F.posB (F.repsB_subset N hB)) := by
  unfold redEnd
  rw [dif_neg (F.repsB_notin_sat N hB), dif_neg (fun hA ↦ F.repsA_notin_repsB N hA hB),
    if_pos rfl]

theorem redEnd_repB_one {f : F.RedE N} (hB : f.1 ∈ F.repsB N) :
    (F.redEnd N f 1).1 = F.B.tour.vertexAt (F.B.nextM (F.W N) (F.posB_marked N hB)) := by
  unfold redEnd
  rw [dif_neg (F.repsB_notin_sat N hB), dif_neg (fun hA ↦ F.repsA_notin_repsB N hA hB),
    if_neg (by decide)]

theorem redEnd_repA_mem {f : F.RedE N} (hA : f.1 ∈ F.repsA N) (k : Fin 2) :
    (F.redEnd N f k).1 ∈ F.A.vertices := by
  rcases fin2_cases k with rfl | rfl
  · rw [F.redEnd_repA_zero N hA]
    exact F.A.vertexAt_mem_vertices _
  · rw [F.redEnd_repA_one N hA]
    exact F.A.vertexAt_mem_vertices _

theorem redEnd_repB_mem {f : F.RedE N} (hB : f.1 ∈ F.repsB N) (k : Fin 2) :
    (F.redEnd N f k).1 ∈ F.B.vertices := by
  rcases fin2_cases k with rfl | rfl
  · rw [F.redEnd_repB_zero N hB]
    exact F.B.vertexAt_mem_vertices _
  · rw [F.redEnd_repB_one N hB]
    exact F.B.vertexAt_mem_vertices _







omit [DecidableEq E] in
theorem _root_.GraphPuzzles.LoopMultigraph.TraversedCircuit.nextM_congr (C : H.TraversedCircuit)
    (W : Finset V) {p p' : C.tour.Pos} (hp : C.Marked W p) (hp' : C.Marked W p') (h : p = p') :
    C.nextM W hp = C.nextM W hp' := by
  subst h
  rfl

section VertexA

variable (hthree : (N ∩ F.cross).card = 3)

/-- A representative of `A` as an edge of the reduced graph. -/
def repEdgeA {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) : F.RedE N :=
  ⟨(F.A.tour.edge p).1, Or.inr (Or.inl (F.edge_mem_repsA N hp))⟩

theorem repEdgeA_val {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    (F.repEdgeA N hp).1 = (F.A.tour.edge p).1 := rfl

theorem posA_repEdge {p : F.A.tour.Pos} (_hp : F.A.Marked (F.W N) p)
    (h : (F.A.tour.edge p).1 ∈ F.A.edges) : F.posA h = p := by
  unfold posA
  rw [Equiv.symm_apply_eq]

theorem redEnd_repEdgeA_zero {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    (F.redEnd N (F.repEdgeA N hp) 0).1 = F.A.tour.vertexAt p := by
  rw [F.redEnd_repA_zero N (F.edge_mem_repsA N hp)]
  exact congrArg F.A.tour.vertexAt (F.posA_repEdge N hp _)

theorem redEnd_repEdgeA_one {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    (F.redEnd N (F.repEdgeA N hp) 1).1 = F.A.tour.vertexAt (F.A.nextM (F.W N) hp) := by
  rw [F.redEnd_repA_one N (F.edge_mem_repsA N hp)]
  congr 1
  exact TraversedCircuit.nextM_congr _ _ _ _ (F.posA_repEdge N hp _)

theorem cross_end_A {e : E} (he : e ∈ F.cross) :
    ∃ k, H.endAt e k ∈ F.A.vertices ∧ H.endAt e (Fin.rev k) ∈ F.B.vertices := by
  have hc := (Finset.mem_filter.mp he).2
  rcases F.cover (H.endAt e 0) with h0 | h0 <;> rcases F.cover (H.endAt e 1) with h1 | h1
  · exact absurd (iff_of_true h0 h1) hc
  · exact ⟨0, h0, h1⟩
  · exact ⟨1, h1, h0⟩
  · exact absurd (iff_of_false (fun hA ↦ F.disjoint _ hA h0) (fun hA ↦ F.disjoint _ hA h1)) hc

include hthree in
theorem exists_markedA : ∃ p, F.A.Marked (F.W N) p := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (N ∩ F.cross).card)
  obtain ⟨k, hk, -⟩ := F.cross_end_A (Finset.mem_inter.mp he).2
  have hW : H.endAt e k ∈ F.W N := H.mem_edgeSupport_iff.mpr ⟨e, Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp he).2).1, (Finset.mem_inter.mp he).1⟩, k, rfl⟩
  refine ⟨F.A.positionVertexEquiv.symm ⟨_, hk⟩, ?_⟩
  unfold TraversedCircuit.Marked
  rw [← F.A.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]
  exact hW

include hN hthree in
/-- Every marked position of `A` has a different marked companion. -/
theorem two_markedA (p : F.A.tour.Pos) :
    ∃ p', F.A.Marked (F.W N) p' ∧ p' ≠ p := by
  set w := F.A.tour.vertexAt p with hw
  have hle : ((N ∩ F.cross).filter fun e ↦ ∃ k, H.endAt e k = w).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha', ka, hka⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb', kb, hkb⟩ := Finset.mem_filter.mp hb
    by_contra hab
    have h2 := H.two_le_degreeIn_of_ne (M := N) ⟨(a, ka), hka⟩ ⟨(b, kb), hkb⟩
      (fun h ↦ hab (congrArg (fun x ↦ x.1.1) h)) (Finset.mem_inter.mp ha').1
      (Finset.mem_inter.mp hb').1
    have := hN w
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := N ∩ F.cross)
    (p := fun e ↦ ∃ k, H.endAt e k = w)
  rw [hthree] at hsplit
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega :
    0 < ((N ∩ F.cross).filter fun e ↦ ¬ ∃ k, H.endAt e k = w).card)
  obtain ⟨he', hne⟩ := Finset.mem_filter.mp he
  obtain ⟨k, hk, -⟩ := F.cross_end_A (Finset.mem_inter.mp he').2
  have hW : H.endAt e k ∈ F.W N := H.mem_edgeSupport_iff.mpr ⟨e, Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp he').2).1, (Finset.mem_inter.mp he').1⟩, k, rfl⟩
  refine ⟨F.A.positionVertexEquiv.symm ⟨_, hk⟩, ?_, ?_⟩
  · unfold TraversedCircuit.Marked
    rw [← F.A.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]
    exact hW
  · intro h
    apply hne
    refine ⟨k, ?_⟩
    have := congrArg F.A.tour.vertexAt h
    rw [← F.A.positionVertexEquiv_apply_val, Equiv.apply_symm_apply] at this
    exact this

variable {w : V} (hw : w ∈ F.W N) (hwA : w ∈ F.A.vertices)

/-- The position of a marked vertex of `A`. -/
noncomputable def posAV : F.A.tour.Pos := F.A.positionVertexEquiv.symm ⟨w, hwA⟩

omit [DecidableEq E] in
theorem vertexAt_posAV : F.A.tour.vertexAt (F.posAV hwA) = w := by
  unfold posAV
  rw [← F.A.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]

include hw in
theorem marked_posAV : F.A.Marked (F.W N) (F.posAV hwA) := by
  unfold TraversedCircuit.Marked
  rw [F.vertexAt_posAV hwA]
  exact hw

theorem boundary_A_mem_sat_of_marked {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    (F.A.boundaryHalfEdge hCubic p).1 ∈ F.sat N :=
  Finset.mem_inter.mpr ⟨F.boundary_A_mem_compl hCubic p,
    (F.marked_iff N hCubic F.A (F.boundary_A_mem_compl hCubic) (F.A_edge_notin_compl) p).mp hp⟩

/-- The three half-edges of the reduced graph at a marked vertex of `A`. -/
noncomputable def yAS : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(⟨(F.A.boundaryHalfEdge hCubic (F.posAV hwA)).1,
      Or.inl (F.boundary_A_mem_sat_of_marked N hCubic (F.marked_posAV N hw hwA))⟩,
    (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).2), by
    apply Subtype.ext
    change (F.redEnd N _ _).1 = w
    rw [F.redEnd_sat N (F.boundary_A_mem_sat_of_marked N hCubic (F.marked_posAV N hw hwA))]
    change H.endAt (F.A.boundaryHalfEdge hCubic _).1 (F.A.boundaryHalfEdge hCubic _).2 = w
    rw [F.A.boundaryHalfEdge_endpoint hCubic, F.vertexAt_posAV hwA]⟩

noncomputable def yA0 : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(F.repEdgeA N (F.marked_posAV N hw hwA), 0), by
    apply Subtype.ext
    change (F.redEnd N _ 0).1 = w
    rw [F.redEnd_repEdgeA_zero, F.vertexAt_posAV hwA]⟩

noncomputable def yA1 : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(F.repEdgeA N (F.A.marked_prevM (F.W N) (F.exists_markedA N hthree) (F.posAV hwA)), 1),
    by
    apply Subtype.ext
    change (F.redEnd N _ 1).1 = w
    rw [F.redEnd_repEdgeA_one, F.A.nextM_prevM (F.W N) (F.exists_markedA N hthree)
      (F.marked_posAV N hw hwA), F.vertexAt_posAV hwA]⟩

theorem yAS_ne_yA0 : F.yAS N hCubic hw hwA ≠ F.yA0 N hw hwA := by
  intro h
  have h' : (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).1 =
      (F.A.tour.edge (F.posAV hwA)).1 := congrArg (fun x ↦ x.1.1.1) h
  apply F.A.boundaryHalfEdge_not_mem hCubic (F.posAV hwA)
  rw [h']
  exact (F.A.tour.edge _).2

theorem yAS_ne_yA1 : F.yAS N hCubic hw hwA ≠ F.yA1 N hthree hw hwA := by
  intro h
  have h' : (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).1 =
      (F.A.tour.edge _).1 := congrArg (fun x ↦ x.1.1.1) h
  apply F.A.boundaryHalfEdge_not_mem hCubic (F.posAV hwA)
  rw [h']
  exact (F.A.tour.edge _).2

include hN hw in
theorem prevM_ne_posAV :
    F.A.prevM (F.W N) (F.exists_markedA N hthree) (F.posAV hwA) ≠ F.posAV hwA := by
  intro h
  have hn := F.A.nextM_prevM (F.W N) (F.exists_markedA N hthree) (F.marked_posAV N hw hwA)
  obtain ⟨p', hp', hne⟩ := F.two_markedA N hN hthree (F.posAV hwA)
  apply F.A.nextM_ne_of_two (F.W N) (F.marked_posAV N hw hwA) hp' hne
  exact (TraversedCircuit.nextM_congr _ _ _ _ h.symm).trans hn

include hN in
theorem yA0_ne_yA1 : F.yA0 N hw hwA ≠ F.yA1 N hthree hw hwA := by
  intro h
  have h' : (F.A.tour.edge (F.posAV hwA)).1 = (F.A.tour.edge _).1 :=
    congrArg (fun x ↦ x.1.1.1) h
  have := F.A.tour.edge.injective (Subtype.ext h')
  exact F.prevM_ne_posAV N hN hthree hw hwA this.symm

/-- The half-edges of the reduced graph at a marked vertex of `A`. -/
theorem red_halfEdge_cases_A (x : (F.red N).halfEdgesAt ⟨w, hw⟩) :
    x = F.yAS N hCubic hw hwA ∨ x = F.yA0 N hw hwA ∨
      x = F.yA1 N hthree hw hwA := by
  obtain ⟨⟨⟨f, hf⟩, k⟩, hx⟩ := x
  have hx' : (F.redEnd N ⟨f, hf⟩ k).1 = w := congrArg Subtype.val hx
  rcases hf with hS | hA | hB
  · rw [F.redEnd_sat N hS] at hx'
    have hxH : H.endAt f k = F.A.tour.vertexAt (F.posAV hwA) := by
      rw [F.vertexAt_posAV hwA]
      exact hx'
    obtain ⟨j, hj⟩ := F.A.positionHalfEdge_surjective hCubic _ ⟨(f, k), hxH⟩
    have hmem : (F.A.positionHalfEdge hCubic (F.posAV hwA) j).1 ∈ F.A.edges ∨
        F.A.positionHalfEdge hCubic (F.posAV hwA) j =
          F.A.boundaryHalfEdge hCubic (F.posAV hwA) := by
      fin_cases j
      · exact Or.inl (F.A.tour.edge _).2
      · exact Or.inl (F.A.tour.edge _).2
      · exact Or.inr rfl
    rw [hj] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (F.sat_subset_compl N hS) (F.A_edge_notin_compl f hmem)
    · left
      have h1 : f = (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).1 := congrArg Prod.fst hmem
      have h2 : k = (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).2 := congrArg Prod.snd hmem
      apply Subtype.ext
      exact Prod.ext (Subtype.ext h1) h2
  ·
    rcases fin2_cases k with rfl | rfl
    · rw [F.redEnd_repA_zero N hA] at hx'
      have hp : F.posA (F.repsA_subset N hA) = F.posAV hwA := by
        apply F.A.positionVertexEquiv.injective
        apply Subtype.ext
        rw [F.A.positionVertexEquiv_apply_val, F.A.positionVertexEquiv_apply_val, hx',
          F.vertexAt_posAV hwA]
      right; left
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change f = (F.A.tour.edge (F.posAV hwA)).1
        rw [← hp, F.edge_posA]
      · rfl
    · rw [F.redEnd_repA_one N hA] at hx'
      have hp : F.A.nextM (F.W N) (F.posA_marked N hA) = F.posAV hwA := by
        apply F.A.positionVertexEquiv.injective
        apply Subtype.ext
        rw [F.A.positionVertexEquiv_apply_val, F.A.positionVertexEquiv_apply_val, hx',
          F.vertexAt_posAV hwA]
      have hp' : F.posA (F.repsA_subset N hA) =
          F.A.prevM (F.W N) (F.exists_markedA N hthree) (F.posAV hwA) := by
        rw [← hp, F.A.prevM_nextM]
      right; right
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change f = (F.A.tour.edge _).1
        rw [← hp', F.edge_posA]
      · rfl
  ·
    exfalso
    have := F.redEnd_repB_mem N (f := ⟨f, Or.inr (Or.inr hB)⟩) hB k
    rw [hx'] at this
    exact F.disjoint _ hwA this

end VertexA

section VertexB

variable (hthree : (N ∩ F.cross).card = 3)

/-- A representative of `B` as an edge of the reduced graph. -/
def repEdgeB {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) : F.RedE N :=
  ⟨(F.B.tour.edge p).1, Or.inr (Or.inr (F.edge_mem_repsB N hp))⟩

theorem repEdgeB_val {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    (F.repEdgeB N hp).1 = (F.B.tour.edge p).1 := rfl

theorem posB_repEdge {p : F.B.tour.Pos} (_hp : F.B.Marked (F.W N) p)
    (h : (F.B.tour.edge p).1 ∈ F.B.edges) : F.posB h = p := by
  unfold posB
  rw [Equiv.symm_apply_eq]

theorem redEnd_repEdgeB_zero {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    (F.redEnd N (F.repEdgeB N hp) 0).1 = F.B.tour.vertexAt p := by
  rw [F.redEnd_repB_zero N (F.edge_mem_repsB N hp)]
  exact congrArg F.B.tour.vertexAt (F.posB_repEdge N hp _)

theorem redEnd_repEdgeB_one {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    (F.redEnd N (F.repEdgeB N hp) 1).1 = F.B.tour.vertexAt (F.B.nextM (F.W N) hp) := by
  rw [F.redEnd_repB_one N (F.edge_mem_repsB N hp)]
  congr 1
  exact TraversedCircuit.nextM_congr _ _ _ _ (F.posB_repEdge N hp _)

theorem cross_end_B {e : E} (he : e ∈ F.cross) :
    ∃ k, H.endAt e k ∈ F.B.vertices ∧ H.endAt e (Fin.rev k) ∈ F.A.vertices := by
  have hc := (Finset.mem_filter.mp he).2
  rcases F.cover (H.endAt e 0) with h0 | h0 <;> rcases F.cover (H.endAt e 1) with h1 | h1
  · exact absurd (iff_of_true h0 h1) hc
  · exact ⟨1, h1, h0⟩
  · exact ⟨0, h0, h1⟩
  · exact absurd (iff_of_false (fun hA ↦ F.disjoint _ hA h0) (fun hA ↦ F.disjoint _ hA h1)) hc

include hthree in
theorem exists_markedB : ∃ p, F.B.Marked (F.W N) p := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (N ∩ F.cross).card)
  obtain ⟨k, hk, -⟩ := F.cross_end_B (Finset.mem_inter.mp he).2
  have hW : H.endAt e k ∈ F.W N := H.mem_edgeSupport_iff.mpr ⟨e, Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp he).2).1, (Finset.mem_inter.mp he).1⟩, k, rfl⟩
  refine ⟨F.B.positionVertexEquiv.symm ⟨_, hk⟩, ?_⟩
  unfold TraversedCircuit.Marked
  rw [← F.B.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]
  exact hW

include hN hthree in
/-- Every marked position of `B` has a different marked companion. -/
theorem two_markedB (p : F.B.tour.Pos) :
    ∃ p', F.B.Marked (F.W N) p' ∧ p' ≠ p := by
  set w := F.B.tour.vertexAt p with hw
  have hle : ((N ∩ F.cross).filter fun e ↦ ∃ k, H.endAt e k = w).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha', ka, hka⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb', kb, hkb⟩ := Finset.mem_filter.mp hb
    by_contra hab
    have h2 := H.two_le_degreeIn_of_ne (M := N) ⟨(a, ka), hka⟩ ⟨(b, kb), hkb⟩
      (fun h ↦ hab (congrArg (fun x ↦ x.1.1) h)) (Finset.mem_inter.mp ha').1
      (Finset.mem_inter.mp hb').1
    have := hN w
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := N ∩ F.cross)
    (p := fun e ↦ ∃ k, H.endAt e k = w)
  rw [hthree] at hsplit
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega :
    0 < ((N ∩ F.cross).filter fun e ↦ ¬ ∃ k, H.endAt e k = w).card)
  obtain ⟨he', hne⟩ := Finset.mem_filter.mp he
  obtain ⟨k, hk, -⟩ := F.cross_end_B (Finset.mem_inter.mp he').2
  have hW : H.endAt e k ∈ F.W N := H.mem_edgeSupport_iff.mpr ⟨e, Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp he').2).1, (Finset.mem_inter.mp he').1⟩, k, rfl⟩
  refine ⟨F.B.positionVertexEquiv.symm ⟨_, hk⟩, ?_, ?_⟩
  · unfold TraversedCircuit.Marked
    rw [← F.B.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]
    exact hW
  · intro h
    apply hne
    refine ⟨k, ?_⟩
    have := congrArg F.B.tour.vertexAt h
    rw [← F.B.positionVertexEquiv_apply_val, Equiv.apply_symm_apply] at this
    exact this

variable {w : V} (hw : w ∈ F.W N) (hwB : w ∈ F.B.vertices)

/-- The position of a marked vertex of `B`. -/
noncomputable def posBV : F.B.tour.Pos := F.B.positionVertexEquiv.symm ⟨w, hwB⟩

omit [DecidableEq E] in
theorem vertexAt_posBV : F.B.tour.vertexAt (F.posBV hwB) = w := by
  unfold posBV
  rw [← F.B.positionVertexEquiv_apply_val, Equiv.apply_symm_apply]

include hw in
theorem marked_posBV : F.B.Marked (F.W N) (F.posBV hwB) := by
  unfold TraversedCircuit.Marked
  rw [F.vertexAt_posBV hwB]
  exact hw

theorem boundary_B_mem_sat_of_marked {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    (F.B.boundaryHalfEdge hCubic p).1 ∈ F.sat N :=
  Finset.mem_inter.mpr ⟨F.boundary_B_mem_compl hCubic p,
    (F.marked_iff N hCubic F.B (F.boundary_B_mem_compl hCubic) (F.B_edge_notin_compl) p).mp hp⟩

/-- The three half-edges of the reduced graph at a marked vertex of `B`. -/
noncomputable def yBS : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(⟨(F.B.boundaryHalfEdge hCubic (F.posBV hwB)).1,
      Or.inl (F.boundary_B_mem_sat_of_marked N hCubic (F.marked_posBV N hw hwB))⟩,
    (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).2), by
    apply Subtype.ext
    change (F.redEnd N _ _).1 = w
    rw [F.redEnd_sat N (F.boundary_B_mem_sat_of_marked N hCubic (F.marked_posBV N hw hwB))]
    change H.endAt (F.B.boundaryHalfEdge hCubic _).1 (F.B.boundaryHalfEdge hCubic _).2 = w
    rw [F.B.boundaryHalfEdge_endpoint hCubic, F.vertexAt_posBV hwB]⟩

noncomputable def yB0 : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(F.repEdgeB N (F.marked_posBV N hw hwB), 0), by
    apply Subtype.ext
    change (F.redEnd N _ 0).1 = w
    rw [F.redEnd_repEdgeB_zero, F.vertexAt_posBV hwB]⟩

noncomputable def yB1 : (F.red N).halfEdgesAt ⟨w, hw⟩ :=
  ⟨(F.repEdgeB N (F.B.marked_prevM (F.W N) (F.exists_markedB N hthree) (F.posBV hwB)), 1),
    by
    apply Subtype.ext
    change (F.redEnd N _ 1).1 = w
    rw [F.redEnd_repEdgeB_one, F.B.nextM_prevM (F.W N) (F.exists_markedB N hthree)
      (F.marked_posBV N hw hwB), F.vertexAt_posBV hwB]⟩

theorem yBS_ne_yB0 : F.yBS N hCubic hw hwB ≠ F.yB0 N hw hwB := by
  intro h
  have h' : (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).1 =
      (F.B.tour.edge (F.posBV hwB)).1 := congrArg (fun x ↦ x.1.1.1) h
  apply F.B.boundaryHalfEdge_not_mem hCubic (F.posBV hwB)
  rw [h']
  exact (F.B.tour.edge _).2

theorem yBS_ne_yB1 : F.yBS N hCubic hw hwB ≠ F.yB1 N hthree hw hwB := by
  intro h
  have h' : (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).1 =
      (F.B.tour.edge _).1 := congrArg (fun x ↦ x.1.1.1) h
  apply F.B.boundaryHalfEdge_not_mem hCubic (F.posBV hwB)
  rw [h']
  exact (F.B.tour.edge _).2

include hN hw in
theorem prevM_ne_posBV :
    F.B.prevM (F.W N) (F.exists_markedB N hthree) (F.posBV hwB) ≠ F.posBV hwB := by
  intro h
  have hn := F.B.nextM_prevM (F.W N) (F.exists_markedB N hthree) (F.marked_posBV N hw hwB)
  obtain ⟨p', hp', hne⟩ := F.two_markedB N hN hthree (F.posBV hwB)
  apply F.B.nextM_ne_of_two (F.W N) (F.marked_posBV N hw hwB) hp' hne
  exact (TraversedCircuit.nextM_congr _ _ _ _ h.symm).trans hn

include hN in
theorem yB0_ne_yB1 : F.yB0 N hw hwB ≠ F.yB1 N hthree hw hwB := by
  intro h
  have h' : (F.B.tour.edge (F.posBV hwB)).1 = (F.B.tour.edge _).1 :=
    congrArg (fun x ↦ x.1.1.1) h
  have := F.B.tour.edge.injective (Subtype.ext h')
  exact F.prevM_ne_posBV N hN hthree hw hwB this.symm

/-- The half-edges of the reduced graph at a marked vertex of `B`. -/
theorem red_halfEdge_cases_B (x : (F.red N).halfEdgesAt ⟨w, hw⟩) :
    x = F.yBS N hCubic hw hwB ∨ x = F.yB0 N hw hwB ∨
      x = F.yB1 N hthree hw hwB := by
  obtain ⟨⟨⟨f, hf⟩, k⟩, hx⟩ := x
  have hx' : (F.redEnd N ⟨f, hf⟩ k).1 = w := congrArg Subtype.val hx
  rcases hf with hS | hA | hB
  · rw [F.redEnd_sat N hS] at hx'
    have hxH : H.endAt f k = F.B.tour.vertexAt (F.posBV hwB) := by
      rw [F.vertexAt_posBV hwB]
      exact hx'
    obtain ⟨j, hj⟩ := F.B.positionHalfEdge_surjective hCubic _ ⟨(f, k), hxH⟩
    have hmem : (F.B.positionHalfEdge hCubic (F.posBV hwB) j).1 ∈ F.B.edges ∨
        F.B.positionHalfEdge hCubic (F.posBV hwB) j =
          F.B.boundaryHalfEdge hCubic (F.posBV hwB) := by
      fin_cases j
      · exact Or.inl (F.B.tour.edge _).2
      · exact Or.inl (F.B.tour.edge _).2
      · exact Or.inr rfl
    rw [hj] at hmem
    rcases hmem with hmem | hmem
    · exact absurd (F.sat_subset_compl N hS) (F.B_edge_notin_compl f hmem)
    · left
      have h1 : f = (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).1 := congrArg Prod.fst hmem
      have h2 : k = (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).2 := congrArg Prod.snd hmem
      apply Subtype.ext
      exact Prod.ext (Subtype.ext h1) h2
  ·
    exfalso
    have := F.redEnd_repA_mem N (f := ⟨f, Or.inr (Or.inl hA)⟩) hA k
    rw [hx'] at this
    exact F.disjoint _ this hwB
  ·
    rcases fin2_cases k with rfl | rfl
    · rw [F.redEnd_repB_zero N hB] at hx'
      have hp : F.posB (F.repsB_subset N hB) = F.posBV hwB := by
        apply F.B.positionVertexEquiv.injective
        apply Subtype.ext
        rw [F.B.positionVertexEquiv_apply_val, F.B.positionVertexEquiv_apply_val, hx',
          F.vertexAt_posBV hwB]
      right; left
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change f = (F.B.tour.edge (F.posBV hwB)).1
        rw [← hp, F.edge_posB]
      · rfl
    · rw [F.redEnd_repB_one N hB] at hx'
      have hp : F.B.nextM (F.W N) (F.posB_marked N hB) = F.posBV hwB := by
        apply F.B.positionVertexEquiv.injective
        apply Subtype.ext
        rw [F.B.positionVertexEquiv_apply_val, F.B.positionVertexEquiv_apply_val, hx',
          F.vertexAt_posBV hwB]
      have hp' : F.posB (F.repsB_subset N hB) =
          F.B.prevM (F.W N) (F.exists_markedB N hthree) (F.posBV hwB) := by
        rw [← hp, F.B.prevM_nextM]
      right; right
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change f = (F.B.tour.edge _).1
        rw [← hp', F.edge_posB]
      · rfl

end VertexB





/-- The edge set of `S` in the reduced graph. -/
def satRed : Finset (F.RedE N) := Finset.univ.filter fun f ↦ f.1 ∈ F.sat N

theorem mem_satRed {f : F.RedE N} : f ∈ F.satRed N ↔ f.1 ∈ F.sat N := by
  simp [satRed]

section CircuitA

variable (hthree : (N ∩ F.cross).card = 3)

omit [DecidableEq E] in
theorem vertexAt_injective_A : Function.Injective F.A.tour.vertexAt := by
  intro p q h
  apply F.A.positionVertexEquiv.injective
  apply Subtype.ext
  rw [F.A.positionVertexEquiv_apply_val, F.A.positionVertexEquiv_apply_val]
  exact h

include hCubic hN hthree in
theorem red_degree_A {w : V} (hw : w ∈ F.W N) (hwA : w ∈ F.A.vertices) :
    (F.red N).degree ⟨w, hw⟩ = 3 := by
  have huniv : (Finset.univ : Finset ((F.red N).halfEdgesAt ⟨w, hw⟩)) =
      {F.yAS N hCubic hw hwA, F.yA0 N hw hwA, F.yA1 N hthree hw hwA} := by
    ext x
    simp only [Finset.mem_univ, true_iff]
    rcases F.red_halfEdge_cases_A N hCubic hthree hw hwA x with rfl | rfl | rfl <;> simp
  change Fintype.card _ = 3
  rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem,
    Finset.card_pair (F.yA0_ne_yA1 N hN hthree hw hwA)]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨F.yAS_ne_yA0 N hCubic hw hwA, F.yAS_ne_yA1 N hCubic hthree hw hwA⟩

include hN hthree in
theorem red_loopless_A {f : F.RedE N} (hf : f.1 ∈ F.repsA N) :
    (F.red N).endAt f 0 ≠ (F.red N).endAt f 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [F.red_endAt, F.red_endAt, F.redEnd_repA_zero N hf, F.redEnd_repA_one N hf] at h'
  have hp := F.vertexAt_injective_A h'
  obtain ⟨p', hp', hne⟩ := F.two_markedA N hN hthree (F.posA (F.repsA_subset N hf))
  exact F.A.nextM_ne_of_two (F.W N) (F.posA_marked N hf) hp' hne hp.symm

end CircuitA

section CircuitB

variable (hthree : (N ∩ F.cross).card = 3)

omit [DecidableEq E] in
theorem vertexAt_injective_B : Function.Injective F.B.tour.vertexAt := by
  intro p q h
  apply F.B.positionVertexEquiv.injective
  apply Subtype.ext
  rw [F.B.positionVertexEquiv_apply_val, F.B.positionVertexEquiv_apply_val]
  exact h

include hCubic hN hthree in
theorem red_degree_B {w : V} (hw : w ∈ F.W N) (hwB : w ∈ F.B.vertices) :
    (F.red N).degree ⟨w, hw⟩ = 3 := by
  have huniv : (Finset.univ : Finset ((F.red N).halfEdgesAt ⟨w, hw⟩)) =
      {F.yBS N hCubic hw hwB, F.yB0 N hw hwB, F.yB1 N hthree hw hwB} := by
    ext x
    simp only [Finset.mem_univ, true_iff]
    rcases F.red_halfEdge_cases_B N hCubic hthree hw hwB x with rfl | rfl | rfl <;> simp
  change Fintype.card _ = 3
  rw [← Finset.card_univ, huniv, Finset.card_insert_of_notMem,
    Finset.card_pair (F.yB0_ne_yB1 N hN hthree hw hwB)]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨F.yBS_ne_yB0 N hCubic hw hwB, F.yBS_ne_yB1 N hCubic hthree hw hwB⟩

include hN hthree in
theorem red_loopless_B {f : F.RedE N} (hf : f.1 ∈ F.repsB N) :
    (F.red N).endAt f 0 ≠ (F.red N).endAt f 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [F.red_endAt, F.red_endAt, F.redEnd_repB_zero N hf, F.redEnd_repB_one N hf] at h'
  have hp := F.vertexAt_injective_B h'
  obtain ⟨p', hp', hne⟩ := F.two_markedB N hN hthree (F.posB (F.repsB_subset N hf))
  exact F.B.nextM_ne_of_two (F.W N) (F.posB_marked N hf) hp' hne hp.symm

end CircuitB

section Cubic

variable (hthree : (N ∩ F.cross).card = 3)

include hCubic hN hthree in
theorem red_cubic : ∀ v : F.RedV N, (F.red N).degree v = 3 := by
  intro ⟨w, hw⟩
  rcases F.cover w with hwA | hwB
  · exact F.red_degree_A N hCubic hN hthree hw hwA
  · exact F.red_degree_B N hCubic hN hthree hw hwB

end Cubic

section CircuitA'

variable (hthree : (N ∩ F.cross).card = 3)

include hCubic hN hthree in
theorem satRed_degree_A {w : V} (hw : w ∈ F.W N) (hwA : w ∈ F.A.vertices) :
    (F.red N).degreeIn (F.satRed N) ⟨w, hw⟩ = 1 := by
  refine degreeIn_eq_one_of_halfEdges (F.yAS N hCubic hw hwA)
    (F.yA0 N hw hwA) (F.yA1 N hthree hw hwA) (F.yAS_ne_yA0 N hCubic hw hwA)
    (F.yAS_ne_yA1 N hCubic hthree hw hwA) (F.yA0_ne_yA1 N hN hthree hw hwA)
    (F.red_halfEdge_cases_A N hCubic hthree hw hwA) ?_ ?_ ?_
  · exact (F.mem_satRed N).mpr (F.boundary_A_mem_sat_of_marked N hCubic (F.marked_posAV N hw hwA))
  · exact fun h ↦ F.repsA_notin_sat N (F.edge_mem_repsA N (F.marked_posAV N hw hwA))
      ((F.mem_satRed N).mp h)
  · exact fun h ↦ F.repsA_notin_sat N (F.edge_mem_repsA N
      (F.A.marked_prevM (F.W N) (F.exists_markedA N hthree) (F.posAV hwA)))
      ((F.mem_satRed N).mp h)

/-- The edges of the reduced circuit `A'`. -/
def repsARed : Finset (F.RedE N) := Finset.univ.filter fun f ↦ f.1 ∈ F.repsA N

theorem mem_repsARed {f : F.RedE N} : f ∈ F.repsARed N ↔ f.1 ∈ F.repsA N := by
  simp [repsARed]

theorem repEdgeA_mem_repsARed {p : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p) :
    F.repEdgeA N hp ∈ F.repsARed N :=
  (F.mem_repsARed N).mpr (F.edge_mem_repsA N hp)

theorem mem_A_of_mem_support {v : F.RedV N}
    (hv : v ∈ (F.red N).edgeSupport (F.repsARed N)) : v.1 ∈ F.A.vertices := by
  obtain ⟨f, hf, k, hk⟩ := (F.red N).mem_edgeSupport_iff.mp hv
  rw [← hk, F.red_endAt]
  exact F.redEnd_repA_mem N ((F.mem_repsARed N).mp hf) k

include hCubic hN hthree in
theorem repsARed_degree {w : V} (hw : w ∈ F.W N) (hwA : w ∈ F.A.vertices) :
    (F.red N).degreeIn (F.repsARed N) ⟨w, hw⟩ = 2 := by
  refine degreeIn_eq_two_of_halfEdges (F.red_cubic N hCubic hN hthree)
    (F.yA0 N hw hwA) (F.yA1 N hthree hw hwA) (F.yAS N hCubic hw hwA)
    (F.yA0_ne_yA1 N hN hthree hw hwA) ?_ ?_ ?_
  · exact F.repEdgeA_mem_repsARed N (F.marked_posAV N hw hwA)
  · exact F.repEdgeA_mem_repsARed N
      (F.A.marked_prevM (F.W N) (F.exists_markedA N hthree) (F.posAV hwA))
  · intro h
    exact F.A.boundaryHalfEdge_not_mem hCubic _ (F.repsA_subset N ((F.mem_repsARed N).mp h))

include hthree in
theorem repsARed_connected : (F.red N).EdgeConnected (F.repsARed N) := by
  obtain ⟨p₀, hp₀⟩ := F.exists_markedA N hthree
  let R : F.RedE N → F.RedE N → Prop := fun x y ↦
    x ∈ F.repsARed N ∧ y ∈ F.repsARed N ∧ (F.red N).EdgeAdjacent x y
  have hreach : ∀ p, F.A.Marked (F.W N) p → ∀ hp : F.A.Marked (F.W N) p,
      Relation.ReflTransGen R (F.repEdgeA N hp₀) (F.repEdgeA N hp) := by
    apply F.A.reach_marked (F.W N) (F.exists_markedA N hthree) hp₀
    · intro _
      exact Relation.ReflTransGen.refl
    · intro p hp ih _
      refine (ih hp).tail ⟨F.repEdgeA_mem_repsARed N hp, F.repEdgeA_mem_repsARed N _, 1, 0, ?_⟩
      apply Subtype.ext
      rw [F.red_endAt, F.red_endAt, F.redEnd_repEdgeA_one, F.redEnd_repEdgeA_zero]
  refine ⟨F.repEdgeA N hp₀, F.repEdgeA_mem_repsARed N hp₀, ?_⟩
  intro f hf
  obtain ⟨p, hp, hfp⟩ := (F.mem_repsA N).mp ((F.mem_repsARed N).mp hf)
  have : f = F.repEdgeA N hp := Subtype.ext hfp
  rw [this]
  exact hreach p hp hp

include hCubic hN hthree in
/-- The reduced circuit `A'`. -/
noncomputable def redA : (F.red N).OrdinaryCircuit where
  edges := F.repsARed N
  nonempty := ⟨_, F.repEdgeA_mem_repsARed N (F.exists_markedA N hthree).choose_spec⟩
  connected := F.repsARed_connected N hthree
  twoRegular := fun v hv ↦ by
    obtain ⟨w, hw⟩ := v
    exact F.repsARed_degree N hCubic hN hthree hw (F.mem_A_of_mem_support N hv)

theorem redA_edges : (F.redA N hCubic hN hthree).edges = F.repsARed N := rfl

end CircuitA'

section CircuitB'

variable (hthree : (N ∩ F.cross).card = 3)

include hCubic hN hthree in
theorem satRed_degree_B {w : V} (hw : w ∈ F.W N) (hwB : w ∈ F.B.vertices) :
    (F.red N).degreeIn (F.satRed N) ⟨w, hw⟩ = 1 := by
  refine degreeIn_eq_one_of_halfEdges (F.yBS N hCubic hw hwB)
    (F.yB0 N hw hwB) (F.yB1 N hthree hw hwB) (F.yBS_ne_yB0 N hCubic hw hwB)
    (F.yBS_ne_yB1 N hCubic hthree hw hwB) (F.yB0_ne_yB1 N hN hthree hw hwB)
    (F.red_halfEdge_cases_B N hCubic hthree hw hwB) ?_ ?_ ?_
  · exact (F.mem_satRed N).mpr (F.boundary_B_mem_sat_of_marked N hCubic (F.marked_posBV N hw hwB))
  · exact fun h ↦ F.repsB_notin_sat N (F.edge_mem_repsB N (F.marked_posBV N hw hwB))
      ((F.mem_satRed N).mp h)
  · exact fun h ↦ F.repsB_notin_sat N (F.edge_mem_repsB N
      (F.B.marked_prevM (F.W N) (F.exists_markedB N hthree) (F.posBV hwB)))
      ((F.mem_satRed N).mp h)

/-- The edges of the reduced circuit `B'`. -/
def repsBRed : Finset (F.RedE N) := Finset.univ.filter fun f ↦ f.1 ∈ F.repsB N

theorem mem_repsBRed {f : F.RedE N} : f ∈ F.repsBRed N ↔ f.1 ∈ F.repsB N := by
  simp [repsBRed]

theorem repEdgeB_mem_repsBRed {p : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p) :
    F.repEdgeB N hp ∈ F.repsBRed N :=
  (F.mem_repsBRed N).mpr (F.edge_mem_repsB N hp)

theorem mem_B_of_mem_support {v : F.RedV N}
    (hv : v ∈ (F.red N).edgeSupport (F.repsBRed N)) : v.1 ∈ F.B.vertices := by
  obtain ⟨f, hf, k, hk⟩ := (F.red N).mem_edgeSupport_iff.mp hv
  rw [← hk, F.red_endAt]
  exact F.redEnd_repB_mem N ((F.mem_repsBRed N).mp hf) k

include hCubic hN hthree in
theorem repsBRed_degree {w : V} (hw : w ∈ F.W N) (hwB : w ∈ F.B.vertices) :
    (F.red N).degreeIn (F.repsBRed N) ⟨w, hw⟩ = 2 := by
  refine degreeIn_eq_two_of_halfEdges (F.red_cubic N hCubic hN hthree)
    (F.yB0 N hw hwB) (F.yB1 N hthree hw hwB) (F.yBS N hCubic hw hwB)
    (F.yB0_ne_yB1 N hN hthree hw hwB) ?_ ?_ ?_
  · exact F.repEdgeB_mem_repsBRed N (F.marked_posBV N hw hwB)
  · exact F.repEdgeB_mem_repsBRed N
      (F.B.marked_prevM (F.W N) (F.exists_markedB N hthree) (F.posBV hwB))
  · intro h
    exact F.B.boundaryHalfEdge_not_mem hCubic _ (F.repsB_subset N ((F.mem_repsBRed N).mp h))

include hthree in
theorem repsBRed_connected : (F.red N).EdgeConnected (F.repsBRed N) := by
  obtain ⟨p₀, hp₀⟩ := F.exists_markedB N hthree
  let R : F.RedE N → F.RedE N → Prop := fun x y ↦
    x ∈ F.repsBRed N ∧ y ∈ F.repsBRed N ∧ (F.red N).EdgeAdjacent x y
  have hreach : ∀ p, F.B.Marked (F.W N) p → ∀ hp : F.B.Marked (F.W N) p,
      Relation.ReflTransGen R (F.repEdgeB N hp₀) (F.repEdgeB N hp) := by
    apply F.B.reach_marked (F.W N) (F.exists_markedB N hthree) hp₀
    · intro _
      exact Relation.ReflTransGen.refl
    · intro p hp ih _
      refine (ih hp).tail ⟨F.repEdgeB_mem_repsBRed N hp, F.repEdgeB_mem_repsBRed N _, 1, 0, ?_⟩
      apply Subtype.ext
      rw [F.red_endAt, F.red_endAt, F.redEnd_repEdgeB_one, F.redEnd_repEdgeB_zero]
  refine ⟨F.repEdgeB N hp₀, F.repEdgeB_mem_repsBRed N hp₀, ?_⟩
  intro f hf
  obtain ⟨p, hp, hfp⟩ := (F.mem_repsB N).mp ((F.mem_repsBRed N).mp hf)
  have : f = F.repEdgeB N hp := Subtype.ext hfp
  rw [this]
  exact hreach p hp hp

include hCubic hN hthree in
/-- The reduced circuit `B'`. -/
noncomputable def redB : (F.red N).OrdinaryCircuit where
  edges := F.repsBRed N
  nonempty := ⟨_, F.repEdgeB_mem_repsBRed N (F.exists_markedB N hthree).choose_spec⟩
  connected := F.repsBRed_connected N hthree
  twoRegular := fun v hv ↦ by
    obtain ⟨w, hw⟩ := v
    exact F.repsBRed_degree N hCubic hN hthree hw (F.mem_B_of_mem_support N hv)

theorem redB_edges : (F.redB N hCubic hN hthree).edges = F.repsBRed N := rfl

end CircuitB'

section Assembly

variable (hthree : (N ∩ F.cross).card = 3)

include hN hthree in
theorem red_loopless (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    ∀ f : F.RedE N, (F.red N).endAt f 0 ≠ (F.red N).endAt f 1 := by
  intro f
  rcases f.2 with hS | hA | hB
  · intro h
    have h' := congrArg Subtype.val h
    rw [F.red_endAt, F.red_endAt, F.redEnd_sat N hS, F.redEnd_sat N hS] at h'
    exact hloopless f.1 h'
  · exact F.red_loopless_A N hN hthree hA
  · exact F.red_loopless_B N hN hthree hB

include hCubic hN hthree in
theorem satRed_perfect : (F.red N).IsPerfectMatching (F.satRed N) := by
  intro ⟨w, hw⟩
  rcases F.cover w with hwA | hwB
  · exact F.satRed_degree_A N hCubic hN hthree hw hwA
  · exact F.satRed_degree_B N hCubic hN hthree hw hwB

theorem mem_satRed_iff (f : F.RedE N) :
    f ∈ F.satRed N ↔ (f ∉ F.repsARed N ∧ f ∉ F.repsBRed N) := by
  rw [F.mem_satRed, F.mem_repsARed, F.mem_repsBRed]
  constructor
  · intro h
    exact ⟨fun h' ↦ F.repsA_notin_sat N h' h, fun h' ↦ F.repsB_notin_sat N h' h⟩
  · rintro ⟨hA, hB⟩
    rcases f.2 with h | h | h
    · exact h
    · exact absurd h hA
    · exact absurd h hB

theorem disjoint_repsRed : Disjoint (F.repsARed N) (F.repsBRed N) :=
  Finset.disjoint_left.mpr fun _ hA hB ↦
    F.repsA_notin_repsB N ((F.mem_repsARed N).mp hA) ((F.mem_repsBRed N).mp hB)

theorem disjoint_support_repsRed :
    ∀ v, v ∈ (F.red N).edgeSupport (F.repsARed N) → v ∉ (F.red N).edgeSupport (F.repsBRed N) :=
  fun v hA hB ↦ F.disjoint v.1 (F.mem_A_of_mem_support N hA) (F.mem_B_of_mem_support N hB)

theorem mem_support_repsARed_iff (v : F.RedV N) :
    v ∈ (F.red N).edgeSupport (F.repsARed N) ↔ v.1 ∈ F.A.vertices := by
  refine ⟨F.mem_A_of_mem_support N, fun hvA ↦ ?_⟩
  obtain ⟨w, hw⟩ := v
  exact (F.red N).mem_edgeSupport_iff.mpr ⟨(F.yA0 N hw hvA).1.1,
    F.repEdgeA_mem_repsARed N (F.marked_posAV N hw hvA), (F.yA0 N hw hvA).1.2,
    (F.yA0 N hw hvA).2⟩

include hthree in
/-- The reduced graph keeps exactly the three cross-spokes of `S`. -/
theorem red_cross_card :
    ((F.satRed N).filter fun e ↦ ¬ (((F.red N).endAt e 0 ∈ (F.red N).edgeSupport (F.repsARed N)) ↔
      ((F.red N).endAt e 1 ∈ (F.red N).edgeSupport (F.repsARed N)))).card = 3 := by
  rw [← hthree]
  apply Finset.card_bij (fun e _ ↦ e.1)
  · intro e he
    obtain ⟨heS, hc⟩ := Finset.mem_filter.mp he
    have heS' := (F.mem_satRed N).mp heS
    refine Finset.mem_inter.mpr ⟨F.sat_subset_N N heS', Finset.mem_filter.mpr
      ⟨F.sat_subset_compl N heS', ?_⟩⟩
    rwa [F.mem_support_repsARed_iff N, F.mem_support_repsARed_iff N, F.red_endAt,
      F.red_endAt, F.redEnd_sat N heS', F.redEnd_sat N heS'] at hc
  · intro e _ e' _ h
    exact Subtype.ext h
  · intro e he
    obtain ⟨heN, hec⟩ := Finset.mem_inter.mp he
    have heS : e ∈ F.sat N := Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hec).1, heN⟩
    refine ⟨⟨e, Or.inl heS⟩, Finset.mem_filter.mpr ⟨(F.mem_satRed N).mpr heS, ?_⟩, rfl⟩
    rw [F.mem_support_repsARed_iff N, F.mem_support_repsARed_iff N, F.red_endAt,
      F.red_endAt, F.redEnd_sat N heS, F.redEnd_sat N heS]
    exact (Finset.mem_filter.mp hec).2

theorem repsRed_union : F.repsARed N ∪ F.repsBRed N = Finset.univ \ F.satRed N := by
  ext f
  rw [Finset.mem_union, Finset.mem_sdiff, F.mem_satRed_iff N f]
  constructor
  · rintro (h | h)
    · exact ⟨Finset.mem_univ _, fun h' ↦ h'.1 h⟩
    · exact ⟨Finset.mem_univ _, fun h' ↦ h'.2 h⟩
  · rintro ⟨-, h⟩
    by_contra h'
    push Not at h'
    exact h h'

end Assembly

/-! ### Parity of the reduced circuits -/

section Parity

variable (hthree : (N ∩ F.cross).card = 3) (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)

/-- The number of ends of `e` lying on `A`. -/
def endsInA (e : E) : ℕ :=
  (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k ∈ F.A.vertices).card

theorem endsInA_mod_two {e : E} (he : e ∈ F.compl) :
    F.endsInA e % 2 = if e ∈ F.cross then 1 else 0 := by
  unfold endsInA
  rw [Finset.card_filter, Fin.sum_univ_two]
  have hc := F.mem_cross_iff_A he
  rcases Classical.em (H.endAt e 0 ∈ F.A.vertices) with h0 | h0 <;>
    rcases Classical.em (H.endAt e 1 ∈ F.A.vertices) with h1 | h1
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩), if_pos h0, if_pos h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h1 (h.mp h0)), if_pos h0, if_neg h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h0 (h.mpr h1)), if_neg h0, if_pos h1]; rfl
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩), if_neg h0,
      if_neg h1]; rfl

include hN hloopless in
theorem card_W_inter_A : (F.W N ∩ F.A.vertices).card = ∑ e ∈ F.sat N, F.endsInA e := by
  have hbi : F.W N ∩ F.A.vertices = (F.sat N).biUnion fun e ↦
      (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k ∈ F.A.vertices).image (H.endAt e) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hwA⟩
      obtain ⟨e, he, k, hk⟩ := H.mem_edgeSupport_iff.mp hw
      exact ⟨e, he, k, hk ▸ hwA, hk⟩
    · rintro ⟨e, he, k, hkA, rfl⟩
      exact ⟨H.mem_edgeSupport_iff.mpr ⟨e, he, k, rfl⟩, hkA⟩
  rw [hbi, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    unfold endsInA
    apply Finset.card_image_of_injOn
    intro k _ k' _ hkk'
    by_contra hne
    apply hloopless e
    rcases fin2_cases k with rfl | rfl <;> rcases fin2_cases k' with rfl | rfl
    · exact absurd rfl hne
    · exact hkk'
    · exact hkk'.symm
    · exact absurd rfl hne
  · intro e he e' he' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hw
    obtain ⟨k', -, hk'⟩ := Finset.mem_image.mp hw'
    have h2 := H.two_le_degreeIn_of_ne (M := N) ⟨(e, k), hk⟩ ⟨(e', k'), hk'⟩
      (fun h ↦ hne (congrArg (fun x ↦ x.1.1) h)) (F.sat_subset_N N he) (F.sat_subset_N N he')
    have := hN w
    omega

include hN hthree hloopless in
theorem card_W_inter_A_odd : Odd (F.W N ∩ F.A.vertices).card := by
  rw [F.card_W_inter_A N hN hloopless, Nat.odd_iff, Finset.sum_nat_mod]
  have h : ∑ e ∈ F.sat N, F.endsInA e % 2 = ∑ e ∈ F.sat N, if e ∈ F.cross then 1 else 0 :=
    Finset.sum_congr rfl fun e he ↦ F.endsInA_mod_two (F.sat_subset_compl N he)
  rw [h, Finset.sum_boole, Finset.filter_mem_eq_inter]
  have : F.sat N ∩ F.cross = N ∩ F.cross := by
    ext e
    simp only [Finset.mem_inter, sat]
    constructor
    · rintro ⟨⟨-, hN'⟩, hc⟩
      exact ⟨hN', hc⟩
    · rintro ⟨hN', hc⟩
      exact ⟨⟨(Finset.mem_filter.mp hc).1, hN'⟩, hc⟩
  rw [this, hthree]
  rfl

include hN hthree hloopless in
/-- The reduced circuit `A'` is odd. -/
theorem card_repsARed_odd : Odd (F.repsARed N).card := by
  have h1 : (F.repsARed N).card = (Finset.univ.filter (F.A.Marked (F.W N))).card := by
    apply Finset.card_bij (fun f hf ↦ F.posA (F.repsA_subset N ((F.mem_repsARed N).mp hf)))
    · intro f hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.posA_marked N ((F.mem_repsARed N).mp hf)⟩
    · intro f hf f' hf' h
      apply Subtype.ext
      rw [← F.edge_posA (F.repsA_subset N ((F.mem_repsARed N).mp hf)),
        ← F.edge_posA (F.repsA_subset N ((F.mem_repsARed N).mp hf')), h]
    · intro p hp
      refine ⟨F.repEdgeA N (Finset.mem_filter.mp hp).2, F.repEdgeA_mem_repsARed N _, ?_⟩
      exact F.posA_repEdge N (Finset.mem_filter.mp hp).2 _
  have h2 : (Finset.univ.filter (F.A.Marked (F.W N))).card = (F.W N ∩ F.A.vertices).card := by
    apply Finset.card_bij (fun p _ ↦ F.A.tour.vertexAt p)
    · intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).2, F.A.vertexAt_mem_vertices p⟩
    · intro p _ q _ h
      exact F.vertexAt_injective_A h
    · intro w hw
      obtain ⟨hwW, hwA⟩ := Finset.mem_inter.mp hw
      exact ⟨F.posAV hwA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.marked_posAV N hwW hwA⟩,
        F.vertexAt_posAV hwA⟩
  rw [h1, h2]
  exact F.card_W_inter_A_odd N hN hthree hloopless

/-- The number of ends of `e` lying on `B`. -/
def endsInB (e : E) : ℕ :=
  (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k ∈ F.B.vertices).card

theorem endsInB_mod_two {e : E} (he : e ∈ F.compl) :
    F.endsInB e % 2 = if e ∈ F.cross then 1 else 0 := by
  unfold endsInB
  rw [Finset.card_filter, Fin.sum_univ_two]
  have hc := F.mem_cross_iff_B he
  rcases Classical.em (H.endAt e 0 ∈ F.B.vertices) with h0 | h0 <;>
    rcases Classical.em (H.endAt e 1 ∈ F.B.vertices) with h1 | h1
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩), if_pos h0, if_pos h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h1 (h.mp h0)), if_pos h0, if_neg h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h0 (h.mpr h1)), if_neg h0, if_pos h1]; rfl
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩), if_neg h0,
      if_neg h1]; rfl

include hN hloopless in
theorem card_W_inter_B : (F.W N ∩ F.B.vertices).card = ∑ e ∈ F.sat N, F.endsInB e := by
  have hbi : F.W N ∩ F.B.vertices = (F.sat N).biUnion fun e ↦
      (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k ∈ F.B.vertices).image (H.endAt e) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hwB⟩
      obtain ⟨e, he, k, hk⟩ := H.mem_edgeSupport_iff.mp hw
      exact ⟨e, he, k, hk ▸ hwB, hk⟩
    · rintro ⟨e, he, k, hkB, rfl⟩
      exact ⟨H.mem_edgeSupport_iff.mpr ⟨e, he, k, rfl⟩, hkB⟩
  rw [hbi, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    unfold endsInB
    apply Finset.card_image_of_injOn
    intro k _ k' _ hkk'
    by_contra hne
    apply hloopless e
    rcases fin2_cases k with rfl | rfl <;> rcases fin2_cases k' with rfl | rfl
    · exact absurd rfl hne
    · exact hkk'
    · exact hkk'.symm
    · exact absurd rfl hne
  · intro e he e' he' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hw
    obtain ⟨k', -, hk'⟩ := Finset.mem_image.mp hw'
    have h2 := H.two_le_degreeIn_of_ne (M := N) ⟨(e, k), hk⟩ ⟨(e', k'), hk'⟩
      (fun h ↦ hne (congrArg (fun x ↦ x.1.1) h)) (F.sat_subset_N N he) (F.sat_subset_N N he')
    have := hN w
    omega

include hN hthree hloopless in
theorem card_W_inter_B_odd : Odd (F.W N ∩ F.B.vertices).card := by
  rw [F.card_W_inter_B N hN hloopless, Nat.odd_iff, Finset.sum_nat_mod]
  have h : ∑ e ∈ F.sat N, F.endsInB e % 2 = ∑ e ∈ F.sat N, if e ∈ F.cross then 1 else 0 :=
    Finset.sum_congr rfl fun e he ↦ F.endsInB_mod_two (F.sat_subset_compl N he)
  rw [h, Finset.sum_boole, Finset.filter_mem_eq_inter]
  have : F.sat N ∩ F.cross = N ∩ F.cross := by
    ext e
    simp only [Finset.mem_inter, sat]
    constructor
    · rintro ⟨⟨-, hN'⟩, hc⟩
      exact ⟨hN', hc⟩
    · rintro ⟨hN', hc⟩
      exact ⟨⟨(Finset.mem_filter.mp hc).1, hN'⟩, hc⟩
  rw [this, hthree]
  rfl

include hN hthree hloopless in
/-- The reduced circuit `B'` is odd. -/
theorem card_repsBRed_odd : Odd (F.repsBRed N).card := by
  have h1 : (F.repsBRed N).card = (Finset.univ.filter (F.B.Marked (F.W N))).card := by
    apply Finset.card_bij (fun f hf ↦ F.posB (F.repsB_subset N ((F.mem_repsBRed N).mp hf)))
    · intro f hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.posB_marked N ((F.mem_repsBRed N).mp hf)⟩
    · intro f hf f' hf' h
      apply Subtype.ext
      rw [← F.edge_posB (F.repsB_subset N ((F.mem_repsBRed N).mp hf)),
        ← F.edge_posB (F.repsB_subset N ((F.mem_repsBRed N).mp hf')), h]
    · intro p hp
      refine ⟨F.repEdgeB N (Finset.mem_filter.mp hp).2, F.repEdgeB_mem_repsBRed N _, ?_⟩
      exact F.posB_repEdge N (Finset.mem_filter.mp hp).2 _
  have h2 : (Finset.univ.filter (F.B.Marked (F.W N))).card = (F.W N ∩ F.B.vertices).card := by
    apply Finset.card_bij (fun p _ ↦ F.B.tour.vertexAt p)
    · intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).2, F.B.vertexAt_mem_vertices p⟩
    · intro p _ q _ h
      exact F.vertexAt_injective_B h
    · intro w hw
      obtain ⟨hwW, hwB⟩ := Finset.mem_inter.mp hw
      exact ⟨F.posBV hwB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.marked_posBV N hwW hwB⟩,
        F.vertexAt_posBV hwB⟩
  rw [h1, h2]
  exact F.card_W_inter_B_odd N hN hthree hloopless

end Parity

/-! ### Lifting a four-cover of the reduced graph -/

section Lifting

variable (hthree : (N ∩ F.cross).card = 3)

/-- The label predicate of a lifted matching.  An edge of `S` keeps its membership in `L`.  An
edge of a factor circuit at distance `back` behind the last marked position of its arc is lifted
when the representative of the arc lies in `L` and `back` is even, or when the representative
does not lie in `L` and `back` is odd.  The remaining edges of `M` are never lifted. -/
def Lab (L : Finset (F.RedE N)) (e : E) : Prop :=
  if he : e ∈ F.sat N then ⟨e, Or.inl he⟩ ∈ L
  else if hA : e ∈ F.A.edges then
    (F.repEdgeA N (F.A.marked_start (F.W N) (F.exists_markedA N hthree) (F.posA hA)) ∈ L ↔
      Even (F.A.back (F.W N) (F.exists_markedA N hthree) (F.posA hA)))
  else if hB : e ∈ F.B.edges then
    (F.repEdgeB N (F.B.marked_start (F.W N) (F.exists_markedB N hthree) (F.posB hB)) ∈ L ↔
      Even (F.B.back (F.W N) (F.exists_markedB N hthree) (F.posB hB)))
  else False

noncomputable instance (L : Finset (F.RedE N)) : DecidablePred (F.Lab N hthree L) :=
  fun _ ↦ Classical.propDecidable _

/-- The lift of a perfect matching of the reduced graph. -/
noncomputable def lift (L : Finset (F.RedE N)) : Finset E :=
  Finset.univ.filter (F.Lab N hthree L)

theorem mem_lift {L : Finset (F.RedE N)} {e : E} :
    e ∈ F.lift N hthree L ↔ F.Lab N hthree L e := by
  unfold lift
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem lab_sat {L : Finset (F.RedE N)} {e : E} (he : e ∈ F.sat N) :
    F.Lab N hthree L e ↔ ⟨e, Or.inl he⟩ ∈ L := by
  unfold Lab
  rw [dif_pos he]

theorem lab_A_of_mem {L : Finset (F.RedE N)} (hex : ∃ p, F.A.Marked (F.W N) p) {e : E}
    (he : e ∈ F.A.edges) :
    F.Lab N hthree L e ↔
      (F.repEdgeA N (F.A.marked_start (F.W N) hex (F.posA he)) ∈ L ↔
        Even (F.A.back (F.W N) hex (F.posA he))) := by
  unfold Lab
  rw [dif_neg (fun h ↦ F.A_edge_notin_compl _ he (F.sat_subset_compl N h)), dif_pos he]

theorem lab_A {L : Finset (F.RedE N)} (hex : ∃ p, F.A.Marked (F.W N) p) (q : F.A.tour.Pos) :
    F.Lab N hthree L (F.A.tour.edge q).1 ↔
      (F.repEdgeA N (F.A.marked_start (F.W N) hex q) ∈ L ↔
        Even (F.A.back (F.W N) hex q)) := by
  rw [F.lab_A_of_mem N hthree hex (F.A.tour.edge q).2, F.posA_edge]

theorem lab_B_of_mem {L : Finset (F.RedE N)} (hex : ∃ p, F.B.Marked (F.W N) p) {e : E}
    (he : e ∈ F.B.edges) :
    F.Lab N hthree L e ↔
      (F.repEdgeB N (F.B.marked_start (F.W N) hex (F.posB he)) ∈ L ↔
        Even (F.B.back (F.W N) hex (F.posB he))) := by
  unfold Lab
  rw [dif_neg (fun h ↦ F.B_edge_notin_compl _ he (F.sat_subset_compl N h)),
    dif_neg (F.not_mem_A_of_mem_B he), dif_pos he]

theorem lab_B {L : Finset (F.RedE N)} (hex : ∃ p, F.B.Marked (F.W N) p) (q : F.B.tour.Pos) :
    F.Lab N hthree L (F.B.tour.edge q).1 ↔
      (F.repEdgeB N (F.B.marked_start (F.W N) hex q) ∈ L ↔
        Even (F.B.back (F.W N) hex q)) := by
  rw [F.lab_B_of_mem N hthree hex (F.B.tour.edge q).2, F.posB_edge]

theorem not_lab_of_compl {L : Finset (F.RedE N)} {e : E} (he : e ∈ F.compl) (heN : e ∉ N) :
    ¬ F.Lab N hthree L e := by
  unfold Lab
  rw [dif_neg (fun h ↦ heN (F.sat_subset_N N h)), dif_neg (F.mem_compl_iff.mp he).1,
    dif_neg (F.mem_compl_iff.mp he).2]
  exact fun h ↦ h

theorem repEdgeA_congr {p p' : F.A.tour.Pos} (hp : F.A.Marked (F.W N) p)
    (hp' : F.A.Marked (F.W N) p') (h : p = p') : F.repEdgeA N hp = F.repEdgeA N hp' := by
  subst h
  rfl

theorem repEdgeB_congr {p p' : F.B.tour.Pos} (hp : F.B.Marked (F.W N) p)
    (hp' : F.B.Marked (F.W N) p') (h : p = p') : F.repEdgeB N hp = F.repEdgeB N hp' := by
  subst h
  rfl

include hCubic hN hthree in
/-- At a marked vertex of `A`, the lift of a perfect matching of the reduced graph has
degree one. -/
theorem lift_degree_A_marked {L : Finset (F.RedE N)} {w : V} (hw : w ∈ F.W N)
    (hwA : w ∈ F.A.vertices) (hL : (F.red N).degreeIn L ⟨w, hw⟩ = 1) :
    H.degreeIn (F.lift N hthree L) w = 1 := by
  rw [(F.red N).degreeIn_eq_card_halfEdges, card_filter_of_three (F.yAS N hCubic hw hwA)
    (F.yA0 N hw hwA) (F.yA1 N hthree hw hwA) (F.yAS_ne_yA0 N hCubic hw hwA)
    (F.yAS_ne_yA1 N hCubic hthree hw hwA) (F.yA0_ne_yA1 N hN hthree hw hwA)
    (F.red_halfEdge_cases_A N hCubic hthree hw hwA)] at hL
  have hex := F.exists_markedA N hthree
  have hp := F.marked_posAV N hw hwA
  have e0 : (F.A.tour.edge (F.posAV hwA)).1 ∈ F.lift N hthree L ↔
      (F.yA0 N hw hwA).1.1 ∈ L := by
    rw [F.mem_lift N hthree, F.lab_A N hthree hex,
      F.repEdgeA_congr N _ hp (F.A.start_of_marked (F.W N) hex hp),
      F.A.back_eq_zero_of_marked (F.W N) hex hp]
    exact ⟨fun h ↦ h.mpr Even.zero, fun h ↦ iff_of_true h Even.zero⟩
  have e1 : (F.A.tour.edge (F.A.tour.prev (F.posAV hwA))).1 ∈ F.lift N hthree L ↔
      (F.yA1 N hthree hw hwA).1.1 ∈ L := by
    have hb := (F.A.back_nextM_sub_one (F.W N) hex
      (F.A.marked_prevM (F.W N) hex (F.posAV hwA))).1
    rw [F.A.nextM_prevM (F.W N) hex hp] at hb
    have hev : Even (F.A.back (F.W N) hex (F.posAV hwA - 1)) := by
      rw [hb]
      exact Nat.Odd.sub_odd (F.forward_odd N hCubic hN F.A (F.boundary_A_mem_compl hCubic)
        F.A_edge_notin_compl _) odd_one
    rw [F.mem_lift N hthree, EulerTour.prev_eq_sub_one, F.lab_A N hthree hex]
    exact ⟨fun h ↦ h.mpr hev, fun h ↦ iff_of_true h hev⟩
  have e2 : (F.A.boundaryHalfEdge hCubic (F.posAV hwA)).1 ∈ F.lift N hthree L ↔
      (F.yAS N hCubic hw hwA).1.1 ∈ L := by
    rw [F.mem_lift N hthree, F.lab_sat N hthree (F.boundary_A_mem_sat_of_marked N hCubic hp)]
    exact Iff.rfl
  rw [← F.vertexAt_posAV hwA, degreeIn_at_position hCubic F.A _ (F.posAV hwA)]
  simp only [e0, e1, e2]
  split_ifs at hL ⊢ <;> omega

include hCubic hthree in
/-- At an unmarked vertex of `A`, exactly one of the two circuit edges is lifted. -/
theorem lift_degree_A_unmarked (L : Finset (F.RedE N)) {p : F.A.tour.Pos}
    (hp : ¬ F.A.Marked (F.W N) p) :
    H.degreeIn (F.lift N hthree L) (F.A.tour.vertexAt p) = 1 := by
  have hex := F.exists_markedA N hthree
  have hb : F.A.back (F.W N) hex p = F.A.back (F.W N) hex (p - 1) + 1 := by
    have h1 := F.A.back_sub_one_of_not_marked (F.W N) hex hp
    have h2 := F.A.back_pos_of_not_marked (F.W N) hex hp
    omega
  have e0 : (F.A.tour.edge p).1 ∈ F.lift N hthree L ↔
      (F.repEdgeA N (F.A.marked_start (F.W N) hex (p - 1)) ∈ L ↔
        ¬ Even (F.A.back (F.W N) hex (p - 1))) := by
    rw [F.mem_lift N hthree, F.lab_A N hthree hex,
      F.repEdgeA_congr N _ (F.A.marked_start (F.W N) hex (p - 1))
        (F.A.start_sub_one_of_not_marked (F.W N) hex hp).symm, hb, Nat.even_add_one]
  have e1 : (F.A.tour.edge (F.A.tour.prev p)).1 ∈ F.lift N hthree L ↔
      (F.repEdgeA N (F.A.marked_start (F.W N) hex (p - 1)) ∈ L ↔
        Even (F.A.back (F.W N) hex (p - 1))) := by
    rw [F.mem_lift N hthree, EulerTour.prev_eq_sub_one, F.lab_A N hthree hex]
  have e2 : (F.A.boundaryHalfEdge hCubic p).1 ∉ F.lift N hthree L := by
    rw [F.mem_lift N hthree]
    exact F.not_lab_of_compl N hthree (F.boundary_A_mem_compl hCubic p) fun h ↦
      hp ((F.marked_iff N hCubic F.A (F.boundary_A_mem_compl hCubic)
        F.A_edge_notin_compl p).mpr h)
  rw [degreeIn_at_position hCubic F.A _ p]
  simp only [e0, e1, if_neg e2]
  by_cases hr : F.repEdgeA N (F.A.marked_start (F.W N) hex (p - 1)) ∈ L <;>
    by_cases he : Even (F.A.back (F.W N) hex (p - 1)) <;> simp [hr, he]

include hCubic hN hthree in
/-- Every edge of `A` is lifted from one of three perfect matchings covering the reduced graph
together with `S`. -/
theorem lift_cover_A {L₁ L₂ L₃ : Finset (F.RedE N)} (h₁ : (F.red N).IsPerfectMatching L₁)
    (h₂ : (F.red N).IsPerfectMatching L₂) (h₃ : (F.red N).IsPerfectMatching L₃)
    (hcov : F.satRed N ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ) {e : E} (he : e ∈ F.A.edges) :
    e ∈ F.lift N hthree L₁ ∨ e ∈ F.lift N hthree L₂ ∨ e ∈ F.lift N hthree L₃ := by
  have hex := F.exists_markedA N hthree
  obtain ⟨q, rfl⟩ : ∃ q, e = (F.A.tour.edge q).1 := ⟨F.posA he, (F.edge_posA he).symm⟩
  have hrS : F.repEdgeA N (F.A.marked_start (F.W N) hex q) ∉ F.satRed N := fun h ↦
    F.repsA_notin_sat N (F.edge_mem_repsA N (F.A.marked_start (F.W N) hex q))
      ((F.mem_satRed N).mp h)
  have hmem : F.repEdgeA N (F.A.marked_start (F.W N) hex q) ∈ L₁ ∨
      F.repEdgeA N (F.A.marked_start (F.W N) hex q) ∈ L₂ ∨
      F.repEdgeA N (F.A.marked_start (F.W N) hex q) ∈ L₃ := by
    have := Finset.mem_univ (F.repEdgeA N (F.A.marked_start (F.W N) hex q))
    rw [← hcov] at this
    simp only [Finset.mem_union] at this
    rcases this with ((h | h) | h) | h
    · exact absurd h hrS
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hnot := exists_not_mem_of_cover (F.red_cubic N hCubic hN hthree)
    (F.satRed_perfect N hCubic hN hthree) h₁ h₂ h₃ hcov
    (F.repEdgeA N (F.A.marked_start (F.W N) hex q))
  rw [F.mem_lift N hthree, F.mem_lift N hthree, F.mem_lift N hthree, F.lab_A N hthree hex,
    F.lab_A N hthree hex, F.lab_A N hthree hex]
  by_cases hev : Even (F.A.back (F.W N) hex q)
  · rcases hmem with h | h | h
    · exact Or.inl (iff_of_true h hev)
    · exact Or.inr (Or.inl (iff_of_true h hev))
    · exact Or.inr (Or.inr (iff_of_true h hev))
  · rcases hnot with h | h | h
    · exact Or.inl (iff_of_false h hev)
    · exact Or.inr (Or.inl (iff_of_false h hev))
    · exact Or.inr (Or.inr (iff_of_false h hev))

include hCubic hN hthree in
/-- At a marked vertex of `B`, the lift of a perfect matching of the reduced graph has
degree one. -/
theorem lift_degree_B_marked {L : Finset (F.RedE N)} {w : V} (hw : w ∈ F.W N)
    (hwB : w ∈ F.B.vertices) (hL : (F.red N).degreeIn L ⟨w, hw⟩ = 1) :
    H.degreeIn (F.lift N hthree L) w = 1 := by
  rw [(F.red N).degreeIn_eq_card_halfEdges, card_filter_of_three (F.yBS N hCubic hw hwB)
    (F.yB0 N hw hwB) (F.yB1 N hthree hw hwB) (F.yBS_ne_yB0 N hCubic hw hwB)
    (F.yBS_ne_yB1 N hCubic hthree hw hwB) (F.yB0_ne_yB1 N hN hthree hw hwB)
    (F.red_halfEdge_cases_B N hCubic hthree hw hwB)] at hL
  have hex := F.exists_markedB N hthree
  have hp := F.marked_posBV N hw hwB
  have e0 : (F.B.tour.edge (F.posBV hwB)).1 ∈ F.lift N hthree L ↔
      (F.yB0 N hw hwB).1.1 ∈ L := by
    rw [F.mem_lift N hthree, F.lab_B N hthree hex,
      F.repEdgeB_congr N _ hp (F.B.start_of_marked (F.W N) hex hp),
      F.B.back_eq_zero_of_marked (F.W N) hex hp]
    exact ⟨fun h ↦ h.mpr Even.zero, fun h ↦ iff_of_true h Even.zero⟩
  have e1 : (F.B.tour.edge (F.B.tour.prev (F.posBV hwB))).1 ∈ F.lift N hthree L ↔
      (F.yB1 N hthree hw hwB).1.1 ∈ L := by
    have hb := (F.B.back_nextM_sub_one (F.W N) hex
      (F.B.marked_prevM (F.W N) hex (F.posBV hwB))).1
    rw [F.B.nextM_prevM (F.W N) hex hp] at hb
    have hev : Even (F.B.back (F.W N) hex (F.posBV hwB - 1)) := by
      rw [hb]
      exact Nat.Odd.sub_odd (F.forward_odd N hCubic hN F.B (F.boundary_B_mem_compl hCubic)
        F.B_edge_notin_compl _) odd_one
    rw [F.mem_lift N hthree, EulerTour.prev_eq_sub_one, F.lab_B N hthree hex]
    exact ⟨fun h ↦ h.mpr hev, fun h ↦ iff_of_true h hev⟩
  have e2 : (F.B.boundaryHalfEdge hCubic (F.posBV hwB)).1 ∈ F.lift N hthree L ↔
      (F.yBS N hCubic hw hwB).1.1 ∈ L := by
    rw [F.mem_lift N hthree, F.lab_sat N hthree (F.boundary_B_mem_sat_of_marked N hCubic hp)]
    exact Iff.rfl
  rw [← F.vertexAt_posBV hwB, degreeIn_at_position hCubic F.B _ (F.posBV hwB)]
  simp only [e0, e1, e2]
  split_ifs at hL ⊢ <;> omega

include hCubic hthree in
/-- At an unmarked vertex of `B`, exactly one of the two circuit edges is lifted. -/
theorem lift_degree_B_unmarked (L : Finset (F.RedE N)) {p : F.B.tour.Pos}
    (hp : ¬ F.B.Marked (F.W N) p) :
    H.degreeIn (F.lift N hthree L) (F.B.tour.vertexAt p) = 1 := by
  have hex := F.exists_markedB N hthree
  have hb : F.B.back (F.W N) hex p = F.B.back (F.W N) hex (p - 1) + 1 := by
    have h1 := F.B.back_sub_one_of_not_marked (F.W N) hex hp
    have h2 := F.B.back_pos_of_not_marked (F.W N) hex hp
    omega
  have e0 : (F.B.tour.edge p).1 ∈ F.lift N hthree L ↔
      (F.repEdgeB N (F.B.marked_start (F.W N) hex (p - 1)) ∈ L ↔
        ¬ Even (F.B.back (F.W N) hex (p - 1))) := by
    rw [F.mem_lift N hthree, F.lab_B N hthree hex,
      F.repEdgeB_congr N _ (F.B.marked_start (F.W N) hex (p - 1))
        (F.B.start_sub_one_of_not_marked (F.W N) hex hp).symm, hb, Nat.even_add_one]
  have e1 : (F.B.tour.edge (F.B.tour.prev p)).1 ∈ F.lift N hthree L ↔
      (F.repEdgeB N (F.B.marked_start (F.W N) hex (p - 1)) ∈ L ↔
        Even (F.B.back (F.W N) hex (p - 1))) := by
    rw [F.mem_lift N hthree, EulerTour.prev_eq_sub_one, F.lab_B N hthree hex]
  have e2 : (F.B.boundaryHalfEdge hCubic p).1 ∉ F.lift N hthree L := by
    rw [F.mem_lift N hthree]
    exact F.not_lab_of_compl N hthree (F.boundary_B_mem_compl hCubic p) fun h ↦
      hp ((F.marked_iff N hCubic F.B (F.boundary_B_mem_compl hCubic)
        F.B_edge_notin_compl p).mpr h)
  rw [degreeIn_at_position hCubic F.B _ p]
  simp only [e0, e1, if_neg e2]
  by_cases hr : F.repEdgeB N (F.B.marked_start (F.W N) hex (p - 1)) ∈ L <;>
    by_cases he : Even (F.B.back (F.W N) hex (p - 1)) <;> simp [hr, he]

include hCubic hN hthree in
/-- Every edge of `B` is lifted from one of three perfect matchings covering the reduced graph
together with `S`. -/
theorem lift_cover_B {L₁ L₂ L₃ : Finset (F.RedE N)} (h₁ : (F.red N).IsPerfectMatching L₁)
    (h₂ : (F.red N).IsPerfectMatching L₂) (h₃ : (F.red N).IsPerfectMatching L₃)
    (hcov : F.satRed N ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ) {e : E} (he : e ∈ F.B.edges) :
    e ∈ F.lift N hthree L₁ ∨ e ∈ F.lift N hthree L₂ ∨ e ∈ F.lift N hthree L₃ := by
  have hex := F.exists_markedB N hthree
  obtain ⟨q, rfl⟩ : ∃ q, e = (F.B.tour.edge q).1 := ⟨F.posB he, (F.edge_posB he).symm⟩
  have hrS : F.repEdgeB N (F.B.marked_start (F.W N) hex q) ∉ F.satRed N := fun h ↦
    F.repsB_notin_sat N (F.edge_mem_repsB N (F.B.marked_start (F.W N) hex q))
      ((F.mem_satRed N).mp h)
  have hmem : F.repEdgeB N (F.B.marked_start (F.W N) hex q) ∈ L₁ ∨
      F.repEdgeB N (F.B.marked_start (F.W N) hex q) ∈ L₂ ∨
      F.repEdgeB N (F.B.marked_start (F.W N) hex q) ∈ L₃ := by
    have := Finset.mem_univ (F.repEdgeB N (F.B.marked_start (F.W N) hex q))
    rw [← hcov] at this
    simp only [Finset.mem_union] at this
    rcases this with ((h | h) | h) | h
    · exact absurd h hrS
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hnot := exists_not_mem_of_cover (F.red_cubic N hCubic hN hthree)
    (F.satRed_perfect N hCubic hN hthree) h₁ h₂ h₃ hcov
    (F.repEdgeB N (F.B.marked_start (F.W N) hex q))
  rw [F.mem_lift N hthree, F.mem_lift N hthree, F.mem_lift N hthree, F.lab_B N hthree hex,
    F.lab_B N hthree hex, F.lab_B N hthree hex]
  by_cases hev : Even (F.B.back (F.W N) hex q)
  · rcases hmem with h | h | h
    · exact Or.inl (iff_of_true h hev)
    · exact Or.inr (Or.inl (iff_of_true h hev))
    · exact Or.inr (Or.inr (iff_of_true h hev))
  · rcases hnot with h | h | h
    · exact Or.inl (iff_of_false h hev)
    · exact Or.inr (Or.inl (iff_of_false h hev))
    · exact Or.inr (Or.inr (iff_of_false h hev))

include hCubic hN hthree in
/-- The lift of a perfect matching of the reduced graph is a perfect matching. -/
theorem lift_perfect {L : Finset (F.RedE N)} (hL : (F.red N).IsPerfectMatching L) :
    H.IsPerfectMatching (F.lift N hthree L) := by
  intro w
  rcases F.cover w with hwA | hwB
  · by_cases hw : w ∈ F.W N
    · exact F.lift_degree_A_marked N hCubic hN hthree hw hwA (hL ⟨w, hw⟩)
    · have := F.lift_degree_A_unmarked N hCubic hthree L (p := F.posAV hwA) (by
        unfold TraversedCircuit.Marked
        rw [F.vertexAt_posAV hwA]
        exact hw)
      rwa [F.vertexAt_posAV hwA] at this
  · by_cases hw : w ∈ F.W N
    · exact F.lift_degree_B_marked N hCubic hN hthree hw hwB (hL ⟨w, hw⟩)
    · have := F.lift_degree_B_unmarked N hCubic hthree L (p := F.posBV hwB) (by
        unfold TraversedCircuit.Marked
        rw [F.vertexAt_posBV hwB]
        exact hw)
      rwa [F.vertexAt_posBV hwB] at this

include hCubic hN hthree in
/-- The lifts of a four-cover of the reduced graph cover `G` together with `M`. -/
theorem lift_cover {L₁ L₂ L₃ : Finset (F.RedE N)} (h₁ : (F.red N).IsPerfectMatching L₁)
    (h₂ : (F.red N).IsPerfectMatching L₂) (h₃ : (F.red N).IsPerfectMatching L₃)
    (hcov : F.satRed N ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ) :
    F.compl ∪ F.lift N hthree L₁ ∪ F.lift N hthree L₂ ∪ F.lift N hthree L₃ = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro e
  simp only [Finset.mem_union]
  by_cases he : e ∈ F.compl
  · exact Or.inl (Or.inl (Or.inl he))
  · have hAB : e ∈ F.A.edges ∨ e ∈ F.B.edges := by
      by_contra h
      push Not at h
      exact he (F.mem_compl_iff.mpr h)
    rcases hAB with hA | hB
    · rcases F.lift_cover_A N hCubic hN hthree h₁ h₂ h₃ hcov hA with h | h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rcases F.lift_cover_B N hCubic hN hthree h₁ h₂ h₃ hcov hB with h | h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

end Lifting

end Reduction

/-- **Four perfect matchings covering a two-circuit factor** (the note's main theorem), conditional
on its two external ingredients.  Given a cubic loopless graph with a two-circuit factor whose
complementary matching `M` is `F.compl`, a perfect matching `N` meeting the cross-spokes in exactly
three edges (supplied by the Campos–Lucchesi theorem for proper snarks other than the Petersen
graph), and the Karabáš–Máčajová corollary `KMThreeSpokes`, there are perfect matchings
`M₁, M₂, M₃` with `M ∪ M₁ ∪ M₂ ∪ M₃ = E(G)`. -/
theorem exists_fourCover (hCubic : ∀ v : V, H.degree v = 3)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hCL : ∃ N, H.IsPerfectMatching N ∧ (N ∩ F.cross).card = 3) (hKM : KMThreeSpokes.{u, v}) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ := by
  obtain ⟨N, hN, hthree⟩ := hCL
  obtain ⟨L₁, L₂, L₃, h₁, h₂, h₃, hcov⟩ := hKM (F.red N) (F.red_cubic N hCubic hN hthree)
    (F.red_loopless N hN hthree hloopless) (F.satRed N)
    (F.satRed_perfect N hCubic hN hthree) (F.redA N hCubic hN hthree) (F.redB N hCubic hN hthree)
    (F.disjoint_repsRed N) (F.repsRed_union N) (F.card_repsARed_odd N hN hthree hloopless)
    (F.card_repsBRed_odd N hN hthree hloopless) (F.red_cross_card N hthree)
  exact ⟨_, _, _, F.lift_perfect N hCubic hN hthree h₁, F.lift_perfect N hCubic hN hthree h₂,
    F.lift_perfect N hCubic hN hthree h₃, F.lift_cover N hCubic hN hthree h₁ h₂ h₃ hcov⟩

end TwoCircuitFactor

end LoopMultigraph
end GraphPuzzles
