import GraphPuzzles.Matching.MatchingHub

/-!
# The cross-spoke cut is a nontrivial separating cut

The note's Lemma (separating): for a two-circuit factor `A ∪ B` of a bridgeless cubic graph with
both circuits odd, the cut `δ(V(A))` between the circuits is a nontrivial separating cut.  The
contraction `G / V(B)` has the contracted vertex `b` of odd degree `|δ(V(A))|`, every other vertex
cubic, is connected and bridgeless, and `G / V(B) − b = G[V(A)]` is factor-critical because the odd
circuit `A` spans it; the hub lemma then shows that the contraction is matching covered.  The
other contraction is handled by exchanging the two circuits.  Together with the Campos–Lucchesi
conclusion for `G` this produces the perfect matching meeting the cross-spokes in exactly three
edges that the four-cover theorem needs.  Finally, the circuits of a two-circuit factor of a
non-3-edge-colourable cubic graph are odd: two even circuits coloured alternately, with a third
colour on the complementary matching, would be a proper colouring.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped Fin.NatCast

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : j = Fin.rev i := by
  revert i j
  decide

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

omit [DecidableEq E] in
theorem next_eq_add_one (p : C.tour.Pos) : C.tour.next p = p + 1 := finRotate_apply p

omit [DecidableEq E] in
/-- The ends of the edge at position `p` are the vertices at positions `p` and `p + 1`. -/
theorem endAt_edge_eq (p : C.tour.Pos) (k : Fin 2) :
    H.endAt (C.tour.edge p).1 k = C.tour.vertexAt p ∨
      H.endAt (C.tour.edge p).1 k = C.tour.vertexAt (p + 1) := by
  rw [← C.next_eq_add_one, ← C.tour.arrival_eq_vertexAt_next]
  by_cases hk : k = C.tour.depart p
  · left
    rw [hk]
    rfl
  · right
    rw [fin2_eq_rev_of_ne (Ne.symm hk)]
    rfl

omit [DecidableEq E] in
/-- A vertex colouring equal across the circuit edges other than the one at position `q` is
constant on the circuit. -/
theorem const_of_step (c : V → Bool) (q : C.tour.Pos)
    (hstep : ∀ p, p ≠ q → c (C.tour.vertexAt p) = c (C.tour.vertexAt (p + 1))) (p : C.tour.Pos) :
    c (C.tour.vertexAt p) = c (C.tour.vertexAt (q + 1)) := by
  have key : ∀ m : ℕ, m ≤ C.tour.n →
      c (C.tour.vertexAt (q + 1 + (m : C.tour.Pos))) = c (C.tour.vertexAt (q + 1)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [C.posCast_zero, add_zero]
    | succ m ih =>
      intro hm
      rw [C.posCast_add, C.posCast_one, ← add_assoc, ← ih (by omega)]
      apply (hstep _ _).symm
      intro h
      have h' : ((1 + m : ℕ) : C.tour.Pos) = 0 := by
        rw [C.posCast_add, C.posCast_one]
        rw [add_assoc] at h
        exact add_eq_left.mp h
      have hv := congrArg Fin.val h'
      rw [Fin.val_cast_of_lt (by omega : 1 + m < C.tour.n + 1)] at hv
      simp at hv
  obtain ⟨m, hm, hpm⟩ : ∃ m : ℕ, m ≤ C.tour.n ∧ p = q + 1 + (m : C.tour.Pos) :=
    ⟨(p - (q + 1)).val, by have := (p - (q + 1)).isLt; omega, by
      rw [Fin.cast_val_eq_self, add_sub_cancel]⟩
  rw [hpm]
  exact key m hm

omit [DecidableEq E] in
theorem const_of_all (c : V → Bool)
    (hstep : ∀ p, c (C.tour.vertexAt p) = c (C.tour.vertexAt (p + 1))) (p p' : C.tour.Pos) :
    c (C.tour.vertexAt p) = c (C.tour.vertexAt p') := by
  rw [C.const_of_step c p (fun p _ ↦ hstep p) p, C.const_of_step c p (fun p _ ↦ hstep p) p']

omit [DecidableEq E] in
theorem exists_pos {v : V} (hv : v ∈ C.vertices) : ∃ p, C.tour.vertexAt p = v :=
  ⟨C.positionVertexEquiv.symm ⟨v, hv⟩,
    congrArg Subtype.val (C.positionVertexEquiv.apply_symm_apply ⟨v, hv⟩)⟩

omit [DecidableEq E] in
theorem vertexAt_injective : Function.Injective C.tour.vertexAt := by
  intro p q h
  apply C.positionVertexEquiv.injective
  apply Subtype.ext
  rw [C.positionVertexEquiv_apply_val, C.positionVertexEquiv_apply_val]
  exact h

omit [DecidableEq E] in
theorem card_vertices_eq : C.vertices.card = C.edges.card := by
  rw [← Fintype.card_coe C.vertices, ← Fintype.card_coe C.edges]
  exact (Fintype.card_congr C.positionVertexEquiv).symm.trans (Fintype.card_congr C.tour.edge)

omit [DecidableEq E] in
theorem card_edges_eq : C.edges.card = C.tour.n + 1 := by
  rw [← Fintype.card_coe C.edges, ← Fintype.card_congr C.tour.edge]
  exact Fintype.card_fin _

omit [DecidableEq E] in
/-- A colouring equal across an edge is equal across the ends of the circuit edge at any
position. -/
theorem step_of_edge (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (c : V → Bool) (p : C.tour.Pos)
    (h : c (H.endAt (C.tour.edge p).1 0) = c (H.endAt (C.tour.edge p).1 1)) :
    c (C.tour.vertexAt p) = c (C.tour.vertexAt (p + 1)) := by
  rcases C.endAt_edge_eq p 0 with h0 | h0 <;> rcases C.endAt_edge_eq p 1 with h1 | h1
  · exact absurd (h0.trans h1.symm) (hloopless _)
  · rw [← h0, ← h1]
    exact h
  · rw [← h0, ← h1]
    exact h.symm
  · exact absurd (h0.trans h1.symm) (hloopless _)

/-- The edges at odd positions. -/
def oddEdges : Finset E :=
  Finset.univ.filter fun e ↦ ∃ p : C.tour.Pos, Odd p.val ∧ e = (C.tour.edge p).1

theorem edge_mem_oddEdges (p : C.tour.Pos) : (C.tour.edge p).1 ∈ C.oddEdges ↔ Odd p.val := by
  simp only [oddEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p', hp', h⟩
    have : p' = p := C.tour.edge.injective (Subtype.ext h.symm)
    rw [← this]
    exact hp'
  · intro h
    exact ⟨p, h, rfl⟩

theorem oddEdges_subset : C.oddEdges ⊆ C.edges := by
  intro e he
  obtain ⟨p, -, rfl⟩ := (Finset.mem_filter.mp he).2
  exact (C.tour.edge p).2

/-- On an odd circuit, the edges at odd positions match every vertex except the starting one. -/
theorem degreeIn_oddEdges (hCubic : ∀ v : V, H.degree v = 3) (hn : Even C.tour.n)
    (p : C.tour.Pos) : H.degreeIn C.oddEdges (C.tour.vertexAt p) = if p = 0 then 0 else 1 := by
  rw [TwoCircuitFactor.degreeIn_at_position hCubic C _ p, C.tour.prev_eq_sub_one]
  have hb : (C.boundaryHalfEdge hCubic p).1 ∉ C.oddEdges := fun h ↦
    C.boundaryHalfEdge_not_mem hCubic p (C.oddEdges_subset h)
  rw [if_neg hb]
  by_cases hp : p = 0
  · subst hp
    have h0 : ¬ Odd (0 : C.tour.Pos).val := by simp
    have h1 : ¬ Odd ((0 : C.tour.Pos) - 1).val := by
      rw [Fin.coe_sub_one, if_pos rfl, Nat.not_odd_iff_even]
      exact hn
    rw [if_pos rfl, if_neg ((C.edge_mem_oddEdges 0).not.mpr h0),
      if_neg ((C.edge_mem_oddEdges _).not.mpr h1)]
  · rw [if_neg hp]
    have hval : (p - 1).val = p.val - 1 := by rw [Fin.coe_sub_one, if_neg hp]
    have hpos : 0 < p.val := Fin.pos_iff_ne_zero.mpr hp
    by_cases ho : Odd p.val
    · have he : ¬ Odd (p - 1).val := by
        rw [hval, Nat.not_odd_iff_even]
        exact Nat.Odd.sub_odd ho odd_one
      rw [if_pos ((C.edge_mem_oddEdges p).mpr ho), if_neg ((C.edge_mem_oddEdges _).not.mpr he)]
    · have he : Odd (p - 1).val := by
        rw [hval]
        rw [Nat.not_odd_iff_even] at ho
        exact Nat.Even.sub_odd hpos ho odd_one
      rw [if_neg ((C.edge_mem_oddEdges p).not.mpr ho), if_pos ((C.edge_mem_oddEdges _).mpr he)]

/-- An edge at an odd position avoids the starting vertex of an odd circuit. -/
theorem endAt_oddEdges_ne (hn : Even C.tour.n) {e : E} (he : e ∈ C.oddEdges) (k : Fin 2) :
    H.endAt e k ≠ C.tour.vertexAt 0 := by
  obtain ⟨p, hp, rfl⟩ := (Finset.mem_filter.mp he).2
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp
    exact absurd hp (by simp)
  have hp1 : p + 1 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_add_one] at hv
    split_ifs at hv with hl
    · rw [hl, Fin.val_last] at hp
      exact (Nat.not_odd_iff_even.mpr hn) hp
    · simp at hv
  rcases C.endAt_edge_eq p k with h | h <;> rw [h]
  · exact fun h' ↦ hp0 (C.vertexAt_injective h')
  · exact fun h' ↦ hp1 (C.vertexAt_injective h')

end TraversedCircuit

section ContractDegree

variable {H : LoopMultigraph V E} (X : Finset V)

/-- Degrees in the contraction at a vertex of `X` are degrees in `H`. -/
theorem contract_degreeIn_some (M₀ : Finset E) (v : {v // v ∈ X}) :
    (H.contract X).degreeIn (Finset.univ.filter fun f ↦ f.1 ∈ M₀) (some v) =
      H.degreeIn M₀ v.1 := by
  rw [(H.contract X).degreeIn_eq_card_halfEdges, H.degreeIn_eq_card_halfEdges]
  apply Finset.card_equiv (contractHalfEdgeEquiv X v)
  intro h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

end ContractDegree

namespace TwoCircuitFactor

variable {H : LoopMultigraph V E} (F : H.TwoCircuitFactor)

omit [DecidableEq E] in
theorem vertices_B_eq : F.B.vertices = Finset.univ \ F.A.vertices := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact ⟨fun h h' ↦ F.disjoint v h' h, fun h ↦ (F.cover v).resolve_left h⟩

/-- The cross-spokes are the dangling edges of `V(A)`. -/
theorem cross_eq_dangling : F.cross = H.dangling F.A.vertices := by
  ext e
  rw [cross, Finset.mem_filter, mem_dangling]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [F.mem_compl_iff]
    refine ⟨fun hA ↦ h ⟨fun _ ↦ F.endAt_mem_A hA 1, fun _ ↦ F.endAt_mem_A hA 0⟩, fun hB ↦ ?_⟩
    have h0 : H.endAt e 0 ∉ F.A.vertices := fun h' ↦ F.disjoint _ h' (F.endAt_mem_B hB 0)
    have h1 : H.endAt e 1 ∉ F.A.vertices := fun h' ↦ F.disjoint _ h' (F.endAt_mem_B hB 1)
    exact h ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩

theorem dangling_subset_compl : H.dangling F.A.vertices ⊆ F.compl := by
  rw [← F.cross_eq_dangling]
  exact Finset.filter_subset _ _

variable (hCubic : ∀ v : V, H.degree v = 3) (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
  (hbridge : H.IsBridgeless)

include hCubic in
/-- With `A` odd, the cut between the circuits is odd. -/
theorem odd_card_dangling_A (hoddA : Odd F.A.edges.card) :
    Odd (H.dangling F.A.vertices).card := by
  have h := card_mod_two_of_degreeIn_one (fun v _ ↦ F.compl_perfect hCubic v)
    (X := F.A.vertices)
  rw [Finset.inter_eq_right.mpr F.dangling_subset_compl, F.A.card_vertices_eq] at h
  rw [Nat.odd_iff] at hoddA ⊢
  omega

include hCubic hbridge in
theorem three_le_card_dangling_A (hoddA : Odd F.A.edges.card) :
    3 ≤ (H.dangling F.A.vertices).card := by
  have h1 := F.odd_card_dangling_A hCubic hoddA
  have h2 := card_dangling_ne_one hbridge F.A.vertices
  rw [Nat.odd_iff] at h1
  omega

omit [DecidableEq E] in
/-- An odd circuit of a loopless graph has at least three edges. -/
theorem three_le_card_edges_A (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hoddA : Odd F.A.edges.card) : 3 ≤ F.A.edges.card := by
  have hne : F.A.edges.card ≠ 1 := by
    intro h1
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
    have hv : H.endAt e 0 ∈ F.A.vertices := by
      apply H.mem_edgeSupport_iff.mpr
      exact ⟨e, he ▸ Finset.mem_singleton_self e, 0, rfl⟩
    have h2 := F.A.twoRegular _ hv
    rw [he, degreeIn_singleton] at h2
    have h1' : H.endAt e 1 = H.endAt e 0 := by
      by_contra hne
      have : (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k = H.endAt e 0) = {0} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rcases fin2_cases k with rfl | rfl
        · simp
        · exact iff_of_false hne (by decide)
      rw [this, Finset.card_singleton] at h2
      exact absurd h2 (by decide)
    exact hloopless e h1'.symm
  rw [Nat.odd_iff] at hoddA
  omega

/-! ### The contraction `G / V(B)` -/

section Contraction

omit [DecidableEq E] in
/-- The ends of an edge of `A` in the contraction. -/
theorem contract_endAt_A {e : E} (he : e ∈ F.A.edges) (k : Fin 2) :
    (H.contract F.A.vertices).endAt
      ⟨e, mem_meets.mpr ⟨0, F.endAt_mem_A he 0⟩⟩ k = some ⟨H.endAt e k, F.endAt_mem_A he k⟩ :=
  (contract_endAt_eq_some_iff _ _ _ _).mpr rfl

/-- Contraction vertices as a colouring of `V`. -/
def liftColouring (c : Option {v // v ∈ F.A.vertices} → Bool) (w : V) : Bool :=
  if h : w ∈ F.A.vertices then c (some ⟨w, h⟩) else c none

omit [DecidableEq E] in
theorem liftColouring_of_mem (c : Option {v // v ∈ F.A.vertices} → Bool) {w : V}
    (h : w ∈ F.A.vertices) : F.liftColouring c w = c (some ⟨w, h⟩) := by
  simp [liftColouring, h]

include hloopless in
omit [DecidableEq E] in
/-- A colouring of the contraction equal across the edges of `A` is constant on `V(A)`. -/
theorem liftColouring_const (c : Option {v // v ∈ F.A.vertices} → Bool)
    (hstep : ∀ e (he : e ∈ F.A.edges),
      c ((H.contract F.A.vertices).endAt ⟨e, mem_meets.mpr ⟨0, F.endAt_mem_A he 0⟩⟩ 0) =
        c ((H.contract F.A.vertices).endAt ⟨e, mem_meets.mpr ⟨0, F.endAt_mem_A he 0⟩⟩ 1))
    {x y : V} (hx : x ∈ F.A.vertices) (hy : y ∈ F.A.vertices) :
    F.liftColouring c x = F.liftColouring c y := by
  obtain ⟨p, rfl⟩ := F.A.exists_pos hx
  obtain ⟨q, rfl⟩ := F.A.exists_pos hy
  apply F.A.const_of_all (F.liftColouring c)
  intro p
  apply F.A.step_of_edge hloopless
  have h := hstep _ (F.A.tour.edge p).2
  rw [F.contract_endAt_A (F.A.tour.edge p).2, F.contract_endAt_A (F.A.tour.edge p).2] at h
  rw [F.liftColouring_of_mem c (F.endAt_mem_A (F.A.tour.edge p).2 0),
    F.liftColouring_of_mem c (F.endAt_mem_A (F.A.tour.edge p).2 1)]
  exact h

omit [DecidableEq E] in
/-- A dangling edge joins its end in `V(A)` to the contracted vertex. -/
theorem contract_endAt_dangling {e : E} (he : e ∈ H.dangling F.A.vertices) :
    ∃ k, ∃ hk : H.endAt e k ∈ F.A.vertices,
      (H.contract F.A.vertices).endAt ⟨e, mem_meets.mpr ⟨k, hk⟩⟩ k = some ⟨H.endAt e k, hk⟩ ∧
      (H.contract F.A.vertices).endAt ⟨e, mem_meets.mpr ⟨k, hk⟩⟩ (Fin.rev k) = none := by
  rw [mem_dangling] at he
  by_cases h0 : H.endAt e 0 ∈ F.A.vertices
  · have h1 : H.endAt e 1 ∉ F.A.vertices := fun h1 ↦ he ⟨fun _ ↦ h1, fun _ ↦ h0⟩
    exact ⟨0, h0, (contract_endAt_eq_some_iff _ _ _ _).mpr rfl,
      (contract_endAt_eq_none_iff _ _ _).mpr h1⟩
  · have h1 : H.endAt e 1 ∈ F.A.vertices := by
      by_contra h1
      exact he ⟨fun h ↦ absurd h h0, fun h ↦ absurd h h1⟩
    exact ⟨1, h1, (contract_endAt_eq_some_iff _ _ _ _).mpr rfl,
      (contract_endAt_eq_none_iff _ _ _).mpr h0⟩

/-- Every edge of the contraction is an edge of `A` or an edge of `M`. -/
theorem contract_edge_cases (f : {e // e ∈ H.meets F.A.vertices}) :
    f.1 ∈ F.A.edges ∨ f.1 ∈ F.compl := by
  by_cases hA : f.1 ∈ F.A.edges
  · exact Or.inl hA
  · right
    rw [F.mem_compl_iff]
    refine ⟨hA, fun hB ↦ ?_⟩
    obtain ⟨k, hk⟩ := mem_meets.mp f.2
    exact F.disjoint _ hk (F.endAt_mem_B hB k)

include hCubic hloopless hbridge in
/-- The contraction is connected. -/
theorem contract_isConnected (hoddA : Odd F.A.edges.card) :
    (H.contract F.A.vertices).IsConnected := by
  intro c hc
  have hconst := fun {x y : V} (hx : x ∈ F.A.vertices) (hy : y ∈ F.A.vertices) ↦
    F.liftColouring_const hloopless c (fun e he ↦ hc _) hx hy
  obtain ⟨d, hd⟩ := Finset.card_pos.mp
    (by have := F.three_le_card_dangling_A hCubic hbridge hoddA; omega :
      0 < (H.dangling F.A.vertices).card)
  obtain ⟨k, hk, hsome, hnone⟩ := F.contract_endAt_dangling hd
  have hdc := hc ⟨d, mem_meets.mpr ⟨k, hk⟩⟩
  have hkey : c (some ⟨H.endAt d k, hk⟩) = c none := by
    rcases fin2_cases k with rfl | rfl
    · rw [← hsome, ← hnone]
      exact hdc
    · rw [← hsome, ← hnone]
      exact hdc.symm
  have hall : ∀ a, c a = c none := by
    intro a
    rcases a with _ | ⟨x, hx⟩
    · rfl
    · rw [← hkey, ← F.liftColouring_of_mem c hx, ← F.liftColouring_of_mem c hk]
      exact hconst hx hk
  intro a b
  rw [hall a, hall b]

include hCubic hloopless hbridge in
/-- The contraction is bridgeless. -/
theorem contract_isBridgeless (hoddA : Odd F.A.edges.card) :
    (H.contract F.A.vertices).IsBridgeless := by
  intro f c hc
  rcases F.contract_edge_cases f with hA | hM
  · -- a rim edge: the rest of the circuit joins its ends
    obtain ⟨q, hq⟩ : ∃ q, (F.A.tour.edge q).1 = f.1 :=
      ⟨F.A.tour.edge.symm ⟨f.1, hA⟩, by simp⟩
    have hstep : ∀ p, p ≠ q →
        F.liftColouring c (F.A.tour.vertexAt p) = F.liftColouring c (F.A.tour.vertexAt (p + 1)) := by
      intro p hpq
      apply F.A.step_of_edge hloopless
      have hne : (⟨(F.A.tour.edge p).1, mem_meets.mpr ⟨0, F.endAt_mem_A (F.A.tour.edge p).2 0⟩⟩ :
          {e // e ∈ H.meets F.A.vertices}) ≠ f := by
        intro h
        apply hpq
        apply F.A.tour.edge.injective
        apply Subtype.ext
        rw [hq]
        exact congrArg Subtype.val h
      have h := hc _ hne
      rw [F.contract_endAt_A (F.A.tour.edge p).2, F.contract_endAt_A (F.A.tour.edge p).2] at h
      rw [F.liftColouring_of_mem c (F.endAt_mem_A (F.A.tour.edge p).2 0),
        F.liftColouring_of_mem c (F.endAt_mem_A (F.A.tour.edge p).2 1)]
      exact h
    have hconst := F.A.const_of_step (F.liftColouring c) q hstep
    have hf : f = ⟨(F.A.tour.edge q).1, mem_meets.mpr ⟨0, F.endAt_mem_A (F.A.tour.edge q).2 0⟩⟩ :=
      Subtype.ext hq.symm
    rw [hf, F.contract_endAt_A (F.A.tour.edge q).2, F.contract_endAt_A (F.A.tour.edge q).2,
      ← F.liftColouring_of_mem c, ← F.liftColouring_of_mem c]
    have key : ∀ a b : V, (a = F.A.tour.vertexAt q ∨ a = F.A.tour.vertexAt (q + 1)) →
        (b = F.A.tour.vertexAt q ∨ b = F.A.tour.vertexAt (q + 1)) →
        F.liftColouring c a = F.liftColouring c b := by
      rintro a b (rfl | rfl) (rfl | rfl)
      · rfl
      · exact (hconst q).trans (hconst (q + 1)).symm
      · exact (hconst (q + 1)).trans (hconst q).symm
      · rfl
    exact key _ _ (F.A.endAt_edge_eq q 0) (F.A.endAt_edge_eq q 1)
  · -- a chord or a cross-spoke: the whole circuit is available
    have hconst := fun {x y : V} (hx : x ∈ F.A.vertices) (hy : y ∈ F.A.vertices) ↦
      F.liftColouring_const hloopless c (fun e he ↦ hc _ (fun h ↦
        F.A_edge_notin_compl e he (by
          have := congrArg Subtype.val h
          rw [← this] at hM
          exact hM))) hx hy
    by_cases hd : f.1 ∈ H.dangling F.A.vertices
    · obtain ⟨k, hk, hsome, hnone⟩ := F.contract_endAt_dangling hd
      have hf : f = ⟨f.1, mem_meets.mpr ⟨k, hk⟩⟩ := Subtype.ext rfl
      -- a second cross-spoke joins `V(A)` to the contracted vertex
      obtain ⟨d, hd', hdf⟩ := Finset.exists_mem_ne
        (by have := F.three_le_card_dangling_A hCubic hbridge hoddA; omega :
          1 < (H.dangling F.A.vertices).card) f.1
      obtain ⟨k', hk', hsome', hnone'⟩ := F.contract_endAt_dangling hd'
      have hdc := hc ⟨d, mem_meets.mpr ⟨k', hk'⟩⟩ (fun h ↦ hdf (congrArg Subtype.val h))
      have hkey : c (some ⟨H.endAt d k', hk'⟩) = c none := by
        rcases fin2_cases k' with rfl | rfl
        · rw [← hsome', ← hnone']
          exact hdc
        · rw [← hsome', ← hnone']
          exact hdc.symm
      have hkey2 : c (some ⟨H.endAt f.1 k, hk⟩) = c none := by
        rw [← hkey, ← F.liftColouring_of_mem c hk, ← F.liftColouring_of_mem c hk']
        exact hconst hk hk'
      rcases fin2_cases k with rfl | rfl
      · rw [show Fin.rev (0 : Fin 2) = 1 from rfl] at hnone
        rw [hf, hsome, hnone]
        exact hkey2
      · rw [show Fin.rev (1 : Fin 2) = 0 from rfl] at hnone
        rw [hf, hsome, hnone]
        exact hkey2.symm
    · -- a chord: both ends in `V(A)`
      rw [mem_dangling, not_not] at hd
      obtain ⟨k, hk⟩ := mem_meets.mp f.2
      have h0 : H.endAt f.1 0 ∈ F.A.vertices := by
        rcases fin2_cases k with rfl | rfl
        · exact hk
        · exact hd.mpr hk
      have h1 : H.endAt f.1 1 ∈ F.A.vertices := hd.mp h0
      rw [(contract_endAt_eq_some_iff _ _ _ ⟨_, h0⟩).mpr rfl,
        (contract_endAt_eq_some_iff _ _ _ ⟨_, h1⟩).mpr rfl, ← F.liftColouring_of_mem c,
        ← F.liftColouring_of_mem c]
      exact hconst h0 h1

include hCubic in
/-- `G / V(B) − b = G[V(A)]` is factor-critical: the odd circuit `A` minus any vertex is matched
by its edges at odd positions. -/
theorem contract_isFactorCritical (hoddA : Odd F.A.edges.card) :
    (H.contract F.A.vertices).IsFactorCritical (Finset.univ.erase none) := by
  intro w hw
  obtain ⟨x, rfl⟩ : ∃ x, w = some x := by
    rcases w with _ | x
    · exact absurd (Finset.mem_erase.mp hw).1 (fun h ↦ h rfl)
    · exact ⟨x, rfl⟩
  let A' := F.A.rotateTo x.2
  have hA'e : A'.edges = F.A.edges := rfl
  have hn : Even A'.tour.n := by
    have h := F.A.card_edges_eq
    have : A'.tour.n = F.A.tour.n := rfl
    rw [this]
    rw [h, Nat.odd_iff] at hoddA
    rw [Nat.even_iff]
    omega
  have hx0 : A'.tour.vertexAt 0 = x.1 := by
    change (F.A.rotate _).tour.vertexAt 0 = _
    rw [F.A.rotate_vertexAt_zero]
    exact congrArg Subtype.val (F.A.positionVertexEquiv.apply_symm_apply ⟨x.1, x.2⟩)
  refine ⟨Finset.univ.filter fun f ↦ f.1 ∈ A'.oddEdges, ?_, ?_⟩
  · intro f hf k
    have hfA : f.1 ∈ F.A.edges := A'.oddEdges_subset (Finset.mem_filter.mp hf).2
    have hend : (H.contract F.A.vertices).endAt f k = some ⟨H.endAt f.1 k, F.endAt_mem_A hfA k⟩ :=
      (contract_endAt_eq_some_iff _ _ _ _).mpr rfl
    rw [hend]
    refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, Finset.mem_erase.mpr ⟨Option.some_ne_none _,
      Finset.mem_univ _⟩⟩
    apply A'.endAt_oddEdges_ne hn (Finset.mem_filter.mp hf).2 k
    rw [hx0]
    exact congrArg Subtype.val (Option.some_injective _ h)
  · intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
    obtain ⟨y, rfl⟩ : ∃ y, w = some y := by
      rcases w with _ | y
      · exact absurd rfl hw.2
      · exact ⟨y, rfl⟩
    rw [contract_degreeIn_some]
    obtain ⟨p, hp⟩ := A'.exists_pos y.2
    rw [← hp, A'.degreeIn_oddEdges hCubic hn p]
    rw [if_neg]
    rintro rfl
    apply hw.1
    congr 1
    apply Subtype.ext
    rw [← hp, hx0]

include hCubic hloopless hbridge in
/-- **Lemma (separating), one side**: the contraction `G / V(B)` is matching covered. -/
theorem contract_isMatchingCovered (hoddA : Odd F.A.edges.card) :
    (H.contract F.A.vertices).IsMatchingCovered := by
  apply isMatchingCovered_of_hub (F.contract_isConnected hCubic hloopless hbridge hoddA)
    (F.contract_isBridgeless hCubic hloopless hbridge hoddA) (contract_loopless _ hloopless) none
  · intro w hw
    obtain ⟨x, rfl⟩ : ∃ x, w = some x := by
      rcases w with _ | x
      · exact absurd rfl hw
      · exact ⟨x, rfl⟩
    rw [contract_degree_some]
    exact hCubic x.1
  · rw [contract_degree_none]
    exact F.odd_card_dangling_A hCubic hoddA
  · exact F.contract_isFactorCritical hCubic hoddA

end Contraction

include hCubic hloopless hbridge in
/-- **Lemma (separating)**: the cross-spoke cut is a nontrivial separating cut. -/
theorem isSeparatingCut_A (hoddA : Odd F.A.edges.card) (hoddB : Odd F.B.edges.card) :
    H.IsSeparatingCut F.A.vertices ∧ IsNontrivialCut F.A.vertices := by
  refine ⟨⟨F.contract_isMatchingCovered hCubic hloopless hbridge hoddA, ?_⟩, ?_, ?_⟩
  · rw [← F.vertices_B_eq]
    exact F.swap.contract_isMatchingCovered hCubic hloopless hbridge hoddB
  · rw [F.A.card_vertices_eq]
    have := F.three_le_card_edges_A hloopless hoddA
    omega
  · rw [← F.vertices_B_eq, F.B.card_vertices_eq]
    have := F.swap.three_le_card_edges_A hloopless hoddB
    change 3 ≤ F.B.edges.card at this
    omega

include hCubic hloopless hbridge in
/-- **The three-crossing perfect matching** from the Campos–Lucchesi conclusion for `G`. -/
theorem exists_three_crossing (hoddA : Odd F.A.edges.card) (hoddB : Odd F.B.edges.card)
    (hCL : H.CamposLucchesiFor) : ∃ N, H.IsPerfectMatching N ∧ (N ∩ F.cross).card = 3 := by
  obtain ⟨hsep, hnt⟩ := F.isSeparatingCut_A hCubic hloopless hbridge hoddA hoddB
  obtain ⟨N, hN, h3⟩ := hCL F.A.vertices hsep hnt
  rw [F.cross_eq_dangling]
  exact ⟨N, hN, h3⟩

/-! ### Both circuits are odd -/

theorem parityColor_sub_one_of_odd {n : ℕ} (hn : Odd n) (p : Fin (n + 1)) :
    parityColor (p - 1) ≠ parityColor p := by
  by_cases hp : p = 0
  · subst hp
    unfold parityColor
    rw [Fin.coe_sub_one, if_pos rfl]
    have : ¬ n % 2 = 0 := by
      rw [Nat.odd_iff] at hn
      omega
    simp only [Fin.val_zero, this, if_false, Nat.zero_mod, if_true]
    decide
  · exact parityColor_sub_one p hp

include hCubic in
/-- An even circuit of a two-circuit factor admits the parity colouring at all its vertices. -/
theorem parity_injective_all {C : H.TraversedCircuit} (hn : Odd C.tour.n) (g : E → Color)
    (hg : ∀ p : C.tour.Pos, g (C.tour.edge p).1 = parityColor p) (p : C.tour.Pos)
    (hbd : g (C.boundaryHalfEdge hCubic p).1 = (1, 1))
    (h₁ h₂ : H.halfEdgesAt (C.tour.vertexAt p)) (heq : g h₁.1.1 = g h₂.1.1) : h₁ = h₂ := by
  apply C.injective_at_of_positions hCubic p g _ _ _ h₁ h₂ heq
  · rw [hg, hg, C.tour.prev_eq_sub_one]
    exact (parityColor_sub_one_of_odd hn p).symm
  · rw [hg, hbd]
    exact parityColor_ne_third p
  · rw [hg, hbd]
    exact parityColor_ne_third _

include hCubic in
/-- If both circuits were even, alternating colours on them and a third colour on `M` would
properly colour the graph. -/
theorem exists_properOff_of_even (hA : Even F.A.edges.card) (hB : Even F.B.edges.card) :
    ∃ g : E → Color, H.ProperOff ∅ g := by
  have hnA : Odd F.A.tour.n := by
    rw [F.A.card_edges_eq, Nat.even_iff] at hA
    rw [Nat.odd_iff]
    omega
  have hnB : Odd F.B.tour.n := by
    rw [F.B.card_edges_eq, Nat.even_iff] at hB
    rw [Nat.odd_iff]
    omega
  let g : E → Color := fun e ↦
    if e ∈ F.A.edges then F.A.parityColoring e
    else if e ∈ F.B.edges then F.B.parityColoring e else (1, 1)
  have hgA : ∀ p : F.A.tour.Pos, g (F.A.tour.edge p).1 = parityColor p := by
    intro p
    have hmem : (F.A.tour.edge p).1 ∈ F.A.edges := (F.A.tour.edge p).2
    simp only [g, if_pos hmem]
    exact F.A.parityColoring_edge p
  have hgB : ∀ p : F.B.tour.Pos, g (F.B.tour.edge p).1 = parityColor p := by
    intro p
    have hmemB : (F.B.tour.edge p).1 ∈ F.B.edges := (F.B.tour.edge p).2
    have hnotA : (F.B.tour.edge p).1 ∉ F.A.edges := F.not_mem_A_of_mem_B hmemB
    simp only [g, if_neg hnotA, if_pos hmemB]
    exact F.B.parityColoring_edge p
  have hnz : ∀ e, g e ≠ 0 := by
    intro e
    simp only [g]
    split_ifs
    · exact F.A.parityColoring_ne_zero e
    · exact F.B.parityColoring_ne_zero e
    · decide
  refine ⟨g, fun e _ ↦ hnz e, ?_⟩
  intro v _ h₁ h₂ _ _ heq
  rcases F.cover v with hvA | hvB
  · obtain ⟨p, hp⟩ := F.A.exists_pos hvA
    subst hp
    apply parity_injective_all hCubic hnA g hgA p _ h₁ h₂ heq
    have hbA : (F.A.boundaryHalfEdge hCubic p).1 ∉ F.A.edges :=
      F.A.boundaryHalfEdge_not_mem hCubic p
    have hbB : (F.A.boundaryHalfEdge hCubic p).1 ∉ F.B.edges := by
      apply F.not_mem_B_of_endAt_mem_A (i := (F.A.boundaryHalfEdge hCubic p).2)
      rw [F.A.boundaryHalfEdge_endpoint]
      exact F.A.vertexAt_mem_vertices p
    simp only [g, if_neg hbA, if_neg hbB]
  · obtain ⟨p, hp⟩ := F.B.exists_pos hvB
    subst hp
    apply parity_injective_all hCubic hnB g hgB p _ h₁ h₂ heq
    have hbB : (F.B.boundaryHalfEdge hCubic p).1 ∉ F.B.edges :=
      F.B.boundaryHalfEdge_not_mem hCubic p
    have hbA : (F.B.boundaryHalfEdge hCubic p).1 ∉ F.A.edges := by
      apply F.not_mem_A_of_endAt_mem_B (i := (F.B.boundaryHalfEdge hCubic p).2)
      rw [F.B.boundaryHalfEdge_endpoint]
      exact F.B.vertexAt_mem_vertices p
    simp only [g, if_neg hbA, if_neg hbB]

include hCubic in
/-- The two circuits of a two-circuit factor of a non-3-edge-colourable cubic graph are odd. -/
theorem odd_of_not_colourable (hsnark : ¬ ∃ g : E → Color, H.ProperOff ∅ g) :
    Odd F.A.edges.card ∧ Odd F.B.edges.card := by
  have hsum : F.A.edges.card + F.B.edges.card = Fintype.card V := by
    rw [← F.A.card_vertices_eq, ← F.B.card_vertices_eq, F.vertices_B_eq,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ F.A.vertices
    omega
  have heven := card_even_of_odd_degrees (H := H) fun w ↦ by
    rw [hCubic w]
    decide
  rw [Nat.even_iff] at heven
  by_contra hcon
  apply hsnark
  apply F.exists_properOff_of_even hCubic
  · rw [Nat.even_iff]
    by_contra hA
    rw [Nat.odd_iff, Nat.odd_iff] at hcon
    apply hcon
    constructor <;> omega
  · rw [Nat.even_iff]
    by_contra hB
    rw [Nat.odd_iff, Nat.odd_iff] at hcon
    apply hcon
    constructor <;> omega

include hCubic hloopless hbridge in
/-- **Four perfect matchings covering a two-circuit factor of a snark**, with the note's
matching-theoretic lemmas formalized: the hypotheses are the Campos–Lucchesi conclusion for `G`
(valid for simple bricks other than the Petersen graph, which every proper snark is) and
Karabáš–Máčajová's Theorem 3.1 in ambient form. -/
theorem exists_fourCover_of_snark (hsnark : ¬ ∃ g : E → Color, H.ProperOff ∅ g)
    (hCL : H.CamposLucchesiFor) (hKM : KMThreePole.{u, v}) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ := by
  obtain ⟨hoddA, hoddB⟩ := F.odd_of_not_colourable hCubic hsnark
  exact F.exists_fourCover_of_kmThreePole hCubic hloopless
    (F.exists_three_crossing hCubic hloopless hbridge hoddA hoddB hCL) hKM

end TwoCircuitFactor

end LoopMultigraph
end GraphPuzzles
