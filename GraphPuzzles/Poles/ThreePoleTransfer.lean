import GraphPuzzles.Poles.PoleTheorem
import GraphPuzzles.Poles.ThreePole
import GraphPuzzles.Cuts.SeparatingCut

/-!
# Theorem 3.1 of Karabáš–Máčajová in the ambient graph

The abstract Theorem 3.1 (`Pole.exists_cover'`) is transferred to the ambient form
`KMThreePole` used by the four-cover modules: a cubic loopless multigraph `K`, a perfect matching
`S`, and a circuit `R` avoiding `S` whose vertex set `X` has exactly three dangling edges.  The
positions of a traversal of `R` (rotated so that a dangling edge sits at position `0`) form the
abstract pole; the chord map sends a position to the position of the other end of its `S`-edge.
A cover of the abstract pole gives the three pole matchings: the circuit edge at position `p`
belongs to `L i` when `i` labels it, the `S`-edge at `p` when `i` labels the chord at `p`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open scoped Fin.NatCast

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

private theorem fin2_eq_or_rev (k k' : Fin 2) : k' = k ∨ k' = Fin.rev k := by
  fin_cases k <;> fin_cases k' <;> decide

namespace PoleTransfer

variable {K : LoopMultigraph V E} (hCubic : ∀ v : V, K.degree v = 3)
  (hloopless : ∀ e, K.endAt e 0 ≠ K.endAt e 1) {S : Finset E} (hS : K.IsPerfectMatching S)
  (C : K.TraversedCircuit) (hCS : Disjoint C.edges S)

/-- The number of positions. -/
abbrev N : ℕ := C.tour.n + 1

/-- The position with a given index. -/
def pos (p : ℕ) : C.tour.Pos := (p : C.tour.Pos)

/-- The `S`-half-edge at a position: the boundary half-edge. -/
noncomputable def bd (q : C.tour.Pos) : E × Fin 2 := C.boundaryHalfEdge hCubic q

/-- The other end of the `S`-edge at a position. -/
noncomputable def other (q : C.tour.Pos) : V := K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2)

/-- The index of the position of a circuit vertex. -/
noncomputable def posOf (v : V) : ℕ :=
  if h : v ∈ C.vertices then (C.positionVertexEquiv.symm ⟨v, h⟩).val else 0

omit [DecidableEq E] in
theorem pos_val {p : ℕ} (hp : p < N C) : (pos C p).val = p := by
  unfold pos
  exact Fin.val_cast_of_lt hp

omit [DecidableEq E] in
theorem pos_of_val (q : C.tour.Pos) : pos C q.val = q := by
  unfold pos
  exact Fin.cast_val_eq_self q

omit [DecidableEq E] in
theorem posOf_lt {v : V} (hv : v ∈ C.vertices) : posOf C v < N C := by
  unfold posOf
  rw [dif_pos hv]
  exact (C.positionVertexEquiv.symm ⟨v, hv⟩).isLt

omit [DecidableEq E] in
theorem vertexAt_pos_posOf {v : V} (hv : v ∈ C.vertices) :
    C.tour.vertexAt (pos C (posOf C v)) = v := by
  unfold posOf
  rw [dif_pos hv, pos_of_val]
  exact congrArg Subtype.val (C.positionVertexEquiv.apply_symm_apply ⟨v, hv⟩)

omit [DecidableEq E] in
theorem posOf_vertexAt (q : C.tour.Pos) : posOf C (C.tour.vertexAt q) = q.val := by
  unfold posOf
  rw [dif_pos (C.vertexAt_mem_vertices q)]
  congr 1
  apply C.positionVertexEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem bd_not_mem (q : C.tour.Pos) : (bd hCubic C q).1 ∉ C.edges :=
  C.boundaryHalfEdge_not_mem hCubic q

theorem bd_endpoint (q : C.tour.Pos) :
    K.endAt (bd hCubic C q).1 (bd hCubic C q).2 = C.tour.vertexAt q :=
  C.boundaryHalfEdge_endpoint hCubic q

/-- Any half-edge at a circuit vertex whose edge is not on the circuit is the boundary
half-edge. -/
theorem eq_bd_of_not_mem {q : C.tour.Pos} {e : E} {k : Fin 2} (he : e ∉ C.edges)
    (hk : K.endAt e k = C.tour.vertexAt q) : (e, k) = bd hCubic C q := by
  obtain ⟨j, hj⟩ := C.positionHalfEdge_surjective hCubic q ⟨(e, k), hk⟩
  fin_cases j
  · have h1 : (C.tour.edge q).1 = e := congrArg Prod.fst hj
    exact absurd (h1 ▸ (C.tour.edge q).2) he
  · have h1 : (C.tour.edge (C.tour.prev q)).1 = e := congrArg Prod.fst hj
    exact absurd (h1 ▸ (C.tour.edge (C.tour.prev q)).2) he
  · exact hj.symm

include hS hCS in
theorem bd_mem_S (q : C.tour.Pos) : (bd hCubic C q).1 ∈ S := by
  have h := hS (C.tour.vertexAt q)
  unfold degreeIn at h
  obtain ⟨⟨e, k⟩, hek⟩ := Finset.card_pos.mp (by rw [h]; exact Nat.one_pos)
  rw [Finset.mem_filter, Finset.mem_product] at hek
  have hne : e ∉ C.edges := fun h' ↦ Finset.disjoint_left.mp hCS h' hek.1.1
  have := eq_bd_of_not_mem hCubic C hne hek.2
  rw [← this]
  exact hek.1.1

include hloopless in
theorem other_ne (q : C.tour.Pos) : other hCubic C q ≠ C.tour.vertexAt q := by
  unfold other
  rw [← bd_endpoint hCubic C q]
  rcases fin2_cases (bd hCubic C q).2 with h | h <;> rw [h]
  · exact (hloopless _).symm
  · exact hloopless _

omit [DecidableEq E] in
/-- Circuit edges have both ends on the circuit. -/
theorem endAt_mem_of_mem {e : E} (he : e ∈ C.edges) (k : Fin 2) : K.endAt e k ∈ C.vertices :=
  K.mem_edgeSupport_iff.mpr ⟨e, he, k, rfl⟩

/-- The boundary half-edge at the position of the other end of an `S`-edge is the reversed
half-edge. -/
theorem bd_other {q : C.tour.Pos} (hw : other hCubic C q ∈ C.vertices) :
    bd hCubic C (pos C (posOf C (other hCubic C q))) = ((bd hCubic C q).1, Fin.rev (bd hCubic C q).2) := by
  symm
  apply eq_bd_of_not_mem hCubic C (bd_not_mem hCubic C q)
  rw [vertexAt_pos_posOf C hw]
  rfl

theorem other_other {q : C.tour.Pos} (hw : other hCubic C q ∈ C.vertices) :
    other hCubic C (pos C (posOf C (other hCubic C q))) = C.tour.vertexAt q := by
  have h := bd_other hCubic C hw
  change K.endAt (bd hCubic C (pos C (posOf C (other hCubic C q)))).1
    (Fin.rev (bd hCubic C (pos C (posOf C (other hCubic C q)))).2) = _
  rw [h, Fin.rev_rev]
  exact bd_endpoint hCubic C q

/-- Spoke positions: positions whose `S`-edge leaves the circuit. -/
def IsSpoke (q : C.tour.Pos) : Prop := other hCubic C q ∉ C.vertices

noncomputable instance : DecidablePred (IsSpoke hCubic C) := fun _ ↦ Classical.propDecidable _

/-- The spoke positions. -/
noncomputable def spokes : Finset C.tour.Pos := Finset.univ.filter (IsSpoke hCubic C)

theorem mem_spokes {q : C.tour.Pos} : q ∈ spokes hCubic C ↔ other hCubic C q ∉ C.vertices := by
  unfold spokes
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

/-- The ends of the `S`-edge at a position are the position's vertex and `other`. -/
theorem endAt_bd_eq (q : C.tour.Pos) (k : Fin 2) :
    K.endAt (bd hCubic C q).1 k = C.tour.vertexAt q ∨ K.endAt (bd hCubic C q).1 k = other hCubic C q := by
  rcases fin2_eq_or_rev (bd hCubic C q).2 k with h | h
  · left
    rw [h]
    exact bd_endpoint hCubic C q
  · right
    rw [h]
    rfl

theorem bd_mem_dangling {q : C.tour.Pos} (hq : q ∈ spokes hCubic C) :
    (bd hCubic C q).1 ∈ K.dangling C.vertices := by
  rw [mem_spokes] at hq
  rw [mem_dangling]
  have hv := C.vertexAt_mem_vertices q
  have e1 := bd_endpoint hCubic C q
  have e2 : K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2) = other hCubic C q := rfl
  rcases fin2_cases (bd hCubic C q).2 with h | h
  · rw [h] at e1 e2
    rw [show Fin.rev (0 : Fin 2) = 1 from rfl] at e2
    rw [e1, e2]
    exact fun h' ↦ hq (h'.mp hv)
  · rw [h] at e1 e2
    rw [show Fin.rev (1 : Fin 2) = 0 from rfl] at e2
    rw [e1, e2]
    exact fun h' ↦ hq (h'.mpr hv)

/-- The map from spoke positions to dangling edges is a bijection. -/
theorem card_spokes : (spokes hCubic C).card = (K.dangling C.vertices).card := by
  apply Finset.card_bij (fun q _ ↦ (bd hCubic C q).1)
  · intro q hq
    exact bd_mem_dangling hCubic C hq
  · intro q hq q' hq' h
    have hq1 := (mem_spokes hCubic C).mp hq
    have hv := C.vertexAt_mem_vertices q
    have hv' := C.vertexAt_mem_vertices q'
    have e1 := bd_endpoint hCubic C q
    have e2 := bd_endpoint hCubic C q'
    rw [h] at e1
    apply C.vertexAt_injective
    rcases fin2_eq_or_rev (bd hCubic C q).2 (bd hCubic C q').2 with hk | hk
    · rw [hk] at e2
      exact e1.symm.trans e2
    · exfalso
      apply hq1
      change K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2) ∈ C.vertices
      rw [h, ← hk, e2]
      exact hv'
  · intro d hd
    have hd' := (mem_dangling.mp hd)
    have hne : d ∉ C.edges :=
      fun h ↦ hd' ⟨fun _ ↦ endAt_mem_of_mem C h 1, fun _ ↦ endAt_mem_of_mem C h 0⟩
    by_cases h0 : K.endAt d 0 ∈ C.vertices
    · obtain ⟨q, hq⟩ := C.exists_pos h0
      have hbd := eq_bd_of_not_mem hCubic C hne hq.symm
      refine ⟨q, ?_, ?_⟩
      · rw [mem_spokes]
        change K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2) ∉ C.vertices
        rw [← hbd]
        exact fun h1 ↦ hd' ⟨fun _ ↦ h1, fun _ ↦ h0⟩
      · rw [← hbd]
    · have h1 : K.endAt d 1 ∈ C.vertices := by
        by_contra h1
        exact hd' ⟨fun h ↦ absurd h h0, fun h ↦ absurd h h1⟩
      obtain ⟨q, hq⟩ := C.exists_pos h1
      have hbd := eq_bd_of_not_mem hCubic C hne hq.symm
      refine ⟨q, ?_, ?_⟩
      · rw [mem_spokes]
        change K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2) ∉ C.vertices
        rw [← hbd]
        exact h0
      · rw [← hbd]

theorem bd_eq_cases {q q' : C.tour.Pos} (h : (bd hCubic C q').1 = (bd hCubic C q).1) :
    q' = q ∨ (other hCubic C q ∈ C.vertices ∧ q' = pos C (posOf C (other hCubic C q))) := by
  have e1 := bd_endpoint hCubic C q
  have e2 := bd_endpoint hCubic C q'
  rw [h] at e2
  rcases fin2_eq_or_rev (bd hCubic C q).2 (bd hCubic C q').2 with hk | hk
  · left
    rw [hk, e1] at e2
    exact C.vertexAt_injective e2.symm
  · right
    rw [hk] at e2
    have hw : other hCubic C q = C.tour.vertexAt q' := e2
    refine ⟨hw ▸ C.vertexAt_mem_vertices q', ?_⟩
    rw [hw, posOf_vertexAt, pos_of_val]

section Build

variable (h3 : (K.dangling C.vertices).card = 3) (h0 : (0 : C.tour.Pos) ∈ spokes hCubic C)

/-- The indices of the spoke positions other than `0`. -/
noncomputable def spokeVals : Finset ℕ := ((spokes hCubic C).erase 0).image Fin.val

include h3 h0 in
theorem card_spokeVals : (spokeVals hCubic C).card = 2 := by
  unfold spokeVals
  rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_erase_of_mem h0,
    card_spokes, h3]

include h3 h0 in
theorem spokeVals_nonempty : (spokeVals hCubic C).Nonempty := by
  rw [← Finset.card_pos, card_spokeVals hCubic C h3 h0]
  omega

/-- The second spoke index. -/
noncomputable def s₂' : ℕ := (spokeVals hCubic C).min' (spokeVals_nonempty hCubic C h3 h0)

/-- The third spoke index. -/
noncomputable def s₁' : ℕ := (spokeVals hCubic C).max' (spokeVals_nonempty hCubic C h3 h0)

theorem mem_spokeVals {p : ℕ} :
    p ∈ spokeVals hCubic C ↔ ∃ q ∈ spokes hCubic C, q ≠ 0 ∧ q.val = p := by
  unfold spokeVals
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Finset.mem_erase] at hq
    exact ⟨q, hq.2, hq.1, rfl⟩
  · rintro ⟨q, hq, hq0, rfl⟩
    exact ⟨q, Finset.mem_erase.mpr ⟨hq0, hq⟩, rfl⟩

theorem s₂'_lt_s₁' : s₂' hCubic C h3 h0 < s₁' hCubic C h3 h0 :=
  Finset.min'_lt_max'_of_card _ (by rw [card_spokeVals hCubic C h3 h0]; omega)

theorem spokeVals_eq : spokeVals hCubic C = {s₂' hCubic C h3 h0, s₁' hCubic C h3 h0} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [card_spokeVals hCubic C h3 h0, Finset.card_pair (s₂'_lt_s₁' hCubic C h3 h0).ne]

theorem mem_spokes_iff (q : C.tour.Pos) :
    q ∈ spokes hCubic C ↔ q = 0 ∨ q.val = s₂' hCubic C h3 h0 ∨ q.val = s₁' hCubic C h3 h0 := by
  constructor
  · intro hq
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · right
      have : q.val ∈ spokeVals hCubic C := (mem_spokeVals hCubic C).mpr ⟨q, hq, hq0, rfl⟩
      rw [spokeVals_eq hCubic C h3 h0, Finset.mem_insert, Finset.mem_singleton] at this
      exact this
  · rintro (rfl | h | h)
    · exact h0
    · have : q.val ∈ spokeVals hCubic C := by
        rw [spokeVals_eq hCubic C h3 h0, h]
        exact Finset.mem_insert_self _ _
      obtain ⟨q', hq', -, hqq'⟩ := (mem_spokeVals hCubic C).mp this
      rwa [← Fin.val_injective hqq']
    · have : q.val ∈ spokeVals hCubic C := by
        rw [spokeVals_eq hCubic C h3 h0, h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      obtain ⟨q', hq', -, hqq'⟩ := (mem_spokeVals hCubic C).mp this
      rwa [← Fin.val_injective hqq']

theorem s₂'_pos : 0 < s₂' hCubic C h3 h0 := by
  have : s₂' hCubic C h3 h0 ∈ spokeVals hCubic C := Finset.min'_mem _ _
  obtain ⟨q, -, hq0, hqv⟩ := (mem_spokeVals hCubic C).mp this
  rw [← hqv]
  exact Nat.pos_of_ne_zero (fun h ↦ hq0 (Fin.ext h))

theorem s₁'_lt : s₁' hCubic C h3 h0 < N C := by
  have : s₁' hCubic C h3 h0 ∈ spokeVals hCubic C := Finset.max'_mem _ _
  obtain ⟨q, -, -, hqv⟩ := (mem_spokeVals hCubic C).mp this
  rw [← hqv]
  exact q.isLt

/-- The other end of the `S`-edge at a non-spoke position lies on the circuit. -/
theorem other_mem_of_inner {p : ℕ} (hp0 : 0 < p) (hpn : p < N C) (hp2 : p ≠ s₂' hCubic C h3 h0)
    (hp1 : p ≠ s₁' hCubic C h3 h0) : other hCubic C (pos C p) ∈ C.vertices := by
  by_contra h
  have hmem : pos C p ∈ spokes hCubic C := (mem_spokes hCubic C).mpr h
  rw [mem_spokes_iff hCubic C h3 h0, pos_val C hpn] at hmem
  rcases hmem with hmem | hmem | hmem
  · have := congrArg Fin.val hmem
    rw [pos_val C hpn, Fin.val_zero] at this
    omega
  · exact hp2 hmem
  · exact hp1 hmem

theorem inner_of_not_spoke {q : C.tour.Pos} (hq : q ∉ spokes hCubic C) :
    0 < q.val ∧ q.val ≠ s₂' hCubic C h3 h0 ∧ q.val ≠ s₁' hCubic C h3 h0 := by
  rw [mem_spokes_iff hCubic C h3 h0] at hq
  refine ⟨?_, fun h ↦ hq (Or.inr (Or.inl h)), fun h ↦ hq (Or.inr (Or.inr h))⟩
  exact Nat.pos_of_ne_zero (fun h ↦ hq (Or.inl (Fin.ext h)))

include hloopless in
/-- The abstract pole of the traversed circuit. -/
noncomputable def pole : Pole where
  n := N C
  s₂ := s₂' hCubic C h3 h0
  s₁ := s₁' hCubic C h3 h0
  μ := fun p ↦ posOf C (other hCubic C (pos C p))
  s₂_pos := s₂'_pos hCubic C h3 h0
  s₂_lt_s₁ := s₂'_lt_s₁' hCubic C h3 h0
  s₁_lt_n := s₁'_lt hCubic C h3 h0
  μ_inner := by
    intro p hp0 hpn hp2 hp1
    have hw := other_mem_of_inner hCubic C h3 h0 hp0 hpn hp2 hp1
    have hlt := posOf_lt C hw
    have hoo := other_other hCubic C hw
    have hns : pos C (posOf C (other hCubic C (pos C p))) ∉ spokes hCubic C := by
      rw [mem_spokes, hoo, not_not]
      exact C.vertexAt_mem_vertices _
    have := inner_of_not_spoke hCubic C h3 h0 hns
    rw [pos_val C hlt] at this
    exact ⟨this.1, hlt, this.2.1, this.2.2⟩
  μ_μ := by
    intro p hp0 hpn hp2 hp1
    have hw := other_mem_of_inner hCubic C h3 h0 hp0 hpn hp2 hp1
    show posOf C (other hCubic C (pos C (posOf C (other hCubic C (pos C p))))) = p
    rw [other_other hCubic C hw, posOf_vertexAt, pos_val C hpn]
  μ_ne := by
    intro p hp0 hpn hp2 hp1 h
    have hw := other_mem_of_inner hCubic C h3 h0 hp0 hpn hp2 hp1
    apply other_ne hCubic hloopless C (pos C p)
    have := vertexAt_pos_posOf C hw
    rw [← this]
    change posOf C (other hCubic C (pos C p)) = p at h
    rw [h]

theorem pole_n : (pole hCubic hloopless C h3 h0).n = N C := rfl

theorem pole_μ (p : ℕ) : (pole hCubic hloopless C h3 h0).μ p = posOf C (other hCubic C (pos C p)) := rfl

theorem pole_prev_val (q : C.tour.Pos) :
    (C.tour.prev q).val = (pole hCubic hloopless C h3 h0).prev q.val := by
  rw [EulerTour.prev_eq_sub_one, Fin.coe_sub_one]
  change _ = if q.val = 0 then C.tour.n + 1 - 1 else q.val - 1
  by_cases h : q = 0
  · have h' : q.val = 0 := by rw [h]; rfl
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ q.val = 0 := fun h' ↦ h (Fin.ext (by rw [h']; rfl))
    rw [if_neg h, if_neg h']

theorem pole_spoke_iff (q : C.tour.Pos) :
    (pole hCubic hloopless C h3 h0).Spoke q.val ↔ q ∈ spokes hCubic C := by
  rw [mem_spokes_iff hCubic C h3 h0]
  change (q.val = 0 ∨ q.val = s₂' hCubic C h3 h0 ∨ q.val = s₁' hCubic C h3 h0) ↔ _
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem pole_inner_of_not_spoke {q : C.tour.Pos} (hq : q ∉ spokes hCubic C) :
    (pole hCubic hloopless C h3 h0).Inner q.val := by
  have := inner_of_not_spoke hCubic C h3 h0 hq
  exact ⟨this.1, q.isLt, this.2.1, this.2.2⟩

section Cover

variable (Cv : (pole hCubic hloopless C h3 h0).Cover)

open Classical in
/-- The three pole matchings from a cover of the abstract pole. -/
noncomputable def L (i : Fin 3) : Finset E := Finset.univ.filter fun e ↦
  (∃ p, p < N C ∧ (C.tour.edge (pos C p)).1 = e ∧ i ∈ Cv.lab p) ∨
    (∃ p, p < N C ∧ (bd hCubic C (pos C p)).1 = e ∧ i ∈ Cv.clab p)

open Classical in
theorem mem_L {i : Fin 3} {e : E} : e ∈ L hCubic hloopless C h3 h0 Cv i ↔
    (∃ p, p < N C ∧ (C.tour.edge (pos C p)).1 = e ∧ i ∈ Cv.lab p) ∨
      (∃ p, p < N C ∧ (bd hCubic C (pos C p)).1 = e ∧ i ∈ Cv.clab p) := by
  unfold L
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem edge_mem_L (q : C.tour.Pos) (i : Fin 3) :
    (C.tour.edge q).1 ∈ L hCubic hloopless C h3 h0 Cv i ↔ i ∈ Cv.lab q.val := by
  rw [mem_L]
  constructor
  · rintro (⟨p, hp, he, hi⟩ | ⟨p, hp, he, hi⟩)
    · have : pos C p = q := C.tour.edge.injective (Subtype.ext he)
      rw [← this, pos_val C hp]
      exact hi
    · exact absurd (he ▸ (C.tour.edge q).2) (bd_not_mem hCubic C (pos C p))
  · intro hi
    exact Or.inl ⟨q.val, q.isLt, by rw [pos_of_val], hi⟩

theorem bd_mem_L (q : C.tour.Pos) (i : Fin 3) :
    (bd hCubic C q).1 ∈ L hCubic hloopless C h3 h0 Cv i ↔ i ∈ Cv.clab q.val := by
  rw [mem_L]
  constructor
  · rintro (⟨p, hp, he, hi⟩ | ⟨p, hp, he, hi⟩)
    · exact absurd (he ▸ (C.tour.edge (pos C p)).2) (bd_not_mem hCubic C q)
    · rcases bd_eq_cases hCubic C he with h | ⟨hw, h⟩
      · rw [← h, pos_val C hp]
        exact hi
      · have hns : q ∉ spokes hCubic C := by
          rw [mem_spokes, not_not]
          exact hw
        have hinner := pole_inner_of_not_spoke hCubic hloopless C h3 h0 hns
        have hchord := Cv.chord q.val hinner
        rw [pole_μ, pos_of_val] at hchord
        have hp' : p = posOf C (other hCubic C q) := by
          have := congrArg Fin.val h
          rwa [pos_val C hp, pos_val C (posOf_lt C hw)] at this
        rw [← hchord, ← hp']
        exact hi
  · intro hi
    exact Or.inr ⟨q.val, q.isLt, by rw [pos_of_val], hi⟩

theorem L_subset_meets (i : Fin 3) : L hCubic hloopless C h3 h0 Cv i ⊆ K.meets C.vertices := by
  intro e he
  rw [mem_L] at he
  rw [mem_meets]
  rcases he with ⟨p, -, he, -⟩ | ⟨p, -, he, -⟩
  · exact ⟨0, he ▸ endAt_mem_of_mem C (C.tour.edge (pos C p)).2 0⟩
  · exact ⟨(bd hCubic C (pos C p)).2, by rw [← he, bd_endpoint]; exact C.vertexAt_mem_vertices _⟩

/-- Exactly one of the three labels at a position contains a given colour. -/
theorem count_one {P : Pole} (Cv : P.Cover) {p : ℕ} (hp : p < P.n) (i : Fin 3) :
    (if i ∈ Cv.lab p then 1 else 0) +
      ((if i ∈ Cv.lab (P.prev p) then 1 else 0) + (if i ∈ Cv.clab p then 1 else 0)) = 1 := by
  have h1 := Finset.disjoint_left.mp (Cv.disj₁ p hp)
  have h2 := Finset.disjoint_left.mp (Cv.disj₂ p hp)
  have h3 := Finset.disjoint_left.mp (Cv.disj₃ p hp)
  have hu : i ∈ Cv.lab (P.prev p) ∪ Cv.lab p ∪ Cv.clab p := by
    rw [Cv.union p hp]
    exact Finset.mem_univ _
  rw [Finset.mem_union, Finset.mem_union] at hu
  by_cases ha : i ∈ Cv.lab p <;> by_cases hb : i ∈ Cv.lab (P.prev p) <;>
    by_cases hc : i ∈ Cv.clab p <;> simp only [ha, hb, hc, if_true, if_false] <;>
    first
    | rfl
    | exact absurd ha (h1 hb)
    | exact absurd hc (h2 hb)
    | exact absurd hc (h3 ha)
    | (exfalso; tauto)

include hS hCS in
/-- The transferred proper four-cover. -/
noncomputable def properFourCover : K.ProperFourCover S C.vertices where
  L := L hCubic hloopless C h3 h0 Cv
  matching := by
    intro i
    refine ⟨L_subset_meets hCubic hloopless C h3 h0 Cv i, ?_⟩
    intro v hv
    obtain ⟨q, rfl⟩ := C.exists_pos hv
    rw [TwoCircuitFactor.degreeIn_at_position hCubic C]
    have hb := bd_mem_L hCubic hloopless C h3 h0 Cv q i
    unfold bd at hb
    simp only [edge_mem_L hCubic hloopless C h3 h0 Cv, hb, pole_prev_val hCubic hloopless C h3 h0]
    exact count_one Cv q.isLt i
  cover := by
    intro e he
    obtain ⟨k, hk⟩ := mem_meets.mp he
    by_cases hce : e ∈ C.edges
    · right
      set q := C.tour.edge.symm ⟨e, hce⟩ with hq
      have he' : (C.tour.edge q).1 = e := by rw [hq, Equiv.apply_symm_apply]
      obtain ⟨i, hi⟩ := Cv.nonempty q.val q.isLt
      refine ⟨i, ?_⟩
      rw [← he', edge_mem_L]
      exact hi
    · left
      obtain ⟨q, hq⟩ := C.exists_pos hk
      have := eq_bd_of_not_mem hCubic C hce hq.symm
      have hS' := bd_mem_S hCubic hS C hCS q
      rw [← this] at hS'
      exact hS'
  dangling_once := by
    intro e he
    have hd := mem_dangling.mp he
    have hne : e ∉ C.edges :=
      fun h ↦ hd ⟨fun _ ↦ endAt_mem_of_mem C h 1, fun _ ↦ endAt_mem_of_mem C h 0⟩
    -- the circuit end of `e`
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, K.endAt e k ∈ C.vertices := by
      by_cases h0' : K.endAt e 0 ∈ C.vertices
      · exact ⟨0, h0'⟩
      · refine ⟨1, ?_⟩
        by_contra h1
        exact hd ⟨fun h ↦ absurd h h0', fun h ↦ absurd h h1⟩
    obtain ⟨q, hq⟩ := C.exists_pos hk
    have hbd := eq_bd_of_not_mem hCubic C hne hq.symm
    have hspoke : q ∈ spokes hCubic C := by
      rw [mem_spokes]
      change K.endAt (bd hCubic C q).1 (Fin.rev (bd hCubic C q).2) ∉ C.vertices
      rw [← hbd]
      intro hrev
      apply hd
      rcases fin2_cases k with rfl | rfl
      · exact ⟨fun _ ↦ hrev, fun _ ↦ hk⟩
      · exact ⟨fun _ ↦ hk, fun _ ↦ hrev⟩
    have hcard := Cv.spoke q.val ((pole_spoke_iff hCubic hloopless C h3 h0 q).mpr hspoke)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have he' : e = (bd hCubic C q).1 := congrArg Prod.fst hbd
    refine ⟨i, ?_, ?_⟩
    · rw [he', bd_mem_L, hi]
      exact Finset.mem_singleton_self _
    · intro j hj
      rw [he', bd_mem_L, hi, Finset.mem_singleton] at hj
      exact hj

end Cover

end Build

end PoleTransfer

open PoleTransfer in
/-- Theorem 3.1 of Karabáš–Máčajová in ambient form: every Hamiltonian cubic `3`-pole has a
proper four-cover. -/
theorem kmThreePole : KMThreePole.{u, v} := by
  intro V' E' _ _ _ _ K hCubic hloopless S hS R hRS h3
  let C₀ : K.TraversedCircuit := R.toTraversedCircuit
  have hC₀ : C₀.edges = R.edges := rfl
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (by rw [h3]; exact Nat.succ_pos 2)
  have hd' := mem_dangling.mp hd
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, K.endAt d k ∈ K.edgeSupport R.edges := by
    by_cases h0' : K.endAt d 0 ∈ K.edgeSupport R.edges
    · exact ⟨0, h0'⟩
    · refine ⟨1, ?_⟩
      by_contra h1
      exact hd' ⟨fun h ↦ absurd h h0', fun h ↦ absurd h h1⟩
  have hkC : K.endAt d k ∈ C₀.vertices := hk
  let C : K.TraversedCircuit := C₀.rotateTo hkC
  have hCe : C.edges = R.edges := rfl
  have hCv : C.vertices = K.edgeSupport R.edges := rfl
  have hCS : Disjoint C.edges S := hRS
  have h3' : (K.dangling C.vertices).card = 3 := h3
  have hne : d ∉ C.edges := fun h ↦ hd' ⟨fun _ ↦ endAt_mem_of_mem C h 1, fun _ ↦ endAt_mem_of_mem C h 0⟩
  have hv0 : C.tour.vertexAt 0 = K.endAt d k := C₀.rotateTo_vertexAt_zero hkC
  have hbd := eq_bd_of_not_mem hCubic C hne hv0.symm
  have h0 : (0 : C.tour.Pos) ∈ spokes hCubic C := by
    rw [mem_spokes]
    change K.endAt (bd hCubic C 0).1 (Fin.rev (bd hCubic C 0).2) ∉ C.vertices
    rw [← hbd]
    intro hrev
    apply hd'
    rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
    · exact ⟨fun _ ↦ hrev, fun _ ↦ hk⟩
    · exact ⟨fun _ ↦ hk, fun _ ↦ hrev⟩
  obtain ⟨Cv⟩ := Pole.exists_cover' (pole hCubic hloopless C h3' h0)
  exact ⟨properFourCover hCubic hloopless hS C hCS h3' h0 Cv⟩

end LoopMultigraph
end GraphPuzzles
