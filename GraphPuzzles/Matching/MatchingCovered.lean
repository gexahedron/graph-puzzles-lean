import GraphPuzzles.Poles.ThreePole
import GraphPuzzles.Graph.Bridgeless
import GraphPuzzles.Graph.Connectivity

/-!
# Matching-covered graphs, contractions, and separating cuts

The matching-theoretic notions used by the note's Section 3, in the endpoint-multigraph model.
Connectivity and bridgelessness are expressed through two-colourings of the vertices: a graph is
connected when every colouring constant along edges is constant, and an edge is not a bridge when
its ends receive the same colour under every colouring constant along the other edges.  The
contraction `G / (V ∖ X)` is realized on the vertex type `Option X`, the new vertex `none` standing
for the contracted complement; edges inside the complement disappear, and an edge with one end in
`X` becomes an edge to `none`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

section Defs

variable (H : LoopMultigraph V E)

/-- A perfect matching of the subgraph induced by `S`: edges inside `S` covering every vertex of
`S` exactly once. -/
def IsPerfectMatchingOn (S : Finset V) (P : Finset E) : Prop :=
  (∀ e ∈ P, ∀ k, H.endAt e k ∈ S) ∧ ∀ w ∈ S, H.degreeIn P w = 1

/-- The subgraph induced by `S` is factor-critical: deleting any one vertex of `S` leaves a
perfect matching. -/
def IsFactorCritical (S : Finset V) : Prop :=
  ∀ w ∈ S, ∃ P, H.IsPerfectMatchingOn (S.erase w) P

/-- Matching covered: connected, and every edge lies in a perfect matching. -/
def IsMatchingCovered : Prop :=
  H.IsConnected ∧ ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M

/-- The contraction of the complement of `X` to the single vertex `none`.  Its edges are the
edges meeting `X`; an end outside `X` is sent to `none`. -/
def contract (X : Finset V) : LoopMultigraph (Option {v // v ∈ X}) {e // e ∈ H.meets X} :=
  ⟨fun e k ↦ if h : H.endAt e.1 k ∈ X then some ⟨_, h⟩ else none⟩

/-- A cut `δ(X)` is separating when both contractions of a shore are matching covered. -/
def IsSeparatingCut (X : Finset V) : Prop :=
  (H.contract X).IsMatchingCovered ∧ (H.contract (Finset.univ \ X)).IsMatchingCovered

omit H in
/-- A cut is nontrivial when neither shore is a single vertex. -/
def IsNontrivialCut (X : Finset V) : Prop :=
  2 ≤ X.card ∧ 2 ≤ (Finset.univ \ X).card

/-- **The Campos–Lucchesi conclusion for `H`**, taken as a hypothesis: every nontrivial separating
cut is met by some perfect matching in exactly three edges.  Campos and Lucchesi prove this for
every simple brick other than the Petersen graph, and the note's Lemma (brick), citing
Kothari–Carvalho–Lucchesi–Little, shows that every proper snark is a simple brick. The brick
reduction is proved in `Brick`; the Campos–Lucchesi theorem is proved in `CamposLucchesi`. -/
def CamposLucchesiFor : Prop :=
  ∀ X : Finset V, H.IsSeparatingCut X → IsNontrivialCut X →
    ∃ N, H.IsPerfectMatching N ∧ (N ∩ H.dangling X).card = 3

end Defs

section Contract

variable {H : LoopMultigraph V E} (X : Finset V)

omit [DecidableEq E] in
theorem contract_endAt (e : {e // e ∈ H.meets X}) (k : Fin 2) :
    (H.contract X).endAt e k = if h : H.endAt e.1 k ∈ X then some ⟨_, h⟩ else none := rfl

omit [DecidableEq E] in
theorem contract_endAt_eq_some_iff (e : {e // e ∈ H.meets X}) (k : Fin 2) (v : {v // v ∈ X}) :
    (H.contract X).endAt e k = some v ↔ H.endAt e.1 k = v.1 := by
  rw [contract_endAt]
  split_ifs with h
  · constructor
    · intro h'
      exact congrArg Subtype.val (Option.some_injective _ h')
    · intro h'
      congr 1
      exact Subtype.ext h'
  · constructor
    · intro h'
      cases h'
    · intro h'
      exact absurd (h' ▸ v.2) h

omit [DecidableEq E] in
theorem contract_endAt_eq_none_iff (e : {e // e ∈ H.meets X}) (k : Fin 2) :
    (H.contract X).endAt e k = none ↔ H.endAt e.1 k ∉ X := by
  rw [contract_endAt]
  split_ifs with h
  · exact iff_of_false (by simp) (fun h' ↦ h' h)
  · exact iff_of_true rfl h

/-- Half-edges of the contraction at a vertex of `X` correspond to half-edges of `H`. -/
def contractHalfEdgeEquiv (v : {v // v ∈ X}) :
    (H.contract X).halfEdgesAt (some v) ≃ H.halfEdgesAt v.1 where
  toFun h := ⟨(h.1.1.1, h.1.2), (contract_endAt_eq_some_iff X h.1.1 h.1.2 v).mp h.2⟩
  invFun h := ⟨(⟨h.1.1, mem_meets.mpr ⟨h.1.2, by
      rw [show H.endAt h.1.1 h.1.2 = v.1 from h.2]
      exact v.2⟩⟩, h.1.2),
    (contract_endAt_eq_some_iff X _ h.1.2 v).mpr h.2⟩
  left_inv h := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext rfl
    · rfl
  right_inv h := by
    apply Subtype.ext
    rfl

omit [DecidableEq E] in
theorem contract_degree_some (v : {v // v ∈ X}) :
    (H.contract X).degree (some v) = H.degree v.1 :=
  Fintype.card_congr (contractHalfEdgeEquiv X v)

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

/-- The contracted vertex has degree the number of dangling edges of `X`. -/
theorem contract_degree_none : (H.contract X).degree none = (H.dangling X).card := by
  rw [← degreeIn_univ']
  unfold degreeIn
  rw [Finset.card_filter, Finset.sum_product]
  have h1 : ∀ e : {e // e ∈ H.meets X},
      (∑ k : Fin 2, if (H.contract X).endAt e k = none then 1 else 0) =
        if e.1 ∈ H.dangling X then 1 else 0 := by
    intro e
    rw [Fin.sum_univ_two]
    have hc := (mem_dangling (K := H) (X := X) (e := e.1))
    have hn0 := contract_endAt_eq_none_iff X e 0
    have hn1 := contract_endAt_eq_none_iff X e 1
    obtain ⟨k, hk⟩ := mem_meets.mp e.2
    rcases Classical.em (H.endAt e.1 0 ∈ X) with h0 | h0 <;>
      rcases Classical.em (H.endAt e.1 1 ∈ X) with h1 | h1
    · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩), if_neg (fun h ↦ (hn0.mp h) h0),
        if_neg (fun h ↦ (hn1.mp h) h1)]
    · rw [if_pos (hc.mpr fun h ↦ h1 (h.mp h0)), if_neg (fun h ↦ (hn0.mp h) h0),
        if_pos (hn1.mpr h1)]
    · rw [if_pos (hc.mpr fun h ↦ h0 (h.mpr h1)), if_pos (hn0.mpr h0),
        if_neg (fun h ↦ (hn1.mp h) h1)]
    · exfalso
      rcases fin2_cases k with rfl | rfl
      · exact h0 hk
      · exact h1 hk
  rw [Finset.sum_congr rfl (fun e _ ↦ h1 e)]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun e : {e // e ∈ H.meets X} ↦ e.1 ∈ H.dangling X).card =
      (H.dangling X).card := by
    apply Finset.card_bij (fun e _ ↦ e.1)
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e _ e' _ h
      exact Subtype.ext h
    · intro e he
      refine ⟨⟨e, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
      rw [mem_dangling] at he
      rw [mem_meets]
      by_contra hcon
      push Not at hcon
      exact he ⟨fun h ↦ absurd h (hcon 0), fun h ↦ absurd h (hcon 1)⟩
  rw [this]
  rfl

omit [DecidableEq E] in
/-- The contraction of a loopless graph is loopless. -/
theorem contract_loopless (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (e : {e // e ∈ H.meets X}) :
    (H.contract X).endAt e 0 ≠ (H.contract X).endAt e 1 := by
  intro h
  rw [contract_endAt, contract_endAt] at h
  split_ifs at h with h0 h1 h1
  · exact hloopless e.1 (congrArg Subtype.val (Option.some_injective _ h))
  · obtain ⟨k, hk⟩ := mem_meets.mp e.2
    rcases fin2_cases k with rfl | rfl
    · exact h0 hk
    · exact h1 hk

end Contract

end LoopMultigraph
end GraphPuzzles
