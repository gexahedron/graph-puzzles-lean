import GraphPuzzles.DefectThree.HexagonDisjointFive
import GraphPuzzles.Core.FiniteCounts
import Mathlib.Tactic.DeriveFintype

/-!
# Oriented cycle double covers and the ordered-pair criterion

An oriented `k`-cycle double cover is a family of `k` directed even subgraphs such that every
edge lies in exactly two members and is traversed in opposite directions by them.  The
defect-three note reduces the construction of such covers to a local criterion: give every edge
a reference direction and an ordered pair of labels `p → q`; if at every vertex the outward
ordered pairs of the incident edges use every label equally often as a tail and as a head, the
label classes form an oriented cycle double cover.

This module defines directed cycles and oriented covers in the endpoint-multigraph model, proves
the ordered-pair criterion, and records the sign-word table of the note together with the finite
balance checks behind its two vertex cases.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A directed even subgraph: an edge set with a tail end for every edge, such that at every
vertex as many chosen edges leave as enter. -/
structure DirectedCycle (G : LoopMultigraph V E) where
  edges : Finset E
  tail : E → Fin 2
  balanced : ∀ w,
    (Finset.univ.filter fun x : G.halfEdgesAt w ↦ x.1.1 ∈ edges ∧ x.1.2 = tail x.1.1).card =
      (Finset.univ.filter fun x : G.halfEdgesAt w ↦ x.1.1 ∈ edges ∧ x.1.2 ≠ tail x.1.1).card

/-- An oriented `k`-cycle double cover: every edge lies in exactly two members, which traverse it
in opposite directions. -/
structure OrientedCycleDoubleCover (G : LoopMultigraph V E) (k : ℕ) where
  cycles : Fin k → G.DirectedCycle
  coveredTwice : ∀ e : E, (Finset.univ.filter fun i ↦ e ∈ (cycles i).edges).card = 2
  opposite : ∀ e i j, i ≠ j → e ∈ (cycles i).edges → e ∈ (cycles j).edges →
    (cycles i).tail e ≠ (cycles j).tail e

/-- An oriented cover contains an edge set when one of its members is exactly that set. -/
def OrientedCycleDoubleCover.Contains {G : LoopMultigraph V E} {k : ℕ}
    (D : G.OrientedCycleDoubleCover k) (F : Finset E) : Prop :=
  ∃ i, (D.cycles i).edges = F

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin2_ne_iff_rev {a b : Fin 2} : a ≠ b ↔ a = Fin.rev b := by
  revert a b
  decide

section Criterion

variable (G : LoopMultigraph V E) (ref : E → Fin 2) (p q : E → Fin 5)

/-- The outward tail label of a half-edge: `p` if the reference direction leaves the vertex
along it, `q` otherwise. -/
def otail (x : HalfEdge E) : Fin 5 := if x.2 = ref x.1 then p x.1 else q x.1

/-- The outward head label of a half-edge. -/
def ohead (x : HalfEdge E) : Fin 5 := if x.2 = ref x.1 then q x.1 else p x.1

omit [Fintype E] [DecidableEq E] in
/-- Membership and direction in the label class `r`, in terms of the outward labels. -/
theorem labelClass_out (r : Fin 5) (hpq : ∀ e, p e ≠ q e) (x : HalfEdge E) :
    ((p x.1 = r ∨ q x.1 = r) ∧ x.2 = (if p x.1 = r then ref x.1 else Fin.rev (ref x.1))) ↔
      otail ref p q x = r := by
  unfold otail
  have hne : ref x.1 ≠ Fin.rev (ref x.1) := by
    rcases fin2_cases (ref x.1) with h | h <;> rw [h] <;> decide
  by_cases hp : p x.1 = r
  · rw [if_pos hp]
    by_cases hk : x.2 = ref x.1
    · rw [if_pos hk]
      exact iff_of_true ⟨Or.inl hp, hk⟩ hp
    · rw [if_neg hk]
      exact iff_of_false (fun h ↦ hk h.2) (fun h ↦ hpq x.1 (hp.trans h.symm))
  · rw [if_neg hp]
    by_cases hk : x.2 = ref x.1
    · rw [if_pos hk]
      exact iff_of_false (fun h ↦ hne (hk.symm.trans h.2)) hp
    · rw [if_neg hk]
      exact ⟨fun h ↦ h.1.resolve_left hp, fun h ↦ ⟨Or.inr h, fin2_ne_iff_rev.mp hk⟩⟩

omit [Fintype E] [DecidableEq E] in
theorem labelClass_in (r : Fin 5) (hpq : ∀ e, p e ≠ q e) (x : HalfEdge E) :
    ((p x.1 = r ∨ q x.1 = r) ∧ x.2 ≠ (if p x.1 = r then ref x.1 else Fin.rev (ref x.1))) ↔
      ohead ref p q x = r := by
  unfold ohead
  have hne : ref x.1 ≠ Fin.rev (ref x.1) := by
    rcases fin2_cases (ref x.1) with h | h <;> rw [h] <;> decide
  by_cases hp : p x.1 = r
  · rw [if_pos hp]
    by_cases hk : x.2 = ref x.1
    · rw [if_pos hk]
      exact iff_of_false (fun h ↦ h.2 hk) (fun h ↦ hpq x.1 (hp.trans h.symm))
    · rw [if_neg hk]
      exact iff_of_true ⟨Or.inl hp, hk⟩ hp
  · rw [if_neg hp]
    by_cases hk : x.2 = ref x.1
    · rw [if_pos hk]
      exact ⟨fun h ↦ h.1.resolve_left hp,
        fun h ↦ ⟨Or.inr h, fun h' ↦ hne (hk.symm.trans h')⟩⟩
    · rw [if_neg hk]
      exact iff_of_false (fun h ↦ h.2 (fin2_ne_iff_rev.mp hk)) hp

/-- The label class `r` with the direction induced by the labels. -/
def labelCycle (r : Fin 5) (hpq : ∀ e, p e ≠ q e)
    (hbal : ∀ w r, (Finset.univ.filter fun x : G.halfEdgesAt w ↦ otail ref p q x.1 = r).card =
      (Finset.univ.filter fun x : G.halfEdgesAt w ↦ ohead ref p q x.1 = r).card) :
    G.DirectedCycle where
  edges := Finset.univ.filter fun e ↦ p e = r ∨ q e = r
  tail e := if p e = r then ref e else Fin.rev (ref e)
  balanced w := by
    have h := hbal w r
    convert h using 2 <;> ext x <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · exact labelClass_out ref p q r hpq x.1
    · exact labelClass_in ref p q r hpq x.1

/-- **Ordered-pair criterion.**  Labels satisfying the local balance condition at every vertex
give an oriented five-cycle double cover whose member `r` is the class of edges labelled `r`. -/
theorem exists_orientedCover_of_labels (hpq : ∀ e, p e ≠ q e)
    (hbal : ∀ w r, (Finset.univ.filter fun x : G.halfEdgesAt w ↦ otail ref p q x.1 = r).card =
      (Finset.univ.filter fun x : G.halfEdgesAt w ↦ ohead ref p q x.1 = r).card) :
    ∃ D : G.OrientedCycleDoubleCover 5, ∀ r,
      (D.cycles r).edges = Finset.univ.filter fun e ↦ p e = r ∨ q e = r := by
  refine ⟨⟨fun r ↦ labelCycle G ref p q r hpq hbal, ?_, ?_⟩, fun r ↦ rfl⟩
  · intro e
    have hfilter : (Finset.univ.filter fun i ↦ e ∈ (labelCycle G ref p q i hpq hbal).edges) =
        {p e, q e} := by
      ext i
      simp only [labelCycle, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    rw [hfilter, Finset.card_pair (hpq e)]
  · intro e i j hij hi hj
    simp only [labelCycle, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hne : ref e ≠ Fin.rev (ref e) := by
      rcases fin2_cases (ref e) with h | h <;> rw [h] <;> decide
    change (if p e = i then ref e else Fin.rev (ref e)) ≠
      (if p e = j then ref e else Fin.rev (ref e))
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact absurd (hi.symm.trans hj) hij
    · rw [if_pos hi, if_neg (fun h ↦ hpq e (h.trans hj.symm))]
      exact hne
    · rw [if_neg (fun h ↦ hpq e (h.trans hi.symm)), if_pos hj]
      exact hne.symm
    · exact absurd (hi.symm.trans hj) hij

end Criterion

section Signs

/-- Signs of an orientation relative to a reference direction. -/
inductive Sgn
  | zero
  | pos
  | neg
  deriving DecidableEq, Fintype

namespace Sgn

/-- Reversal of a sign. -/
def flip : Sgn → Sgn
  | zero => zero
  | pos => neg
  | neg => pos

theorem flip_flip (s : Sgn) : s.flip.flip = s := by
  cases s <;> rfl

theorem flip_ne_zero {s : Sgn} (h : s ≠ zero) : s.flip ≠ zero := by
  cases s <;> simp_all [flip]

end Sgn

/-- The ordered-pair table of the defect-three note: a sign word gives a tail label and a head
label in `Fin 5` (the note's labels `1,…,5` are `0,…,4`).  Invalid words get a dummy value. -/
def signTable : Sgn → Sgn → Sgn → Fin 5 × Fin 5
  | .pos, .pos, .pos => (0, 4)
  | .pos, .neg, .neg => (1, 4)
  | .neg, .pos, .neg => (2, 4)
  | .neg, .neg, .pos => (3, 4)
  | .neg, .neg, .neg => (4, 0)
  | .neg, .pos, .pos => (4, 1)
  | .pos, .neg, .pos => (4, 2)
  | .pos, .pos, .neg => (4, 3)
  | .zero, .pos, .pos => (0, 1)
  | .zero, .pos, .neg => (2, 3)
  | .zero, .neg, .neg => (1, 0)
  | .zero, .neg, .pos => (3, 2)
  | .pos, .zero, .pos => (0, 2)
  | .pos, .zero, .neg => (1, 3)
  | .neg, .zero, .neg => (2, 0)
  | .neg, .zero, .pos => (3, 1)
  | .pos, .pos, .zero => (0, 3)
  | .pos, .neg, .zero => (1, 2)
  | .neg, .neg, .zero => (3, 0)
  | .neg, .pos, .zero => (2, 1)
  | _, _, _ => (0, 0)

/-- Valid sign words: all three nonzero (core edges), or exactly one zero (exterior edges). -/
def ValidWord (a b c : Sgn) : Prop :=
  (a ≠ .zero ∧ b ≠ .zero ∧ c ≠ .zero) ∨ (a = .zero ∧ b ≠ .zero ∧ c ≠ .zero) ∨
    (b = .zero ∧ a ≠ .zero ∧ c ≠ .zero) ∨ (c = .zero ∧ a ≠ .zero ∧ b ≠ .zero)

instance (a b c : Sgn) : Decidable (ValidWord a b c) := by
  unfold ValidWord
  infer_instance

theorem signTable_ne (a b c : Sgn) (h : ValidWord a b c) :
    (signTable a b c).1 ≠ (signTable a b c).2 := by
  revert a b c
  decide

theorem signTable_flip (a b c : Sgn) (h : ValidWord a b c) :
    signTable a.flip b.flip c.flip = ((signTable a b c).2, (signTable a b c).1) := by
  revert a b c
  decide

/-- Label `4` occurs exactly on the words with three nonzero signs. -/
theorem signTable_four_iff (a b c : Sgn) (h : ValidWord a b c) :
    ((signTable a b c).1 = 4 ∨ (signTable a b c).2 = 4) ↔
      (a ≠ .zero ∧ b ≠ .zero ∧ c ≠ .zero) := by
  revert a b c
  decide

/-- The balance count of three ordered pairs at a label. -/
def pairBalance (t₁ t₂ t₃ : Fin 5 × Fin 5) (r : Fin 5) : Prop :=
  ((if t₁.1 = r then 1 else 0) + ((if t₂.1 = r then 1 else 0) + (if t₃.1 = r then 1 else 0)) : ℕ) =
    (if t₁.2 = r then 1 else 0) + ((if t₂.2 = r then 1 else 0) + (if t₃.2 = r then 1 else 0))

instance (t₁ t₂ t₃ : Fin 5 × Fin 5) (r : Fin 5) : Decidable (pairBalance t₁ t₂ t₃ r) := by
  unfold pairBalance
  infer_instance

/-- **Balance at an exterior vertex.**  The three edges have the three colours; in each
coordinate the two edges carrying that orientation point oppositely. -/
theorem balance_exterior (s01 s02 s10 : Sgn) (h01 : s01 ≠ .zero) (h02 : s02 ≠ .zero)
    (h10 : s10 ≠ .zero) (r : Fin 5) :
    pairBalance (signTable .zero s01 s02) (signTable s10 .zero s02.flip)
      (signTable s10.flip s01.flip .zero) r := by
  revert s01 s02 s10 r
  decide

/-- Placing a sign at coordinate `a` and two signs at the other coordinates in order. -/
def wordAt (a : Fin 3) (za o₁ o₂ : Sgn) : Fin 3 → Sgn :=
  fun b ↦ if b = a then za else if b < a then o₁ else o₂

/-- A word as a function of coordinates, evaluated by the table. -/
def tableOf (w : Fin 3 → Sgn) : Fin 5 × Fin 5 := signTable (w 0) (w 1) (w 2)

/-- **Balance at a core vertex** whose spoke has colour `a`: the spoke word vanishes at `a`,
the two core edges point oppositely in orientation `a`, and in the other two orientations both
core edges point against the spoke. -/
theorem balance_core (a : Fin 3) (tb tc s : Sgn) (hb : tb ≠ .zero) (hc : tc ≠ .zero)
    (hs : s ≠ .zero) (r : Fin 5) :
    pairBalance (tableOf (wordAt a .zero tb tc)) (tableOf (wordAt a s tb.flip tc.flip))
      (tableOf (wordAt a s.flip tb.flip tc.flip)) r := by
  revert a tb tc s r
  decide

/-- **Balance at a core vertex**, in coordinate form: the spoke word `t` vanishes exactly at the
spoke colour `a`; the two core edges carry the word `t` flipped, with opposite signs `s`,
`s.flip` at coordinate `a`. -/
theorem balance_core' (a : Fin 3) (t : Fin 3 → Sgn) (s : Sgn) (ha : t a = .zero)
    (ht : ∀ b, b ≠ a → t b ≠ .zero) (hs : s ≠ .zero) (r : Fin 5) :
    pairBalance (tableOf t) (tableOf (Function.update (fun b ↦ (t b).flip) a s))
      (tableOf (Function.update (fun b ↦ (t b).flip) a s.flip)) r := by
  revert a t s r
  decide

end Signs

namespace Hexagon

variable {H : LoopMultigraph V E} (X : H.Hexagon) (g : X.ExteriorColoring)

/-- The edges carrying the `a`-th auxiliary orientation: the hexagon edges and the exterior
edges not of colour `a`. -/
def K (a : Fin 3) : Finset E :=
  Finset.univ.filter fun e ↦ (∃ i, e = X.h i) ∨ g.color e ≠ g.c a

omit [DecidableEq V] in
theorem h_mem_K (a : Fin 3) (i : Fin 6) : X.h i ∈ X.K g a := by
  simp [K]

omit [DecidableEq V] in
theorem mem_K_of_not_h {e : E} (he : ∀ i, e ≠ X.h i) (a : Fin 3) :
    e ∈ X.K g a ↔ g.idx (g.color e) ≠ a := by
  simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, hi⟩ | h)
    · exact absurd hi (he i)
    · intro hidx
      exact h (by rw [← hidx, g.c_idx (g.nonzero e he)])
  · intro h
    refine Or.inr (fun hc ↦ h ?_)
    rw [hc, g.idx_c]

/-- Three auxiliary orientations with the local properties used by the note: each passes
through every exterior vertex; at a core vertex the two core edges are opposite in the
orientation of the spoke's colour, and in the other two orientations they agree with each other
and are opposite to the spoke. -/
structure Orientations where
  o : Fin 3 → E → Fin 2
  exterior : ∀ (a : Fin 3) (w : V), (∀ i, w ≠ X.v i) → ∀ x y : H.halfEdgesAt w, x ≠ y →
    x.1.1 ∈ X.K g a → y.1.1 ∈ X.K g a → (x.1.2 = o a x.1.1 ↔ ¬ (y.1.2 = o a y.1.1))
  core_own : ∀ i, (0 = o (hexWord (i + g.r)) (X.h i)) ↔ ¬ (1 = o (hexWord (i + g.r)) (X.h (i - 1)))
  core_other : ∀ i (b : Fin 3), b ≠ hexWord (i + g.r) →
    ((0 = o b (X.h i)) ↔ (1 = o b (X.h (i - 1)))) ∧
      ((X.side i = o b (X.spoke i)) ↔ ¬ (0 = o b (X.h i)))

namespace Orientations

variable {X g} (O : X.Orientations g)

/-- The sign of an edge in orientation `a` relative to the reference direction from end `0`. -/
def sgn (a : Fin 3) (e : E) : Sgn :=
  if e ∈ X.K g a then (if O.o a e = 0 then .pos else .neg) else .zero

/-- The outward sign of a half-edge in orientation `a`. -/
def osgn (a : Fin 3) (x : HalfEdge E) : Sgn :=
  if x.1 ∈ X.K g a then (if x.2 = O.o a x.1 then .pos else .neg) else .zero

omit [DecidableEq V] in
theorem osgn_eq (a : Fin 3) (x : HalfEdge E) :
    O.osgn a x = if x.2 = 0 then O.sgn a x.1 else (O.sgn a x.1).flip := by
  unfold osgn sgn
  by_cases hK : x.1 ∈ X.K g a
  · rw [if_pos hK, if_pos hK]
    rcases fin2_cases x.2 with hk | hk <;> rcases fin2_cases (O.o a x.1) with ho | ho <;>
      rw [hk, ho] <;> decide
  · rw [if_neg hK, if_neg hK]
    split_ifs <;> rfl

omit [DecidableEq V] in
theorem sgn_ne_zero_iff (a : Fin 3) (e : E) : O.sgn a e ≠ .zero ↔ e ∈ X.K g a := by
  unfold sgn
  by_cases hK : e ∈ X.K g a
  · rw [if_pos hK]
    split_ifs <;> simp [hK]
  · rw [if_neg hK]
    simp [hK]

omit [DecidableEq V] in
theorem osgn_ne_zero_iff (a : Fin 3) (x : HalfEdge E) : O.osgn a x ≠ .zero ↔ x.1 ∈ X.K g a := by
  unfold osgn
  by_cases hK : x.1 ∈ X.K g a
  · rw [if_pos hK]
    split_ifs <;> simp [hK]
  · rw [if_neg hK]
    simp [hK]

omit [DecidableEq V] in
theorem osgn_pos_iff (a : Fin 3) (x : HalfEdge E) (hK : x.1 ∈ X.K g a) :
    O.osgn a x = .pos ↔ x.2 = O.o a x.1 := by
  unfold osgn
  rw [if_pos hK]
  split_ifs with h <;> simp [h]

omit [DecidableEq V] in
/-- Two half-edges in `K a` with opposite directions have flipped outward signs. -/
theorem osgn_flip_of_opposite (a : Fin 3) (x y : HalfEdge E) (hx : x.1 ∈ X.K g a)
    (hy : y.1 ∈ X.K g a) (h : x.2 = O.o a x.1 ↔ ¬ (y.2 = O.o a y.1)) :
    O.osgn a y = (O.osgn a x).flip := by
  unfold osgn
  rw [if_pos hx, if_pos hy]
  by_cases hx' : x.2 = O.o a x.1
  · rw [if_pos hx', if_neg (h.mp hx')]
    rfl
  · rw [if_neg hx', if_pos (by
      by_contra hy'
      exact hx' (h.mpr hy'))]
    rfl

/-- The tail label of an edge. -/
def plab (e : E) : Fin 5 := (signTable (O.sgn 0 e) (O.sgn 1 e) (O.sgn 2 e)).1

/-- The head label of an edge. -/
def qlab (e : E) : Fin 5 := (signTable (O.sgn 0 e) (O.sgn 1 e) (O.sgn 2 e)).2

omit [DecidableEq V] in
theorem valid_word (e : E) : ValidWord (O.sgn 0 e) (O.sgn 1 e) (O.sgn 2 e) := by
  by_cases he : ∃ i, e = X.h i
  · obtain ⟨i, rfl⟩ := he
    exact Or.inl ⟨(O.sgn_ne_zero_iff 0 _).mpr (X.h_mem_K g 0 i),
      (O.sgn_ne_zero_iff 1 _).mpr (X.h_mem_K g 1 i), (O.sgn_ne_zero_iff 2 _).mpr (X.h_mem_K g 2 i)⟩
  · push Not at he
    have hK : ∀ a, e ∈ X.K g a ↔ g.idx (g.color e) ≠ a := fun a ↦ X.mem_K_of_not_h g he a
    have hz : ∀ a, O.sgn a e = .zero ↔ g.idx (g.color e) = a := by
      intro a
      rw [← not_not (a := O.sgn a e = .zero), ← ne_eq, O.sgn_ne_zero_iff, hK, not_not]
    have hnz : ∀ a, O.sgn a e ≠ .zero ↔ g.idx (g.color e) ≠ a := by
      intro a
      rw [O.sgn_ne_zero_iff, hK]
    unfold ValidWord
    rcases (show g.idx (g.color e) = 0 ∨ g.idx (g.color e) = 1 ∨ g.idx (g.color e) = 2 by
      generalize g.idx (g.color e) = a
      revert a
      decide) with h | h | h
    · exact Or.inr (Or.inl ⟨(hz 0).mpr h, (hnz 1).mpr (by rw [h]; decide),
        (hnz 2).mpr (by rw [h]; decide)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(hz 1).mpr h, (hnz 0).mpr (by rw [h]; decide),
        (hnz 2).mpr (by rw [h]; decide)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨(hz 2).mpr h, (hnz 0).mpr (by rw [h]; decide),
        (hnz 1).mpr (by rw [h]; decide)⟩))

omit [DecidableEq V] in
theorem plab_ne_qlab (e : E) : O.plab e ≠ O.qlab e :=
  signTable_ne _ _ _ (O.valid_word e)

omit [DecidableEq V] in
/-- The outward pair of a half-edge is the table value of its outward sign word. -/
theorem outward_pair (x : HalfEdge E) :
    (otail (fun _ ↦ 0) O.plab O.qlab x, ohead (fun _ ↦ 0) O.plab O.qlab x) =
      signTable (O.osgn 0 x) (O.osgn 1 x) (O.osgn 2 x) := by
  unfold otail ohead
  by_cases hk : x.2 = 0
  · simp only [hk, if_true, O.osgn_eq, plab, qlab]
  · simp only [hk, if_false, O.osgn_eq, plab, qlab, signTable_flip _ _ _ (O.valid_word x.1)]

omit [DecidableEq V] in
theorem outward_tail (x : HalfEdge E) :
    otail (fun _ ↦ 0) O.plab O.qlab x = (signTable (O.osgn 0 x) (O.osgn 1 x) (O.osgn 2 x)).1 :=
  congrArg Prod.fst (O.outward_pair x)

omit [DecidableEq V] in
theorem outward_head (x : HalfEdge E) :
    ohead (fun _ ↦ 0) O.plab O.qlab x = (signTable (O.osgn 0 x) (O.osgn 1 x) (O.osgn 2 x)).2 :=
  congrArg Prod.snd (O.outward_pair x)

/-- Balance at a cubic vertex with half-edges `y₁ y₂ y₃` reduces to the pair balance of their
outward sign words. -/
theorem balance_of_three {w : V} (y₁ y₂ y₃ : H.halfEdgesAt w) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃)
    (h23 : y₂ ≠ y₃) (hcases : ∀ x : H.halfEdgesAt w, x = y₁ ∨ x = y₂ ∨ x = y₃) (r : Fin 5)
    (hb : pairBalance (signTable (O.osgn 0 y₁.1) (O.osgn 1 y₁.1) (O.osgn 2 y₁.1))
      (signTable (O.osgn 0 y₂.1) (O.osgn 1 y₂.1) (O.osgn 2 y₂.1))
      (signTable (O.osgn 0 y₃.1) (O.osgn 1 y₃.1) (O.osgn 2 y₃.1)) r) :
    (Finset.univ.filter fun x : H.halfEdgesAt w ↦ otail (fun _ ↦ 0) O.plab O.qlab x.1 = r).card =
      (Finset.univ.filter fun x : H.halfEdgesAt w ↦ ohead (fun _ ↦ 0) O.plab O.qlab x.1 = r).card := by
  rw [card_filter_of_three y₁ y₂ y₃ h12 h13 h23 hcases, card_filter_of_three y₁ y₂ y₃ h12 h13 h23 hcases]
  simp only [O.outward_tail, O.outward_head]
  exact hb

/-- Balance at an exterior vertex. -/
theorem balance_exterior_vertex (hCubic : ∀ v : V, H.degree v = 3) {w : V} (hw : ∀ i, w ≠ X.v i)
    (r : Fin 5) :
    (Finset.univ.filter fun x : H.halfEdgesAt w ↦ otail (fun _ ↦ 0) O.plab O.qlab x.1 = r).card =
      (Finset.univ.filter fun x : H.halfEdgesAt w ↦ ohead (fun _ ↦ 0) O.plab O.qlab x.1 = r).card := by
  -- the colour bijection at `w`
  let φ : H.halfEdgesAt w → Fin 3 := fun x ↦ g.idx (g.color x.1.1)
  have hnoth : ∀ x : H.halfEdgesAt w, ∀ i, x.1.1 ≠ X.h i := fun x ↦
    ExteriorColoring.halfEdge_not_h hw x
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply g.injective_at w x y (hnoth x) (hnoth y)
    have := congrArg g.c hxy
    simp only [φ] at this
    rwa [g.c_idx (g.nonzero _ (hnoth x)), g.c_idx (g.nonzero _ (hnoth y))] at this
  have hcard : Fintype.card (H.halfEdgesAt w) = Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    exact hCubic w
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, hcard⟩
  obtain ⟨y₀, hy₀⟩ := hbij.2 0
  obtain ⟨y₁, hy₁⟩ := hbij.2 1
  obtain ⟨y₂, hy₂⟩ := hbij.2 2
  have hcases : ∀ x : H.halfEdgesAt w, x = y₀ ∨ x = y₁ ∨ x = y₂ := by
    intro x
    rcases (show φ x = 0 ∨ φ x = 1 ∨ φ x = 2 by
      generalize φ x = a
      revert a
      decide) with h | h | h
    · exact Or.inl (hφ (h.trans hy₀.symm))
    · exact Or.inr (Or.inl (hφ (h.trans hy₁.symm)))
    · exact Or.inr (Or.inr (hφ (h.trans hy₂.symm)))
  have h01 : y₀ ≠ y₁ := fun h ↦ by
    have := hy₀.symm.trans ((congrArg φ h).trans hy₁)
    exact absurd this (by decide)
  have h02 : y₀ ≠ y₂ := fun h ↦ by
    have := hy₀.symm.trans ((congrArg φ h).trans hy₂)
    exact absurd this (by decide)
  have h12 : y₁ ≠ y₂ := fun h ↦ by
    have := hy₁.symm.trans ((congrArg φ h).trans hy₂)
    exact absurd this (by decide)
  -- membership in the orientation classes
  have hK : ∀ (x : H.halfEdgesAt w) (a : Fin 3), x.1.1 ∈ X.K g a ↔ φ x ≠ a := fun x a ↦
    X.mem_K_of_not_h g (hnoth x) a
  have hz : ∀ (x : H.halfEdgesAt w) (a : Fin 3), φ x = a → O.osgn a x.1 = .zero := by
    intro x a h
    by_contra hne
    exact ((O.osgn_ne_zero_iff a x.1).mp hne |> (hK x a).mp) h
  have hnz : ∀ (x : H.halfEdgesAt w) (a : Fin 3), φ x ≠ a → O.osgn a x.1 ≠ .zero := by
    intro x a h
    exact (O.osgn_ne_zero_iff a x.1).mpr ((hK x a).mpr h)
  have hopp : ∀ (x y : H.halfEdgesAt w) (a : Fin 3), x ≠ y → φ x ≠ a → φ y ≠ a →
      O.osgn a y.1 = (O.osgn a x.1).flip := by
    intro x y a hxy hx hy
    exact O.osgn_flip_of_opposite a x.1 y.1 ((hK x a).mpr hx) ((hK y a).mpr hy)
      (O.exterior a w hw x y hxy ((hK x a).mpr hx) ((hK y a).mpr hy))
  apply O.balance_of_three y₀ y₁ y₂ h01 h02 h12 hcases r
  rw [hz y₀ 0 hy₀, hz y₁ 1 hy₁, hz y₂ 2 hy₂,
    hopp y₀ y₁ 2 h01 (by rw [hy₀]; decide) (by rw [hy₁]; decide),
    hopp y₁ y₂ 0 h12 (by rw [hy₁]; decide) (by rw [hy₂]; decide),
    hopp y₀ y₂ 1 h02 (by rw [hy₀]; decide) (by rw [hy₂]; decide)]
  exact balance_exterior _ _ _ (hnz y₀ 1 (by rw [hy₀]; decide)) (hnz y₀ 2 (by rw [hy₀]; decide))
    (hnz y₁ 0 (by rw [hy₁]; decide)) r

/-- Balance at a core vertex. -/
theorem balance_core_vertex (hCubic : ∀ v : V, H.degree v = 3) (i : Fin 6) (r : Fin 5) :
    (Finset.univ.filter fun x : H.halfEdgesAt (X.v i) ↦
        otail (fun _ ↦ 0) O.plab O.qlab x.1 = r).card =
      (Finset.univ.filter fun x : H.halfEdgesAt (X.v i) ↦
        ohead (fun _ ↦ 0) O.plab O.qlab x.1 = r).card := by
  set a := hexWord (i + g.r) with ha
  have hspoke_not_h : ∀ i', X.spoke i ≠ X.h i' := fun i' ↦ X.spoke_ne_h i i'
  have hKs : ∀ b, X.spoke i ∈ X.K g b ↔ b ≠ a := by
    intro b
    rw [X.mem_K_of_not_h g hspoke_not_h, g.spoke_color, g.idx_c]
    exact ne_comm
  -- the three words as functions of the coordinate
  let t : Fin 3 → Sgn := fun b ↦ O.osgn b (X.spokeHalf i).1
  let s : Sgn := O.osgn a (X.hex0 i).1
  have hta : t a = .zero := by
    simp only [t]
    by_contra hne
    exact absurd ((hKs a).mp ((O.osgn_ne_zero_iff a _).mp hne)) (fun h ↦ h rfl)
  have htb : ∀ b, b ≠ a → t b ≠ .zero := fun b hb ↦
    (O.osgn_ne_zero_iff b _).mpr ((hKs b).mpr hb)
  have hs : s ≠ .zero := (O.osgn_ne_zero_iff a _).mpr (X.h_mem_K g a i)
  have hx : (fun b ↦ O.osgn b (X.hex0 i).1) = Function.update (fun b ↦ (t b).flip) a s := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp [s]
    · rw [Function.update_of_ne hb]
      simp only [t]
      have h := (O.core_other i b (by rw [ha] at hb; exact hb)).2
      -- osgn b (spokeHalf) = (osgn b (hex0)).flip, so osgn b (hex0) = (osgn b spoke).flip
      have hK₁ : (X.hex0 i).1.1 ∈ X.K g b := X.h_mem_K g b i
      have hK₂ : (X.spokeHalf i).1.1 ∈ X.K g b := (hKs b).mpr hb
      have := O.osgn_flip_of_opposite b (X.hex0 i).1 (X.spokeHalf i).1 hK₁ hK₂
        (by
          change (0 = O.o b (X.h i)) ↔ ¬ (X.side i = O.o b (X.spoke i))
          rw [h]
          exact not_not.symm)
      rw [this, Sgn.flip_flip]
  have hy : (fun b ↦ O.osgn b (X.hex1 i).1) = Function.update (fun b ↦ (t b).flip) a s.flip := by
    funext b
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self]
      simp only [s]
      exact O.osgn_flip_of_opposite _ (X.hex0 i).1 (X.hex1 i).1 (X.h_mem_K g _ i)
        (X.h_mem_K g _ (i - 1)) (by
          change (0 = O.o _ (X.h i)) ↔ ¬ (1 = O.o _ (X.h (i - 1)))
          exact O.core_own i)
    · rw [Function.update_of_ne hb]
      simp only [t]
      have h := O.core_other i b (by rw [ha] at hb; exact hb)
      have hK₁ : (X.hex1 i).1.1 ∈ X.K g b := X.h_mem_K g b (i - 1)
      have hK₂ : (X.spokeHalf i).1.1 ∈ X.K g b := (hKs b).mpr hb
      have := O.osgn_flip_of_opposite b (X.hex1 i).1 (X.spokeHalf i).1 hK₁ hK₂
        (by
          change (1 = O.o b (X.h (i - 1))) ↔ ¬ (X.side i = O.o b (X.spoke i))
          rw [← h.1, h.2]
          exact not_not.symm)
      rw [this, Sgn.flip_flip]
  apply O.balance_of_three (X.spokeHalf i) (X.hex0 i) (X.hex1 i) (X.hex0_ne_spokeHalf i).symm
    (X.hex1_ne_spokeHalf i).symm (X.hex0_ne_hex1 i)
    (fun x ↦ by
      rcases X.halfEdge_cases hCubic i x with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h) r
  have hb := balance_core' a t s hta htb hs r
  simp only [tableOf] at hb
  have e1 : ∀ b, O.osgn b (X.hex0 i).1 = Function.update (fun b ↦ (t b).flip) a s b :=
    fun b ↦ congrFun hx b
  have e2 : ∀ b, O.osgn b (X.hex1 i).1 = Function.update (fun b ↦ (t b).flip) a s.flip b :=
    fun b ↦ congrFun hy b
  rw [e1 0, e1 1, e1 2, e2 0, e2 1, e2 2]
  exact hb

include O in
/-- **Oriented five-cycle double cover from three auxiliary orientations.**  The label classes
of the sign-word table form an oriented five-cycle double cover with the hexagon as the member
labelled `4`. -/
theorem exists_orientedCover (hCubic : ∀ v : V, H.degree v = 3) :
    ∃ D : H.OrientedCycleDoubleCover 5, D.Contains X.edgeSet := by
  obtain ⟨D, hD⟩ := exists_orientedCover_of_labels H (fun _ ↦ 0) O.plab O.qlab O.plab_ne_qlab
    (fun w r ↦ by
      by_cases hw : ∃ i, X.v i = w
      · obtain ⟨i, rfl⟩ := hw
        exact O.balance_core_vertex hCubic i r
      · push Not at hw
        exact O.balance_exterior_vertex hCubic (fun i h ↦ hw i h.symm) r)
  refine ⟨D, 4, ?_⟩
  rw [hD 4]
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, X.mem_edgeSet]
  change ((signTable (O.sgn 0 e) (O.sgn 1 e) (O.sgn 2 e)).1 = 4 ∨
    (signTable (O.sgn 0 e) (O.sgn 1 e) (O.sgn 2 e)).2 = 4) ↔ _
  rw [signTable_four_iff _ _ _ (O.valid_word e), O.sgn_ne_zero_iff, O.sgn_ne_zero_iff,
    O.sgn_ne_zero_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    by_contra hne
    push Not at hne
    have hne' : ∀ i, e ≠ X.h i := fun i h ↦ hne i h.symm
    rw [X.mem_K_of_not_h g hne'] at h0 h1 h2
    exact absurd (show g.idx (g.color e) = 0 ∨ g.idx (g.color e) = 1 ∨ g.idx (g.color e) = 2 by
      generalize g.idx (g.color e) = a
      revert a
      decide) (by
      push Not
      exact ⟨h0, h1, h2⟩)
  · rintro ⟨i, rfl⟩
    exact ⟨X.h_mem_K g 0 i, X.h_mem_K g 1 i, X.h_mem_K g 2 i⟩

end Orientations

end Hexagon

end LoopMultigraph
end GraphPuzzles
