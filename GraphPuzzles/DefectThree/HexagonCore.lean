import GraphPuzzles.CycleCovers.CircuitExtensionCorollaries

/-!
# Hexagonal cores and prescribed circuits meeting them

The defect-three argument starts from an induced hexagon `H` whose complement is
properly three-edge-coloured with spoke word `1,1,2,2,3,3`.  This module formalizes the two
colouring arguments used when a prescribed circuit `C` meets the hexagon:

* if at least three hexagon vertices lie on `C`, the exterior colouring extends over the
  surviving hexagon paths, so `G − V(C)` is three-edge-colourable;
* if exactly the two ends of a hexagon edge lie on `C` and the spoke word has its equal pair at
  that edge, the surviving four-vertex path is coloured `3,1,2` against spokes `2,2,3,3`.

Both cases feed the prescribed-circuit extension theorem.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

section Word

/-- The standard spoke word `0,0,1,1,2,2` read at the six hexagon positions. -/
def hexWord (i : Fin 6) : Fin 3 := ⟨i.val / 2, by omega⟩

/-- The index different from two distinct indices of `Fin 3`. -/
def thirdIndex (a b : Fin 3) : Fin 3 := ⟨(3 - a.val - b.val) % 3, Nat.mod_lt _ (by omega)⟩

/-- The colour index assigned to the hexagon edge `i` (joining positions `i` and `i + 1`) when the
spoke word is rotated by `r`.  The Boolean `b` records whether position `i - 1` survives. -/
def edgeIndex (r : Fin 6) (b : Bool) (i : Fin 6) : Fin 3 :=
  if hexWord (i + r) = hexWord (i + 1 + r) then
    (if b then hexWord (i - 1 + r) else hexWord (i + 2 + r))
  else thirdIndex (hexWord (i + r)) (hexWord (i + 1 + r))

theorem thirdIndex_ne_left {a b : Fin 3} (h : a ≠ b) : thirdIndex a b ≠ a := by
  revert a b
  decide

theorem thirdIndex_ne_right {a b : Fin 3} (h : a ≠ b) : thirdIndex a b ≠ b := by
  revert a b
  decide

theorem edgeIndex_ne_left (r : Fin 6) (b : Bool) (i : Fin 6) :
    edgeIndex r b i ≠ hexWord (i + r) := by
  revert r b i
  decide

theorem edgeIndex_ne_right (r : Fin 6) (b : Bool) (i : Fin 6) :
    edgeIndex r b i ≠ hexWord (i + 1 + r) := by
  revert r b i
  decide

/-- Three consecutive survivors and no others: the two path edges receive distinct indices. -/
theorem edgeIndex_ne_of_three (r m : Fin 6) :
    edgeIndex r false (m - 1) ≠ edgeIndex r true m := by
  revert r m
  decide

/-- Exactly the ends of a hexagon edge carrying an equal pair are deleted: the three edges of the
surviving path receive pairwise distinct indices at each interior vertex. -/
theorem edgeIndex_ne_of_pair (r m j : Fin 6) (hj : (j + r).val % 2 = 0)
    (h₁ : m - 1 ≠ j) (h₂ : m - 1 ≠ j + 1) (h₃ : m ≠ j) (h₄ : m ≠ j + 1)
    (h₅ : m + 1 ≠ j) (h₆ : m + 1 ≠ j + 1) :
    edgeIndex r (decide (¬ (m - 1 - 1 = j) ∧ ¬ (m - 1 - 1 = j + 1))) (m - 1) ≠
      edgeIndex r true m := by
  revert r m j
  decide

/-- Three distinct nonzero colours: the first two sum to the third. -/
theorem three_colors_sum (x y z : Color) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : x + y = z := by
  revert x y z
  decide

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin2_rev_of_ne {a b : Fin 2} (h : a ≠ b) : b = Fin.rev a := by
  revert a b
  decide

private theorem fin6_ne_add_one (a : Fin 6) : a ≠ a + 1 := by
  revert a
  decide

private theorem fin6_card_four (m : Fin 6) :
    ({m - 1 - 1, m - 1, m, m + 1} : Finset (Fin 6)).card = 4 := by
  revert m
  decide

end Word

section Hexagon

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- An induced hexagon of a cubic endpoint multigraph: six distinct vertices `v i`, the hexagon
edge `h i` joining `v i` to `v (i + 1)`, and the spoke at `v i`, whose other end lies off the
hexagon. -/
structure Hexagon (H : LoopMultigraph V E) where
  v : Fin 6 → V
  h : Fin 6 → E
  spoke : Fin 6 → E
  side : Fin 6 → Fin 2
  v_injective : Function.Injective v
  h_end0 : ∀ i, H.endAt (h i) 0 = v i
  h_end1 : ∀ i, H.endAt (h i) 1 = v (i + 1)
  spoke_end : ∀ i, H.endAt (spoke i) (side i) = v i
  spoke_far : ∀ i j, H.endAt (spoke i) (Fin.rev (side i)) ≠ v j

instance (H : LoopMultigraph V E) (v : V) : DecidableEq (H.halfEdgesAt v) :=
  inferInstanceAs (DecidableEq {h : HalfEdge E // H.vertex h = v})

namespace Hexagon

variable {H : LoopMultigraph V E} (X : H.Hexagon)

omit [DecidableEq V] [DecidableEq E] in
theorem h_injective : Function.Injective X.h := by
  intro i j hij
  apply X.v_injective
  rw [← X.h_end0 i, ← X.h_end0 j, hij]

omit [DecidableEq V] [DecidableEq E] in
theorem spoke_ne_h (i j : Fin 6) : X.spoke i ≠ X.h j := by
  intro heq
  have hfar := X.spoke_far i
  rw [heq] at hfar
  rcases fin2_cases (Fin.rev (X.side i)) with hk | hk
  · rw [hk] at hfar
    exact hfar j (X.h_end0 j)
  · rw [hk] at hfar
    exact hfar (j + 1) (X.h_end1 j)

/-- The half-edge of `h i` at `v i`. -/
def hex0 (i : Fin 6) : H.halfEdgesAt (X.v i) := ⟨(X.h i, 0), X.h_end0 i⟩

/-- The half-edge of `h (i - 1)` at `v i`. -/
def hex1 (i : Fin 6) : H.halfEdgesAt (X.v i) :=
  ⟨(X.h (i - 1), 1), by
    change H.endAt (X.h (i - 1)) 1 = X.v i
    rw [X.h_end1, sub_add_cancel]⟩

/-- The half-edge of the spoke at `v i`. -/
def spokeHalf (i : Fin 6) : H.halfEdgesAt (X.v i) := ⟨(X.spoke i, X.side i), X.spoke_end i⟩

omit [DecidableEq V] [DecidableEq E] in
theorem hex0_ne_hex1 (i : Fin 6) : X.hex0 i ≠ X.hex1 i := by
  intro h
  have := congrArg (fun x ↦ x.1.2) h
  simp [hex0, hex1] at this

omit [DecidableEq V] [DecidableEq E] in
theorem hex0_ne_spokeHalf (i : Fin 6) : X.hex0 i ≠ X.spokeHalf i := by
  intro h
  have := congrArg (fun x ↦ x.1.1) h
  exact X.spoke_ne_h i i this.symm

omit [DecidableEq V] [DecidableEq E] in
theorem hex1_ne_spokeHalf (i : Fin 6) : X.hex1 i ≠ X.spokeHalf i := by
  intro h
  have := congrArg (fun x ↦ x.1.1) h
  exact X.spoke_ne_h i (i - 1) this.symm

/-- In a cubic graph the three half-edges at a hexagon vertex are the two hexagon half-edges and
the spoke. -/
theorem halfEdge_cases (hCubic : ∀ v : V, H.degree v = 3) (i : Fin 6)
    (x : H.halfEdgesAt (X.v i)) : x = X.hex0 i ∨ x = X.hex1 i ∨ x = X.spokeHalf i := by
  have hcard : Fintype.card (H.halfEdgesAt (X.v i)) = 3 := hCubic _
  have hsub : ({X.hex0 i, X.hex1 i, X.spokeHalf i} : Finset (H.halfEdgesAt (X.v i))) =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem, Finset.card_pair (X.hex1_ne_spokeHalf i), hcard]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨X.hex0_ne_hex1 i, X.hex0_ne_spokeHalf i⟩
  have hx : x ∈ ({X.hex0 i, X.hex1 i, X.spokeHalf i} : Finset (H.halfEdgesAt (X.v i))) := by
    rw [hsub]
    exact Finset.mem_univ x
  simpa using hx

/-- A half-edge at a hexagon vertex that is not a hexagon edge is the spoke. -/
theorem spoke_of_not_h (hCubic : ∀ v : V, H.degree v = 3) (i : Fin 6)
    (x : H.halfEdgesAt (X.v i)) (hx : ∀ j, x.1.1 ≠ X.h j) : x.1.1 = X.spoke i := by
  rcases X.halfEdge_cases hCubic i x with rfl | rfl | rfl
  · exact absurd rfl (hx i)
  · exact absurd rfl (hx (i - 1))
  · rfl

/-- A proper three-edge-colouring of the complement of the hexagon whose spoke word is the
standard word `0,0,1,1,2,2` rotated by `r` and read through the injective colour table `c`. -/
structure ExteriorColoring where
  color : E → Color
  r : Fin 6
  c : Fin 3 → Color
  c_injective : Function.Injective c
  nonzero : ∀ e, (∀ i, e ≠ X.h i) → color e ≠ 0
  injective_at : ∀ w, ∀ h₁ h₂ : H.halfEdgesAt w, (∀ i, h₁.1.1 ≠ X.h i) →
    (∀ i, h₂.1.1 ≠ X.h i) → color h₁.1.1 = color h₂.1.1 → h₁ = h₂
  spoke_color : ∀ i, color (X.spoke i) = c (hexWord (i + r))

variable {X} in
/-- The spoke word of `g` has its equal pair at the hexagon edge `j`. -/
def ExteriorColoring.PairAt (g : X.ExteriorColoring) (j : Fin 6) : Prop := (j + g.r).val % 2 = 0

/-- Whether hexagon position `i` survives the deletion of `S`. -/
def surv (S : Finset V) (i : Fin 6) : Bool := decide (X.v i ∉ S)

/-- The hexagon positions lying on a circuit. -/
def onCircuit (C : H.OrdinaryCircuit) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ X.v i ∈ H.edgeSupport C.edges

namespace ExteriorColoring

variable {X} (g : X.ExteriorColoring)

omit [DecidableEq V] [DecidableEq E] in
theorem c_ne_zero (a : Fin 3) : g.c a ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, hexWord (i + g.r) = a :=
    ⟨⟨2 * a.val, by omega⟩ - g.r, by
      rw [sub_add_cancel]
      apply Fin.ext
      simp only [hexWord]
      omega⟩
  rw [← hi, ← g.spoke_color]
  exact g.nonzero _ (fun j ↦ X.spoke_ne_h i j)

omit [DecidableEq V] [DecidableEq E] in
theorem c_add {a b : Fin 3} (hab : a ≠ b) : g.c a + g.c b = g.c (thirdIndex a b) := by
  have hne : ∀ p q : Fin 3, p ≠ q → g.c p ≠ g.c q := fun p q hpq h ↦ hpq (g.c_injective h)
  exact three_colors_sum _ _ _ (g.c_ne_zero a) (g.c_ne_zero b) (g.c_ne_zero _) (hne _ _ hab)
    (hne _ _ (thirdIndex_ne_left hab).symm) (hne _ _ (thirdIndex_ne_right hab).symm)

/-- The colour of the hexagon edge `i` after deleting `S`. -/
def edgeColor (S : Finset V) (i : Fin 6) : Color := g.c (edgeIndex g.r (X.surv S (i - 1)) i)

/-- The exterior colouring extended over the hexagon edges. -/
noncomputable def extend (S : Finset V) (e : E) : Color :=
  if hi : ∃ i, e = X.h i then g.edgeColor S hi.choose else g.color e

theorem extend_h (S : Finset V) (i : Fin 6) : g.extend S (X.h i) = g.edgeColor S i := by
  have hi : ∃ j, X.h i = X.h j := ⟨i, rfl⟩
  unfold extend
  rw [dif_pos hi]
  congr 1
  exact X.h_injective hi.choose_spec.symm

theorem extend_of_not_h (S : Finset V) {e : E} (he : ∀ i, e ≠ X.h i) :
    g.extend S e = g.color e := by
  unfold extend
  rw [dif_neg (fun ⟨i, hi⟩ ↦ he i hi)]

omit [DecidableEq E] in
theorem edgeColor_ne_zero (S : Finset V) (i : Fin 6) : g.edgeColor S i ≠ 0 := g.c_ne_zero _

omit [DecidableEq E] in
theorem edgeColor_ne_spoke_left (S : Finset V) (i : Fin 6) :
    g.edgeColor S i ≠ g.color (X.spoke i) := by
  rw [g.spoke_color]
  intro h
  exact edgeIndex_ne_left g.r _ i (g.c_injective h)

omit [DecidableEq E] in
theorem edgeColor_ne_spoke_right (S : Finset V) (i : Fin 6) :
    g.edgeColor S i ≠ g.color (X.spoke (i + 1)) := by
  rw [g.spoke_color]
  intro h
  exact edgeIndex_ne_right g.r _ i (g.c_injective h)

/-- The two deletion patterns handled by the hexagon colouring: at least three hexagon vertices
deleted, or exactly the ends of a hexagon edge carrying the equal spoke pair. -/
def Admissible (S : Finset V) : Prop :=
  3 ≤ (Finset.univ.filter fun i ↦ X.v i ∈ S).card ∨
    ∃ j, g.PairAt j ∧ ∀ i, X.v i ∈ S ↔ (i = j ∨ i = j + 1)

omit [DecidableEq E] in
/-- Three consecutive surviving hexagon vertices: the two path edges get different colours. -/
theorem edgeColor_ne_of_path (S : Finset V) (hS : g.Admissible S) (m : Fin 6)
    (h₁ : X.v (m - 1) ∉ S) (h₂ : X.v m ∉ S) (h₃ : X.v (m + 1) ∉ S) :
    g.edgeColor S (m - 1) ≠ g.edgeColor S m := by
  intro heq
  have heq' := g.c_injective heq
  have hsurv : X.surv S (m - 1) = true := by simp [surv, h₁]
  rw [hsurv] at heq'
  rcases hS with h3 | ⟨j, hj, hT⟩
  · have hW : X.surv S (m - 1 - 1) = false := by
      simp only [surv, decide_eq_false_iff_not, not_not]
      by_contra hno
      have hsub : ({m - 1 - 1, m - 1, m, m + 1} : Finset (Fin 6)) ⊆
          Finset.univ.filter fun i ↦ X.v i ∉ S := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hi with rfl | rfl | rfl | rfl <;> assumption
      have hle := Finset.card_le_card hsub
      rw [fin6_card_four] at hle
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 6))) (p := fun i ↦ X.v i ∈ S)
      simp only [Finset.card_univ, Fintype.card_fin] at hsplit
      omega
    rw [hW] at heq'
    exact edgeIndex_ne_of_three g.r m heq'
  · have hW : X.surv S (m - 1 - 1) = decide (¬ (m - 1 - 1 = j) ∧ ¬ (m - 1 - 1 = j + 1)) := by
      simp only [surv, hT, not_or]
    rw [hW] at heq'
    have hm1 : ¬ (m - 1 = j ∨ m - 1 = j + 1) := fun h ↦ h₁ ((hT (m - 1)).mpr h)
    have hm : ¬ (m = j ∨ m = j + 1) := fun h ↦ h₂ ((hT m).mpr h)
    have hp1 : ¬ (m + 1 = j ∨ m + 1 = j + 1) := fun h ↦ h₃ ((hT (m + 1)).mpr h)
    rw [not_or] at hm1 hm hp1
    exact edgeIndex_ne_of_pair g.r m j hj hm1.1 hm1.2 hm.1 hm.2 hp1.1 hp1.2 heq'

omit [DecidableEq E] in
/-- Two hexagon half-edges at a surviving vertex with all ends surviving and equal colours are
the same half-edge. -/
theorem hex_hex (S : Finset V) (hS : g.Admissible S) {w : V} (_hw : w ∉ S)
    (h₁ h₂ : H.halfEdgesAt w) (hh₁ : ∀ k, H.endAt h₁.1.1 k ∉ S)
    (hh₂ : ∀ k, H.endAt h₂.1.1 k ∉ S) {i j : Fin 6} (hi : h₁.1.1 = X.h i)
    (hj : h₂.1.1 = X.h j) (heq : g.edgeColor S i = g.edgeColor S j) : h₁ = h₂ := by
  have hw1 : w = H.endAt (X.h i) h₁.1.2 := by
    rw [← hi]
    exact h₁.2.symm
  have hw2 : w = H.endAt (X.h j) h₂.1.2 := by
    rw [← hj]
    exact h₂.2.symm
  have hvi : X.v (i + 1) ∉ S := by
    have := hh₁ 1
    rwa [hi, X.h_end1] at this
  have hvi0 : X.v i ∉ S := by
    have := hh₁ 0
    rwa [hi, X.h_end0] at this
  have hvj : X.v (j + 1) ∉ S := by
    have := hh₂ 1
    rwa [hj, X.h_end1] at this
  have hvj0 : X.v j ∉ S := by
    have := hh₂ 0
    rwa [hj, X.h_end0] at this
  rcases fin2_cases h₁.1.2 with k₁ | k₁ <;> rcases fin2_cases h₂.1.2 with k₂ | k₂
  · rw [k₁, X.h_end0] at hw1
    rw [k₂, X.h_end0] at hw2
    have hij : i = j := X.v_injective (hw1.symm.trans hw2)
    apply Subtype.ext
    apply Prod.ext
    · rw [hi, hj, hij]
    · rw [k₁, k₂]
  · exfalso
    rw [k₁, X.h_end0] at hw1
    rw [k₂, X.h_end1] at hw2
    have hij : i = j + 1 := X.v_injective (hw1.symm.trans hw2)
    subst hij
    have hpath := g.edgeColor_ne_of_path S hS (j + 1) (by rwa [add_sub_cancel_right]) hvi0 hvi
    rw [add_sub_cancel_right] at hpath
    exact hpath heq.symm
  · exfalso
    rw [k₁, X.h_end1] at hw1
    rw [k₂, X.h_end0] at hw2
    have hij : j = i + 1 := X.v_injective (hw2.symm.trans hw1)
    subst hij
    have hpath := g.edgeColor_ne_of_path S hS (i + 1) (by rwa [add_sub_cancel_right]) hvj0 hvj
    rw [add_sub_cancel_right] at hpath
    exact hpath heq
  · rw [k₁, X.h_end1] at hw1
    rw [k₂, X.h_end1] at hw2
    have hij : i = j := add_right_cancel (X.v_injective (hw1.symm.trans hw2))
    apply Subtype.ext
    apply Prod.ext
    · rw [hi, hj, hij]
    · rw [k₁, k₂]

/-- A hexagon half-edge and a non-hexagon half-edge at a surviving vertex get different
colours. -/
theorem hex_ne_other (hCubic : ∀ v : V, H.degree v = 3) (S : Finset V) {w : V}
    (h₁ h₂ : H.halfEdgesAt w) (hh₂ : ∀ i, h₂.1.1 ≠ X.h i) {i : Fin 6} (hi : h₁.1.1 = X.h i) :
    g.edgeColor S i ≠ g.color h₂.1.1 := by
  have hw1 : w = H.endAt (X.h i) h₁.1.2 := by
    rw [← hi]
    exact h₁.2.symm
  rcases fin2_cases h₁.1.2 with k₁ | k₁
  · rw [k₁, X.h_end0] at hw1
    subst hw1
    rw [X.spoke_of_not_h hCubic i h₂ hh₂]
    exact g.edgeColor_ne_spoke_left S i
  · rw [k₁, X.h_end1] at hw1
    subst hw1
    rw [X.spoke_of_not_h hCubic (i + 1) h₂ hh₂]
    exact g.edgeColor_ne_spoke_right S i

/-- The extended colouring is proper off `S` in the admissible cases. -/
theorem extend_properOff (hCubic : ∀ v : V, H.degree v = 3) (S : Finset V)
    (hS : g.Admissible S) : H.ProperOff S (g.extend S) := by
  constructor
  · intro e _
    by_cases he : ∃ i, e = X.h i
    · obtain ⟨i, rfl⟩ := he
      rw [g.extend_h]
      exact g.edgeColor_ne_zero S i
    · push Not at he
      rw [g.extend_of_not_h S he]
      exact g.nonzero e he
  · intro w hw h₁ h₂ hh₁ hh₂ heq
    by_cases e₁ : ∃ i, h₁.1.1 = X.h i <;> by_cases e₂ : ∃ i, h₂.1.1 = X.h i
    · obtain ⟨i, hi⟩ := e₁
      obtain ⟨j, hj⟩ := e₂
      rw [hi, hj, g.extend_h, g.extend_h] at heq
      exact g.hex_hex S hS hw h₁ h₂ hh₁ hh₂ hi hj heq
    · obtain ⟨i, hi⟩ := e₁
      push Not at e₂
      rw [hi, g.extend_h, g.extend_of_not_h S e₂] at heq
      exact absurd heq (g.hex_ne_other hCubic S h₁ h₂ e₂ hi)
    · obtain ⟨j, hj⟩ := e₂
      push Not at e₁
      rw [hj, g.extend_h, g.extend_of_not_h S e₁] at heq
      exact absurd heq.symm (g.hex_ne_other hCubic S h₂ h₁ e₁ hj)
    · push Not at e₁ e₂
      rw [g.extend_of_not_h S e₁, g.extend_of_not_h S e₂] at heq
      exact g.injective_at w h₁ h₂ e₁ e₂ heq

end ExteriorColoring

/-- The extension theorem applied to the hexagon colouring. -/
theorem exists_fiveCycleDoubleCover_of_admissible (hCubic : ∀ v : V, H.degree v = 3)
    (g : X.ExteriorColoring) (C : H.OrdinaryCircuit)
    (hS : g.Admissible (H.edgeSupport C.edges)) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_properOff hCubic
    (g.extend_properOff hCubic _ hS)

/-- **At least three hexagon vertices on the circuit.**  Any exterior colouring extends over the
surviving hexagon paths, so the circuit is an entire member of a five-cycle double cover. -/
theorem exists_fiveCycleDoubleCover_of_three (hCubic : ∀ v : V, H.degree v = 3)
    (g : X.ExteriorColoring) (C : H.OrdinaryCircuit) (h3 : 3 ≤ (X.onCircuit C).card) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  X.exists_fiveCycleDoubleCover_of_admissible hCubic g C (Or.inl h3)

/-- **Exactly the ends of a hexagon edge on the circuit.**  If the exterior colouring has its
equal spoke pair at that edge, the circuit is an entire member of a five-cycle double cover. -/
theorem exists_fiveCycleDoubleCover_of_pair (hCubic : ∀ v : V, H.degree v = 3)
    (g : X.ExteriorColoring) (C : H.OrdinaryCircuit) (j : Fin 6) (hj : g.PairAt j)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1)) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  X.exists_fiveCycleDoubleCover_of_admissible hCubic g C (Or.inr ⟨j, hj, hT⟩)

/-- A circuit through a hexagon vertex also passes through a hexagon neighbour of it. -/
theorem neighbor_onCircuit (hCubic : ∀ v : V, H.degree v = 3) (C : H.OrdinaryCircuit)
    {i : Fin 6} (hi : X.v i ∈ H.edgeSupport C.edges) :
    X.v (i - 1) ∈ H.edgeSupport C.edges ∨ X.v (i + 1) ∈ H.edgeSupport C.edges := by
  by_contra hno
  push Not at hno
  have h2 : H.degreeIn C.edges (X.v i) = 2 := C.twoRegular _ hi
  have hnot0 : X.h i ∉ C.edges :=
    fun hmem ↦ hno.2 (H.mem_edgeSupport_iff.mpr ⟨X.h i, hmem, 1, X.h_end1 i⟩)
  have hnot1 : X.h (i - 1) ∉ C.edges :=
    fun hmem ↦ hno.1 (H.mem_edgeSupport_iff.mpr ⟨X.h (i - 1), hmem, 0, X.h_end0 (i - 1)⟩)
  have hsub : ((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun x ↦ H.endAt x.1 x.2 = X.v i) ⊆ {(X.spoke i, X.side i)} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hxE : x.1 ∈ C.edges := (Finset.mem_product.mp hx1).1
    rcases X.halfEdge_cases hCubic i ⟨x, hx2⟩ with h | h | h
    · have hx' : x = (X.h i, 0) := congrArg Subtype.val h
      rw [hx'] at hxE
      exact absurd hxE hnot0
    · have hx' : x = (X.h (i - 1), 1) := congrArg Subtype.val h
      rw [hx'] at hxE
      exact absurd hxE hnot1
    · have hx' : x = (X.spoke i, X.side i) := congrArg Subtype.val h
      exact Finset.mem_singleton.mpr hx'
  have hle := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hle
  unfold degreeIn at h2
  omega

end Hexagon

end Hexagon

end LoopMultigraph
end GraphPuzzles
