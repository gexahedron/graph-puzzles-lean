import GraphPuzzles.CycleCovers.OrientationParity
import GraphPuzzles.CycleCovers.OrientedCover

/-! The parity and recolouring lemmas for orienting a hexagonal core. -/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- A weighted handshake identity, counting loops twice. -/
theorem sum_mul_degreeIn (F : Finset E) (w : V → ℕ) :
    ∑ v, w v * H.degreeIn F v = ∑ e ∈ F, (w (H.endAt e 0) + w (H.endAt e 1)) := by
  simp only [degreeIn, Finset.card_filter, Finset.sum_product, Finset.mul_sum,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  simp [Fin.sum_univ_two]

namespace Hexagon
namespace ExteriorColoring

variable {X : H.Hexagon} (g : X.ExteriorColoring)

/-- The two colours other than `a` are interchanged. -/
def otherSwap (a : Fin 3) : Equiv.Perm (Fin 3) := Equiv.swap (a + 1) (a + 2)

@[simp] theorem otherSwap_self (a : Fin 3) : otherSwap a a = a := by
  revert a
  decide

/-- Positions relative to the pair of spokes of colour `a`. -/
def relativePosition (r : Fin 6) (a : Fin 3) (i : Fin 6) : Fin 6 :=
  i + r - ⟨2 * a.val, by omega⟩

/-- The two terminals prescribed to direct their spokes away from the core. -/
def isSource (r : Fin 6) (a : Fin 3) (i : Fin 6) : Bool :=
  decide (relativePosition r a i = 2 ∨ relativePosition r a i = 4)

def coreTail (r : Fin 6) (a : Fin 3) (i : Fin 6) : Fin 2 :=
  ![0, 0, 1, 0, 1, 0] (relativePosition r a i)

theorem coreTail_own (r : Fin 6) (i : Fin 6) :
    (0 = coreTail r (hexWord (i + r)) i) ↔
      ¬ (1 = coreTail r (hexWord (i + r)) (i - 1)) := by
  revert r i
  decide

theorem coreTail_other (r : Fin 6) (i : Fin 6) (a : Fin 3)
    (ha : a ≠ hexWord (i + r)) :
    ((0 = coreTail r a i) ↔ (1 = coreTail r a (i - 1))) ∧
      ((isSource r a i = true) ↔ ¬ (0 = coreTail r a i)) := by
  revert r i a
  decide

theorem source_ne_own (r : Fin 6) (i : Fin 6) (a : Fin 3)
    (hs : isSource r a i = true) : hexWord (i + r) ≠ a := by
  revert r i a
  decide

/-- The only even terminal selections with the wrong source parity are the two sources
or the two sinks. Own-colour spokes do not belong to the bicoloured subgraph. -/
theorem terminal_parity_cases (r : Fin 6) (a : Fin 3) (p : Fin 6 → Bool)
    (heven : (∑ i : Fin 6, if hexWord (i + r) ≠ a ∧ p i = true then 1 else 0) % 2 = 0) :
    (∑ i : Fin 6, if isSource r a i = true ∧ p i = true then 1 else 0) % 2 =
        ((∑ i : Fin 6, if hexWord (i + r) ≠ a ∧ p i = true then 1 else 0) / 2) % 2 ∨
      (∀ i, hexWord (i + r) ≠ a → p i = isSource r a i) ∨
      (∀ i, hexWord (i + r) ≠ a → p i = !(isSource r a i)) := by
  revert r a p
  decide

/-- A componentwise interchange of the two colours other than `a`. -/
noncomputable def kempeIndex (a : Fin 3) (c : V → F₂) (e : E) : Fin 3 :=
  if c (H.endAt e 0) = 1 then otherSwap a (g.idx (g.color e)) else g.idx (g.color e)

omit [DecidableEq V] in
/-- At a vertex, the interchange acts uniformly on the incident exterior colours. -/
theorem kempeIndex_at (a : Fin 3) (c : V → F₂)
    (hc : ∀ e ∈ g.bLayer a, c (H.endAt e 0) = c (H.endAt e 1))
    {w : V} (x : H.halfEdgesAt w) (hx : ∀ i, x.1.1 ≠ X.h i) :
    g.kempeIndex a c x.1.1 =
      if c w = 1 then otherSwap a (g.idx (g.color x.1.1)) else g.idx (g.color x.1.1) := by
  by_cases ha : g.idx (g.color x.1.1) = a
  · simp [kempeIndex, ha]
  · have he := hc x.1.1 ((g.mem_bLayer_iff hx).mpr ha)
    have hv : c (H.endAt x.1.1 0) = c w := by
      have hw : H.endAt x.1.1 x.1.2 = w := x.2
      rcases (show ∀ j : Fin 2, j = 0 ∨ j = 1 by decide) x.1.2 with hi | hi
      · simpa only [hi] using congrArg c hw
      · exact he.trans (by simpa only [hi] using congrArg c hw)
    simp only [kempeIndex, hv]

omit [DecidableEq V] in
theorem kempeIndex_injective_at (a : Fin 3) (c : V → F₂)
    (hc : ∀ e ∈ g.bLayer a, c (H.endAt e 0) = c (H.endAt e 1))
    (w : V) (x y : H.halfEdgesAt w) (hx : ∀ i, x.1.1 ≠ X.h i)
    (hy : ∀ i, y.1.1 ≠ X.h i)
    (hxy : g.kempeIndex a c x.1.1 = g.kempeIndex a c y.1.1) : x = y := by
  rw [g.kempeIndex_at a c hc x hx, g.kempeIndex_at a c hc y hy] at hxy
  have hidx : g.idx (g.color x.1.1) = g.idx (g.color y.1.1) := by
    split_ifs at hxy
    · exact (otherSwap a).injective hxy
    · exact hxy
  apply g.injective_at w x y hx hy
  have hh := congrArg g.c hidx
  simpa only [g.c_idx (g.nonzero _ hx), g.c_idx (g.nonzero _ hy)] using hh

/-- The core colouring that repairs either forbidden terminal selection. -/
def repairIndex (r : Fin 6) (a : Fin 3) (t : Bool) (i : Fin 6) : Fin 3 :=
  let q := a + ![2, 1, 0, 2, 0, 1] (relativePosition r a i)
  if t then otherSwap a q else q

def selectedTerminal (r : Fin 6) (a : Fin 3) (t : Bool) (i : Fin 6) : Bool :=
  if t then !(isSource r a i) else isSource r a i

def repairedSpoke (r : Fin 6) (a : Fin 3) (t : Bool) (i : Fin 6) : Fin 3 :=
  if selectedTerminal r a t i then otherSwap a (hexWord (i + r)) else hexWord (i + r)

theorem repair_table (r : Fin 6) (a : Fin 3) (t : Bool) (i : Fin 6) :
    repairIndex r a t i ≠ repairIndex r a t (i - 1) ∧
      repairIndex r a t i ≠ repairedSpoke r a t i ∧
      repairIndex r a t (i - 1) ≠ repairedSpoke r a t i := by
  revert r a t i
  decide

noncomputable def patchedIndex (q : Fin 6 → Fin 3) (a : Fin 3) (c : V → F₂) (e : E) : Fin 3 :=
  if he : ∃ i, X.h i = e then q he.choose else g.kempeIndex a c e

omit [DecidableEq V] in
theorem patchedIndex_h (q : Fin 6 → Fin 3) (a : Fin 3) (c : V → F₂) (i : Fin 6) :
    g.patchedIndex q a c (X.h i) = q i := by
  unfold patchedIndex
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact X.h_injective (Exists.choose_spec (show ∃ j, X.h j = X.h i from ⟨i, rfl⟩))

omit [DecidableEq V] in
theorem patchedIndex_off (q : Fin 6 → Fin 3) (a : Fin 3) (c : V → F₂)
    {e : E} (he : ∀ i, e ≠ X.h i) : g.patchedIndex q a c e = g.kempeIndex a c e := by
  simp only [patchedIndex, show ¬ (∃ i, X.h i = e) from fun ⟨i, hi⟩ ↦ he i hi.symm,
    ↓reduceDIte]

/-- A forbidden selection would extend the Kempe recolouring over the entire hexagon. -/
theorem colourable_of_bad_terminals (hCubic : ∀ v, H.degree v = 3)
    (a : Fin 3) (c : V → F₂)
    (hc : ∀ e ∈ g.bLayer a, c (H.endAt e 0) = c (H.endAt e 1))
    (t : Bool)
    (hbad : ∀ i, hexWord (i + g.r) ≠ a →
      (c (X.v i) = 1 ↔ selectedTerminal g.r a t i = true)) :
    ∃ f : E → Color, H.ProperOff ∅ f := by
  let q := repairIndex g.r a t
  let f := fun e ↦ g.c (g.patchedIndex q a c e)
  have hspoke (i : Fin 6) :
      g.patchedIndex q a c (X.spoke i) = repairedSpoke g.r a t i := by
    rw [g.patchedIndex_off q a c (X.spoke_ne_h i)]
    have hi := g.kempeIndex_at a c hc (X.spokeHalf i) (X.spoke_ne_h i)
    change g.kempeIndex a c (X.spoke i) = _ at hi
    rw [hi]
    simp only [spokeHalf, g.spoke_color, g.idx_c, repairedSpoke]
    by_cases hi : hexWord (i + g.r) = a
    · simp [hi]
    · simp only [hbad i hi]
  refine ⟨f, fun e _ ↦ g.c_ne_zero _, ?_⟩
  intro w _ x y _ _ hxy
  have hidx := g.c_injective hxy
  change g.patchedIndex q a c x.1.1 = g.patchedIndex q a c y.1.1 at hidx
  by_cases hw : ∃ i, X.v i = w
  · obtain ⟨i, rfl⟩ := hw
    obtain ⟨h01, h02, h12⟩ := repair_table g.r a t i
    rcases X.halfEdge_cases hCubic i x with rfl | rfl | rfl <;>
      rcases X.halfEdge_cases hCubic i y with rfl | rfl | rfl
    all_goals try rfl
    all_goals simp only [hex0, hex1, spokeHalf, g.patchedIndex_h, hspoke, q] at hidx
    · exact (h01 hidx).elim
    · exact (h02 hidx).elim
    · exact (h01 hidx.symm).elim
    · exact (h12 hidx).elim
    · exact (h02 hidx.symm).elim
    · exact (h12 hidx.symm).elim
  · have hwo : ∀ i, w ≠ X.v i := fun i hi ↦ hw ⟨i, hi.symm⟩
    have hx := halfEdge_not_h hwo x
    have hy := halfEdge_not_h hwo y
    rw [g.patchedIndex_off q a c hx, g.patchedIndex_off q a c hy] at hidx
    exact g.kempeIndex_injective_at a c hc w x y hx hy hidx

/-- At an exterior vertex, the three incident half-edges have the three colour indices. -/
noncomputable def exteriorIndexEquiv (hCubic : ∀ v, H.degree v = 3) {w : V}
    (hw : ∀ i, w ≠ X.v i) : H.halfEdgesAt w ≃ Fin 3 :=
  Equiv.ofBijective (fun x ↦ g.idx (g.color x.1.1))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro x y hxy
      apply g.injective_at w x y (halfEdge_not_h hw x) (halfEdge_not_h hw y)
      have hh := congrArg g.c hxy
      simpa only [g.c_idx (g.nonzero _ (halfEdge_not_h hw x)),
        g.c_idx (g.nonzero _ (halfEdge_not_h hw y))] using hh,
      by rw [Fintype.card_fin]; exact hCubic w⟩)

theorem degree_bLayer_off (hCubic : ∀ v, H.degree v = 3) (a : Fin 3) {w : V}
    (hw : ∀ i, w ≠ X.v i) : H.degreeIn (g.bLayer a) w = 2 := by
  rw [H.degreeIn_eq_card_halfEdges, ← Fintype.card_subtype]
  calc
    Fintype.card {x : H.halfEdgesAt w // x.1.1 ∈ g.bLayer a} =
        Fintype.card {b : Fin 3 // b ≠ a} :=
      Fintype.card_congr ((g.exteriorIndexEquiv hCubic hw).subtypeEquiv fun x ↦
        g.mem_bLayer_iff (halfEdge_not_h hw x))
    _ = 2 := (show ∀ b : Fin 3, Fintype.card {j : Fin 3 // j ≠ b} = 2 by decide) a

omit [DecidableEq V] in
theorem spoke_mem_bLayer (a : Fin 3) (i : Fin 6) :
    X.spoke i ∈ g.bLayer a ↔ hexWord (i + g.r) ≠ a := by
  rw [g.mem_bLayer_iff (X.spoke_ne_h i), g.spoke_color, g.idx_c]

theorem degree_bLayer_core (hCubic : ∀ v, H.degree v = 3) (a : Fin 3) (i : Fin 6) :
    H.degreeIn (g.bLayer a) (X.v i) = if hexWord (i + g.r) ≠ a then 1 else 0 := by
  rw [H.degreeIn_eq_card_halfEdges, card_filter_of_three (X.hex0 i) (X.hex1 i) (X.spokeHalf i)
    (X.hex0_ne_hex1 i) (X.hex0_ne_spokeHalf i) (X.hex1_ne_spokeHalf i)
    (X.halfEdge_cases hCubic i)]
  simp only [hex0, hex1, spokeHalf, g.h_notin_bLayer, if_false, zero_add, g.spoke_mem_bLayer]

omit [DecidableEq E] in
/-- Sum a vertex function over exterior vertices and the six core vertices. -/
theorem sum_vertex_partition {A : Type*} [AddCommMonoid A] (f : V → A) :
    ∑ v, f v = (∑ v ∈ Finset.univ \ X.vertexSet, f v) + ∑ i : Fin 6, f (X.v i) := by
  have hx : ∑ v ∈ X.vertexSet, f v = ∑ i : Fin 6, f (X.v i) := by
    exact Finset.sum_image (fun i _ j _ hij ↦ X.v_injective hij)
  rw [← hx]
  rw [Finset.sum_sdiff (Finset.subset_univ X.vertexSet)]

theorem weighted_degree_bLayer (hCubic : ∀ v, H.degree v = 3) (a : Fin 3) (w : V → ℕ) :
    ∑ v, w v * H.degreeIn (g.bLayer a) v =
      2 * (∑ v ∈ Finset.univ \ X.vertexSet, w v) +
        ∑ i : Fin 6, if hexWord (i + g.r) ≠ a then w (X.v i) else 0 := by
  rw [sum_vertex_partition (X := X)]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvo : ∀ i, v ≠ X.v i := fun i hi ↦
      (Finset.mem_sdiff.mp hv).2 (X.mem_vertexSet.mpr ⟨i, hi.symm⟩)
    rw [g.degree_bLayer_off hCubic a hvo, Nat.mul_comm]
  · apply Finset.sum_congr rfl
    intro i _
    rw [g.degree_bLayer_core hCubic]
    split_ifs <;> simp

/-- Desired outgoing parity in the bicoloured exterior subgraph. -/
noncomputable def orientationTarget (a : Fin 3) (w : V) : F₂ :=
  if hw : ∃ i, X.v i = w then (if isSource g.r a hw.choose then 1 else 0) else 1

omit [DecidableEq E] in
theorem orientationTarget_core (a : Fin 3) (i : Fin 6) :
    g.orientationTarget a (X.v i) = if isSource g.r a i then 1 else 0 := by
  unfold orientationTarget
  rw [dif_pos ⟨i, rfl⟩]
  have hi := X.v_injective (Exists.choose_spec (show ∃ j, X.v j = X.v i from ⟨i, rfl⟩))
  rw [hi]

omit [DecidableEq E] in
theorem orientationTarget_off (a : Fin 3) {w : V} (hw : ∀ i, w ≠ X.v i) :
    g.orientationTarget a w = 1 := by
  simp [orientationTarget, fun i ↦ (hw i).symm]

/-- Noncolourability rules out precisely the terminal selections that would obstruct the
binary orientation equation. -/
theorem orientation_cut_condition (hCubic : ∀ v, H.degree v = 3)
    (hnc : ¬ ∃ f : E → Color, H.ProperOff ∅ f) (a : Fin 3) (c : V → F₂)
    (hc : ∀ e ∈ g.bLayer a, c (H.endAt e 0) = c (H.endAt e 1)) :
    ∑ v, c v * g.orientationTarget a v = ∑ e ∈ g.bLayer a, c (H.endAt e 0) := by
  let w : V → ℕ := fun v ↦ if c v = 1 then 1 else 0
  let m := ∑ v ∈ Finset.univ \ X.vertexSet, w v
  let t := ∑ i : Fin 6, if hexWord (i + g.r) ≠ a then w (X.v i) else 0
  let s := ∑ i : Fin 6, if isSource g.r a i = true then w (X.v i) else 0
  let n := ∑ e ∈ g.bLayer a, w (H.endAt e 0)
  have hw (v : V) : (w v : F₂) = c v := by
    rcases (show ∀ z : F₂, z = 0 ∨ z = 1 by decide) (c v) with h | h <;> simp [w, h]
  have hcount : 2 * m + t = 2 * n := by
    calc
      2 * m + t = ∑ v, w v * H.degreeIn (g.bLayer a) v :=
        (g.weighted_degree_bLayer hCubic a w).symm
      _ = ∑ e ∈ g.bLayer a, (w (H.endAt e 0) + w (H.endAt e 1)) := H.sum_mul_degreeIn _ w
      _ = 2 * n := by
        dsimp [n]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [w, ← hc e he, two_mul]
  have heven : t % 2 = 0 := by omega
  have hpar : s % 2 = (t / 2) % 2 := by
    have ht : (∑ i : Fin 6,
        if hexWord (i + g.r) ≠ a ∧ (decide (c (X.v i) = 1)) = true then 1 else 0) % 2 = 0 := by
      simpa only [decide_eq_true_eq, ite_and] using heven
    rcases terminal_parity_cases g.r a (fun i ↦ decide (c (X.v i) = 1)) ht with h | h | h
    · simpa only [decide_eq_true_eq, ite_and] using h
    · exact (hnc (g.colourable_of_bad_terminals hCubic a c hc false (by
        intro i hi
        have hh := congrArg (fun b : Bool ↦ b = true) (h i hi)
        simpa only [decide_eq_true_eq, selectedTerminal, Bool.false_eq_true, if_false]
          using Iff.of_eq hh))).elim
    · exact (hnc (g.colourable_of_bad_terminals hCubic a c hc true (by
        intro i hi
        have hh := congrArg (fun b : Bool ↦ b = true) (h i hi)
        simpa only [decide_eq_true_eq, selectedTerminal, if_true] using Iff.of_eq hh))).elim
  have hn : n = m + t / 2 := by omega
  have hs : (s : F₂) = ((t / 2 : ℕ) : F₂) := (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr hpar
  have hoff : (∑ v ∈ Finset.univ \ X.vertexSet, c v * g.orientationTarget a v) = (m : F₂) := by
    dsimp [m]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvo : ∀ i, v ≠ X.v i := fun i hi ↦
      (Finset.mem_sdiff.mp hv).2 (X.mem_vertexSet.mpr ⟨i, hi.symm⟩)
    rw [g.orientationTarget_off a hvo, mul_one, hw]
  have hcore : (∑ i : Fin 6, c (X.v i) * g.orientationTarget a (X.v i)) = (s : F₂) := by
    dsimp [s]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [g.orientationTarget_core]
    by_cases hi : isSource g.r a i = true <;> simp [hi, hw]
  have hedge : (∑ e ∈ g.bLayer a, c (H.endAt e 0)) = (n : F₂) := by
    dsimp [n]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e _ ↦ (hw _).symm
  rw [sum_vertex_partition (X := X), hoff, hcore, hedge, hs, ← Nat.cast_add, ← hn]

/-- The exterior bicoloured subgraph admits the required outgoing parity. -/
theorem exists_exterior_orientation (hCubic : ∀ v, H.degree v = 3)
    (hnc : ¬ ∃ f : E → Color, H.ProperOff ∅ f) (a : Fin 3) :
    ∃ tail : E → Fin 2, ∀ v, H.outParity (g.bLayer a) tail v = g.orientationTarget a v :=
  H.exists_orientation_of_parity _ _ (g.orientation_cut_condition hCubic hnc a)

private theorem opposite_of_outParity {F : Finset E} {tail : E → Fin 2} {w : V}
    (hdeg : H.degreeIn F w = 2) (hp : H.outParity F tail w = 1)
    (x y : H.halfEdgesAt w) (hxy : x ≠ y) (hx : x.1.1 ∈ F) (hy : y.1.1 ∈ F) :
    (x.1.2 = tail x.1.1 ↔ ¬ (y.1.2 = tail y.1.1)) := by
  let S := Finset.univ.filter fun z : H.halfEdgesAt w ↦ z.1.1 ∈ F
  have hS : S = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [S, hx, hy]
    · rw [show S.card = 2 from (H.degreeIn_eq_card_halfEdges F w).symm.trans hdeg,
        Finset.card_pair hxy]
  have hout : (Finset.univ.filter fun z : H.halfEdgesAt w ↦
      z.1.1 ∈ F ∧ z.1.2 = tail z.1.1).card =
      (if x.1.2 = tail x.1.1 then 1 else 0) + (if y.1.2 = tail y.1.1 then 1 else 0) := by
    rw [← Finset.filter_filter]
    change (S.filter fun z ↦ z.1.2 = tail z.1.1).card = _
    rw [hS, Finset.filter_insert, Finset.filter_singleton]
    by_cases hx' : x.1.2 = tail x.1.1 <;> by_cases hy' : y.1.2 = tail y.1.1 <;>
      simp [hx', hy', hxy]
  rw [H.outParity_eq_card_halfEdges, hout] at hp
  by_cases hx' : x.1.2 = tail x.1.1 <;> by_cases hy' : y.1.2 = tail y.1.1 <;>
    simp_all
  exact (show (2 : F₂) ≠ 1 by decide) hp

noncomputable def orientationWithCore (a : Fin 3) (tail : E → Fin 2) (e : E) : Fin 2 :=
  if he : ∃ i, X.h i = e then coreTail g.r a he.choose else tail e

omit [DecidableEq V] in
theorem orientationWithCore_h (a : Fin 3) (tail : E → Fin 2) (i : Fin 6) :
    g.orientationWithCore a tail (X.h i) = coreTail g.r a i := by
  unfold orientationWithCore
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact X.h_injective (Exists.choose_spec (show ∃ j, X.h j = X.h i from ⟨i, rfl⟩))

omit [DecidableEq V] in
theorem orientationWithCore_off (a : Fin 3) (tail : E → Fin 2) {e : E}
    (he : ∀ i, e ≠ X.h i) : g.orientationWithCore a tail e = tail e := by
  simp [orientationWithCore, fun i ↦ (he i).symm]

theorem spoke_out_iff (hCubic : ∀ v, H.degree v = 3) (a : Fin 3) (tail : E → Fin 2)
    (hp : ∀ w, H.outParity (g.bLayer a) tail w = g.orientationTarget a w)
    (i : Fin 6) (hi : a ≠ hexWord (i + g.r)) :
    (X.side i = tail (X.spoke i)) ↔ isSource g.r a i = true := by
  have hv := hp (X.v i)
  rw [H.outParity_eq_card_halfEdges, g.orientationTarget_core,
    card_filter_of_three (X.hex0 i) (X.hex1 i) (X.spokeHalf i)
      (X.hex0_ne_hex1 i) (X.hex0_ne_spokeHalf i) (X.hex1_ne_spokeHalf i)
      (X.halfEdge_cases hCubic i)] at hv
  simp only [hex0, hex1, spokeHalf, g.h_notin_bLayer, false_and, if_false, zero_add,
    g.spoke_mem_bLayer] at hv
  by_cases hs : X.side i = tail (X.spoke i) <;>
    by_cases ht : isSource g.r a i = true <;> simp_all

/-- Construct the three auxiliary orientations from cubicity and noncolourability. -/
theorem exists_orientations (hCubic : ∀ v, H.degree v = 3)
    (hnc : ¬ ∃ f : E → Color, H.ProperOff ∅ f) : Nonempty (X.Orientations g) := by
  choose tail hp using g.exists_exterior_orientation hCubic hnc
  refine ⟨{
    o := fun a ↦ g.orientationWithCore a (tail a)
    exterior := ?_
    core_own := ?_
    core_other := ?_ }⟩
  · intro a w hw x y hxy hx hy
    have hxo := halfEdge_not_h hw x
    have hyo := halfEdge_not_h hw y
    have hxP : x.1.1 ∈ g.bLayer a :=
      (g.mem_bLayer_iff hxo).mpr ((X.mem_K_of_not_h g hxo a).mp hx)
    have hyP : y.1.1 ∈ g.bLayer a :=
      (g.mem_bLayer_iff hyo).mpr ((X.mem_K_of_not_h g hyo a).mp hy)
    rw [g.orientationWithCore_off a (tail a) hxo, g.orientationWithCore_off a (tail a) hyo]
    exact opposite_of_outParity (g.degree_bLayer_off hCubic a hw)
      ((hp a w).trans (g.orientationTarget_off a hw)) x y hxy hxP hyP
  · intro i
    simp only [g.orientationWithCore_h]
    exact coreTail_own g.r i
  · intro i a hi
    simp only [g.orientationWithCore_h, g.orientationWithCore_off a (tail a) (X.spoke_ne_h i)]
    obtain ⟨hcore, hsource⟩ := coreTail_other g.r i a hi
    exact ⟨hcore, (g.spoke_out_iff hCubic a (tail a) (hp a) i hi).trans hsource⟩

include g in
/-- An induced hexagonal exterior colouring in a noncolourable cubic graph gives an o5CDC.
No auxiliary orientation is assumed. The core is an entire member of the cover. -/
theorem exists_oriented_five_cover (hCubic : ∀ v, H.degree v = 3)
    (hnc : ¬ ∃ f : E → Color, H.ProperOff ∅ f) :
    ∃ D : H.OrientedCycleDoubleCover 5, D.Contains X.edgeSet := by
  obtain ⟨O⟩ := exists_orientations g hCubic hnc
  exact O.exists_orientedCover hCubic

end ExteriorColoring
end Hexagon
end LoopMultigraph
end GraphPuzzles
