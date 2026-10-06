import GraphPuzzles.CycleCovers.StrongProperties
import GraphPuzzles.DefectThree.HexagonMatching

/-!
# Strong five-cycle double covers from a single hexagonal core

The prescribed circuit is a component of an even layer. In the unequal-spoke intersection
case the layer may include a vertex-disjoint even companion. Binary T-joins supply that
companion; failure of the T-join condition supplies a recolouring of one terminal incidence.
Repeated outer endpoints are allowed throughout.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace Hexagon
namespace ExteriorColoring

variable {X : H.Hexagon} (g : X.ExteriorColoring)

/-- Toggle the complement of a completed colour matching by the prescribed even set. -/
noncomputable def strongLayer (F : Finset E) (a : Fin 3) : Finset E :=
  Finset.univ.filter fun e ↦
    (if e ∈ F then (1 : F₂) else 0) +
      (if e ∈ Finset.univ \ g.matchingSet a then 1 else 0) = 1

theorem strongLayer_even (hCubic : ∀ v, H.degree v = 3) {F : Finset E}
    (hF : H.IsEvenEdgeSet F) (a : Fin 3) : H.IsEvenEdgeSet (g.strongLayer F a) := by
  intro w
  change H.boundary _ w = 0
  rw [strongLayer, H.boundary_filter_eq]
  simp only [add_mul, Finset.sum_add_distrib, sum_indicator_mul]
  change H.boundary F w + H.boundary (Finset.univ \ g.matchingSet a) w = 0
  have hFw : H.boundary F w = 0 := hF w
  rw [hFw, zero_add, H.boundary_sdiff (Finset.subset_univ _),
    H.boundary_eq_degreeIn_cast, H.boundary_eq_degreeIn_cast,
    g.matchingSet_perfect hCubic a w, H.degreeIn_eq_card_halfEdges]
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ]
  change (H.degree w : F₂) + 1 = 0
  rw [hCubic w]
  decide

/-- The explicit five-layer construction for an even set using exactly the three
unequal-spoke edges of the hexagon. The two final layers are `F` and the hexagon. -/
theorem exists_fiveCover_of_alternating (hCubic : ∀ v, H.degree v = 3)
    (F : Finset E) (hF : H.IsEvenEdgeSet F)
    (hcore : ∀ i, X.h i ∈ F ↔ ¬ g.PairAt i) :
    ∃ D : H.CycleDoubleCover 5, D.Contains F ∧ D.Contains X.edgeSet := by
  let layers : Fin 5 → H.EvenSubgraph :=
    ![⟨g.strongLayer F 0, g.strongLayer_even hCubic hF 0⟩,
      ⟨g.strongLayer F 1, g.strongLayer_even hCubic hF 1⟩,
      ⟨g.strongLayer F 2, g.strongLayer_even hCubic hF 2⟩,
      ⟨F, hF⟩, ⟨X.edgeSet, X.edgeSet_even hCubic⟩]
  have twice : ∀ e, (Finset.univ.filter fun k ↦ e ∈ (layers k).edges).card = 2 := by
    intro e
    rw [Finset.card_filter]
    simp only [Fin.sum_univ_succ, layers, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    by_cases he : ∃ i, X.h i = e
    · obtain ⟨i, rfl⟩ := he
      simp only [strongLayer, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, g.h_mem_matchingSet, hcore, X.h_mem_edgeSet, if_true]
      have tab : ∀ (b : Bool) (a : Fin 3),
          (if (if !b then (1 : F₂) else 0) + (if ¬ (b = true ∧ 0 ≠ a) then 1 else 0) = 1 then 1 else 0) +
          ((if (if !b then (1 : F₂) else 0) + (if ¬ (b = true ∧ 1 ≠ a) then 1 else 0) = 1 then 1 else 0) +
          ((if (if !b then (1 : F₂) else 0) + (if ¬ (b = true ∧ 2 ≠ a) then 1 else 0) = 1 then 1 else 0) +
          ((if !b then 1 else 0) + 1))) = (2 : ℕ) := by decide
      simpa using tab (decide (g.PairAt i)) (hexWord (i + g.r))
    · have hn : ∀ i, e ≠ X.h i := fun i h ↦ he ⟨i, h.symm⟩
      have hne : e ∉ X.edgeSet := fun h ↦ he (X.mem_edgeSet.mp h)
      simp only [strongLayer, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, g.mem_matchingSet_of_not_h _ hn, hne, if_false, add_zero]
      generalize g.idx (g.color e) = a
      by_cases h : e ∈ F <;> fin_cases a <;> simp [h]
  exact ⟨⟨layers, twice⟩, ⟨3, rfl⟩, ⟨4, rfl⟩⟩

end ExteriorColoring

/-! The four terminals left after deleting positions `j` and `j + 1`. -/

def terminal (j : Fin 6) (t : Fin 4) : Fin 6 := j + ⟨t.val + 2, by omega⟩

theorem terminal_injective (j : Fin 6) : Function.Injective (terminal j) := by
  revert j
  decide

theorem terminal_ne (j : Fin 6) (t : Fin 4) :
    terminal j t ≠ j ∧ terminal j t ≠ j + 1 := by
  revert j t
  decide

theorem exists_terminal (j i : Fin 6) (hi : ¬ (i = j ∨ i = j + 1)) :
    ∃ t, terminal j t = i := by
  revert j i
  decide

/-- Four odd binary terminal values have a unique value on one side of the separation. -/
theorem four_terminal_odd (p : Fin 4 → F₂) (hp : ∑ t, p t ≠ 0) :
    ∃ t, ∀ s, p s = p t ↔ s = t := by
  revert p
  decide

section Companion

variable (X : H.Hexagon) (j : Fin 6)

/-- The four surviving spokes and the two alternating edges joining their core ends. -/
def companionFrame : Finset E :=
  (Finset.univ.image fun t ↦ X.spoke (terminal j t)) ∪ {X.h (j + 2), X.h (j + 4)}

omit [DecidableEq V] in
theorem h_mem_companionFrame (i : Fin 6) :
    X.h i ∈ X.companionFrame j ↔ i = j + 2 ∨ i = j + 4 := by
  simp [companionFrame, X.h_injective.eq_iff, fun t ↦ X.spoke_ne_h (terminal j t) i]

omit [DecidableEq V] in
theorem spoke_mem_companionFrame (i : Fin 6) :
    X.spoke i ∈ X.companionFrame j ↔ ¬ (i = j ∨ i = j + 1) := by
  simp only [companionFrame, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton, X.spoke_ne_h, or_false,
    X.spoke_injective.eq_iff]
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ not_or.mpr (terminal_ne j t), exists_terminal j i⟩

theorem companionFrame_even_at (hCubic : ∀ v, H.degree v = 3) (i : Fin 6) :
    H.boundary (X.companionFrame j) (X.v i) = 0 := by
  rw [X.boundary_at_vertex hCubic]
  simp only [X.h_mem_companionFrame, X.spoke_mem_companionFrame]
  exact (show ∀ j i : Fin 6,
    (if i = j + 2 ∨ i = j + 4 then (1 : F₂) else 0) +
      ((if i - 1 = j + 2 ∨ i - 1 = j + 4 then 1 else 0) +
        (if ¬ (i = j ∨ i = j + 1) then 1 else 0)) = 0 by decide) j i

theorem companionFrame_boundary_off {w : V} (hw : ∀ i, w ≠ X.v i) :
    H.boundary (X.companionFrame j) w =
      ∑ t, if X.far (terminal j t) = w then (1 : F₂) else 0 := by
  have hd : Disjoint (Finset.univ.image fun t ↦ X.spoke (terminal j t))
      {X.h (j + 2), X.h (j + 4)} := by
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rintro e ⟨t, rfl⟩ (he | he)
    · exact X.spoke_ne_h _ _ he
    · exact X.spoke_ne_h _ _ he
  rw [companionFrame, H.boundary_union _ _ hd]
  have hz : H.boundary {X.h (j + 2), X.h (j + 4)} w = 0 :=
    X.boundary_eq_zero_of_subset_edgeSet (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> exact X.h_mem_edgeSet _) hw
  rw [hz, add_zero, boundary, Finset.sum_image]
  · exact Finset.sum_congr rfl (fun t _ ↦ X.edgeIncidence_spoke hw (terminal j t))
  · exact fun a _ b _ h ↦ terminal_injective j (X.spoke_injective h)

theorem companionFrame_avoids (C : H.OrdinaryCircuit)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
    (hfar : ∀ t, X.far (terminal j t) ∉ H.edgeSupport C.edges) :
    ∀ e ∈ X.companionFrame j, ∀ k, H.endAt e k ∉ H.edgeSupport C.edges := by
  intro e he k
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    by_cases hk : k = X.side (terminal j t)
    · rw [hk, X.spoke_end, hT]
      exact not_or.mpr (terminal_ne j t)
    · have hk' : k = Fin.rev (X.side (terminal j t)) := by
        have : ∀ a b : Fin 2, a ≠ b → a = Fin.rev b := by decide
        exact this k _ hk
      rw [hk']
      exact hfar t
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    have hk : k = 0 ∨ k = 1 := (show ∀ k : Fin 2, k = 0 ∨ k = 1 by decide) k
    rcases he with rfl | rfl <;> rcases hk with rfl | rfl
    · rw [X.h_end0, hT]
      exact (show ∀ j : Fin 6, ¬ (j + 2 = j ∨ j + 2 = j + 1) by decide) j
    · rw [X.h_end1, hT]
      exact (show ∀ j : Fin 6, ¬ (j + 2 + 1 = j ∨ j + 2 + 1 = j + 1) by decide) j
    · rw [X.h_end0, hT]
      exact (show ∀ j : Fin 6, ¬ (j + 4 = j ∨ j + 4 = j + 1) by decide) j
    · rw [X.h_end1, hT]
      exact (show ∀ j : Fin 6, ¬ (j + 4 + 1 = j ∨ j + 4 + 1 = j + 1) by decide) j

/-- Even parity on each free component supplies an even companion disjoint from the circuit. -/
theorem exists_even_companion (hCubic : ∀ v, H.degree v = 3) (C : H.OrdinaryCircuit)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
    (hfar : ∀ t, X.far (terminal j t) ∉ H.edgeSupport C.edges)
    (hpar : ∀ c : V → F₂,
      (∀ e ∈ X.freeEdges C, c (H.endAt e 0) = c (H.endAt e 1)) →
        ∑ t, c (X.far (terminal j t)) = 0) :
    ∃ D : Finset E, H.IsEvenEdgeSet D ∧
      (∀ e ∈ D, ∀ k, H.endAt e k ∉ H.edgeSupport C.edges) ∧
      (∀ i, X.h i ∈ D ↔ i = j + 2 ∨ i = j + 4) := by
  obtain ⟨R, hR, hbd⟩ := H.exists_boundary_eq (X.freeEdges C)
    (fun w ↦ ∑ t, if X.far (terminal j t) = w then (1 : F₂) else 0) (by
      intro c hc
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        using hpar c hc)
  have hd : Disjoint R (X.companionFrame j) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      exact X.spoke_notin_freeEdges C _ (hR he)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl <;>
        exact X.h_notin_freeEdges C _ (hR he)
  refine ⟨R ∪ X.companionFrame j, ?_, ?_, ?_⟩
  · intro w
    change H.boundary _ w = 0
    rw [H.boundary_union _ _ hd, hbd]
    by_cases hw : ∃ i, X.v i = w
    · obtain ⟨i, rfl⟩ := hw
      rw [X.companionFrame_even_at j hCubic]
      simp [X.far_ne_v]
    · have hw' : ∀ i, w ≠ X.v i := fun i hi ↦ hw ⟨i, hi.symm⟩
      rw [X.companionFrame_boundary_off j hw']
      exact F₂_add_self _
  · intro e he k
    rcases Finset.mem_union.mp he with he | he
    · exact ((X.mem_freeEdges C).mp (hR he) k).1
    · exact X.companionFrame_avoids j C hT hfar e he k
  · intro i
    have hi : X.h i ∉ R := fun hi ↦ X.h_notin_freeEdges C i (hR hi)
    simp only [Finset.mem_union, hi, false_or, X.h_mem_companionFrame]

end Companion

section Patch

variable {X : H.Hexagon} (C : H.OrdinaryCircuit) (g : X.ExteriorColoring)
  (π : V → Equiv.Perm (Fin 3))

/-- Choose the permutation at a free endpoint. It agrees at both endpoints of every free edge. -/
noncomputable def freeEdgePerm (e : E) : Equiv.Perm (Fin 3) :=
  if X.IsFree C (H.endAt e 0) then π (H.endAt e 0)
  else if X.IsFree C (H.endAt e 1) then π (H.endAt e 1) else 1

theorem freeEdgePerm_at
    (hπ : ∀ e ∈ X.freeEdges C, π (H.endAt e 0) = π (H.endAt e 1))
    {e : E} {w : V} (hw : X.IsFree C w) {k : Fin 2} (hk : H.endAt e k = w) :
    freeEdgePerm (X := X) C π e = π w := by
  unfold freeEdgePerm
  have hcases : k = 0 ∨ k = 1 := (show ∀ k : Fin 2, k = 0 ∨ k = 1 by decide) k
  by_cases h0 : X.IsFree C (H.endAt e 0)
  · rw [if_pos h0]
    rcases hcases with rfl | rfl
    · rw [hk]
    · have h1 : X.IsFree C (H.endAt e 1) := by rw [hk]; exact hw
      rw [hπ e (X.mem_freeEdges_of_isFree C h0 h1), hk]
  · rw [if_neg h0]
    rcases hcases with rfl | rfl
    · exact absurd (by rw [hk]; exact hw) h0
    · have h1 : X.IsFree C (H.endAt e 1) := by rw [hk]; exact hw
      rw [if_pos h1, hk]

/-- Recolour the exterior by component permutations and prescribe new hexagon colours. -/
noncomputable def patchColor (f : Fin 6 → Fin 3) (e : E) : Color :=
  if hi : ∃ i, e = X.h i then g.c (f hi.choose)
  else g.c (freeEdgePerm (X := X) C π e (g.idx (g.color e)))

theorem patchColor_h (f : Fin 6 → Fin 3) (i : Fin 6) :
    patchColor C g π f (X.h i) = g.c (f i) := by
  have hi : ∃ k, X.h i = X.h k := ⟨i, rfl⟩
  unfold patchColor
  rw [dif_pos hi]
  congr 2
  exact X.h_injective hi.choose_spec.symm

theorem patchColor_off (f : Fin 6 → Fin 3) {e : E} (he : ∀ i, e ≠ X.h i) :
    patchColor C g π f e = g.c (freeEdgePerm (X := X) C π e (g.idx (g.color e))) := by
  unfold patchColor
  rw [dif_neg (fun ⟨i, hi⟩ ↦ he i hi)]

theorem patchColor_properOff (hCubic : ∀ v, H.degree v = 3)
    (hπ : ∀ e ∈ X.freeEdges C, π (H.endAt e 0) = π (H.endAt e 1))
    (f s : Fin 6 → Fin 3)
    (hspoke : ∀ i, X.v i ∉ H.edgeSupport C.edges → X.far i ∉ H.edgeSupport C.edges →
      π (X.far i) (hexWord (i + g.r)) = s i)
    (hlocal : ∀ i, X.v i ∉ H.edgeSupport C.edges →
      f i ≠ s i ∧ f (i - 1) ≠ s i ∧ f (i - 1) ≠ f i) :
    H.ProperOff (H.edgeSupport C.edges) (patchColor C g π f) := by
  refine ⟨?_, ?_⟩
  · intro e _
    unfold patchColor
    split <;> exact g.c_ne_zero _
  · intro w hw x y hx hy heq
    by_cases hwv : ∃ i, X.v i = w
    · obtain ⟨i, rfl⟩ := hwv
      have v0 : patchColor C g π f (X.hex0 i).1.1 = g.c (f i) := patchColor_h C g π f i
      have v1 : patchColor C g π f (X.hex1 i).1.1 = g.c (f (i - 1)) :=
        patchColor_h C g π f (i - 1)
      have v2 : ∀ z : H.halfEdgesAt (X.v i), z = X.spokeHalf i →
          (∀ k, H.endAt z.1.1 k ∉ H.edgeSupport C.edges) →
          patchColor C g π f z.1.1 = g.c (s i) := by
        rintro z rfl hz
        have hf : X.far i ∉ H.edgeSupport C.edges := hz (Fin.rev (X.side i))
        change patchColor C g π f (X.spoke i) = g.c (s i)
        rw [patchColor_off C g π f (X.spoke_ne_h i), g.spoke_color, g.idx_c,
          freeEdgePerm_at C π hπ ⟨hf, X.far_ne_v i⟩ (k := Fin.rev (X.side i)) rfl]
        exact congrArg g.c (hspoke i hw hf)
      obtain ⟨d0, d1, d2⟩ := hlocal i hw
      rcases X.halfEdge_cases hCubic i x with hx' | hx' | hx' <;>
        rcases X.halfEdge_cases hCubic i y with hy' | hy' | hy'
      · exact hx'.trans hy'.symm
      · rw [hx', hy', v0, v1] at heq
        exact absurd (g.c_injective heq).symm d2
      · rw [hx', v0, v2 y hy' hy] at heq
        exact absurd (g.c_injective heq) d0
      · rw [hx', hy', v1, v0] at heq
        exact absurd (g.c_injective heq) d2
      · exact hx'.trans hy'.symm
      · rw [hx', v1, v2 y hy' hy] at heq
        exact absurd (g.c_injective heq) d1
      · rw [hy', v2 x hx' hx, v0] at heq
        exact absurd (g.c_injective heq).symm d0
      · rw [hy', v2 x hx' hx, v1] at heq
        exact absurd (g.c_injective heq).symm d1
      · exact hx'.trans hy'.symm
    · have hw' : ∀ i, w ≠ X.v i := fun i hi ↦ hwv ⟨i, hi.symm⟩
      have xf := ExteriorColoring.halfEdge_not_h hw' x
      have yf := ExteriorColoring.halfEdge_not_h hw' y
      rw [patchColor_off C g π f xf, patchColor_off C g π f yf,
        freeEdgePerm_at C π hπ ⟨hw, hw'⟩ x.2,
        freeEdgePerm_at C π hπ ⟨hw, hw'⟩ y.2] at heq
      have hidx := (π w).injective (g.c_injective heq)
      have hcol := congrArg g.c hidx
      rw [g.c_idx (g.nonzero _ xf), g.c_idx (g.nonzero _ yf)] at hcol
      exact g.injective_at w x y xf yf hcol

end Patch

section RepairTable

/-- The new colour of the one affected terminal, in coordinates based at the shared edge. -/
def repairNew : Fin 4 → Fin 3 := ![0, 1, 0, 1]

def repairSpoke (t : Fin 4) (q : Fin 6) : Fin 3 :=
  if q = terminal 0 t then repairNew t else hexWord (q + 1)

/-- Four path-colouring rows, completed at the two deleted boundary edges for convenience. -/
def repairEdge : Fin 4 → Fin 6 → Fin 3 :=
  ![![0, 2, 1, 0, 1, 2], ![0, 0, 2, 0, 1, 2],
    ![0, 2, 0, 1, 2, 1], ![0, 2, 0, 1, 0, 2]]

theorem repair_local (t : Fin 4) (q : Fin 6) (hq : q ≠ 0 ∧ q ≠ 1) :
    repairEdge t q ≠ repairSpoke t q ∧ repairEdge t (q - 1) ≠ repairSpoke t q ∧
      repairEdge t (q - 1) ≠ repairEdge t q := by
  revert t q
  decide

theorem unequal_hexWord (r j i : Fin 6) (hj : ¬ (j + r).val % 2 = 0) :
    hexWord (i + r) = hexWord (j + r) + hexWord (i - j + 1) := by
  revert r j i
  decide

theorem terminal_sub (j : Fin 6) (t : Fin 4) : terminal j t - j = terminal 0 t := by
  revert j t
  decide

theorem sub_ne_of_surviving (j i : Fin 6) (hi : ¬ (i = j ∨ i = j + 1)) :
    i - j ≠ 0 ∧ i - j ≠ 1 := by
  revert j i
  decide

end RepairTable

section Repair

variable {X : H.Hexagon} (g : X.ExteriorColoring) (C : H.OrdinaryCircuit) (j : Fin 6)

/-- Applying a row of the local table after a coherent exterior permutation gives an
entire-layer extension of the circuit. -/
theorem exists_fiveCover_of_terminal_perms (hCubic : ∀ v, H.degree v = 3)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
    (t : Fin 4) (π : V → Equiv.Perm (Fin 3))
    (hπ : ∀ e ∈ X.freeEdges C, π (H.endAt e 0) = π (H.endAt e 1))
    (hterm : ∀ s, X.far (terminal j s) ∉ H.edgeSupport C.edges →
      π (X.far (terminal j s)) (hexWord (terminal j s + g.r)) =
        pc g j (repairSpoke t (terminal 0 s))) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  apply C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_properOff hCubic
  apply patchColor_properOff C g π hCubic hπ
    (fun i ↦ pc g j (repairEdge t (i - j))) (fun i ↦ pc g j (repairSpoke t (i - j)))
  · intro i hi hf
    obtain ⟨s, rfl⟩ := exists_terminal j i (fun h ↦ hi ((hT i).mpr h))
    rw [terminal_sub]
    exact hterm s hf
  · intro i hi
    have hq := sub_ne_of_surviving j i (fun h ↦ hi ((hT i).mpr h))
    obtain ⟨d0, d1, d2⟩ := repair_local t (i - j) hq
    rw [sub_right_comm i 1 j]
    exact ⟨fun h ↦ d0 (pc_injective g j h), fun h ↦ d1 (pc_injective g j h),
      fun h ↦ d2 (pc_injective g j h)⟩

/-- A missing terminal spoke removes the only constraint changed by its repair row. -/
theorem exists_fiveCover_of_missing_terminal (hCubic : ∀ v, H.degree v = 3)
    (hj : ¬ g.PairAt j)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
    (t : Fin 4) (ht : X.far (terminal j t) ∈ H.edgeSupport C.edges) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  apply exists_fiveCover_of_terminal_perms g C j hCubic hT t (fun _ ↦ 1)
    (fun _ _ ↦ rfl)
  intro s hs
  have hst : s ≠ t := by intro h; subst s; exact hs ht
  have hq : terminal 0 s ≠ terminal 0 t := fun h ↦ hst (terminal_injective 0 h)
  simp only [Equiv.Perm.one_apply, repairSpoke, if_neg hq]
  simpa only [pc, terminal_sub] using unequal_hexWord g.r j (terminal j s) hj

/-- A binary separation isolating one terminal incidence allows its colour to be swapped.
The permutation acts on all free vertices on that side, so properness is preserved. -/
theorem exists_fiveCover_of_separated_terminal (hCubic : ∀ v, H.degree v = 3)
    (hj : ¬ g.PairAt j)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
    (c : V → F₂)
    (hc : ∀ e ∈ X.freeEdges C, c (H.endAt e 0) = c (H.endAt e 1))
    (t : Fin 4) (ht : ∀ s, c (X.far (terminal j s)) = c (X.far (terminal j t)) ↔ s = t) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  let π : V → Equiv.Perm (Fin 3) := fun w ↦
    if c w = c (X.far (terminal j t)) then
      Equiv.swap (hexWord (terminal j t + g.r)) (pc g j (repairNew t)) else 1
  have hπ : ∀ e ∈ X.freeEdges C, π (H.endAt e 0) = π (H.endAt e 1) := by
    intro e he
    simp only [π, hc e he]
  apply exists_fiveCover_of_terminal_perms g C j hCubic hT t π hπ
  intro s _
  by_cases hst : s = t
  · subst s
    simp [π, repairSpoke, Equiv.swap_apply_left]
  · have hn := (ht s).not.mpr hst
    have hq : terminal 0 s ≠ terminal 0 t := fun h ↦ hst (terminal_injective 0 h)
    simp only [π, if_neg hn, Equiv.Perm.one_apply, repairSpoke, if_neg hq]
    simpa only [pc, terminal_sub] using unequal_hexWord g.r j (terminal j s) hj

end Repair

section Assembly

variable {X : H.Hexagon}

/-- The previously missing single-core case: a circuit sharing the endpoints of an
unequal-spoke edge is a component of a layer of a five-cycle double cover. -/
theorem exists_fiveCycleDoubleCover_of_unequal (hCubic : ∀ v, H.degree v = 3)
    (g : X.ExteriorColoring) (C : H.OrdinaryCircuit) (j : Fin 6) (hj : ¬ g.PairAt j)
    (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1)) :
    ∃ D : H.CycleDoubleCover 5, D.ContainsComponent C := by
  classical
  by_cases hfar : ∀ t, X.far (terminal j t) ∉ H.edgeSupport C.edges
  · by_cases hpar : ∀ c : V → F₂,
        (∀ e ∈ X.freeEdges C, c (H.endAt e 0) = c (H.endAt e 1)) →
          ∑ t, c (X.far (terminal j t)) = 0
    · obtain ⟨F, hF, havoid, hcore⟩ := X.exists_even_companion j hCubic C hT hfar hpar
      have hdisj : Disjoint C.edges F := by
        apply Finset.disjoint_left.mpr
        intro e he hf
        exact havoid e hf 0 (H.mem_edgeSupport_iff.mpr ⟨e, he, 0, rfl⟩)
      have hCF : H.IsEvenEdgeSet (C.edges ∪ F) := by
        intro w
        change H.boundary _ w = 0
        rw [H.boundary_union _ _ hdisj]
        have hc : H.boundary C.edges w = 0 := OrdinaryCircuit.even H C w
        have hf : H.boundary F w = 0 := hF w
        rw [hc, hf, zero_add]
      have hCcore : ∀ i, X.h i ∈ C.edges ↔ i = j := by
        intro i
        exact ⟨fun h ↦ by
          by_contra hn
          exact X.h_notin_C_of_ne j C hT hn h,
          fun h ↦ by subst i; exact X.e_mem_C j C hT hCubic⟩
      have hpattern : ∀ i, X.h i ∈ C.edges ∪ F ↔ ¬ g.PairAt i := by
        intro i
        rw [Finset.mem_union, hCcore, hcore]
        exact (show ∀ r j i : Fin 6, ¬ (j + r).val % 2 = 0 →
          ((i = j ∨ i = j + 2 ∨ i = j + 4) ↔ ¬ (i + r).val % 2 = 0) by decide) g.r j i hj
      obtain ⟨D, hD, _⟩ := g.exists_fiveCover_of_alternating hCubic (C.edges ∪ F) hCF hpattern
      exact ⟨D, D.containsComponent_of_contains_union C F hD havoid⟩
    · push Not at hpar
      obtain ⟨c, hc, hodd⟩ := hpar
      obtain ⟨t, ht⟩ := four_terminal_odd (fun t ↦ c (X.far (terminal j t))) hodd
      obtain ⟨D, hD⟩ := exists_fiveCover_of_separated_terminal g C j hCubic hj hT c hc t ht
      exact ⟨D, hD.containsComponent⟩
  · push Not at hfar
    obtain ⟨t, ht⟩ := hfar
    obtain ⟨D, hD⟩ := exists_fiveCover_of_missing_terminal g C j hCubic hj hT t ht
    exact ⟨D, hD.containsComponent⟩

/-- **Single hexagonal core theorem.** Every prescribed circuit is a component of an even
layer of a five-cycle double cover. No non-colourability assumption is needed. -/
theorem ExteriorColoring.hasStrongCycleDoubleCover (g : X.ExteriorColoring)
    (hCubic : ∀ v, H.degree v = 3) : H.HasStrongCycleDoubleCover 5 := by
  intro C
  by_cases hmeet : ∃ i, X.v i ∈ H.edgeSupport C.edges
  · rcases X.meet_cases hCubic C hmeet with h3 | ⟨j, hT⟩
    · obtain ⟨D, hD⟩ := X.exists_fiveCycleDoubleCover_of_three hCubic g C h3
      exact ⟨D, hD.containsComponent⟩
    · by_cases hj : g.PairAt j
      · obtain ⟨D, hD⟩ := X.exists_fiveCycleDoubleCover_of_pair hCubic g C j hj hT
        exact ⟨D, hD.containsComponent⟩
      · exact exists_fiveCycleDoubleCover_of_unequal hCubic g C j hj hT
  · push Not at hmeet
    rcases exists_cover_of_disjoint hCubic g C hmeet with ⟨D, hD⟩ | ⟨_, D, hD⟩
    · exact ⟨D, hD.containsComponent⟩
    · refine ⟨D, D.containsComponent_of_contains_union C X.edgeSet hD ?_⟩
      intro e he k
      obtain ⟨i, rfl⟩ := X.mem_edgeSet.mp he
      rcases (show k = 0 ∨ k = 1 from (by fin_cases k <;> simp)) with rfl | rfl
      · rw [X.h_end0]
        exact hmeet i
      · rw [X.h_end1]
        exact hmeet (i + 1)

end Assembly

end Hexagon
end LoopMultigraph
end GraphPuzzles
