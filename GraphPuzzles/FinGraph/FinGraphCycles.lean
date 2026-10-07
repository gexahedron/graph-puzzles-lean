import GraphPuzzles.FinGraph.FinGraph
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

/-!
# Even edge sets, the forest bound, and small acyclic vertex sets

A vertex set `X` of a `FinGraph` *has a cycle* when it spans a nonempty even edge set.  The
`F₂` rank argument shows that a vertex set spanning no cycle spans fewer edges than it has
vertices.  In a cubic closed graph this gives `|X| + 2 ≤ |∂X|` for nonempty acyclic `X`, so an
acyclic set with boundary at most `4` has at most two vertices.  Two acyclic sets joined by at
most one edge form an acyclic set, and deleting a vertex of internal degree at most one preserves
cycles.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section Degrees

theorem degIn_eq_sum (F : Finset ℕ) (v : ℕ) :
    Γ.degIn F v = ∑ e ∈ F, ((if Γ.ends e 0 = v then 1 else 0) + (if Γ.ends e 1 = v then 1 else 0)) := by
  unfold degIn halfEdgesIn
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fin.sum_univ_two]

theorem degIn_mono {F F' : Finset ℕ} (h : F ⊆ F') (v : ℕ) : Γ.degIn F v ≤ Γ.degIn F' v := by
  unfold degIn halfEdgesIn
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter, Finset.mem_product] at hx ⊢
  exact ⟨⟨h hx.1.1, hx.1.2⟩, hx.2⟩

theorem degIn_union_of_disjoint {F F' : Finset ℕ} (h : Disjoint F F') (v : ℕ) :
    Γ.degIn (F ∪ F') v = Γ.degIn F v + Γ.degIn F' v := by
  rw [degIn_eq_sum, degIn_eq_sum, degIn_eq_sum, Finset.sum_union h]

theorem degIn_eq_zero_iff {F : Finset ℕ} {v : ℕ} :
    Γ.degIn F v = 0 ↔ ∀ e ∈ F, ∀ i, Γ.ends e i ≠ v := by
  unfold degIn
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h e he i hi
    exact h (e, i) (mem_halfEdgesIn.mpr ⟨he, hi⟩)
  · intro h x hx
    rw [mem_halfEdgesIn] at hx
    exact h x.1 hx.1 x.2 hx.2

theorem degIn_le_deg (F : Finset ℕ) (hF : F ⊆ Γ.Es) (v : ℕ) : Γ.degIn F v ≤ Γ.deg v :=
  degIn_mono hF v

theorem degIn_pos_of {F : Finset ℕ} {e : ℕ} {i : Fin 2} (he : e ∈ F) :
    0 < Γ.degIn F (Γ.ends e i) := by
  unfold degIn
  apply Finset.card_pos.mpr
  exact ⟨(e, i), mem_halfEdgesIn.mpr ⟨he, rfl⟩⟩

/-- At a vertex of `X`, the edges of `Es` meeting it lie inside `X` or on its boundary. -/
theorem degIn_edgesIn_add_bd {X : Finset ℕ} {v : ℕ} (hv : v ∈ X) :
    Γ.degIn (Γ.edgesIn X) v + Γ.degIn (Γ.bd X) v = Γ.deg v := by
  unfold deg
  rw [← degIn_union_of_disjoint (disjoint_edgesIn_bd X)]
  unfold degIn halfEdgesIn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_union,
    mem_edgesIn, mem_bd]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨h.elim (fun h ↦ h.1) (fun h ↦ h.1), hx⟩
  · rintro ⟨he, hx⟩
    refine ⟨?_, hx⟩
    by_cases hall : ∀ i, Γ.ends x.1 i ∈ X
    · exact Or.inl ⟨he, hall⟩
    · refine Or.inr ⟨he, fun hiff ↦ hall fun i ↦ ?_⟩
      have hx' : Γ.ends x.1 x.2 ∈ X := hx ▸ hv
      obtain ⟨e, j⟩ := x
      have hj : j = 0 ∨ j = 1 := by omega
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hj with rfl | rfl <;> rcases hi with rfl | rfl
      · exact hx'
      · exact hiff.mp hx'
      · exact hiff.mpr hx'
      · exact hx'

end Degrees

section Rank

/-- The incidence indicator of an edge at a vertex over `F₂`. -/
def inc (v e : ℕ) : F₂ := (if Γ.ends e 0 = v then 1 else 0) + (if Γ.ends e 1 = v then 1 else 0)

theorem even_degIn_iff (F : Finset ℕ) (v : ℕ) :
    Even (Γ.degIn F v) ↔ ∑ e ∈ F, Γ.inc v e = 0 := by
  rw [degIn_eq_sum]
  unfold inc
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  push_cast
  rfl

/-- The boundary of the edges inside `X`, as a linear map over `F₂`. -/
noncomputable def boundaryMap (Γ : FinGraph) (X : Finset ℕ) :
    (Γ.edgesIn X → F₂) →ₗ[F₂] (X → F₂) where
  toFun x v := ∑ e : Γ.edgesIn X, x e * Γ.inc v.1 e.1
  map_add' x y := by
    funext v
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext v
    simp [Finset.mul_sum, mul_assoc]

/-- The sum of the values of a vertex function on `X`. -/
noncomputable def sumMap (X : Finset ℕ) : (X → F₂) →ₗ[F₂] F₂ where
  toFun y := ∑ v, y v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private theorem F₂_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sumMap_boundaryMap (X : Finset ℕ) (x : Γ.edgesIn X → F₂) :
    sumMap X (Γ.boundaryMap X x) = 0 := by
  change ∑ v : X, ∑ e : Γ.edgesIn X, x e * Γ.inc v.1 e.1 = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have hmem := (mem_edgesIn.mp e.2).2
  have : ∑ v : X, Γ.inc v.1 e.1 = 0 := by
    rw [Finset.sum_coe_sort X (fun v ↦ Γ.inc v e.1)]
    unfold inc
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (hmem 0),
      if_pos (hmem 1)]
    decide
  rw [this, mul_zero]

theorem sumMap_surjective {X : Finset ℕ} (hX : X.Nonempty) : Function.Surjective (sumMap X) := by
  obtain ⟨v₀, hv₀⟩ := hX
  intro c
  refine ⟨fun v ↦ if v = ⟨v₀, hv₀⟩ then c else 0, ?_⟩
  change ∑ v : X, (if v = ⟨v₀, hv₀⟩ then c else 0) = c
  simp

/-- A kernel vector of the boundary map selects an even edge set inside `X`. -/
theorem even_of_mem_ker (X : Finset ℕ) {x : Γ.edgesIn X → F₂}
    (hx : x ∈ LinearMap.ker (Γ.boundaryMap X)) :
    Γ.IsEven
      ((Finset.univ.filter fun e : Γ.edgesIn X ↦ x e = 1).map (Function.Embedding.subtype _)) := by
  intro v _
  rw [even_degIn_iff, Finset.sum_map]
  simp only [Function.Embedding.coe_subtype]
  rw [Finset.sum_filter]
  have hsum : ∑ e : Γ.edgesIn X, (if x e = 1 then Γ.inc v e.1 else 0) =
      ∑ e : Γ.edgesIn X, x e * Γ.inc v e.1 := by
    apply Finset.sum_congr rfl
    intro e _
    rcases F₂_eq_zero_or_one (x e) with h | h
    · rw [h, if_neg (by decide), zero_mul]
    · rw [h, if_pos rfl, one_mul]
  rw [hsum]
  by_cases hv : v ∈ X
  · have h0 : Γ.boundaryMap X x = 0 := LinearMap.mem_ker.mp hx
    exact congr_fun h0 ⟨v, hv⟩
  · apply Finset.sum_eq_zero
    intro e _
    have hmem := (mem_edgesIn.mp e.2).2
    have h0 : Γ.ends e.1 0 ≠ v := fun h ↦ hv (h ▸ hmem 0)
    have h1 : Γ.ends e.1 1 ≠ v := fun h ↦ hv (h ▸ hmem 1)
    unfold inc
    rw [if_neg h0, if_neg h1]
    simp

/-- A vertex set spanning no cycle spans fewer edges than it has vertices. -/
theorem card_edgesIn_lt {X : Finset ℕ} (hX : X.Nonempty) (hno : ¬ Γ.HasCycle X) :
    (Γ.edgesIn X).card < X.card := by
  by_contra hle
  push Not at hle
  have hrange : LinearMap.range (Γ.boundaryMap X) ≤ LinearMap.ker (sumMap X) := by
    rintro y ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (sumMap_boundaryMap X x)
  have hS : Module.finrank F₂ (LinearMap.ker (sumMap X)) + 1 = X.card := by
    have h := LinearMap.finrank_range_add_finrank_ker (sumMap X)
    rw [LinearMap.range_eq_top.mpr (sumMap_surjective hX), finrank_top, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (Γ.boundaryMap X)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  have hle' := Submodule.finrank_mono hrange
  have hker : 0 < Module.finrank F₂ (LinearMap.ker (Γ.boundaryMap X)) := by omega
  have hne : LinearMap.ker (Γ.boundaryMap X) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    exact absurd hker (lt_irrefl 0)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have heven := even_of_mem_ker X hx
  have hnonempty : ((Finset.univ.filter fun e : Γ.edgesIn X ↦ x e = 1).map
      (Function.Embedding.subtype _)).Nonempty := by
    obtain ⟨e, he⟩ : ∃ e, x e ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    refine ⟨e.1, Finset.mem_map.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩⟩
    rcases F₂_eq_zero_or_one (x e) with h | h
    · exact absurd h he
    · exact h
  apply hno
  refine ⟨_, fun f hf ↦ ?_, hnonempty, heven⟩
  obtain ⟨e, -, rfl⟩ := Finset.mem_map.mp hf
  exact e.2

end Rank

section Consequences

/-- In a cubic closed graph a nonempty acyclic vertex set has boundary at least `|X| + 2`. -/
theorem card_add_two_le_card_bd (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hne : X.Nonempty) (hno : ¬ Γ.HasCycle X) : X.card + 2 ≤ (Γ.bd X).card := by
  have h1 := three_mul_card_eq hcub hX
  have h2 := card_edgesIn_lt hne hno
  omega

theorem hasCycle_of_card_bd_lt (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hne : X.Nonempty) (h : (Γ.bd X).card < X.card + 2) : Γ.HasCycle X := by
  by_contra hno
  have := card_add_two_le_card_bd hcub hX hne hno
  omega

theorem card_le_of_not_hasCycle (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hno : ¬ Γ.HasCycle X) : X.card + 2 ≤ (Γ.bd X).card ∨ X = ∅ := by
  rcases X.eq_empty_or_nonempty with h | h
  · exact Or.inr h
  · exact Or.inl (card_add_two_le_card_bd hcub hX h hno)

/-- Deleting a vertex of internal degree at most one preserves cycles. -/
theorem HasCycle.erase {X : Finset ℕ} {v : ℕ} (hvV : v ∈ Γ.Vs) (hX : Γ.HasCycle X)
    (hv : Γ.degIn (Γ.edgesIn X) v ≤ 1) : Γ.HasCycle (X.erase v) := by
  obtain ⟨F, hF, hne, hev⟩ := hX
  have hdeg : Γ.degIn F v = 0 := by
    have h1 := degIn_mono (Γ := Γ) hF v
    obtain ⟨k, hk⟩ := hev v hvV
    omega
  rw [degIn_eq_zero_iff] at hdeg
  refine ⟨F, fun e he ↦ ?_, hne, hev⟩
  have h := mem_edgesIn.mp (hF he)
  rw [mem_edgesIn]
  refine ⟨h.1, fun i ↦ Finset.mem_erase.mpr ⟨hdeg e he i, h.2 i⟩⟩

/-- The edges of `X ∪ Y` not inside `X` or `Y`, for disjoint `X`, `Y`: the cross edges. -/
def crossEdges (Γ : FinGraph) (X Y : Finset ℕ) : Finset ℕ :=
  Γ.edgesIn (X ∪ Y) \ (Γ.edgesIn X ∪ Γ.edgesIn Y)

theorem endsIn_of_mem_crossEdges {X Y : Finset ℕ} (_hXY : Disjoint X Y) {e : ℕ}
    (he : e ∈ Γ.crossEdges X Y) : Γ.endsIn X e = 1 := by
  unfold crossEdges at he
  rw [Finset.mem_sdiff, Finset.mem_union, mem_edgesIn, mem_edgesIn, mem_edgesIn] at he
  obtain ⟨⟨hEs, hXY'⟩, hnot⟩ := he
  rw [endsIn_eq]
  have h0 := hXY' 0
  have h1 := hXY' 1
  rw [Finset.mem_union] at h0 h1
  by_cases a0 : Γ.ends e 0 ∈ X
  · have a1 : Γ.ends e 1 ∉ X := fun a1 ↦ hnot (Or.inl ⟨hEs, fun i ↦ by fin_cases i <;> assumption⟩)
    rw [if_pos a0, if_neg a1]
  · have b0 : Γ.ends e 0 ∈ Y := h0.resolve_left a0
    have a1 : Γ.ends e 1 ∈ X := by
      by_contra a1
      have b1 : Γ.ends e 1 ∈ Y := h1.resolve_left a1
      exact hnot (Or.inr ⟨hEs, fun i ↦ by fin_cases i <;> assumption⟩)
    rw [if_neg a0, if_pos a1]

/-- An even edge set inside a disjoint union uses an even number of cross edges. -/
theorem even_card_inter_crossEdges {X Y F : Finset ℕ} (hXV : X ⊆ Γ.Vs) (hXY : Disjoint X Y)
    (hF : F ⊆ Γ.edgesIn (X ∪ Y)) (hev : Γ.IsEven F) : Even (F ∩ Γ.crossEdges X Y).card := by
  have hsum := sum_degIn_eq (Γ := Γ) F X
  have hL : Even (∑ v ∈ X, Γ.degIn F v) := Finset.even_sum _ fun v hv ↦ hev v (hXV hv)
  rw [hsum] at hL
  have hsplit : F = (F ∩ Γ.edgesIn X) ∪ (F ∩ Γ.edgesIn Y) ∪ (F ∩ Γ.crossEdges X Y) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, crossEdges, Finset.mem_sdiff]
    constructor
    · intro he
      by_cases h : e ∈ Γ.edgesIn X ∪ Γ.edgesIn Y
      · rw [Finset.mem_union] at h
        rcases h with h | h
        · exact Or.inl (Or.inl ⟨he, h⟩)
        · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr ⟨he, hF he, fun h' ↦ h (Finset.mem_union.mpr h')⟩
    · rintro ((h | h) | h) <;> exact h.1
  have hd1 : Disjoint (F ∩ Γ.edgesIn X) (F ∩ Γ.edgesIn Y) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [Finset.mem_inter, mem_edgesIn] at h1 h2
    exact Finset.disjoint_left.mp hXY (h1.2.2 0) (h2.2.2 0)
  have hd2 : Disjoint ((F ∩ Γ.edgesIn X) ∪ (F ∩ Γ.edgesIn Y)) (F ∩ Γ.crossEdges X Y) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [Finset.mem_inter] at h2
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at h1
    unfold crossEdges at h2
    rw [Finset.mem_sdiff, Finset.mem_union] at h2
    exact h2.2.2 (h1.elim (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr h.2))
  rw [hsplit, Finset.sum_union hd2, Finset.sum_union hd1] at hL
  rw [Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_edgesIn (Finset.mem_inter.mp he).2),
    Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_crossEdges hXY (Finset.mem_inter.mp he).2)] at hL
  have hY : ∑ e ∈ F ∩ Γ.edgesIn Y, Γ.endsIn X e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have h := (mem_edgesIn.mp (Finset.mem_inter.mp he).2).2
    rw [endsIn_eq, if_neg (Finset.disjoint_right.mp hXY (h 0)),
      if_neg (Finset.disjoint_right.mp hXY (h 1))]
    rfl
  rw [hY] at hL
  simp only [Finset.sum_const, smul_eq_mul, mul_one, add_zero] at hL
  rcases hL with ⟨k, hk⟩
  exact ⟨k - (F ∩ Γ.edgesIn X).card, by omega⟩

/-- Two acyclic vertex sets joined by at most one edge form an acyclic set. -/
theorem not_hasCycle_union {X Y : Finset ℕ} (hXV : X ⊆ Γ.Vs)
    (hXY : Disjoint X Y) (hX : ¬ Γ.HasCycle X)
    (hY : ¬ Γ.HasCycle Y) (hcross : (Γ.crossEdges X Y).card ≤ 1) : ¬ Γ.HasCycle (X ∪ Y) := by
  rintro ⟨F, hF, hne, hev⟩
  have hev' := even_card_inter_crossEdges hXV hXY hF hev
  have hle : (F ∩ Γ.crossEdges X Y).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hcross
  have hzero : (F ∩ Γ.crossEdges X Y).card = 0 := by
    obtain ⟨k, hk⟩ := hev'
    omega
  rw [Finset.card_eq_zero] at hzero
  -- every edge of `F` lies inside `X` or inside `Y`
  have hsplit : ∀ e ∈ F, e ∈ Γ.edgesIn X ∨ e ∈ Γ.edgesIn Y := by
    intro e he
    by_contra h
    rw [not_or] at h
    have : e ∈ F ∩ Γ.crossEdges X Y := by
      rw [Finset.mem_inter]
      refine ⟨he, ?_⟩
      unfold crossEdges
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨hF he, fun h' ↦ h'.elim h.1 h.2⟩
    rw [hzero] at this
    exact Finset.notMem_empty _ this
  -- the part inside `X` is even
  have hevX : Γ.IsEven (F ∩ Γ.edgesIn X) := by
    intro v hvV
    by_cases hv : v ∈ X
    · have : Γ.degIn (F ∩ Γ.edgesIn X) v = Γ.degIn F v := by
        rw [degIn_eq_sum, degIn_eq_sum, ← Finset.sum_filter_add_sum_filter_not F
          (fun e ↦ e ∈ Γ.edgesIn X)]
        have h0 : ∑ e ∈ F.filter (fun e ↦ e ∉ Γ.edgesIn X),
            ((if Γ.ends e 0 = v then 1 else 0) + (if Γ.ends e 1 = v then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro e he
          rw [Finset.mem_filter] at he
          have hY' := (hsplit e he.1).resolve_left he.2
          have h := (mem_edgesIn.mp hY').2
          have e0 : Γ.ends e 0 ≠ v := fun h' ↦ Finset.disjoint_left.mp hXY hv (h' ▸ h 0)
          have e1 : Γ.ends e 1 ≠ v := fun h' ↦ Finset.disjoint_left.mp hXY hv (h' ▸ h 1)
          rw [if_neg e0, if_neg e1]
          rfl
        rw [h0, add_zero]
        congr 1
      rw [this]
      exact hev v hvV
    · rw [degIn_eq_zero_iff.mpr]
      · exact ⟨0, rfl⟩
      intro e he i hi
      have h := (mem_edgesIn.mp (Finset.mem_inter.mp he).2).2 i
      exact hv (hi ▸ h)
  have hevY : Γ.IsEven (F ∩ Γ.edgesIn Y) := by
    intro v hvV
    by_cases hv : v ∈ Y
    · have : Γ.degIn (F ∩ Γ.edgesIn Y) v = Γ.degIn F v := by
        rw [degIn_eq_sum, degIn_eq_sum, ← Finset.sum_filter_add_sum_filter_not F
          (fun e ↦ e ∈ Γ.edgesIn Y)]
        have h0 : ∑ e ∈ F.filter (fun e ↦ e ∉ Γ.edgesIn Y),
            ((if Γ.ends e 0 = v then 1 else 0) + (if Γ.ends e 1 = v then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro e he
          rw [Finset.mem_filter] at he
          have hX' := (hsplit e he.1).resolve_right he.2
          have h := (mem_edgesIn.mp hX').2
          have e0 : Γ.ends e 0 ≠ v := fun h' ↦ Finset.disjoint_right.mp hXY hv (h' ▸ h 0)
          have e1 : Γ.ends e 1 ≠ v := fun h' ↦ Finset.disjoint_right.mp hXY hv (h' ▸ h 1)
          rw [if_neg e0, if_neg e1]
          rfl
        rw [h0, add_zero]
        congr 1
      rw [this]
      exact hev v hvV
    · rw [degIn_eq_zero_iff.mpr]
      · exact ⟨0, rfl⟩
      intro e he i hi
      have h := (mem_edgesIn.mp (Finset.mem_inter.mp he).2).2 i
      exact hv (hi ▸ h)
  have hXe : F ∩ Γ.edgesIn X = ∅ := by
    by_contra h
    exact hX ⟨_, Finset.inter_subset_right, Finset.nonempty_iff_ne_empty.mpr h, hevX⟩
  have hYe : F ∩ Γ.edgesIn Y = ∅ := by
    by_contra h
    exact hY ⟨_, Finset.inter_subset_right, Finset.nonempty_iff_ne_empty.mpr h, hevY⟩
  obtain ⟨e, he⟩ := hne
  rcases hsplit e he with h | h
  · have : e ∈ F ∩ Γ.edgesIn X := Finset.mem_inter.mpr ⟨he, h⟩
    rw [hXe] at this
    exact Finset.notMem_empty _ this
  · have : e ∈ F ∩ Γ.edgesIn Y := Finset.mem_inter.mpr ⟨he, h⟩
    rw [hYe] at this
    exact Finset.notMem_empty _ this

/-- Evenness of an edge set inside `Y` only depends on the vertices of `Y`. -/
theorem isEven_iff_of_subset {Y F : Finset ℕ} (hY : Y ⊆ Γ.Vs) (hF : F ⊆ Γ.edgesIn Y) :
    Γ.IsEven F ↔ ∀ v ∈ Y, Even (Γ.degIn F v) := by
  constructor
  · intro h v hv
    exact h v (hY hv)
  · intro h v _
    by_cases hv : v ∈ Y
    · exact h v hv
    · rw [degIn_eq_zero_iff.mpr]
      · exact ⟨0, rfl⟩
      intro e he i hi
      exact hv (hi ▸ (mem_edgesIn.mp (hF he)).2 i)

end Consequences

end FinGraph
end GraphPuzzles
