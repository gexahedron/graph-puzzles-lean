import GraphPuzzles.Cuts.CohesiveCuts
import Mathlib.Order.Preorder.Finite

/-!
# Matching-equivalent cuts and precedence

The order compares crossing counts for every perfect matching, as in Section 3 of
Campos--Lucchesi. Edmonds' theorem extends this comparison to all rational fractional
perfect matchings. No converse from inclusion of one-crossing faces is assumed.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Two cuts have the same crossing count in every perfect matching. -/
def MatchingEquivalentCuts (H : LoopMultigraph V E) (X Y : Finset V) : Prop :=
  ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = (M ∩ H.dangling Y).card

theorem matchingEquivalentCuts_iff_precedes {X Y : Finset V} :
    H.MatchingEquivalentCuts X Y ↔ H.CutPrecedes X Y ∧ H.CutPrecedes Y X :=
  ⟨fun h ↦ ⟨fun M hM ↦ (h M hM).le, fun M hM ↦ (h M hM).ge⟩,
    fun h M hM ↦ Nat.le_antisymm (h.1 M hM) (h.2 M hM)⟩

theorem MatchingEquivalentCuts.refl (X : Finset V) : H.MatchingEquivalentCuts X X :=
  fun _ _ ↦ rfl

theorem MatchingEquivalentCuts.symm {X Y : Finset V} (h : H.MatchingEquivalentCuts X Y) :
    H.MatchingEquivalentCuts Y X := fun M hM ↦ (h M hM).symm

theorem MatchingEquivalentCuts.trans {X Y Z : Finset V}
    (hXY : H.MatchingEquivalentCuts X Y) (hYZ : H.MatchingEquivalentCuts Y Z) :
    H.MatchingEquivalentCuts X Z := fun M hM ↦ (hXY M hM).trans (hYZ M hM)

theorem MatchingEquivalentCuts.tight_iff {X Y : Finset V}
    (h : H.MatchingEquivalentCuts X Y) : H.IsTightCut X ↔ H.IsTightCut Y :=
  ⟨fun ht M hM ↦ (h M hM).symm.trans (ht M hM),
    fun ht M hM ↦ (h M hM).trans (ht M hM)⟩

/-- Precedence holds on the entire rational matching polytope. -/
theorem CutPrecedes.cutWeight_le {X Y : Finset V} (h : H.CutPrecedes X Y)
    {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x) :
    H.cutWeight x X ≤ H.cutWeight x Y := by
  obtain ⟨D⟩ := hx.exists_matchingCombination
  rw [D.cutWeight, D.cutWeight]
  apply Finset.sum_le_sum
  intro M _
  by_cases hz : D.weight M = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_left ?_ (D.nonneg M)
    exact_mod_cast h M (D.valid M hz)

theorem cutPrecedes_iff_fractional {X Y : Finset V} :
    H.CutPrecedes X Y ↔ ∀ x, H.IsFractionalPerfectMatching x →
      H.cutWeight x X ≤ H.cutWeight x Y := by
  constructor
  · exact fun h _ hx ↦ h.cutWeight_le hx
  · intro h M hM
    have hh := h _ hM.isFractional
    simp only [cutWeight_matchingVector] at hh
    exact_mod_cast hh

theorem MatchingEquivalentCuts.cutWeight_eq {X Y : Finset V}
    (h : H.MatchingEquivalentCuts X Y) {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x) :
    H.cutWeight x X = H.cutWeight x Y := by
  obtain ⟨hXY, hYX⟩ := matchingEquivalentCuts_iff_precedes.mp h
  exact le_antisymm (hXY.cutWeight_le hx) (hYX.cutWeight_le hx)

/-- Strict precedence includes a strict crossing inequality for at least one matching. -/
def CutStrictlyPrecedes (H : LoopMultigraph V E) (X Y : Finset V) : Prop :=
  H.CutPrecedes X Y ∧ ∃ M, H.IsPerfectMatching M ∧
    (M ∩ H.dangling X).card < (M ∩ H.dangling Y).card

theorem cutStrictlyPrecedes_iff {X Y : Finset V} :
    H.CutStrictlyPrecedes X Y ↔ H.CutPrecedes X Y ∧ ¬ H.CutPrecedes Y X := by
  constructor
  · rintro ⟨h, M, hM, hlt⟩
    exact ⟨h, fun hh ↦ (not_lt_of_ge (hh M hM)) hlt⟩
  · rintro ⟨h, hn⟩
    simp only [CutPrecedes, not_forall, not_le] at hn
    obtain ⟨M, hM, hlt⟩ := hn
    exact ⟨h, M, hM, hlt⟩

/-- Every nonempty finite family contains a minimal cut in the crossing-count order. -/
theorem exists_minimal_cut (C : Finset (Finset V)) (hC : C.Nonempty) :
    ∃ X ∈ C, ∀ Y ∈ C, ¬ H.CutStrictlyPrecedes Y X := by
  classical
  let f (X : Finset V) (M : {M : Finset E // H.IsPerfectMatching M}) :=
    (M.1 ∩ H.dangling X).card
  obtain ⟨X, hX, hm⟩ := C.exists_minimalFor f hC
  refine ⟨X, hX, ?_⟩
  intro Y hY hp
  obtain ⟨hYX, hn⟩ := cutStrictlyPrecedes_iff.mp hp
  apply hn
  have hh : f X ≤ f Y := hm hY (fun M ↦ hYX M.1 M.2)
  exact fun M hM ↦ hh ⟨M, hM⟩

/-- Precedence preserves separation for odd cuts with nonempty shores. -/
theorem CutPrecedes.isSeparatingCut {X Y : Finset V} (hp : H.CutPrecedes Y X)
    (hs : H.IsSeparatingCut X) (hc : H.IsConnected) (ho : Odd Y.card)
    (hY : Y.Nonempty) (hYC : (Finset.univ \ Y).Nonempty) : H.IsSeparatingCut Y := by
  apply isSeparatingCut_of_crossing_one hc hY hYC
  intro e
  obtain ⟨M, hM, he, hm⟩ := hs.exists_perfectMatching_through e
  exact ⟨M, hM, he, hp.facePrecedes ho M hM hm⟩

/-- The finite minimality choice in the setup of Campos--Lucchesi Lemma 3.3.
The assertion that this minimal cut is robust is a further structural theorem. -/
theorem IsSeparatingCut.exists_minimal_preceding {X : Finset V} (hs : H.IsSeparatingCut X)
    {M : Finset E} (hcross : 1 < (M ∩ H.dangling X).card) :
    ∃ Y, H.IsSeparatingCut Y ∧ 1 < (M ∩ H.dangling Y).card ∧ H.CutPrecedes Y X ∧
      ∀ Z, H.IsSeparatingCut Z → 1 < (M ∩ H.dangling Z).card → H.CutPrecedes Z X →
        ¬ H.CutStrictlyPrecedes Z Y := by
  classical
  let C := Finset.univ.filter fun Y ↦ H.IsSeparatingCut Y ∧
    1 < (M ∩ H.dangling Y).card ∧ H.CutPrecedes Y X
  have hC : C.Nonempty := ⟨X, by simp [C, hs, hcross, CutPrecedes.refl]⟩
  obtain ⟨Y, hY, hm⟩ := exists_minimal_cut (H := H) C hC
  obtain ⟨hYs, hYm, hYX⟩ := (Finset.mem_filter.mp hY).2
  exact ⟨Y, hYs, hYm, hYX, fun Z hZs hZm hZX ↦
    hm Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZs, hZm, hZX⟩)⟩

end GraphPuzzles.LoopMultigraph
