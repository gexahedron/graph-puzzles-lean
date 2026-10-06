import GraphPuzzles.DefectThree.MatchingTriple
import GraphPuzzles.DefectThree.HexagonDisjointFive
import GraphPuzzles.Core.FiniteCounts

/-! Matching triples associated with hexagonal exterior colourings. -/

namespace GraphPuzzles
namespace LoopMultigraph
namespace Hexagon
namespace ExteriorColoring

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : H.Hexagon} (g : X.ExteriorColoring)

instance (i : Fin 6) : Decidable (g.PairAt i) :=
  inferInstanceAs (Decidable ((i + g.r).val % 2 = 0))

/-- The exterior colour class, completed by the doubled edges of the core. -/
noncomputable def matchingSet (a : Fin 3) : Finset E := Finset.univ.filter fun e ↦
  ((∀ i, e ≠ X.h i) ∧ g.idx (g.color e) = a) ∨
    ∃ i, X.h i = e ∧ g.PairAt i ∧ a ≠ hexWord (i + g.r)

omit [DecidableEq V] in
theorem h_mem_matchingSet (a : Fin 3) (i : Fin 6) :
    X.h i ∈ g.matchingSet a ↔ g.PairAt i ∧ a ≠ hexWord (i + g.r) := by
  simp [matchingSet, X.h_injective.eq_iff]

omit [DecidableEq V] in
theorem mem_matchingSet_of_not_h (a : Fin 3) {e : E} (he : ∀ i, e ≠ X.h i) :
    e ∈ g.matchingSet a ↔ g.idx (g.color e) = a := by
  simp [matchingSet, he, fun i ↦ (he i).symm]

omit [DecidableEq V] in
theorem spoke_mem_matchingSet (a : Fin 3) (i : Fin 6) :
    X.spoke i ∈ g.matchingSet a ↔ hexWord (i + g.r) = a := by
  rw [g.mem_matchingSet_of_not_h a (X.spoke_ne_h i), g.spoke_color, g.idx_c]

private theorem matching_hexagon_table (r i : Fin 6) (a : Fin 3) :
    (if (i + r).val % 2 = 0 ∧ a ≠ hexWord (i + r) then 1 else 0) +
      ((if (i - 1 + r).val % 2 = 0 ∧ a ≠ hexWord (i - 1 + r) then 1 else 0) +
        (if hexWord (i + r) = a then 1 else 0)) = (1 : ℕ) := by
  revert r i a
  decide

/-- Each completed colour class is a perfect matching. -/
theorem matchingSet_perfect (hCubic : ∀ v, H.degree v = 3) (a : Fin 3) :
    H.IsPerfectMatching (g.matchingSet a) := by
  intro w
  rw [H.degreeIn_eq_card_halfEdges]
  by_cases hw : ∃ i, X.v i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [card_filter_of_three (X.hex0 i) (X.hex1 i) (X.spokeHalf i)
      (X.hex0_ne_hex1 i) (X.hex0_ne_spokeHalf i) (X.hex1_ne_spokeHalf i)
      (X.halfEdge_cases hCubic i)]
    simp only [hex0, hex1, spokeHalf, g.h_mem_matchingSet, g.spoke_mem_matchingSet, PairAt]
    exact matching_hexagon_table g.r i a
  · have hwo : ∀ i, w ≠ X.v i := fun i hi ↦ hw ⟨i, hi.symm⟩
    let φ : H.halfEdgesAt w → Fin 3 := fun x ↦ g.idx (g.color x.1.1)
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply g.injective_at w x y (halfEdge_not_h hwo x) (halfEdge_not_h hwo y)
      have hh := congrArg g.c hxy
      simpa only [φ, g.c_idx (g.nonzero _ (halfEdge_not_h hwo x)),
        g.c_idx (g.nonzero _ (halfEdge_not_h hwo y))] using hh
    have hbij : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, by
        rw [Fintype.card_fin]; exact hCubic w⟩
    obtain ⟨x₀, hx₀⟩ := hbij.2 a
    apply Finset.card_eq_one.mpr
    refine ⟨x₀, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      g.mem_matchingSet_of_not_h a (halfEdge_not_h hwo x)]
    exact ⟨fun hx ↦ hφ (hx.trans hx₀.symm), fun h ↦ h ▸ hx₀⟩

/-- The actual matching triple determined by an exterior colouring. -/
noncomputable def matchingTriple (hCubic : ∀ v, H.degree v = 3) : H.MatchingTriple :=
  ⟨g.matchingSet, g.matchingSet_perfect hCubic⟩

theorem matchingTriple_multiplicity_h (hCubic : ∀ v, H.degree v = 3) (i : Fin 6) :
    (g.matchingTriple hCubic).multiplicity (X.h i) = if g.PairAt i then 2 else 0 := by
  unfold MatchingTriple.multiplicity matchingTriple
  simp only [g.h_mem_matchingSet]
  by_cases hi : g.PairAt i
  · simp only [hi, true_and, if_true]
    exact (show ∀ a : Fin 3, (Finset.univ.filter fun b : Fin 3 ↦ b ≠ a).card = 2 by
      decide) _
  · simp [hi]

theorem matchingTriple_multiplicity_off (hCubic : ∀ v, H.degree v = 3)
    {e : E} (he : ∀ i, e ≠ X.h i) : (g.matchingTriple hCubic).multiplicity e = 1 := by
  unfold MatchingTriple.multiplicity matchingTriple
  simp only [g.mem_matchingSet_of_not_h _ he]
  exact Finset.card_eq_one.mpr ⟨g.idx (g.color e), by ext a; simp [eq_comm]⟩

/-- The matching triple's core is precisely the given hexagon. -/
theorem matchingTriple_core (hCubic : ∀ v, H.degree v = 3) :
    (g.matchingTriple hCubic).core = X.edgeSet := by
  ext e
  rw [MatchingTriple.mem_core, X.mem_edgeSet]
  by_cases he : ∃ i, X.h i = e
  · obtain ⟨i, rfl⟩ := he
    rw [g.matchingTriple_multiplicity_h]
    simp only [exists_apply_eq_apply, iff_true]
    split_ifs <;> decide
  · have hne : ∀ i, e ≠ X.h i := fun i hi ↦ he ⟨i, hi.symm⟩
    rw [g.matchingTriple_multiplicity_off hCubic hne]
    simp [he]

/-- Every matching triple arising from an exterior colouring is regular. -/
theorem matchingTriple_regular (hCubic : ∀ v, H.degree v = 3) :
    (g.matchingTriple hCubic).IsRegular := by
  intro e
  by_cases he : ∃ i, X.h i = e
  · obtain ⟨i, rfl⟩ := he
    rw [g.matchingTriple_multiplicity_h]
    split_ifs <;> decide
  · rw [g.matchingTriple_multiplicity_off hCubic (fun i hi ↦ he ⟨i, hi.symm⟩)]
    decide

theorem matchingTriple_uncovered (hCubic : ∀ v, H.degree v = 3) :
    (g.matchingTriple hCubic).uncovered =
      (Finset.univ.filter fun i : Fin 6 ↦ ¬ g.PairAt i).image X.h := by
  ext e
  by_cases he : ∃ i, X.h i = e
  · obtain ⟨i, rfl⟩ := he
    rw [MatchingTriple.mem_uncovered, g.matchingTriple_multiplicity_h]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      X.h_injective.eq_iff, exists_eq_right]
    by_cases hi : g.PairAt i <;> simp [hi]
  · have hne : ∀ i, e ≠ X.h i := fun i hi ↦ he ⟨i, hi.symm⟩
    rw [MatchingTriple.mem_uncovered, g.matchingTriple_multiplicity_off hCubic hne]
    apply iff_of_false (by decide)
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    exact he ⟨i, hi⟩

/-- Each exterior colouring supplies a triple with precisely three uncovered edges. -/
theorem matchingTriple_uncovered_card (hCubic : ∀ v, H.degree v = 3) :
    (g.matchingTriple hCubic).uncovered.card = 3 := by
  rw [g.matchingTriple_uncovered, Finset.card_image_of_injective _ X.h_injective]
  exact (show ∀ r : Fin 6,
    (Finset.univ.filter fun i : Fin 6 ↦ ¬ (i + r).val % 2 = 0).card = 3 by decide) g.r

end ExteriorColoring
end Hexagon
end LoopMultigraph
end GraphPuzzles
