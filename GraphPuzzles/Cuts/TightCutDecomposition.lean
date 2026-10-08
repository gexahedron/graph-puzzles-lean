import GraphPuzzles.Cuts.Contraction.BipartiteContraction

/-!
# Tight-cut decompositions

Splitting a matching-covered graph along nontrivial tight cuts terminates because
both contractions have fewer vertices. Leaves are matching-covered graphs with
no nontrivial tight cuts. This module constructs the decomposition; uniqueness of
the brick factors is a separate structural assertion.
-/

namespace GraphPuzzles.LoopMultigraph

universe u v

/-- A complete binary tight-cut decomposition, retaining the actual contraction graphs. -/
inductive TightCutDecomposition :
    {V : Type u} → {E : Type v} → [Fintype V] → [Fintype E] →
    [DecidableEq V] → [DecidableEq E] → LoopMultigraph V E → Type (max (u + 1) (v + 1)) where
  | leaf {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {H : LoopMultigraph V E} (hm : H.IsMatchingCovered)
      (ht : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X) : TightCutDecomposition H
  | split {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {H : LoopMultigraph V E} (hm : H.IsMatchingCovered) (X : Finset V)
      (ht : H.IsTightCut X) (hn : IsNontrivialCut X)
      (left : TightCutDecomposition (H.contract X))
      (right : TightCutDecomposition (H.contract (Finset.univ \ X))) : TightCutDecomposition H

private theorem exists_tightCutDecomposition_aux (n : ℕ) :
    ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (H : LoopMultigraph V E), Fintype.card V = n → H.IsMatchingCovered →
      Nonempty (TightCutDecomposition H) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ H hn hm
    by_cases ht : ∃ X : Finset V, H.IsTightCut X ∧ IsNontrivialCut X
    · obtain ⟨X, ht, hX⟩ := ht
      have hsep := ht.isSeparatingCut hm
        (Finset.card_pos.mp (by have hh := hX.1; omega))
        (Finset.card_pos.mp (by have hh := hX.2; omega))
      have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
      rw [Finset.card_univ, hn] at hcard
      have hL : Fintype.card (Option X) < n := by
        rw [Fintype.card_option, Fintype.card_coe]
        have hh := hX.2
        omega
      have hR : Fintype.card (Option ↥(Finset.univ \ X)) < n := by
        rw [Fintype.card_option, Fintype.card_coe]
        have hh := hX.1
        omega
      obtain ⟨L⟩ := ih _ hL (H.contract X) rfl hsep.1
      obtain ⟨R⟩ := ih _ hR (H.contract (Finset.univ \ X)) rfl hsep.2
      exact ⟨.split hm X ht hX L R⟩
    · exact ⟨.leaf hm (fun X hX hn ↦ ht ⟨X, hX, hn⟩)⟩

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every finite matching-covered graph has a complete tight-cut decomposition. -/
theorem IsMatchingCovered.exists_tightCutDecomposition (hm : H.IsMatchingCovered) :
    Nonempty (TightCutDecomposition H) := exists_tightCutDecomposition_aux _ H rfl hm

/-- A leaf of a tight-cut decomposition is a brace when it is bipartite. -/
structure IsBrace (H : LoopMultigraph V E) : Prop where
  bipartite : H.IsBipartite
  matchingCovered : H.IsMatchingCovered
  tight_trivial : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X

theorem brick_or_brace_of_terminal (hm : H.IsMatchingCovered)
    (ht : ∀ X, H.IsTightCut X → ¬ IsNontrivialCut X) : H.IsBrick ∨ H.IsBrace := by
  by_cases hb : H.IsBipartite
  · exact Or.inr ⟨hb, hm, ht⟩
  · exact Or.inl ⟨hb, hm, ht⟩

namespace TightCutDecomposition

def matchingCovered (D : TightCutDecomposition H) : H.IsMatchingCovered :=
  match D with
  | .leaf hm _ => hm
  | .split hm _ _ _ _ _ => hm

/-- Number of nonbipartite terminal graphs in this particular decomposition. -/
noncomputable def brickCount {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E} : TightCutDecomposition H → ℕ
  | .leaf _ _ => by classical exact if H.IsBipartite then 0 else 1
  | .split _ _ _ _ L R => brickCount L + brickCount R

/-- Every leaf is bipartite exactly when the original graph is bipartite. -/
theorem brickCount_eq_zero_iff (D : TightCutDecomposition H) :
    D.brickCount = 0 ↔ H.IsBipartite := by
  induction D with
  | leaf hm ht =>
    classical
    simp only [brickCount]
    split <;> simp_all
  | split hm X ht hn L R ihL ihR =>
    rw [brickCount, Nat.add_eq_zero_iff, ihL, ihR]
    exact (ht.isSeparatingCut hm
      (Finset.card_pos.mp (by have hh := hn.1; omega))
      (Finset.card_pos.mp (by have hh := hn.2; omega))).bipartite_iff.symm

/-- A brick admits only the terminal decomposition. -/
theorem brickCount_of_brick (D : TightCutDecomposition H) (hb : H.IsBrick) :
    D.brickCount = 1 := by
  classical
  cases D with
  | leaf hm ht => simp [brickCount, hb.notBipartite]
  | split hm X ht hn L R => exact (hb.tight_trivial X ht hn).elim

theorem brickCount_of_brace (D : TightCutDecomposition H) (hb : H.IsBrace) :
    D.brickCount = 0 := D.brickCount_eq_zero_iff.mpr hb.bipartite

end TightCutDecomposition
end GraphPuzzles.LoopMultigraph
