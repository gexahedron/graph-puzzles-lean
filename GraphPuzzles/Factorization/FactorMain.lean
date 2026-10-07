import GraphPuzzles.Factorization.FactorQuasi

/-!
# Unique factorisation for a good class (Chladný–Škoviera, Theorem C)

Every good class of snarks (`GoodClass`) forms a decomposition system satisfying the atom
property, hence any two complete decompositions of a member along cycle-separating `4`-cuts
produce the same multiset of terminal factors up to isomorphism.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section System

variable {P : FinGraph → Prop} (hG : GoodClass P)

/-- The decomposition system of a good class. -/
noncomputable def factorSystem : DecompSystem FinGraph where
  Step := Step
  size := fun Γ ↦ Γ.Vs.card
  R := fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)
  P := P
  R_refl := fun Γ ↦ ⟨Iso.refl Γ⟩
  R_symm := fun ⟨f⟩ ↦ ⟨f.symm⟩
  R_trans := fun ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩
  step_symm := Step.symm
  size_lt := Step.size_lt
  step_transport := fun ⟨f⟩ h ↦ Step.transport f h
  P_step := fun hΔ h ↦ Step.class_mem hG hΔ h

theorem factorSystem_Step (Δ C D : FinGraph) : (factorSystem hG).Step Δ C D ↔ Step Δ C D := Iff.rfl

theorem factorSystem_R (Γ₁ Γ₂ : FinGraph) :
    (factorSystem hG).R Γ₁ Γ₂ ↔ Nonempty (Iso Γ₁ Γ₂) := Iff.rfl

theorem factorSystem_P (Γ : FinGraph) : (factorSystem hG).P Γ ↔ P Γ := Iff.rfl

variable {Δ : FinGraph} (hΔ : P Δ)
include hG hΔ

/-- A shore containing the atom: the factors are associated to the atom's factors or the two
decompositions close up in a diamond. -/
theorem assoc_or_diamond {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y) :
    (Nonempty (Iso (factorOf Δ Y) (factorOf Δ A)) ∧
      Nonempty (Iso (factorOf Δ (Δ.Vs \ Y)) (factorOf Δ (Δ.Vs \ A)))) ∨
    (factorSystem hG).Diamond (factorOf Δ A) (factorOf Δ (Δ.Vs \ A)) (factorOf Δ Y)
      (factorOf Δ (Δ.Vs \ Y)) := by
  by_cases hne : Y = A
  · left
    subst hne
    exact ⟨⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  by_cases hnq : Δ.IsQuasiatomic A Y
  · left
    exact quasi_iso hG hΔ hA hY hAY hnq
  · right
    obtain ⟨A₀', C', C'', D', h1, h2, h3, h4, h5⟩ := diamond_of_subset hG hΔ hA hY hAY hne hnq
    exact ⟨A₀', C', C'', D', h1, h2, h3, h4, h5⟩

/-- **The atom property of a good class.** -/
theorem atomProperty_aux (hstep : ∃ A B, Step Δ A B) : ∃ A₀ B₀, Step Δ A₀ B₀ ∧
    ∀ C D, Step Δ C D →
      ((factorSystem hG).R C A₀ ∧ (factorSystem hG).R D B₀) ∨
      ((factorSystem hG).R C B₀ ∧ (factorSystem hG).R D A₀) ∨
      (factorSystem hG).Diamond A₀ B₀ C D ∨ (factorSystem hG).Diamond A₀ B₀ D C := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  have hc4 := hG.cyc4 Δ hΔ
  obtain ⟨_, _, Z₀, _, -, -, -, -, -, hv₀, -⟩ := hstep
  obtain ⟨A, hA⟩ := exists_atom ⟨Z₀, hv₀.cycSep⟩
  refine ⟨factorOf Δ A, factorOf Δ (Δ.Vs \ A), exists_step_of_cycSep hG hΔ hA.1, ?_⟩
  intro C D hCD
  obtain ⟨Z, m, -, -, -, -, -, hv, h7⟩ := hCD
  have hZ := hv.cycSep
  have hZV := hZ.1
  have hZc := cycSep_compl hcl hZ
  have eZ : Δ.Vs \ (Δ.Vs \ Z) = Z := Finset.sdiff_sdiff_eq_self hZV
  rcases IsAtom.subset_or_subset_compl hcl hcub hg hc4 hA hZ with hAZ | hAZ
  · rcases assoc_or_diamond hG hΔ hA hZ hAZ with ⟨h1, h2⟩ | hd
    · rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inr (Or.inr hd))
  · rcases assoc_or_diamond hG hΔ hA hZc hAZ with ⟨h1, h2⟩ | hd
    · rw [eZ] at h2
      rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨h2, h1⟩)
      · exact Or.inl ⟨h1, h2⟩
    · rw [eZ] at hd
      rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr (Or.inl hd))

end System

section Main

variable {P : FinGraph → Prop} (hG : GoodClass P)

theorem atomProperty : (factorSystem hG).AtomProperty := by
  intro G hG' hstep
  exact atomProperty_aux hG hG' hstep

/-- **Unique factorisation (Chladný–Škoviera, Theorem C) for a good class.**  Any two
complete decompositions of a member of the class along cycle-separating `4`-cuts yield the
same multiset of terminal factors up to isomorphism. -/
theorem unique_factorisation {Δ : FinGraph} (hΔ : P Δ) {M M' : Multiset FinGraph}
    (hM : (factorSystem hG).Chain Δ M) (hM' : (factorSystem hG).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  (factorSystem hG).unique_chain (atomProperty hG) Δ hΔ M M' hM hM'

/-- Every member of the class has a complete decomposition. -/
theorem exists_factorisation (Δ : FinGraph) : ∃ M, (factorSystem hG).Chain Δ M :=
  (factorSystem hG).exists_chain Δ

end Main

end FinGraph
end GraphPuzzles
