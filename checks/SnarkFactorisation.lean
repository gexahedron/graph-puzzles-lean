import GraphPuzzles

/-! The paper's main conclusions with explicit hypotheses, terminal connectivity,
multiset multiplicities and intermediate class closure. -/

open GraphPuzzles GraphPuzzles.FinGraph

example {Γ : FinGraph} (hΓ : IsHypohamiltonianSnark Γ) :
    ∃ M, (factorSystem goodClass_hypohamiltonian).Chain Γ M ∧
      (∀ H ∈ M, IsHypohamiltonianSnark H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_hypohamiltonian).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  Claims.hypohamiltonian_factorisation hΓ

example {Γ : FinGraph} (hΓ : IsPermutationSnark Γ) :
    ∃ M, (factorSystem goodClass_permutation).Chain Γ M ∧
      (∀ H ∈ M, IsPermutationSnark H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_permutation).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  Claims.permutation_factorisation hΓ

example {Γ : FinGraph} (hΓ : IsHypohamiltonianSnark Γ ∧ IsPermutationSnark Γ) :
    ∃ M, (factorSystem goodClass_hp).Chain Γ M ∧
      (∀ H ∈ M, (IsHypohamiltonianSnark H ∧ IsPermutationSnark H) ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_hp).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  Claims.hypohamiltonian_permutation_factorisation hΓ

example {Γ A B : FinGraph} (hΓ : IsHypohamiltonianSnark Γ) (hs : Step Γ A B) :
    IsHypohamiltonianSnark A ∧ IsHypohamiltonianSnark B :=
  Claims.hypohamiltonian_factor_step hΓ hs

example {Γ A B : FinGraph} (hΓ : IsPermutationSnark Γ) (hs : Step Γ A B) :
    IsPermutationSnark A ∧ IsPermutationSnark B :=
  Claims.permutation_factor_step hΓ hs

example {Γ A B : FinGraph} (hΓ : IsHypohamiltonianSnark Γ ∧ IsPermutationSnark Γ)
    (hs : Step Γ A B) :
    (IsHypohamiltonianSnark A ∧ IsPermutationSnark A) ∧
      (IsHypohamiltonianSnark B ∧ IsPermutationSnark B) :=
  Claims.hypohamiltonian_permutation_factor_step hΓ hs

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {G : LoopMultigraph V E}

/-- Lemma 3.2 in the ambient endpoint model, with independent label universes. -/
example (P : G.DotProduct)
    (hA : ¬ ∃ D, G.IsHamiltonCycleIn P.EA P.L D)
    (hB : ¬ ∃ D, G.IsHamiltonCycleIn P.EB P.VB D)
    (hG : ∀ w ∈ P.VG, ∃ D, G.IsHamiltonCycleIn P.EG (P.VG.erase w) D) :
    G.IsHypohamiltonianIn P.EA P.L ∧ G.IsHypohamiltonianIn P.EB P.VB :=
  P.descent hA hB hG
