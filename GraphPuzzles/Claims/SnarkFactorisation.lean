import GraphPuzzles.Results.SnarkFactorisation

namespace GraphPuzzles.Claims

open FinGraph

/-- Paper Theorem 4.3: existence, terminal class membership and uniqueness for a good class. -/
theorem factorisation_criterion (P : FinGraph → Prop) (hG : GoodClass P)
    {Γ : FinGraph} (hΓ : P Γ) :
    ∃ M, (factorSystem hG).Chain Γ M ∧
      (∀ H ∈ M, P H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem hG).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N := by
  obtain ⟨M, hM⟩ := exists_factorisation hG Γ
  refine ⟨M, hM, ?_, fun _ hN ↦ unique_factorisation hG hΓ hM hN⟩
  intro H hH
  obtain ⟨hP, hT⟩ := hM.mem_P hΓ H hH
  exact ⟨hP, fun X hX ↦ hT ⟨_, _, exists_step_of_cycSep hG hP hX⟩⟩

/-- Paper Theorem 1.1: unique terminal hypohamiltonian factors, including multiplicities. -/
theorem hypohamiltonian_factorisation {Γ : FinGraph} (hΓ : IsHypohamiltonianSnark Γ) :
    ∃ M, (factorSystem goodClass_hypohamiltonian).Chain Γ M ∧
      (∀ H ∈ M, IsHypohamiltonianSnark H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_hypohamiltonian).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  factorisation_criterion _ goodClass_hypohamiltonian hΓ

/-- Paper Theorem 1.2: permutation factorisation without assuming bicriticality. -/
theorem permutation_factorisation {Γ : FinGraph} (hΓ : IsPermutationSnark Γ) :
    ∃ M, (factorSystem goodClass_permutation).Chain Γ M ∧
      (∀ H ∈ M, IsPermutationSnark H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_permutation).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  factorisation_criterion _ goodClass_permutation hΓ

/-- Paper Corollary 1.3: factors retain both hypohamiltonian and permutation properties. -/
theorem hypohamiltonian_permutation_factorisation {Γ : FinGraph} (hΓ : IsHPSnark Γ) :
    ∃ M, (factorSystem goodClass_hp).Chain Γ M ∧
      (∀ H ∈ M, IsHPSnark H ∧ ∀ X, ¬ H.CycSep X) ∧
      ∀ N, (factorSystem goodClass_hp).Chain Γ N →
        Multiset.Rel (fun A B ↦ Nonempty (FinGraph.Iso A B)) M N :=
  factorisation_criterion _ goodClass_hp hΓ

/-- Every intermediate decomposition preserves the hypohamiltonian class. -/
theorem hypohamiltonian_factor_step {Γ A B : FinGraph} (hΓ : IsHypohamiltonianSnark Γ)
    (hs : Step Γ A B) : IsHypohamiltonianSnark A ∧ IsHypohamiltonianSnark B :=
  hΓ.step hs

/-- Every intermediate decomposition preserves the permutation class. -/
theorem permutation_factor_step {Γ A B : FinGraph} (hΓ : IsPermutationSnark Γ)
    (hs : Step Γ A B) : IsPermutationSnark A ∧ IsPermutationSnark B :=
  hΓ.step hs

/-- Every intermediate decomposition preserves both properties. -/
theorem hypohamiltonian_permutation_factor_step {Γ A B : FinGraph} (hΓ : IsHPSnark Γ)
    (hs : Step Γ A B) : IsHPSnark A ∧ IsHPSnark B :=
  hΓ.step hs

end GraphPuzzles.Claims
