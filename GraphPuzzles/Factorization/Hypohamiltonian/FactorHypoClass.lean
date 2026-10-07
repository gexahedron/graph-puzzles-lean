import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoDescent
import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoUnique

/-!
# Unique factorisation of hypohamiltonian snarks, with hypohamiltonian factors

The hypohamiltonian snarks with at least six vertices form a good class: the descent lemma shows
that both factors of a decomposition along a cycle-separating `4`-cut are again
hypohamiltonian.  Hence every factor in every complete decomposition is a cyclically
`5`-edge-connected hypohamiltonian snark, and the multiset of terminal factors is unique.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- **Theorem B for hypohamiltonian snarks.** -/
theorem goodClass_hypohamiltonian : GoodClass IsHypohamiltonianSnark where
  closed := fun _ h ↦ h.1
  cubic := fun _ h ↦ h.2.1
  girth := fun _ h ↦ h.isBicriticalSnark.girth5
  cyc4 := fun _ h ↦ h.isBicriticalSnark.cyc4Conn
  snark := fun _ h ↦ h.2.2.1
  pole_colourable := fun Γ h X hX ↦
    goodClass_bicritical.pole_colourable Γ h.isBicriticalSnark X hX
  cap_mem := by
    intro Γ h X m hP hv
    have hb := h.isBicriticalSnark
    have hg5 := hb.girth5
    have hc4 := hb.cyc4Conn
    obtain ⟨hcl, hcub, hnc, hH, h6⟩ := h
    obtain ⟨_, hiso⟩ := hv.iso
    obtain ⟨hPc, hhet⟩ := hv.het
    have hcap := goodClass_bicritical.cap_mem Γ hb X m hP hv
    refine ⟨hcap.1, hcap.2.1, hcap.2.2.1, ?_, hcap.2.2.2.2⟩
    have hind := hv.cycSep.independent hcl hcub hg5 hc4
    have hY := hv.cycSep.1
    have hbd4 := hv.cycSep.2.1
    have h6X := CycSep.six_le hcub hg5 hv.cycSep
    have h6Xc := CycSep.six_le hcub hg5 (cycSep_compl hcl hv.cycSep)
    have hB : ¬ (cap hP m).IsHamiltonian :=
      not_isHamiltonian_of_not_colourable hcap.1 hcap.2.1 (by have := hcap.2.2.2.2; omega) hcap.2.2.1
    have hA : ¬ (join hPc m).IsHamiltonian :=
      not_isHamiltonian_of_not_colourable (join_isClosed hPc m) (join_isCubic hPc m)
        (by rw [join_Vs, pole_Vs]; omega) (not_colourable_join_of_hetWith hPc m hhet)
    refine ⟨hB, ?_⟩
    intro t ht
    rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at ht
    rcases ht with rfl | rfl | ht
    · -- the new vertex `u`
      have hdbd : bdEmb hP 0 ∈ Γ.bd X := by rw [← dangling_pole]; exact bdEmb_mem hP 0
      obtain ⟨C, hC⟩ := hH.2 _ (Finset.mem_sdiff.mp (innerEnd_compl_mem hcl hPc hdbd)).1
      exact descent_cap_u hcl hY hind hP hPc m hbd4 hC (by omega)
        (Finset.card_pos.mp (by omega)) (by omega) hB
    · -- the new vertex `w`
      have hdbd : bdEmb hP (other m) ∈ Γ.bd X := by rw [← dangling_pole]; exact bdEmb_mem hP _
      obtain ⟨C, hC⟩ := hH.2 _ (Finset.mem_sdiff.mp (innerEnd_compl_mem hcl hPc hdbd)).1
      exact descent_cap_w hcl hY hind hP hPc m hbd4 hC (by omega)
        (Finset.card_pos.mp (by omega)) (by omega) hB
    · -- an old vertex
      obtain ⟨C, hC⟩ := hH.2 t (hY ht)
      exact descent_cap_old hcl hY hind hP hPc m hbd4 ht hC (by omega) (by omega)
        (Finset.card_pos.mp (by omega)) hA
  join_mem := by
    intro Γ h X m hP hv
    have hb := h.isBicriticalSnark
    have hg5 := hb.girth5
    have hc4 := hb.cyc4Conn
    obtain ⟨hcl, hcub, hnc, hH, h6⟩ := h
    obtain ⟨hP', hiso⟩ := hv.iso
    obtain ⟨_, hhet⟩ := hv.het
    have hjoin := goodClass_bicritical.join_mem Γ hb X m hP hv
    refine ⟨hjoin.1, hjoin.2.1, hjoin.2.2.1, ?_, hjoin.2.2.2.2⟩
    have hind := hv.cycSep.independent hcl hcub hg5 hc4
    have hY := hv.cycSep.1
    have hbd4 := hv.cycSep.2.1
    have h6X := CycSep.six_le hcub hg5 hv.cycSep
    have h6Xc := CycSep.six_le hcub hg5 (cycSep_compl hcl hv.cycSep)
    have hA : ¬ (join hP m).IsHamiltonian :=
      not_isHamiltonian_of_not_colourable hjoin.1 hjoin.2.1 (by have := hjoin.2.2.2.2; omega)
        hjoin.2.2.1
    have hB : ¬ (cap hP' m).IsHamiltonian :=
      not_isHamiltonian_of_not_colourable (cap_isClosed hP' m) (cap_isCubic hP' m)
        (by rw [cap_Vs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
            · rw [pole_Vs]; omega
            · exact freshV_succ_notMem
            · rw [Finset.mem_insert]; rintro (h | h); omega; exact freshV_notMem h)
        (not_colourable_cap_of_isoWith hP' m hiso)
    refine ⟨hA, ?_⟩
    intro t ht
    rw [join_Vs, pole_Vs] at ht
    obtain ⟨C, hC⟩ := hH.2 t (Finset.mem_sdiff.mp ht).1
    obtain ⟨C', hC'⟩ := descent_join hcl hY hind hP' hP m hbd4 ht hC (by omega)
      (Finset.card_pos.mp (by omega)) (by omega) hB
    exact ⟨C', by rw [join_Vs, pole_Vs]; exact hC'⟩

/-- **Unique factorisation of hypohamiltonian snarks, with hypohamiltonian factors.**  In the
decomposition system of the class of hypohamiltonian snarks, any two complete decompositions
give the same multiset of terminal factors up to isomorphism. -/
theorem hypohamiltonian_unique_factorisation_class {Δ : FinGraph} (hΔ : IsHypohamiltonianSnark Δ)
    {M M' : Multiset FinGraph} (hM : (factorSystem goodClass_hypohamiltonian).Chain Δ M)
    (hM' : (factorSystem goodClass_hypohamiltonian).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  unique_factorisation goodClass_hypohamiltonian hΔ hM hM'

theorem hypohamiltonian_exists_factorisation (Δ : FinGraph) :
    ∃ M, (factorSystem goodClass_hypohamiltonian).Chain Δ M :=
  exists_factorisation goodClass_hypohamiltonian Δ

/-- **Every factor is a cyclically `5`-edge-connected hypohamiltonian snark.** -/
theorem hypohamiltonian_factors {Δ : FinGraph} (hΔ : IsHypohamiltonianSnark Δ)
    {M : Multiset FinGraph} (hM : (factorSystem goodClass_hypohamiltonian).Chain Δ M) :
    ∀ H ∈ M, IsHypohamiltonianSnark H ∧ ∀ X, ¬ H.CycSep X := by
  intro H hH
  obtain ⟨hP, hT⟩ := hM.mem_P hΔ H hH
  refine ⟨hP, fun X hX ↦ hT ⟨_, _, exists_step_of_cycSep goodClass_hypohamiltonian hP hX⟩⟩

/-- The terminal members of the class are exactly those without cycle-separating `4`-cuts, i.e.
the cyclically `5`-edge-connected hypohamiltonian snarks. -/
theorem hypohamiltonian_terminal_iff {Γ : FinGraph} (h : IsHypohamiltonianSnark Γ) :
    (factorSystem goodClass_hypohamiltonian).Terminal Γ ↔ ∀ X, ¬ Γ.CycSep X := by
  constructor
  · intro ht X hX
    exact ht ⟨_, _, exists_step_of_cycSep goodClass_hypohamiltonian h hX⟩
  · rintro hno ⟨A, B, Z, m, -, -, -, -, -, hv, -⟩
    exact hno Z hv.cycSep

/-- The factors of a decomposition of a hypohamiltonian snark are hypohamiltonian snarks. -/
theorem IsHypohamiltonianSnark.step {Δ C D : FinGraph} (hΔ : IsHypohamiltonianSnark Δ)
    (h : Step Δ C D) : IsHypohamiltonianSnark C ∧ IsHypohamiltonianSnark D :=
  Step.class_mem goodClass_hypohamiltonian hΔ h

end FinGraph
end GraphPuzzles
