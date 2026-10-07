import GraphPuzzles.FinGraph.FinGraphHypoBicritical
import GraphPuzzles.Factorization.Bicritical.FactorBicriticalClass

/-!
# Unique factorisation of hypohamiltonian snarks (via bicriticality)

A hypohamiltonian snark with at least six vertices is a bicritical snark, so Theorem C applies:
its multiset of cyclically `5`-edge-connected factors is unique up to isomorphism.  (The
stronger statement that all factors are again hypohamiltonian is `FactorHypoClass`.)
-/

namespace GraphPuzzles
namespace FinGraph

/-- **Hypohamiltonian snarks** with at least six vertices. -/
def IsHypohamiltonianSnark (Γ : FinGraph) : Prop :=
  Γ.IsClosed ∧ Γ.IsCubic ∧ ¬ Γ.Colourable ∧ Γ.IsHypohamiltonian ∧ 6 ≤ Γ.Vs.card

theorem IsHypohamiltonianSnark.isBicriticalSnark {Γ : FinGraph} (h : IsHypohamiltonianSnark Γ) :
    IsBicriticalSnark Γ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.isBicritical h.1 h.2.1 (by have := h.2.2.2.2; omega),
    h.2.2.2.2⟩

/-- **Unique factorisation of hypohamiltonian snarks.** -/
theorem hypohamiltonian_unique_factorisation {Δ : FinGraph} (hΔ : IsHypohamiltonianSnark Δ)
    {M M' : Multiset FinGraph} (hM : (factorSystem goodClass_bicritical).Chain Δ M)
    (hM' : (factorSystem goodClass_bicritical).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  bicritical_unique_factorisation hΔ.isBicriticalSnark hM hM'

end FinGraph
end GraphPuzzles
