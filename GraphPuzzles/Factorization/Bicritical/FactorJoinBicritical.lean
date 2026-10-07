import GraphPuzzles.Factorization.Bicritical.FactorJoinTransfer

/-!
# The join factor of a bicritical snark is bicritical

Chladný–Škoviera, Proposition 4.3: pairs of vertices of the join factor are pairs of vertices
of the original snark, and the colouring transfers.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hb : Δ.IsBicritical) (hY : Y ⊆ Δ.Vs)
  (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)
  (hiso : IsoWith hPY m)
include hcl hb hY hiso

/-- **The join factor of a bicritical snark is bicritical.** -/
theorem join_isBicritical : (join hPYc m).IsBicritical := by
  intro a ha b hb' hab
  have haV : a ∈ Δ.Vs := (Finset.mem_sdiff.mp ha).1
  have hbV : b ∈ Δ.Vs := (Finset.mem_sdiff.mp hb').1
  obtain ⟨c, hc⟩ := hb a haV b hbV hab
  have hXW : Y ⊆ Δ.Vs \ {a, b} := by
    intro v hv
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨hY hv, ?_⟩
    rintro (rfl | rfl)
    · exact (Finset.mem_sdiff.mp ha).2 hv
    · exact (Finset.mem_sdiff.mp hb').2 hv
  obtain ⟨c', hc', -⟩ := join_transfer hcl hXW hPY hPYc m hiso hc
  have hshore : (join hPYc m).Vs \ {a, b} = (Δ.Vs \ {a, b}) \ Y := by
    rw [join_Vs, pole_Vs]
    ext v
    simp only [Finset.mem_sdiff]
    tauto
  exact ⟨c', by rw [hshore]; exact hc'⟩

end FinGraph
end GraphPuzzles
