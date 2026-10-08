import GraphPuzzles.Poles.ThreePoleTransfer
import GraphPuzzles.Bricks.Brick
import GraphPuzzles.Bricks.CamposLucchesi

/-!
# The four-cover theorems with both mathematical inputs discharged

Theorem 3.1 of Karabáš–Máčajová (`kmThreePole`) and the Campos–Lucchesi
theorem (`camposLucchesi`) are proved in this development. The public
proper-snark endpoint therefore has no external theorem hypothesis.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Corollary 3.7 of Karabáš–Máčajová in the note's prescribed-matching form. -/
theorem kmThreeSpokes : KMThreeSpokes.{u, v} := kmThreePole.kmThreeSpokes

/-- **Four perfect matchings covering a two-circuit factor**, given a perfect matching crossing
the factor in exactly three edges. -/
theorem TwoCircuitFactor.exists_fourCover_of_three_crossing {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hCubic : ∀ v : V, H.degree v = 3)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hCL : ∃ N, H.IsPerfectMatching N ∧ (N ∩ F.cross).card = 3) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover_of_kmThreePole hCubic hloopless hCL kmThreePole

/-- **Four perfect matchings covering a two-circuit factor of a snark**, given the
Campos–Lucchesi conclusion for the graph. -/
theorem TwoCircuitFactor.exists_fourCover_of_snark' {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hCubic : ∀ v : V, H.degree v = 3)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (hbridge : H.IsBridgeless)
    (hsnark : ¬ ∃ g : E → Color, H.ProperOff ∅ g) (hCL : H.CamposLucchesiFor) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover_of_snark hCubic hloopless hbridge hsnark hCL kmThreePole

/-- The proper-snark four-cover theorem using the proved Campos–Lucchesi
theorem, with the ambient three-pole theorem supplied explicitly. -/
theorem TwoCircuitFactor.exists_fourCover_of_properSnark {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen)
    (hKM : KMThreePole.{u, v}) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover_of_properSnark_of_camposLucchesi hs hnotP camposLucchesi hKM

/-- **Four perfect matchings covering a two-circuit factor of a proper snark
other than the Petersen graph**, with no external theorem hypothesis. -/
theorem TwoCircuitFactor.exists_fourCover_of_properSnark' {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover_of_properSnark hs hnotP kmThreePole

end LoopMultigraph
end GraphPuzzles
