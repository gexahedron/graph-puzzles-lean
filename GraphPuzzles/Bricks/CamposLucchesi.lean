import GraphPuzzles.Reduction.Wheels.CubicTwoWheelReduction
import GraphPuzzles.Reduction.Wheels.TwoWheelBicontraction
import GraphPuzzles.Reduction.Wheels.PentagonalPairTransport

/-!
# The Campos–Lucchesi theorem

The final two-wheel case closes the induction for near-bricks. Its brick
specialization proves the published three-crossing statement with no
external mathematical hypothesis.
-/

namespace GraphPuzzles.LoopMultigraph

universe u v

/-- The terminal cubic two-wheel case is the Petersen graph unless the
selected cut admits a perfect matching crossing exactly three times. -/
theorem cubicTwoWheelClassification : CubicTwoWheelClassification.{u, v} := by
  intro V E _ _ _ _ H _ _ X _ _ _ hwl hwr hC h5 hno hthree
  have hcard := hC.cut_card_five_of_no_deleted_nearBrick hwl hwr h5 hno
  rcases three_or_petersen_of_five_matching_spokes hwl hwr hC hcard with h | h
  · exact (hthree h).elim
  · exact h

/-- Campos–Lucchesi's stronger near-brick theorem, including the tight
Petersen-minor alternative. -/
theorem nearBrickCutTheorem : NearBrickCutTheorem.{u, v} :=
  nearBrickCutTheorem_of_cubic_twoWheel_classification cubicTwoWheelClassification

/-- Every nontrivial separating cut of a simple brick other than the
Petersen graph is met by a perfect matching in exactly three edges. -/
theorem camposLucchesi : CamposLucchesi.{u, v} :=
  camposLucchesi_of_nearBrickCutTheorem nearBrickCutTheorem

end GraphPuzzles.LoopMultigraph
