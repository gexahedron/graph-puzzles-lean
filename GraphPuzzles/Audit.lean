import GraphPuzzles
import GraphPuzzles.Audit.StrongFiveCycleDoubleCover
import GraphPuzzles.Audit.SnarkFactorisation
import GraphPuzzles.Audit.TwoCircuitFourMatchings
import GraphPuzzles.Audit.OrientedFiveCycleDoubleCover

/-! Exact axiom guards for all released proof families. Whitespace is ignored so
namespace length and pretty-printer wrapping do not affect the axiom checks. -/

/--
info: 'GraphPuzzles.OddBalance.solutions_card_odd_of_card_eq_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.OddBalance.solutions_card_odd_of_card_eq_three

/--
info: 'GraphPuzzles.OddBalance.exists_balanced_of_card_eq_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.OddBalance.exists_balanced_of_card_eq_three

/--
info: 'GraphPuzzles.all_colorFiber_card_even_iff_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.all_colorFiber_card_even_iff_moments

/--
info: 'GraphPuzzles.CyclicWord.Word.exists_coloring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.CyclicWord.Word.exists_coloring

/--
info: 'GraphPuzzles.LoopMultigraph.loop_sabidussi_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.loop_sabidussi_compatibility

/--
info: 'GraphPuzzles.LoopMultigraph.Cycle.toOrdinaryCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.Cycle.toOrdinaryCircuit

/--
info: 'GraphPuzzles.LoopMultigraph.loop_sabidussi_compatibility_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.loop_sabidussi_compatibility_ordinary

/--
info: 'GraphPuzzles.LoopMultigraph.exists_sabidussi_coloring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.exists_sabidussi_coloring

/--
info: 'GraphPuzzles.LoopMultigraph.sabidussi_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.sabidussi_theorem

/--
info: 'GraphPuzzles.LoopMultigraph.OrdinaryCircuit.exists_fiveCycleDoubleCover_containing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.OrdinaryCircuit.exists_fiveCycleDoubleCover_containing

/--
info: 'GraphPuzzles.CycleDoubleCoverProof.exists_indexed_even_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.CycleDoubleCoverProof.exists_indexed_even_cover

/--
info: 'GraphPuzzles.CycleDoubleCoverProof.nonLoopGraph_bridgeless' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.CycleDoubleCoverProof.nonLoopGraph_bridgeless

/--
info: 'GraphPuzzles.CycleDoubleCoverProof.layer_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.CycleDoubleCoverProof.layer_even

/--
info: 'GraphPuzzles.CycleDoubleCoverProof.toEightCover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.CycleDoubleCoverProof.toEightCover

/--
info: 'GraphPuzzles.LoopMultigraph.CycleDoubleCover.toOrdinary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.CycleDoubleCover.toOrdinary

/--
info: 'GraphPuzzles.LoopMultigraph.exists_eightCycleDoubleCover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.exists_eightCycleDoubleCover

/--
info: 'GraphPuzzles.LoopMultigraph.exists_ordinaryCycleDoubleCover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.exists_ordinaryCycleDoubleCover

/--
info: 'GraphPuzzles.LoopMultigraph.cycleDoubleCover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.LoopMultigraph.cycleDoubleCover

/--
info: 'GraphPuzzles.Claims.cycle_double_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.Claims.cycle_double_cover

/--
info: 'GraphPuzzles.Claims.eight_cycle_double_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GraphPuzzles.Claims.eight_cycle_double_cover
