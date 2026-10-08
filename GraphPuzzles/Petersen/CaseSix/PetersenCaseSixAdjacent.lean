import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixBase

/-! Explicit finite matching patches for Section 6.

Explicit witness data are checked by Lean kernel reduction.
The certificate checks do not depend on a search program. -/

namespace GraphPuzzles.LoopMultigraph

private def petersenAdjacentPatchWitness : Fin 31 → Fin 10 × Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15) :=
  ![(0, 0, 0, 0, ∅),
    (0, 2, 8, 9, {3, 10}),
    (0, 3, 6, 7, {1, 13}),
    (0, 6, 3, 7, {9, 13}),
    (0, 7, 3, 6, {1, 9}),
    (0, 8, 2, 9, {3, 6}),
    (0, 9, 2, 8, {6, 10}),
    (1, 3, 5, 9, {4, 11}),
    (1, 4, 7, 8, {2, 14}),
    (1, 5, 3, 9, {7, 11}),
    (1, 7, 4, 8, {5, 14}),
    (1, 8, 4, 7, {2, 5}),
    (1, 9, 3, 5, {4, 7}),
    (2, 4, 5, 6, {0, 12}),
    (2, 5, 4, 6, {0, 8}),
    (2, 6, 4, 5, {8, 12}),
    (2, 8, 0, 9, {6, 10}),
    (2, 9, 0, 8, {3, 6}),
    (3, 5, 1, 9, {4, 7}),
    (3, 6, 0, 7, {1, 9}),
    (3, 7, 0, 6, {9, 13}),
    (3, 9, 1, 5, {7, 11}),
    (4, 5, 2, 6, {8, 12}),
    (4, 6, 2, 5, {0, 8}),
    (4, 7, 1, 8, {2, 5}),
    (4, 8, 1, 7, {5, 14}),
    (5, 6, 2, 4, {0, 12}),
    (5, 9, 1, 3, {4, 11}),
    (6, 7, 0, 3, {1, 13}),
    (7, 8, 1, 4, {2, 14}),
    (8, 9, 0, 2, {3, 10})]

private def petersenAdjacentPatchCode : Fin 6 → Bool → Fin 10 → Fin 10 → Fin 31 :=
  ![(fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 12, 11],
    ![0, 0, 0, 0, 0, 17, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 19, 18, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 24, 23, 0, 0]] else ![![0, 22, 0, 0, 9, 0, 0, 0, 0, 0],
    ![15, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 20, 0, 10, 0, 0, 0, 0, 0, 0],
    ![0, 0, 25, 0, 16, 0, 0, 0, 0, 0],
    ![21, 0, 0, 6, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 10, 0, 0, 0, 7, 0, 0],
    ![0, 0, 25, 0, 0, 0, 0, 0, 13, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 27, 0, 0, 17, 0, 0, 0, 0],
    ![0, 0, 0, 26, 0, 19, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 22, 0, 0, 9, 0, 0, 0, 0, 0],
    ![15, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![21, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 30, 0, 0, 0, 0, 0, 0, 0, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 28, 0, 24, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 16, 0, 0, 0, 13, 0],
    ![0, 0, 0, 6, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 12, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 26, 0, 0, 18, 0, 0, 0],
    ![0, 0, 0, 0, 28, 0, 24, 0, 0, 0]] else ![![0, 22, 0, 0, 0, 8, 0, 0, 0, 0],
    ![15, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 20, 0, 0, 0, 0, 0, 7, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![29, 0, 0, 0, 0, 0, 0, 5, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 27, 0, 0, 17, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 1, 0, 0, 0],
    ![0, 20, 0, 10, 0, 0, 0, 0, 0, 0],
    ![0, 0, 25, 0, 0, 0, 0, 0, 13, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 30, 0, 0, 0, 0, 0, 0, 12, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 26, 0, 0, 18, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 9, 8, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![21, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![29, 0, 0, 0, 0, 0, 0, 5, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 17, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 28, 0, 0, 23, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 10, 0, 0, 0, 7, 0, 0],
    ![0, 0, 25, 0, 16, 0, 0, 0, 0, 0],
    ![0, 0, 0, 6, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 27, 0, 0, 0, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 28, 0, 0, 23, 0, 0]] else ![![0, 22, 0, 0, 0, 8, 0, 0, 0, 0],
    ![15, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![29, 0, 0, 0, 0, 0, 0, 0, 4, 0],
    ![0, 30, 0, 0, 0, 0, 0, 0, 12, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 19, 18, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 1, 0, 0, 0],
    ![0, 20, 0, 0, 0, 0, 0, 7, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 30, 0, 0, 0, 0, 0, 0, 0, 11],
    ![0, 0, 27, 0, 0, 0, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 24, 23, 0, 0]] else ![![0, 0, 0, 0, 9, 8, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 16, 0, 0, 0, 13, 0],
    ![21, 0, 0, 6, 0, 0, 0, 0, 0, 0],
    ![29, 0, 0, 0, 0, 0, 0, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 26, 0, 19, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]])]

private def petersenAdjacentPatchProperty (X : Finset (Fin 10)) (p q : Fin 10)
    (d : Fin 10 × Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15)) : Prop :=
  let (x₁, y₁, x₂, y₂, M) := d
  x₁ ≠ y₁ ∧ x₂ ≠ y₂ ∧
    Disjoint ({x₁, y₁} : Finset (Fin 10)) {x₂, y₂} ∧
    Disjoint ({x₁, y₁, x₂, y₂} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, q, x₁, y₁} ∧
    petersenClosedNeighborhood q = {p, q, x₂, y₂} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x₁, y₁, x₂, y₂}) M ∧
    ({x₁, y₁, x₂, y₂} \ X).card = 2 ∧
    (M ∩ petersen.dangling X).card = 1

private def petersenAdjacentPatchCertificate (i : Fin 6) (b : Bool) (p q : Fin 10) : Prop :=
  p ∈ petersenPatchShore i b → q ∈ petersenPatchShore i b → p ≠ q →
    (∃ e, petersen.Joins e p q) →
    petersenAdjacentPatchProperty (petersenPatchShore i b) p q
      (petersenAdjacentPatchWitness (petersenAdjacentPatchCode i b p q))

private theorem petersenAdjacentPatch_row_0_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_0_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 0 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_1_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 1 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_2_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 2 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_3_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 3 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_4_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 4 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_false_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 false 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_0 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 0 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_1 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 1 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_2 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 2 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_3 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 3 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_4 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 4 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_5 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 5 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_6 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 6 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_7 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 7 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_8 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 8 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_row_5_true_9 (q : Fin 10) :
    petersenAdjacentPatchCertificate 5 true 9 q := by
  unfold petersenAdjacentPatchCertificate petersenAdjacentPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenAdjacentPatch_certificate (i : Fin 6) (b : Bool) (p q : Fin 10) :
    petersenAdjacentPatchCertificate i b p q := by
  revert q
  fin_cases i <;> cases b <;> fin_cases p
  · exact petersenAdjacentPatch_row_0_false_0
  · exact petersenAdjacentPatch_row_0_false_1
  · exact petersenAdjacentPatch_row_0_false_2
  · exact petersenAdjacentPatch_row_0_false_3
  · exact petersenAdjacentPatch_row_0_false_4
  · exact petersenAdjacentPatch_row_0_false_5
  · exact petersenAdjacentPatch_row_0_false_6
  · exact petersenAdjacentPatch_row_0_false_7
  · exact petersenAdjacentPatch_row_0_false_8
  · exact petersenAdjacentPatch_row_0_false_9
  · exact petersenAdjacentPatch_row_0_true_0
  · exact petersenAdjacentPatch_row_0_true_1
  · exact petersenAdjacentPatch_row_0_true_2
  · exact petersenAdjacentPatch_row_0_true_3
  · exact petersenAdjacentPatch_row_0_true_4
  · exact petersenAdjacentPatch_row_0_true_5
  · exact petersenAdjacentPatch_row_0_true_6
  · exact petersenAdjacentPatch_row_0_true_7
  · exact petersenAdjacentPatch_row_0_true_8
  · exact petersenAdjacentPatch_row_0_true_9
  · exact petersenAdjacentPatch_row_1_false_0
  · exact petersenAdjacentPatch_row_1_false_1
  · exact petersenAdjacentPatch_row_1_false_2
  · exact petersenAdjacentPatch_row_1_false_3
  · exact petersenAdjacentPatch_row_1_false_4
  · exact petersenAdjacentPatch_row_1_false_5
  · exact petersenAdjacentPatch_row_1_false_6
  · exact petersenAdjacentPatch_row_1_false_7
  · exact petersenAdjacentPatch_row_1_false_8
  · exact petersenAdjacentPatch_row_1_false_9
  · exact petersenAdjacentPatch_row_1_true_0
  · exact petersenAdjacentPatch_row_1_true_1
  · exact petersenAdjacentPatch_row_1_true_2
  · exact petersenAdjacentPatch_row_1_true_3
  · exact petersenAdjacentPatch_row_1_true_4
  · exact petersenAdjacentPatch_row_1_true_5
  · exact petersenAdjacentPatch_row_1_true_6
  · exact petersenAdjacentPatch_row_1_true_7
  · exact petersenAdjacentPatch_row_1_true_8
  · exact petersenAdjacentPatch_row_1_true_9
  · exact petersenAdjacentPatch_row_2_false_0
  · exact petersenAdjacentPatch_row_2_false_1
  · exact petersenAdjacentPatch_row_2_false_2
  · exact petersenAdjacentPatch_row_2_false_3
  · exact petersenAdjacentPatch_row_2_false_4
  · exact petersenAdjacentPatch_row_2_false_5
  · exact petersenAdjacentPatch_row_2_false_6
  · exact petersenAdjacentPatch_row_2_false_7
  · exact petersenAdjacentPatch_row_2_false_8
  · exact petersenAdjacentPatch_row_2_false_9
  · exact petersenAdjacentPatch_row_2_true_0
  · exact petersenAdjacentPatch_row_2_true_1
  · exact petersenAdjacentPatch_row_2_true_2
  · exact petersenAdjacentPatch_row_2_true_3
  · exact petersenAdjacentPatch_row_2_true_4
  · exact petersenAdjacentPatch_row_2_true_5
  · exact petersenAdjacentPatch_row_2_true_6
  · exact petersenAdjacentPatch_row_2_true_7
  · exact petersenAdjacentPatch_row_2_true_8
  · exact petersenAdjacentPatch_row_2_true_9
  · exact petersenAdjacentPatch_row_3_false_0
  · exact petersenAdjacentPatch_row_3_false_1
  · exact petersenAdjacentPatch_row_3_false_2
  · exact petersenAdjacentPatch_row_3_false_3
  · exact petersenAdjacentPatch_row_3_false_4
  · exact petersenAdjacentPatch_row_3_false_5
  · exact petersenAdjacentPatch_row_3_false_6
  · exact petersenAdjacentPatch_row_3_false_7
  · exact petersenAdjacentPatch_row_3_false_8
  · exact petersenAdjacentPatch_row_3_false_9
  · exact petersenAdjacentPatch_row_3_true_0
  · exact petersenAdjacentPatch_row_3_true_1
  · exact petersenAdjacentPatch_row_3_true_2
  · exact petersenAdjacentPatch_row_3_true_3
  · exact petersenAdjacentPatch_row_3_true_4
  · exact petersenAdjacentPatch_row_3_true_5
  · exact petersenAdjacentPatch_row_3_true_6
  · exact petersenAdjacentPatch_row_3_true_7
  · exact petersenAdjacentPatch_row_3_true_8
  · exact petersenAdjacentPatch_row_3_true_9
  · exact petersenAdjacentPatch_row_4_false_0
  · exact petersenAdjacentPatch_row_4_false_1
  · exact petersenAdjacentPatch_row_4_false_2
  · exact petersenAdjacentPatch_row_4_false_3
  · exact petersenAdjacentPatch_row_4_false_4
  · exact petersenAdjacentPatch_row_4_false_5
  · exact petersenAdjacentPatch_row_4_false_6
  · exact petersenAdjacentPatch_row_4_false_7
  · exact petersenAdjacentPatch_row_4_false_8
  · exact petersenAdjacentPatch_row_4_false_9
  · exact petersenAdjacentPatch_row_4_true_0
  · exact petersenAdjacentPatch_row_4_true_1
  · exact petersenAdjacentPatch_row_4_true_2
  · exact petersenAdjacentPatch_row_4_true_3
  · exact petersenAdjacentPatch_row_4_true_4
  · exact petersenAdjacentPatch_row_4_true_5
  · exact petersenAdjacentPatch_row_4_true_6
  · exact petersenAdjacentPatch_row_4_true_7
  · exact petersenAdjacentPatch_row_4_true_8
  · exact petersenAdjacentPatch_row_4_true_9
  · exact petersenAdjacentPatch_row_5_false_0
  · exact petersenAdjacentPatch_row_5_false_1
  · exact petersenAdjacentPatch_row_5_false_2
  · exact petersenAdjacentPatch_row_5_false_3
  · exact petersenAdjacentPatch_row_5_false_4
  · exact petersenAdjacentPatch_row_5_false_5
  · exact petersenAdjacentPatch_row_5_false_6
  · exact petersenAdjacentPatch_row_5_false_7
  · exact petersenAdjacentPatch_row_5_false_8
  · exact petersenAdjacentPatch_row_5_false_9
  · exact petersenAdjacentPatch_row_5_true_0
  · exact petersenAdjacentPatch_row_5_true_1
  · exact petersenAdjacentPatch_row_5_true_2
  · exact petersenAdjacentPatch_row_5_true_3
  · exact petersenAdjacentPatch_row_5_true_4
  · exact petersenAdjacentPatch_row_5_true_5
  · exact petersenAdjacentPatch_row_5_true_6
  · exact petersenAdjacentPatch_row_5_true_7
  · exact petersenAdjacentPatch_row_5_true_8
  · exact petersenAdjacentPatch_row_5_true_9

/-- A finite Petersen completion patch with explicit boundary neighbors. -/
theorem IsSeparatingCut.petersen_adjacent_expansion_patch {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {p q : Fin 10} (hp : p ∈ X) (hq : q ∈ X) (hne : p ≠ q)
    (hadj : (∃ e, petersen.Joins e p q)) :
    ∃ x₁ y₁ x₂ y₂ : Fin 10, ∃ M : Finset (Fin 15),
    x₁ ≠ y₁ ∧ x₂ ≠ y₂ ∧
    Disjoint ({x₁, y₁} : Finset (Fin 10)) {x₂, y₂} ∧
    Disjoint ({x₁, y₁, x₂, y₂} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, q, x₁, y₁} ∧
    petersenClosedNeighborhood q = {p, q, x₂, y₂} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x₁, y₁, x₂, y₂}) M ∧
    ({x₁, y₁, x₂, y₂} \ X).card = 2 ∧
    (M ∩ petersen.dangling X).card = 1 := by
  obtain ⟨i, b, rfl⟩ := hs.eq_petersenPatchShore hX
  let d := petersenAdjacentPatchWitness (petersenAdjacentPatchCode i b p q)
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2, petersenAdjacentPatch_certificate i b p q hp hq hne hadj⟩

end GraphPuzzles.LoopMultigraph
