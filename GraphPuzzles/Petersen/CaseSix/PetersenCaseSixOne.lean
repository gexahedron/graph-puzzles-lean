import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixBase

/-! Explicit finite matching patches for Section 6.

Explicit witness data are checked by Lean kernel reduction.
The certificate checks do not depend on a search program. -/

namespace GraphPuzzles.LoopMultigraph

private def petersenOnePatchWitness : Fin 61 → Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15) :=
  ![(0, 0, 0, ∅),
    (0, 2, 6, {3, 10, 11}),
    (0, 2, 6, {3, 10, 14}),
    (0, 3, 9, {1, 12, 13}),
    (0, 3, 9, {1, 13, 14}),
    (0, 6, 2, {2, 9, 13}),
    (0, 6, 2, {7, 9, 13}),
    (0, 7, 8, {1, 8, 9}),
    (0, 7, 8, {1, 9, 11}),
    (0, 8, 7, {3, 6, 7}),
    (0, 8, 7, {3, 6, 12}),
    (0, 9, 3, {2, 6, 10}),
    (0, 9, 3, {6, 8, 10}),
    (1, 3, 7, {4, 10, 11}),
    (1, 3, 7, {4, 11, 12}),
    (1, 4, 5, {2, 10, 14}),
    (1, 4, 5, {2, 13, 14}),
    (1, 5, 4, {3, 7, 11}),
    (1, 5, 4, {7, 9, 11}),
    (1, 7, 3, {3, 5, 14}),
    (1, 7, 3, {5, 8, 14}),
    (1, 8, 9, {2, 5, 9}),
    (1, 8, 9, {2, 5, 12}),
    (1, 9, 8, {4, 7, 8}),
    (1, 9, 8, {4, 7, 13}),
    (2, 4, 8, {0, 11, 12}),
    (2, 4, 8, {0, 12, 13}),
    (2, 5, 9, {0, 8, 9}),
    (2, 5, 9, {0, 8, 14}),
    (2, 6, 0, {4, 8, 12}),
    (2, 6, 0, {5, 8, 12}),
    (2, 8, 4, {4, 6, 10}),
    (2, 8, 4, {6, 9, 10}),
    (2, 9, 5, {3, 5, 6}),
    (2, 9, 5, {3, 6, 13}),
    (3, 5, 6, {4, 6, 7}),
    (3, 5, 6, {4, 7, 14}),
    (3, 6, 5, {1, 5, 9}),
    (3, 6, 5, {1, 9, 10}),
    (3, 7, 1, {0, 9, 13}),
    (3, 7, 1, {6, 9, 13}),
    (3, 9, 0, {0, 7, 11}),
    (3, 9, 0, {5, 7, 11}),
    (4, 5, 1, {1, 8, 12}),
    (4, 5, 1, {6, 8, 12}),
    (4, 6, 7, {0, 7, 8}),
    (4, 6, 7, {0, 8, 10}),
    (4, 7, 6, {2, 5, 6}),
    (4, 7, 6, {2, 5, 11}),
    (4, 8, 2, {1, 5, 14}),
    (4, 8, 2, {5, 7, 14}),
    (5, 6, 3, {0, 2, 12}),
    (5, 6, 3, {0, 3, 12}),
    (5, 9, 2, {1, 4, 11}),
    (5, 9, 2, {2, 4, 11}),
    (6, 7, 4, {1, 3, 13}),
    (6, 7, 4, {1, 4, 13}),
    (7, 8, 0, {0, 2, 14}),
    (7, 8, 0, {2, 4, 14}),
    (8, 9, 1, {0, 3, 10}),
    (8, 9, 1, {1, 3, 10})]

private def petersenOnePatchCode : Fin 6 → Bool → Fin 10 → Fin 10 → Fin 61 :=
  ![(fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 7, 0, 0, 9],
    ![0, 0, 0, 0, 0, 23, 0, 21, 0, 0],
    ![0, 0, 0, 0, 0, 0, 27, 0, 33, 0],
    ![0, 0, 0, 0, 0, 0, 0, 37, 0, 35],
    ![0, 0, 0, 0, 0, 45, 0, 0, 47, 0]] else ![![0, 0, 44, 18, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 6, 30, 0, 0, 0, 0, 0],
    ![40, 0, 0, 0, 20, 0, 0, 0, 0, 0],
    ![32, 50, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 42, 12, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 14, 0, 0, 19, 0],
    ![0, 0, 0, 0, 0, 25, 0, 49, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 10, 8, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 53, 0, 0, 0, 0, 33, 0],
    ![0, 0, 52, 0, 0, 0, 0, 37, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 43, 0, 0, 17],
    ![0, 0, 0, 0, 30, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 42, 0, 0, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![60, 0, 0, 0, 22, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![55, 48, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 26, 0, 0, 31],
    ![0, 0, 0, 0, 0, 0, 3, 0, 11, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 24, 22, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 51, 0, 0, 0, 0, 35],
    ![0, 0, 0, 56, 0, 0, 0, 0, 47, 0]] else ![![0, 0, 44, 0, 0, 0, 0, 16, 0, 0],
    ![0, 0, 0, 0, 0, 29, 0, 5, 0, 0],
    ![40, 0, 0, 0, 0, 14, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 58, 10, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![34, 54, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 6, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 39, 0, 19, 0],
    ![0, 50, 0, 0, 0, 0, 26, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 59, 24, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 36, 52, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 0, 16, 0, 17],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 41, 0, 4, 0, 0],
    ![0, 0, 0, 0, 57, 0, 0, 0, 0, 9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![34, 0, 0, 0, 28, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![55, 0, 0, 0, 0, 45, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 20, 0, 0, 0, 0, 13],
    ![0, 0, 0, 0, 0, 0, 0, 49, 0, 31],
    ![0, 0, 12, 0, 0, 0, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 53, 28, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 46, 56, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 43, 0, 15, 0],
    ![0, 0, 0, 0, 0, 29, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 58, 0, 0, 0, 0, 7, 0, 0, 0],
    ![60, 0, 0, 0, 0, 23, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![38, 36, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 0, 1],
    ![0, 0, 0, 0, 0, 0, 39, 0, 0, 13],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 59, 0, 0, 0, 0, 21, 0, 0],
    ![0, 54, 0, 0, 0, 0, 27, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 48, 46, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 18, 0, 0, 0, 0, 15, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![32, 0, 0, 0, 0, 25, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 41, 0, 0, 11, 0],
    ![0, 0, 0, 8, 57, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![38, 0, 0, 0, 51, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]])]

private def petersenOnePatchProperty (X : Finset (Fin 10)) (p q : Fin 10)
    (d : Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15)) : Prop :=
  let (x, y, z, M) := d
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    Disjoint ({x, y, z} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x, y, z} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x, y}) M ∧
    (M ∩ petersen.dangling X).card + ({x, y} \ X).card = 3

private def petersenOnePatchCertificate (i : Fin 6) (b : Bool) (p q : Fin 10) : Prop :=
  p ∈ petersenPatchShore i b → q ∈ petersenPatchShore i b → p ≠ q →
    (∀ e, ¬ petersen.Joins e p q) →
    petersenOnePatchProperty (petersenPatchShore i b) p q
      (petersenOnePatchWitness (petersenOnePatchCode i b p q))

private theorem petersenOnePatch_row_0_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 0 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_0_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 0 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 1 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_1_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 1 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 2 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_2_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 2 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 3 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_3_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 3 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 4 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_4_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 4 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_0 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_1 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_2 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_3 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_4 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_5 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_6 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_7 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_8 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_false_9 (q : Fin 10) :
    petersenOnePatchCertificate 5 false 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_0 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 0 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_1 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 1 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_2 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 2 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_3 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 3 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_4 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 4 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_5 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 5 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_6 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 6 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_7 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 7 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_8 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 8 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_row_5_true_9 (q : Fin 10) :
    petersenOnePatchCertificate 5 true 9 q := by
  unfold petersenOnePatchCertificate petersenOnePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOnePatch_certificate (i : Fin 6) (b : Bool) (p q : Fin 10) :
    petersenOnePatchCertificate i b p q := by
  revert q
  fin_cases i <;> cases b <;> fin_cases p
  · exact petersenOnePatch_row_0_false_0
  · exact petersenOnePatch_row_0_false_1
  · exact petersenOnePatch_row_0_false_2
  · exact petersenOnePatch_row_0_false_3
  · exact petersenOnePatch_row_0_false_4
  · exact petersenOnePatch_row_0_false_5
  · exact petersenOnePatch_row_0_false_6
  · exact petersenOnePatch_row_0_false_7
  · exact petersenOnePatch_row_0_false_8
  · exact petersenOnePatch_row_0_false_9
  · exact petersenOnePatch_row_0_true_0
  · exact petersenOnePatch_row_0_true_1
  · exact petersenOnePatch_row_0_true_2
  · exact petersenOnePatch_row_0_true_3
  · exact petersenOnePatch_row_0_true_4
  · exact petersenOnePatch_row_0_true_5
  · exact petersenOnePatch_row_0_true_6
  · exact petersenOnePatch_row_0_true_7
  · exact petersenOnePatch_row_0_true_8
  · exact petersenOnePatch_row_0_true_9
  · exact petersenOnePatch_row_1_false_0
  · exact petersenOnePatch_row_1_false_1
  · exact petersenOnePatch_row_1_false_2
  · exact petersenOnePatch_row_1_false_3
  · exact petersenOnePatch_row_1_false_4
  · exact petersenOnePatch_row_1_false_5
  · exact petersenOnePatch_row_1_false_6
  · exact petersenOnePatch_row_1_false_7
  · exact petersenOnePatch_row_1_false_8
  · exact petersenOnePatch_row_1_false_9
  · exact petersenOnePatch_row_1_true_0
  · exact petersenOnePatch_row_1_true_1
  · exact petersenOnePatch_row_1_true_2
  · exact petersenOnePatch_row_1_true_3
  · exact petersenOnePatch_row_1_true_4
  · exact petersenOnePatch_row_1_true_5
  · exact petersenOnePatch_row_1_true_6
  · exact petersenOnePatch_row_1_true_7
  · exact petersenOnePatch_row_1_true_8
  · exact petersenOnePatch_row_1_true_9
  · exact petersenOnePatch_row_2_false_0
  · exact petersenOnePatch_row_2_false_1
  · exact petersenOnePatch_row_2_false_2
  · exact petersenOnePatch_row_2_false_3
  · exact petersenOnePatch_row_2_false_4
  · exact petersenOnePatch_row_2_false_5
  · exact petersenOnePatch_row_2_false_6
  · exact petersenOnePatch_row_2_false_7
  · exact petersenOnePatch_row_2_false_8
  · exact petersenOnePatch_row_2_false_9
  · exact petersenOnePatch_row_2_true_0
  · exact petersenOnePatch_row_2_true_1
  · exact petersenOnePatch_row_2_true_2
  · exact petersenOnePatch_row_2_true_3
  · exact petersenOnePatch_row_2_true_4
  · exact petersenOnePatch_row_2_true_5
  · exact petersenOnePatch_row_2_true_6
  · exact petersenOnePatch_row_2_true_7
  · exact petersenOnePatch_row_2_true_8
  · exact petersenOnePatch_row_2_true_9
  · exact petersenOnePatch_row_3_false_0
  · exact petersenOnePatch_row_3_false_1
  · exact petersenOnePatch_row_3_false_2
  · exact petersenOnePatch_row_3_false_3
  · exact petersenOnePatch_row_3_false_4
  · exact petersenOnePatch_row_3_false_5
  · exact petersenOnePatch_row_3_false_6
  · exact petersenOnePatch_row_3_false_7
  · exact petersenOnePatch_row_3_false_8
  · exact petersenOnePatch_row_3_false_9
  · exact petersenOnePatch_row_3_true_0
  · exact petersenOnePatch_row_3_true_1
  · exact petersenOnePatch_row_3_true_2
  · exact petersenOnePatch_row_3_true_3
  · exact petersenOnePatch_row_3_true_4
  · exact petersenOnePatch_row_3_true_5
  · exact petersenOnePatch_row_3_true_6
  · exact petersenOnePatch_row_3_true_7
  · exact petersenOnePatch_row_3_true_8
  · exact petersenOnePatch_row_3_true_9
  · exact petersenOnePatch_row_4_false_0
  · exact petersenOnePatch_row_4_false_1
  · exact petersenOnePatch_row_4_false_2
  · exact petersenOnePatch_row_4_false_3
  · exact petersenOnePatch_row_4_false_4
  · exact petersenOnePatch_row_4_false_5
  · exact petersenOnePatch_row_4_false_6
  · exact petersenOnePatch_row_4_false_7
  · exact petersenOnePatch_row_4_false_8
  · exact petersenOnePatch_row_4_false_9
  · exact petersenOnePatch_row_4_true_0
  · exact petersenOnePatch_row_4_true_1
  · exact petersenOnePatch_row_4_true_2
  · exact petersenOnePatch_row_4_true_3
  · exact petersenOnePatch_row_4_true_4
  · exact petersenOnePatch_row_4_true_5
  · exact petersenOnePatch_row_4_true_6
  · exact petersenOnePatch_row_4_true_7
  · exact petersenOnePatch_row_4_true_8
  · exact petersenOnePatch_row_4_true_9
  · exact petersenOnePatch_row_5_false_0
  · exact petersenOnePatch_row_5_false_1
  · exact petersenOnePatch_row_5_false_2
  · exact petersenOnePatch_row_5_false_3
  · exact petersenOnePatch_row_5_false_4
  · exact petersenOnePatch_row_5_false_5
  · exact petersenOnePatch_row_5_false_6
  · exact petersenOnePatch_row_5_false_7
  · exact petersenOnePatch_row_5_false_8
  · exact petersenOnePatch_row_5_false_9
  · exact petersenOnePatch_row_5_true_0
  · exact petersenOnePatch_row_5_true_1
  · exact petersenOnePatch_row_5_true_2
  · exact petersenOnePatch_row_5_true_3
  · exact petersenOnePatch_row_5_true_4
  · exact petersenOnePatch_row_5_true_5
  · exact petersenOnePatch_row_5_true_6
  · exact petersenOnePatch_row_5_true_7
  · exact petersenOnePatch_row_5_true_8
  · exact petersenOnePatch_row_5_true_9

/-- A finite Petersen completion patch with explicit boundary neighbors. -/
theorem IsSeparatingCut.petersen_one_expansion_patch {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {p q : Fin 10} (hp : p ∈ X) (hq : q ∈ X) (hne : p ≠ q)
    (hadj : (∀ e, ¬ petersen.Joins e p q)) :
    ∃ x y z : Fin 10, ∃ M : Finset (Fin 15),
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    Disjoint ({x, y, z} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x, y, z} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x, y}) M ∧
    (M ∩ petersen.dangling X).card + ({x, y} \ X).card = 3 := by
  obtain ⟨i, b, rfl⟩ := hs.eq_petersenPatchShore hX
  let d := petersenOnePatchWitness (petersenOnePatchCode i b p q)
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2, petersenOnePatch_certificate i b p q hp hq hne hadj⟩

end GraphPuzzles.LoopMultigraph
