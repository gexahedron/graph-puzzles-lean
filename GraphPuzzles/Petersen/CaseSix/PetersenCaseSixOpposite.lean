import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixBase

/-! Explicit finite matching patches for Section 6.

Explicit witness data are checked by Lean kernel reduction.
The certificate checks do not depend on a search program. -/

namespace GraphPuzzles.LoopMultigraph

private def petersenOppositePatchWitness : Fin 121 → Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15) :=
  ![(0, 0, 0, ∅),
    (0, 2, 6, {3, 10, 11}),
    (0, 2, 6, {3, 10, 14}),
    (0, 2, 6, {3, 11, 12}),
    (0, 2, 6, {3, 13, 14}),
    (0, 2, 6, {8, 10, 14}),
    (0, 2, 6, {9, 10, 11}),
    (0, 3, 9, {1, 10, 14}),
    (0, 3, 9, {1, 11, 12}),
    (0, 3, 9, {1, 12, 13}),
    (0, 3, 9, {1, 13, 14}),
    (0, 3, 9, {6, 12, 13}),
    (0, 3, 9, {7, 13, 14}),
    (0, 6, 2, {2, 9, 10}),
    (0, 6, 2, {2, 9, 13}),
    (0, 6, 2, {3, 7, 13}),
    (0, 6, 2, {7, 9, 13}),
    (0, 7, 8, {1, 3, 11}),
    (0, 7, 8, {1, 8, 9}),
    (0, 7, 8, {1, 8, 14}),
    (0, 7, 8, {1, 9, 11}),
    (0, 7, 8, {2, 9, 11}),
    (0, 7, 8, {6, 8, 9}),
    (0, 8, 7, {1, 3, 12}),
    (0, 8, 7, {3, 6, 7}),
    (0, 8, 7, {3, 6, 12}),
    (0, 8, 7, {6, 7, 9}),
    (0, 9, 3, {1, 8, 10}),
    (0, 9, 3, {2, 6, 10}),
    (0, 9, 3, {2, 6, 13}),
    (0, 9, 3, {6, 8, 10}),
    (1, 3, 7, {4, 10, 11}),
    (1, 3, 7, {4, 10, 14}),
    (1, 3, 7, {4, 11, 12}),
    (1, 3, 7, {4, 12, 13}),
    (1, 3, 7, {5, 11, 12}),
    (1, 3, 7, {9, 10, 11}),
    (1, 4, 5, {2, 10, 11}),
    (1, 4, 5, {2, 10, 14}),
    (1, 4, 5, {2, 12, 13}),
    (1, 4, 5, {2, 13, 14}),
    (1, 4, 5, {7, 13, 14}),
    (1, 4, 5, {8, 10, 14}),
    (1, 5, 4, {2, 9, 11}),
    (1, 5, 4, {3, 7, 11}),
    (1, 5, 4, {3, 7, 14}),
    (1, 5, 4, {7, 9, 11}),
    (1, 7, 3, {3, 5, 11}),
    (1, 7, 3, {3, 5, 14}),
    (1, 7, 3, {4, 8, 14}),
    (1, 7, 3, {5, 8, 14}),
    (1, 8, 9, {2, 4, 12}),
    (1, 8, 9, {2, 5, 9}),
    (1, 8, 9, {2, 5, 12}),
    (1, 8, 9, {2, 9, 10}),
    (1, 8, 9, {3, 5, 12}),
    (1, 8, 9, {5, 7, 9}),
    (1, 9, 8, {2, 4, 13}),
    (1, 9, 8, {4, 7, 8}),
    (1, 9, 8, {4, 7, 13}),
    (1, 9, 8, {5, 7, 8}),
    (2, 4, 8, {0, 10, 11}),
    (2, 4, 8, {0, 11, 12}),
    (2, 4, 8, {0, 12, 13}),
    (2, 4, 8, {0, 13, 14}),
    (2, 4, 8, {5, 11, 12}),
    (2, 4, 8, {6, 12, 13}),
    (2, 5, 9, {0, 3, 14}),
    (2, 5, 9, {0, 8, 9}),
    (2, 5, 9, {0, 8, 14}),
    (2, 5, 9, {0, 9, 11}),
    (2, 5, 9, {4, 8, 14}),
    (2, 5, 9, {6, 8, 9}),
    (2, 6, 0, {4, 8, 12}),
    (2, 6, 0, {5, 8, 12}),
    (2, 8, 4, {0, 9, 10}),
    (2, 8, 4, {4, 6, 10}),
    (2, 8, 4, {4, 6, 12}),
    (2, 8, 4, {6, 9, 10}),
    (2, 9, 5, {0, 3, 13}),
    (2, 9, 5, {3, 5, 6}),
    (2, 9, 5, {3, 6, 13}),
    (2, 9, 5, {5, 6, 8}),
    (3, 5, 6, {0, 7, 14}),
    (3, 5, 6, {1, 4, 14}),
    (3, 5, 6, {4, 6, 7}),
    (3, 5, 6, {4, 6, 12}),
    (3, 5, 6, {4, 7, 14}),
    (3, 5, 6, {6, 7, 9}),
    (3, 6, 5, {1, 4, 10}),
    (3, 6, 5, {1, 5, 9}),
    (3, 6, 5, {1, 9, 10}),
    (3, 6, 5, {5, 7, 9}),
    (3, 7, 1, {0, 9, 13}),
    (3, 7, 1, {6, 9, 13}),
    (3, 9, 0, {0, 7, 11}),
    (3, 9, 0, {5, 7, 11}),
    (4, 5, 1, {1, 8, 12}),
    (4, 5, 1, {6, 8, 12}),
    (4, 6, 7, {0, 2, 10}),
    (4, 6, 7, {0, 7, 8}),
    (4, 6, 7, {0, 7, 13}),
    (4, 6, 7, {0, 8, 10}),
    (4, 6, 7, {1, 8, 10}),
    (4, 6, 7, {5, 7, 8}),
    (4, 7, 6, {0, 2, 11}),
    (4, 7, 6, {2, 5, 6}),
    (4, 7, 6, {2, 5, 11}),
    (4, 7, 6, {5, 6, 8}),
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

private def petersenOppositePatchCode : Fin 6 → Bool → Fin 10 → Fin 10 → Fin 121 :=
  ![(fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 21, 25, 20, 19, 0, 0, 0, 0, 0],
    ![54, 0, 55, 59, 53, 0, 0, 0, 0, 0],
    ![81, 71, 0, 70, 69, 0, 0, 0, 0, 0],
    ![91, 87, 86, 0, 83, 0, 0, 0, 0, 0],
    ![103, 107, 102, 101, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 97, 43, 45, 44],
    ![0, 0, 0, 0, 0, 73, 0, 14, 13, 15],
    ![0, 0, 0, 0, 0, 49, 93, 0, 48, 47],
    ![0, 0, 0, 0, 0, 77, 75, 109, 0, 76],
    ![0, 0, 0, 0, 0, 95, 27, 29, 28, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![36, 0, 0, 0, 50, 0, 34, 0, 0, 31],
    ![66, 110, 0, 0, 0, 0, 63, 0, 0, 61],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 21, 0, 0, 19, 0, 18, 0, 0, 24],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![81, 114, 0, 0, 82, 0, 79, 0, 0, 0],
    ![91, 92, 0, 0, 111, 0, 0, 0, 0, 89],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 98, 46, 0, 0, 0, 43, 45, 0],
    ![0, 0, 0, 6, 0, 73, 0, 4, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 11, 0, 0, 95, 0, 10, 7, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 119, 56, 0, 51, 0, 52, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 108, 116, 0, 105, 0, 0, 106, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![78, 65, 0, 0, 0, 62, 0, 64, 0, 0],
    ![0, 12, 30, 0, 0, 8, 0, 10, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![54, 0, 55, 0, 0, 58, 0, 52, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![88, 87, 112, 0, 0, 0, 0, 84, 0, 0],
    ![115, 107, 108, 0, 0, 105, 0, 0, 0, 0]] else ![![0, 0, 0, 41, 0, 0, 97, 0, 38, 37],
    ![0, 0, 0, 16, 74, 0, 0, 0, 13, 15],
    ![0, 0, 0, 0, 35, 0, 93, 0, 32, 31],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 26, 117, 0, 23, 0, 0, 24],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 113, 82, 0, 79, 0, 80, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 5, 3, 0, 14, 0, 1],
    ![94, 0, 0, 0, 50, 49, 0, 0, 0, 47],
    ![66, 0, 0, 0, 0, 62, 0, 109, 0, 61],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![120, 0, 0, 0, 60, 58, 0, 57, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![88, 0, 0, 0, 111, 0, 0, 84, 0, 85],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 42, 46, 0, 0, 39, 0, 38, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 96, 11, 0, 0, 0, 9, 0, 7, 0],
    ![0, 118, 25, 26, 0, 0, 23, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 71, 0, 70, 0, 0, 68, 0, 80, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 104, 102, 116, 0, 0, 0, 0, 99, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![36, 0, 0, 0, 0, 33, 34, 0, 48, 0],
    ![78, 110, 0, 0, 0, 77, 75, 0, 0, 0],
    ![0, 12, 0, 0, 0, 8, 9, 0, 28, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![72, 114, 0, 0, 0, 0, 68, 0, 67, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![115, 104, 0, 0, 0, 100, 0, 0, 99, 0]] else ![![0, 0, 98, 41, 0, 0, 0, 40, 0, 37],
    ![0, 0, 0, 6, 74, 0, 0, 4, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 22, 20, 117, 0, 0, 0, 0, 17],
    ![0, 0, 119, 59, 60, 0, 0, 57, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 86, 0, 83, 0, 0, 90, 0, 85],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 16, 5, 3, 0, 0, 2, 0],
    ![94, 0, 0, 0, 35, 33, 0, 0, 32, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![120, 0, 0, 56, 53, 51, 0, 0, 0, 0],
    ![72, 0, 0, 113, 69, 0, 0, 0, 67, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![103, 0, 0, 101, 0, 100, 0, 0, 106, 0]] else ![![0, 0, 42, 0, 0, 0, 39, 40, 0, 44],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 65, 0, 0, 0, 0, 63, 64, 0, 76],
    ![0, 96, 30, 0, 0, 0, 27, 29, 0, 0],
    ![0, 118, 22, 0, 0, 0, 18, 0, 0, 17],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 92, 112, 0, 0, 0, 0, 90, 0, 89],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]])]

private def petersenOppositePatchProperty (X : Finset (Fin 10)) (p q : Fin 10)
    (d : Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15)) : Prop :=
  let (x, y, z, M) := d
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    Disjoint ({x, y, z} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x, y, z} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x, y}) M ∧
    (M ∩ petersen.dangling X).card + 1 + ({x, y} \ X).card = 3

private def petersenOppositePatchCertificate (i : Fin 6) (b : Bool) (p q : Fin 10) : Prop :=
  p ∈ petersenPatchShore i b → q ∉ petersenPatchShore i b → p ≠ q →
    (∀ e, ¬ petersen.Joins e p q) →
    petersenOppositePatchProperty (petersenPatchShore i b) p q
      (petersenOppositePatchWitness (petersenOppositePatchCode i b p q))

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 0 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_0_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 0 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 1 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_1_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 1 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 2 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_2_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 2 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 3 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_3_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 3 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 4 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_4_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 4 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_0 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_1 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_2 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_3 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_4 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_5 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_6 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_7 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_8 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_false_9 (q : Fin 10) :
    petersenOppositePatchCertificate 5 false 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_0 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 0 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_1 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 1 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_2 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 2 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_3 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 3 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_4 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 4 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_5 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 5 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_6 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 6 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_7 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 7 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_8 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 8 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenOppositePatch_row_5_true_9 (q : Fin 10) :
    petersenOppositePatchCertificate 5 true 9 q := by
  unfold petersenOppositePatchCertificate petersenOppositePatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenOppositePatch_certificate (i : Fin 6) (b : Bool) (p q : Fin 10) :
    petersenOppositePatchCertificate i b p q := by
  revert q
  fin_cases i <;> cases b <;> fin_cases p
  · exact petersenOppositePatch_row_0_false_0
  · exact petersenOppositePatch_row_0_false_1
  · exact petersenOppositePatch_row_0_false_2
  · exact petersenOppositePatch_row_0_false_3
  · exact petersenOppositePatch_row_0_false_4
  · exact petersenOppositePatch_row_0_false_5
  · exact petersenOppositePatch_row_0_false_6
  · exact petersenOppositePatch_row_0_false_7
  · exact petersenOppositePatch_row_0_false_8
  · exact petersenOppositePatch_row_0_false_9
  · exact petersenOppositePatch_row_0_true_0
  · exact petersenOppositePatch_row_0_true_1
  · exact petersenOppositePatch_row_0_true_2
  · exact petersenOppositePatch_row_0_true_3
  · exact petersenOppositePatch_row_0_true_4
  · exact petersenOppositePatch_row_0_true_5
  · exact petersenOppositePatch_row_0_true_6
  · exact petersenOppositePatch_row_0_true_7
  · exact petersenOppositePatch_row_0_true_8
  · exact petersenOppositePatch_row_0_true_9
  · exact petersenOppositePatch_row_1_false_0
  · exact petersenOppositePatch_row_1_false_1
  · exact petersenOppositePatch_row_1_false_2
  · exact petersenOppositePatch_row_1_false_3
  · exact petersenOppositePatch_row_1_false_4
  · exact petersenOppositePatch_row_1_false_5
  · exact petersenOppositePatch_row_1_false_6
  · exact petersenOppositePatch_row_1_false_7
  · exact petersenOppositePatch_row_1_false_8
  · exact petersenOppositePatch_row_1_false_9
  · exact petersenOppositePatch_row_1_true_0
  · exact petersenOppositePatch_row_1_true_1
  · exact petersenOppositePatch_row_1_true_2
  · exact petersenOppositePatch_row_1_true_3
  · exact petersenOppositePatch_row_1_true_4
  · exact petersenOppositePatch_row_1_true_5
  · exact petersenOppositePatch_row_1_true_6
  · exact petersenOppositePatch_row_1_true_7
  · exact petersenOppositePatch_row_1_true_8
  · exact petersenOppositePatch_row_1_true_9
  · exact petersenOppositePatch_row_2_false_0
  · exact petersenOppositePatch_row_2_false_1
  · exact petersenOppositePatch_row_2_false_2
  · exact petersenOppositePatch_row_2_false_3
  · exact petersenOppositePatch_row_2_false_4
  · exact petersenOppositePatch_row_2_false_5
  · exact petersenOppositePatch_row_2_false_6
  · exact petersenOppositePatch_row_2_false_7
  · exact petersenOppositePatch_row_2_false_8
  · exact petersenOppositePatch_row_2_false_9
  · exact petersenOppositePatch_row_2_true_0
  · exact petersenOppositePatch_row_2_true_1
  · exact petersenOppositePatch_row_2_true_2
  · exact petersenOppositePatch_row_2_true_3
  · exact petersenOppositePatch_row_2_true_4
  · exact petersenOppositePatch_row_2_true_5
  · exact petersenOppositePatch_row_2_true_6
  · exact petersenOppositePatch_row_2_true_7
  · exact petersenOppositePatch_row_2_true_8
  · exact petersenOppositePatch_row_2_true_9
  · exact petersenOppositePatch_row_3_false_0
  · exact petersenOppositePatch_row_3_false_1
  · exact petersenOppositePatch_row_3_false_2
  · exact petersenOppositePatch_row_3_false_3
  · exact petersenOppositePatch_row_3_false_4
  · exact petersenOppositePatch_row_3_false_5
  · exact petersenOppositePatch_row_3_false_6
  · exact petersenOppositePatch_row_3_false_7
  · exact petersenOppositePatch_row_3_false_8
  · exact petersenOppositePatch_row_3_false_9
  · exact petersenOppositePatch_row_3_true_0
  · exact petersenOppositePatch_row_3_true_1
  · exact petersenOppositePatch_row_3_true_2
  · exact petersenOppositePatch_row_3_true_3
  · exact petersenOppositePatch_row_3_true_4
  · exact petersenOppositePatch_row_3_true_5
  · exact petersenOppositePatch_row_3_true_6
  · exact petersenOppositePatch_row_3_true_7
  · exact petersenOppositePatch_row_3_true_8
  · exact petersenOppositePatch_row_3_true_9
  · exact petersenOppositePatch_row_4_false_0
  · exact petersenOppositePatch_row_4_false_1
  · exact petersenOppositePatch_row_4_false_2
  · exact petersenOppositePatch_row_4_false_3
  · exact petersenOppositePatch_row_4_false_4
  · exact petersenOppositePatch_row_4_false_5
  · exact petersenOppositePatch_row_4_false_6
  · exact petersenOppositePatch_row_4_false_7
  · exact petersenOppositePatch_row_4_false_8
  · exact petersenOppositePatch_row_4_false_9
  · exact petersenOppositePatch_row_4_true_0
  · exact petersenOppositePatch_row_4_true_1
  · exact petersenOppositePatch_row_4_true_2
  · exact petersenOppositePatch_row_4_true_3
  · exact petersenOppositePatch_row_4_true_4
  · exact petersenOppositePatch_row_4_true_5
  · exact petersenOppositePatch_row_4_true_6
  · exact petersenOppositePatch_row_4_true_7
  · exact petersenOppositePatch_row_4_true_8
  · exact petersenOppositePatch_row_4_true_9
  · exact petersenOppositePatch_row_5_false_0
  · exact petersenOppositePatch_row_5_false_1
  · exact petersenOppositePatch_row_5_false_2
  · exact petersenOppositePatch_row_5_false_3
  · exact petersenOppositePatch_row_5_false_4
  · exact petersenOppositePatch_row_5_false_5
  · exact petersenOppositePatch_row_5_false_6
  · exact petersenOppositePatch_row_5_false_7
  · exact petersenOppositePatch_row_5_false_8
  · exact petersenOppositePatch_row_5_false_9
  · exact petersenOppositePatch_row_5_true_0
  · exact petersenOppositePatch_row_5_true_1
  · exact petersenOppositePatch_row_5_true_2
  · exact petersenOppositePatch_row_5_true_3
  · exact petersenOppositePatch_row_5_true_4
  · exact petersenOppositePatch_row_5_true_5
  · exact petersenOppositePatch_row_5_true_6
  · exact petersenOppositePatch_row_5_true_7
  · exact petersenOppositePatch_row_5_true_8
  · exact petersenOppositePatch_row_5_true_9

/-- A finite Petersen completion patch with explicit boundary neighbors. -/
theorem IsSeparatingCut.petersen_opposite_expansion_patch {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {p q : Fin 10} (hp : p ∈ X) (hq : q ∉ X) (hne : p ≠ q)
    (hadj : (∀ e, ¬ petersen.Joins e p q)) :
    ∃ x y z : Fin 10, ∃ M : Finset (Fin 15),
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    Disjoint ({x, y, z} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x, y, z} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x, y}) M ∧
    (M ∩ petersen.dangling X).card + 1 + ({x, y} \ X).card = 3 := by
  obtain ⟨i, b, rfl⟩ := hs.eq_petersenPatchShore hX
  let d := petersenOppositePatchWitness (petersenOppositePatchCode i b p q)
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2, petersenOppositePatch_certificate i b p q hp hq hne hadj⟩

end GraphPuzzles.LoopMultigraph
