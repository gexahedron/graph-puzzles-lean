import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixBase

/-! Explicit finite matching patches for Section 6.

Explicit witness data are checked by Lean kernel reduction.
The certificate checks do not depend on a search program. -/

namespace GraphPuzzles.LoopMultigraph

private def petersenTwoPatchWitness : Fin 121 → Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15) :=
  ![(0, 0, 0, 0, 0, 0, ∅),
    (0, 2, 6, 3, 6, 5, {9, 10}),
    (0, 2, 6, 3, 9, 0, {10, 11}),
    (0, 2, 6, 4, 6, 7, {8, 10}),
    (0, 2, 6, 4, 8, 2, {10, 14}),
    (0, 2, 6, 5, 6, 3, {3, 12}),
    (0, 2, 6, 5, 9, 2, {3, 11}),
    (0, 2, 6, 6, 7, 4, {3, 13}),
    (0, 2, 6, 7, 8, 0, {3, 14}),
    (0, 3, 9, 1, 7, 3, {13, 14}),
    (0, 3, 9, 1, 9, 8, {7, 13}),
    (0, 3, 9, 2, 6, 0, {12, 13}),
    (0, 3, 9, 2, 9, 5, {6, 13}),
    (0, 3, 9, 5, 6, 3, {1, 12}),
    (0, 3, 9, 5, 9, 2, {1, 11}),
    (0, 3, 9, 7, 8, 0, {1, 14}),
    (0, 3, 9, 8, 9, 1, {1, 10}),
    (0, 6, 2, 2, 8, 4, {9, 10}),
    (0, 6, 2, 2, 9, 5, {3, 13}),
    (0, 6, 2, 3, 9, 0, {7, 13}),
    (0, 6, 2, 7, 8, 0, {2, 9}),
    (0, 7, 8, 1, 3, 7, {9, 11}),
    (0, 7, 8, 1, 8, 9, {2, 9}),
    (0, 7, 8, 2, 6, 0, {8, 9}),
    (0, 7, 8, 2, 8, 4, {6, 9}),
    (0, 7, 8, 3, 9, 0, {1, 11}),
    (0, 7, 8, 4, 6, 7, {1, 8}),
    (0, 7, 8, 4, 8, 2, {1, 14}),
    (0, 7, 8, 8, 9, 1, {1, 3}),
    (0, 8, 7, 2, 6, 0, {3, 12}),
    (0, 8, 7, 3, 7, 1, {6, 9}),
    (0, 8, 7, 3, 9, 0, {6, 7}),
    (0, 8, 7, 6, 7, 4, {1, 3}),
    (0, 9, 3, 2, 6, 0, {8, 10}),
    (0, 9, 3, 3, 6, 5, {1, 10}),
    (0, 9, 3, 3, 7, 1, {6, 13}),
    (0, 9, 3, 7, 8, 0, {2, 6}),
    (1, 3, 7, 0, 7, 8, {9, 11}),
    (1, 3, 7, 0, 9, 3, {10, 11}),
    (1, 3, 7, 4, 5, 1, {11, 12}),
    (1, 3, 7, 4, 7, 6, {5, 11}),
    (1, 3, 7, 5, 6, 3, {4, 12}),
    (1, 3, 7, 6, 7, 4, {4, 13}),
    (1, 3, 7, 7, 8, 0, {4, 14}),
    (1, 3, 7, 8, 9, 1, {4, 10}),
    (1, 4, 5, 2, 5, 9, {8, 14}),
    (1, 4, 5, 2, 8, 4, {10, 14}),
    (1, 4, 5, 3, 5, 6, {7, 14}),
    (1, 4, 5, 3, 7, 1, {13, 14}),
    (1, 4, 5, 5, 6, 3, {2, 12}),
    (1, 4, 5, 5, 9, 2, {2, 11}),
    (1, 4, 5, 6, 7, 4, {2, 13}),
    (1, 4, 5, 8, 9, 1, {2, 10}),
    (1, 5, 4, 3, 7, 1, {9, 11}),
    (1, 5, 4, 4, 7, 6, {2, 11}),
    (1, 5, 4, 4, 8, 2, {7, 14}),
    (1, 5, 4, 8, 9, 1, {3, 7}),
    (1, 7, 3, 3, 5, 6, {4, 14}),
    (1, 7, 3, 3, 9, 0, {5, 11}),
    (1, 7, 3, 4, 5, 1, {8, 14}),
    (1, 7, 3, 8, 9, 1, {3, 5}),
    (1, 8, 9, 0, 7, 8, {2, 9}),
    (1, 8, 9, 0, 9, 3, {2, 10}),
    (1, 8, 9, 2, 4, 8, {5, 12}),
    (1, 8, 9, 2, 9, 5, {3, 5}),
    (1, 8, 9, 3, 7, 1, {5, 9}),
    (1, 8, 9, 3, 9, 0, {5, 7}),
    (1, 8, 9, 4, 5, 1, {2, 12}),
    (1, 8, 9, 5, 9, 2, {2, 4}),
    (1, 9, 8, 3, 7, 1, {4, 13}),
    (1, 9, 8, 4, 5, 1, {7, 8}),
    (1, 9, 8, 4, 8, 2, {5, 7}),
    (1, 9, 8, 7, 8, 0, {2, 4}),
    (2, 4, 8, 0, 6, 2, {12, 13}),
    (2, 4, 8, 0, 8, 7, {6, 12}),
    (2, 4, 8, 1, 5, 4, {11, 12}),
    (2, 4, 8, 1, 8, 9, {5, 12}),
    (2, 4, 8, 5, 9, 2, {0, 11}),
    (2, 4, 8, 6, 7, 4, {0, 13}),
    (2, 4, 8, 7, 8, 0, {0, 14}),
    (2, 4, 8, 8, 9, 1, {0, 10}),
    (2, 5, 9, 0, 6, 2, {8, 9}),
    (2, 5, 9, 0, 9, 3, {6, 8}),
    (2, 5, 9, 1, 4, 5, {8, 14}),
    (2, 5, 9, 1, 9, 8, {4, 8}),
    (2, 5, 9, 3, 6, 5, {0, 9}),
    (2, 5, 9, 3, 9, 0, {0, 11}),
    (2, 5, 9, 4, 8, 2, {0, 14}),
    (2, 5, 9, 8, 9, 1, {0, 3}),
    (2, 8, 4, 0, 6, 2, {9, 10}),
    (2, 8, 4, 4, 5, 1, {6, 12}),
    (2, 8, 4, 4, 6, 7, {0, 10}),
    (2, 8, 4, 5, 9, 2, {4, 6}),
    (2, 9, 5, 0, 6, 2, {3, 13}),
    (2, 9, 5, 4, 5, 1, {6, 8}),
    (2, 9, 5, 4, 8, 2, {5, 6}),
    (2, 9, 5, 5, 6, 3, {0, 3}),
    (3, 5, 6, 0, 6, 2, {7, 9}),
    (3, 5, 6, 0, 9, 3, {6, 7}),
    (3, 5, 6, 1, 4, 5, {7, 14}),
    (3, 5, 6, 1, 7, 3, {4, 14}),
    (3, 5, 6, 2, 6, 0, {4, 12}),
    (3, 5, 6, 2, 9, 5, {4, 6}),
    (3, 5, 6, 4, 6, 7, {0, 7}),
    (3, 5, 6, 6, 7, 4, {1, 4}),
    (3, 6, 5, 0, 9, 3, {1, 10}),
    (3, 6, 5, 1, 5, 4, {7, 9}),
    (3, 6, 5, 1, 7, 3, {5, 9}),
    (3, 6, 5, 5, 9, 2, {1, 4}),
    (4, 6, 7, 0, 2, 6, {8, 10}),
    (4, 6, 7, 0, 7, 8, {1, 8}),
    (4, 6, 7, 1, 5, 4, {7, 8}),
    (4, 6, 7, 1, 7, 3, {5, 8}),
    (4, 6, 7, 2, 8, 4, {0, 10}),
    (4, 6, 7, 3, 5, 6, {0, 7}),
    (4, 6, 7, 3, 7, 1, {0, 13}),
    (4, 6, 7, 7, 8, 0, {0, 2}),
    (4, 7, 6, 1, 5, 4, {2, 11}),
    (4, 7, 6, 2, 6, 0, {5, 8}),
    (4, 7, 6, 2, 8, 4, {5, 6}),
    (4, 7, 6, 5, 6, 3, {0, 2})]

private def petersenTwoPatchCode : Fin 6 → Bool → Fin 10 → Fin 10 → Fin 121 :=
  ![(fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 22, 0, 0, 26],
    ![0, 0, 0, 0, 0, 61, 0, 64, 0, 0],
    ![0, 0, 0, 0, 0, 0, 84, 0, 85, 0],
    ![0, 0, 0, 0, 0, 0, 0, 102, 0, 103],
    ![0, 0, 0, 0, 0, 110, 0, 0, 114, 0]] else ![![0, 0, 53, 55, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 17, 19, 0, 0, 0, 0, 0],
    ![59, 0, 0, 0, 58, 0, 0, 0, 0, 0],
    ![90, 89, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 33, 35, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 37, 0, 0, 41, 0],
    ![0, 0, 0, 0, 0, 74, 0, 77, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 21, 27, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 95, 0, 0, 0, 0, 96, 0],
    ![0, 0, 107, 0, 0, 0, 0, 108, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 56, 0, 0, 54],
    ![0, 0, 0, 0, 2, 0, 0, 0, 0, 7],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 11, 0, 0, 0, 0, 16, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![67, 0, 0, 0, 66, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![117, 118, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 76, 0, 0, 78],
    ![0, 0, 0, 0, 0, 0, 10, 0, 13, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 63, 62, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 98, 0, 0, 0, 0, 104],
    ![0, 0, 0, 119, 0, 0, 0, 0, 120, 0]] else ![![0, 0, 48, 0, 0, 0, 0, 50, 0, 0],
    ![0, 0, 0, 0, 0, 20, 0, 18, 0, 0],
    ![39, 0, 0, 0, 0, 43, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 29, 30, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![94, 93, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 0, 5, 0],
    ![0, 0, 0, 0, 0, 0, 60, 0, 57, 0],
    ![0, 73, 0, 0, 0, 0, 80, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 69, 71, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 97, 100, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 0, 45, 0, 51],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 15, 0, 12, 0, 0],
    ![0, 0, 0, 0, 31, 0, 0, 0, 0, 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![83, 0, 0, 0, 86, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![111, 0, 0, 0, 0, 116, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 38, 0, 0, 0, 0, 42],
    ![0, 0, 0, 0, 0, 0, 0, 92, 0, 91],
    ![0, 0, 9, 0, 0, 0, 0, 14, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 87, 82, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 112, 113, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 0, 0, 0, 52, 0, 47, 0],
    ![0, 0, 0, 0, 0, 8, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 23, 0, 0, 0, 0, 28, 0, 0, 0],
    ![70, 0, 0, 0, 0, 72, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![99, 101, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]),
    (fun b ↦ if b then ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 6, 0, 3],
    ![0, 0, 0, 0, 0, 0, 44, 0, 0, 40],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 65, 0, 0, 0, 0, 68, 0, 0],
    ![0, 81, 0, 0, 0, 0, 88, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 109, 115, 0, 0, 0, 0, 0, 0, 0]] else ![![0, 0, 0, 46, 0, 0, 0, 0, 49, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![75, 0, 0, 0, 0, 79, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 36, 0, 0, 34, 0],
    ![0, 0, 0, 24, 25, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![106, 0, 0, 0, 105, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]])]

private def petersenTwoPatchProperty (X : Finset (Fin 10)) (p q : Fin 10)
    (d : Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Finset (Fin 15)) : Prop :=
  let (x₁, y₁, z₁, x₂, y₂, z₂, M) := d
  x₁ ≠ y₁ ∧ x₁ ≠ z₁ ∧ y₁ ≠ z₁ ∧
    x₂ ≠ y₂ ∧ x₂ ≠ z₂ ∧ y₂ ≠ z₂ ∧
    Disjoint ({x₁, y₁} : Finset (Fin 10)) {x₂, y₂} ∧
    Disjoint ({x₁, y₁, z₁} : Finset (Fin 10)) {p, q} ∧
    Disjoint ({x₂, y₂, z₂} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x₁, y₁, z₁} ∧
    petersenClosedNeighborhood q = {q, x₂, y₂, z₂} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x₁, y₁, x₂, y₂}) M ∧
    (M ∩ petersen.dangling X).card + ({x₁, y₁, x₂, y₂} \ X).card = 3

private def petersenTwoPatchCertificate (i : Fin 6) (b : Bool) (p q : Fin 10) : Prop :=
  p ∈ petersenPatchShore i b → q ∈ petersenPatchShore i b → p ≠ q →
    (∀ e, ¬ petersen.Joins e p q) →
    petersenTwoPatchProperty (petersenPatchShore i b) p q
      (petersenTwoPatchWitness (petersenTwoPatchCode i b p q))

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 0 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_0_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 0 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 1 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_1_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 1 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 2 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_2_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 2 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 3 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_3_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 3 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 4 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_4_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 4 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_0 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_1 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_2 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_3 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_4 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_5 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_6 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_7 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_8 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_false_9 (q : Fin 10) :
    petersenTwoPatchCertificate 5 false 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_0 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 0 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_1 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 1 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_2 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 2 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_3 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 3 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_4 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 4 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_5 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 5 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_6 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 6 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_7 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 7 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_8 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 8 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

set_option maxRecDepth 4000 in
private theorem petersenTwoPatch_row_5_true_9 (q : Fin 10) :
    petersenTwoPatchCertificate 5 true 9 q := by
  unfold petersenTwoPatchCertificate petersenTwoPatchProperty IsPerfectMatchingOn Joins
  fin_cases q <;> decide

private theorem petersenTwoPatch_certificate (i : Fin 6) (b : Bool) (p q : Fin 10) :
    petersenTwoPatchCertificate i b p q := by
  revert q
  fin_cases i <;> cases b <;> fin_cases p
  · exact petersenTwoPatch_row_0_false_0
  · exact petersenTwoPatch_row_0_false_1
  · exact petersenTwoPatch_row_0_false_2
  · exact petersenTwoPatch_row_0_false_3
  · exact petersenTwoPatch_row_0_false_4
  · exact petersenTwoPatch_row_0_false_5
  · exact petersenTwoPatch_row_0_false_6
  · exact petersenTwoPatch_row_0_false_7
  · exact petersenTwoPatch_row_0_false_8
  · exact petersenTwoPatch_row_0_false_9
  · exact petersenTwoPatch_row_0_true_0
  · exact petersenTwoPatch_row_0_true_1
  · exact petersenTwoPatch_row_0_true_2
  · exact petersenTwoPatch_row_0_true_3
  · exact petersenTwoPatch_row_0_true_4
  · exact petersenTwoPatch_row_0_true_5
  · exact petersenTwoPatch_row_0_true_6
  · exact petersenTwoPatch_row_0_true_7
  · exact petersenTwoPatch_row_0_true_8
  · exact petersenTwoPatch_row_0_true_9
  · exact petersenTwoPatch_row_1_false_0
  · exact petersenTwoPatch_row_1_false_1
  · exact petersenTwoPatch_row_1_false_2
  · exact petersenTwoPatch_row_1_false_3
  · exact petersenTwoPatch_row_1_false_4
  · exact petersenTwoPatch_row_1_false_5
  · exact petersenTwoPatch_row_1_false_6
  · exact petersenTwoPatch_row_1_false_7
  · exact petersenTwoPatch_row_1_false_8
  · exact petersenTwoPatch_row_1_false_9
  · exact petersenTwoPatch_row_1_true_0
  · exact petersenTwoPatch_row_1_true_1
  · exact petersenTwoPatch_row_1_true_2
  · exact petersenTwoPatch_row_1_true_3
  · exact petersenTwoPatch_row_1_true_4
  · exact petersenTwoPatch_row_1_true_5
  · exact petersenTwoPatch_row_1_true_6
  · exact petersenTwoPatch_row_1_true_7
  · exact petersenTwoPatch_row_1_true_8
  · exact petersenTwoPatch_row_1_true_9
  · exact petersenTwoPatch_row_2_false_0
  · exact petersenTwoPatch_row_2_false_1
  · exact petersenTwoPatch_row_2_false_2
  · exact petersenTwoPatch_row_2_false_3
  · exact petersenTwoPatch_row_2_false_4
  · exact petersenTwoPatch_row_2_false_5
  · exact petersenTwoPatch_row_2_false_6
  · exact petersenTwoPatch_row_2_false_7
  · exact petersenTwoPatch_row_2_false_8
  · exact petersenTwoPatch_row_2_false_9
  · exact petersenTwoPatch_row_2_true_0
  · exact petersenTwoPatch_row_2_true_1
  · exact petersenTwoPatch_row_2_true_2
  · exact petersenTwoPatch_row_2_true_3
  · exact petersenTwoPatch_row_2_true_4
  · exact petersenTwoPatch_row_2_true_5
  · exact petersenTwoPatch_row_2_true_6
  · exact petersenTwoPatch_row_2_true_7
  · exact petersenTwoPatch_row_2_true_8
  · exact petersenTwoPatch_row_2_true_9
  · exact petersenTwoPatch_row_3_false_0
  · exact petersenTwoPatch_row_3_false_1
  · exact petersenTwoPatch_row_3_false_2
  · exact petersenTwoPatch_row_3_false_3
  · exact petersenTwoPatch_row_3_false_4
  · exact petersenTwoPatch_row_3_false_5
  · exact petersenTwoPatch_row_3_false_6
  · exact petersenTwoPatch_row_3_false_7
  · exact petersenTwoPatch_row_3_false_8
  · exact petersenTwoPatch_row_3_false_9
  · exact petersenTwoPatch_row_3_true_0
  · exact petersenTwoPatch_row_3_true_1
  · exact petersenTwoPatch_row_3_true_2
  · exact petersenTwoPatch_row_3_true_3
  · exact petersenTwoPatch_row_3_true_4
  · exact petersenTwoPatch_row_3_true_5
  · exact petersenTwoPatch_row_3_true_6
  · exact petersenTwoPatch_row_3_true_7
  · exact petersenTwoPatch_row_3_true_8
  · exact petersenTwoPatch_row_3_true_9
  · exact petersenTwoPatch_row_4_false_0
  · exact petersenTwoPatch_row_4_false_1
  · exact petersenTwoPatch_row_4_false_2
  · exact petersenTwoPatch_row_4_false_3
  · exact petersenTwoPatch_row_4_false_4
  · exact petersenTwoPatch_row_4_false_5
  · exact petersenTwoPatch_row_4_false_6
  · exact petersenTwoPatch_row_4_false_7
  · exact petersenTwoPatch_row_4_false_8
  · exact petersenTwoPatch_row_4_false_9
  · exact petersenTwoPatch_row_4_true_0
  · exact petersenTwoPatch_row_4_true_1
  · exact petersenTwoPatch_row_4_true_2
  · exact petersenTwoPatch_row_4_true_3
  · exact petersenTwoPatch_row_4_true_4
  · exact petersenTwoPatch_row_4_true_5
  · exact petersenTwoPatch_row_4_true_6
  · exact petersenTwoPatch_row_4_true_7
  · exact petersenTwoPatch_row_4_true_8
  · exact petersenTwoPatch_row_4_true_9
  · exact petersenTwoPatch_row_5_false_0
  · exact petersenTwoPatch_row_5_false_1
  · exact petersenTwoPatch_row_5_false_2
  · exact petersenTwoPatch_row_5_false_3
  · exact petersenTwoPatch_row_5_false_4
  · exact petersenTwoPatch_row_5_false_5
  · exact petersenTwoPatch_row_5_false_6
  · exact petersenTwoPatch_row_5_false_7
  · exact petersenTwoPatch_row_5_false_8
  · exact petersenTwoPatch_row_5_false_9
  · exact petersenTwoPatch_row_5_true_0
  · exact petersenTwoPatch_row_5_true_1
  · exact petersenTwoPatch_row_5_true_2
  · exact petersenTwoPatch_row_5_true_3
  · exact petersenTwoPatch_row_5_true_4
  · exact petersenTwoPatch_row_5_true_5
  · exact petersenTwoPatch_row_5_true_6
  · exact petersenTwoPatch_row_5_true_7
  · exact petersenTwoPatch_row_5_true_8
  · exact petersenTwoPatch_row_5_true_9

/-- A finite Petersen completion patch with explicit boundary neighbors. -/
theorem IsSeparatingCut.petersen_two_expansion_patch {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {p q : Fin 10} (hp : p ∈ X) (hq : q ∈ X) (hne : p ≠ q)
    (hadj : (∀ e, ¬ petersen.Joins e p q)) :
    ∃ x₁ y₁ z₁ x₂ y₂ z₂ : Fin 10, ∃ M : Finset (Fin 15),
    x₁ ≠ y₁ ∧ x₁ ≠ z₁ ∧ y₁ ≠ z₁ ∧
    x₂ ≠ y₂ ∧ x₂ ≠ z₂ ∧ y₂ ≠ z₂ ∧
    Disjoint ({x₁, y₁} : Finset (Fin 10)) {x₂, y₂} ∧
    Disjoint ({x₁, y₁, z₁} : Finset (Fin 10)) {p, q} ∧
    Disjoint ({x₂, y₂, z₂} : Finset (Fin 10)) {p, q} ∧
    petersenClosedNeighborhood p = {p, x₁, y₁, z₁} ∧
    petersenClosedNeighborhood q = {q, x₂, y₂, z₂} ∧
    petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x₁, y₁, x₂, y₂}) M ∧
    (M ∩ petersen.dangling X).card + ({x₁, y₁, x₂, y₂} \ X).card = 3 := by
  obtain ⟨i, b, rfl⟩ := hs.eq_petersenPatchShore hX
  let d := petersenTwoPatchWitness (petersenTwoPatchCode i b p q)
  exact ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2, petersenTwoPatch_certificate i b p q hp hq hne hadj⟩

end GraphPuzzles.LoopMultigraph
