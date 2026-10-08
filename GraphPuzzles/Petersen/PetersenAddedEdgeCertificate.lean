import GraphPuzzles.Petersen.PetersenMatching

namespace GraphPuzzles.LoopMultigraph

/-- Add one labelled edge to the Petersen graph. -/
def petersenAddEdge (u v : Fin 10) : LoopMultigraph (Fin 10) (Fin 16) :=
  ⟨fun e k ↦ if h : e.val < 15 then petersen.endAt ⟨e.val, h⟩ k else ![u, v] k⟩

-- Each entry j*15+e selects a displayed perfect matching and a replacement edge.
-- Delete that matching's two edges at u and v, insert e, then add the new edge uv.
-- Entries at equal or adjacent vertex pairs are unused.
private def petersenRepairCode : Fin 6 → Fin 10 → Fin 10 → Fin 90 :=
  ![![![0, 0, 10, 13, 0, 0, 69, 39, 81, 51],
    ![0, 0, 0, 11, 14, 67, 0, 80, 50, 22],
    ![10, 0, 0, 0, 12, 38, 83, 0, 21, 66],
    ![13, 11, 0, 0, 0, 82, 54, 24, 0, 37],
    ![0, 14, 12, 0, 0, 53, 23, 65, 35, 0],
    ![0, 67, 38, 82, 53, 0, 0, 0, 0, 4],
    ![69, 0, 83, 54, 23, 0, 0, 1, 0, 0],
    ![39, 80, 0, 24, 65, 0, 1, 0, 2, 0],
    ![81, 50, 21, 0, 35, 0, 0, 2, 0, 3],
    ![51, 22, 66, 37, 0, 4, 0, 0, 3, 0]],
   ![![0, 0, 33, 76, 0, 0, 28, 46, 63, 25],
    ![0, 0, 0, 11, 17, 41, 0, 80, 50, 22],
    ![33, 0, 0, 0, 12, 15, 57, 0, 21, 78],
    ![76, 11, 0, 0, 0, 19, 31, 24, 0, 71],
    ![0, 17, 12, 0, 0, 87, 23, 65, 35, 0],
    ![0, 41, 15, 19, 87, 0, 72, 0, 0, 56],
    ![28, 0, 57, 31, 23, 72, 0, 1, 0, 0],
    ![46, 80, 0, 24, 65, 0, 1, 0, 29, 0],
    ![63, 50, 21, 0, 35, 0, 0, 29, 0, 3],
    ![25, 22, 78, 71, 0, 56, 0, 0, 3, 0]],
   ![![0, 0, 33, 13, 0, 0, 28, 39, 81, 51],
    ![0, 0, 0, 49, 17, 41, 0, 44, 62, 79],
    ![33, 0, 0, 0, 12, 38, 57, 0, 21, 66],
    ![13, 49, 0, 0, 0, 19, 31, 73, 0, 37],
    ![0, 17, 12, 0, 0, 87, 30, 47, 35, 0],
    ![0, 41, 38, 19, 87, 0, 72, 0, 0, 4],
    ![28, 0, 57, 31, 30, 72, 0, 88, 0, 0],
    ![39, 44, 0, 73, 47, 0, 88, 0, 2, 0],
    ![81, 62, 21, 0, 35, 0, 0, 2, 0, 40],
    ![51, 79, 66, 37, 0, 4, 0, 0, 40, 0]],
   ![![0, 0, 33, 13, 0, 0, 28, 46, 63, 51],
    ![0, 0, 0, 49, 14, 67, 0, 44, 50, 22],
    ![33, 0, 0, 0, 60, 15, 57, 0, 55, 78],
    ![13, 49, 0, 0, 0, 82, 54, 73, 0, 37],
    ![0, 14, 60, 0, 0, 53, 30, 47, 89, 0],
    ![0, 67, 15, 82, 53, 0, 0, 0, 0, 56],
    ![28, 0, 57, 54, 30, 0, 0, 88, 0, 0],
    ![46, 44, 0, 73, 47, 0, 88, 0, 29, 0],
    ![63, 50, 55, 0, 89, 0, 0, 29, 0, 3],
    ![51, 22, 78, 37, 0, 56, 0, 0, 3, 0]],
   ![![0, 0, 10, 76, 0, 0, 69, 46, 63, 25],
    ![0, 0, 0, 49, 14, 67, 0, 44, 62, 79],
    ![10, 0, 0, 0, 60, 38, 83, 0, 55, 66],
    ![76, 49, 0, 0, 0, 19, 31, 73, 0, 71],
    ![0, 14, 60, 0, 0, 53, 23, 65, 89, 0],
    ![0, 67, 38, 19, 53, 0, 72, 0, 0, 4],
    ![69, 0, 83, 31, 23, 72, 0, 1, 0, 0],
    ![46, 44, 0, 73, 65, 0, 1, 0, 29, 0],
    ![63, 62, 55, 0, 89, 0, 0, 29, 0, 40],
    ![25, 79, 66, 71, 0, 4, 0, 0, 40, 0]],
   ![![0, 0, 10, 76, 0, 0, 69, 39, 81, 25],
    ![0, 0, 0, 11, 17, 41, 0, 80, 62, 79],
    ![10, 0, 0, 0, 60, 15, 83, 0, 55, 78],
    ![76, 11, 0, 0, 0, 82, 54, 24, 0, 71],
    ![0, 17, 60, 0, 0, 87, 30, 47, 89, 0],
    ![0, 41, 15, 82, 87, 0, 0, 0, 0, 56],
    ![69, 0, 83, 54, 30, 0, 0, 88, 0, 0],
    ![39, 80, 0, 24, 47, 0, 88, 0, 2, 0],
    ![81, 62, 55, 0, 89, 0, 0, 2, 0, 40],
    ![25, 79, 78, 71, 0, 56, 0, 0, 40, 0]]]

private def petersenAddMatching (i : Fin 6) (u v : Fin 10) : Finset (Fin 16) :=
  let z := petersenRepairCode i u v
  let j : Fin 6 := ⟨z.val / 15, by have h := z.isLt; omega⟩
  let e : Fin 15 := ⟨z.val % 15, Nat.mod_lt _ (by decide)⟩
  ((petersenMatching j).filter fun f ↦
    ∀ k : Fin 2, petersen.endAt f k ≠ u ∧ petersen.endAt f k ≠ v).image Fin.castSucc ∪
      {e.castSucc, 15}

private def PetersenAddedCertificate (i : Fin 6) (u v : Fin 10) : Prop :=
  u ≠ v → (∀ e, ¬ petersen.Joins e u v) →
    (petersenAddEdge u v).IsPerfectMatching (petersenAddMatching i u v) ∧
      (petersenAddMatching i u v ∩
        (petersenAddEdge u v).dangling (petersenMatchingShore i)).card = 3

-- At most ten endpoint cases are reduced in any one declaration.
private theorem added_certificate_0_0 (v : Fin 10) :
    PetersenAddedCertificate 0 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_1 (v : Fin 10) :
    PetersenAddedCertificate 0 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_2 (v : Fin 10) :
    PetersenAddedCertificate 0 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_3 (v : Fin 10) :
    PetersenAddedCertificate 0 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_4 (v : Fin 10) :
    PetersenAddedCertificate 0 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_5 (v : Fin 10) :
    PetersenAddedCertificate 0 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_6 (v : Fin 10) :
    PetersenAddedCertificate 0 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_7 (v : Fin 10) :
    PetersenAddedCertificate 0 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_8 (v : Fin 10) :
    PetersenAddedCertificate 0 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_0_9 (v : Fin 10) :
    PetersenAddedCertificate 0 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_0 (v : Fin 10) :
    PetersenAddedCertificate 1 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_1 (v : Fin 10) :
    PetersenAddedCertificate 1 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_2 (v : Fin 10) :
    PetersenAddedCertificate 1 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_3 (v : Fin 10) :
    PetersenAddedCertificate 1 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_4 (v : Fin 10) :
    PetersenAddedCertificate 1 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_5 (v : Fin 10) :
    PetersenAddedCertificate 1 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_6 (v : Fin 10) :
    PetersenAddedCertificate 1 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_7 (v : Fin 10) :
    PetersenAddedCertificate 1 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_8 (v : Fin 10) :
    PetersenAddedCertificate 1 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_1_9 (v : Fin 10) :
    PetersenAddedCertificate 1 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_0 (v : Fin 10) :
    PetersenAddedCertificate 2 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_1 (v : Fin 10) :
    PetersenAddedCertificate 2 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_2 (v : Fin 10) :
    PetersenAddedCertificate 2 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_3 (v : Fin 10) :
    PetersenAddedCertificate 2 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_4 (v : Fin 10) :
    PetersenAddedCertificate 2 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_5 (v : Fin 10) :
    PetersenAddedCertificate 2 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_6 (v : Fin 10) :
    PetersenAddedCertificate 2 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_7 (v : Fin 10) :
    PetersenAddedCertificate 2 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_8 (v : Fin 10) :
    PetersenAddedCertificate 2 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_2_9 (v : Fin 10) :
    PetersenAddedCertificate 2 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_0 (v : Fin 10) :
    PetersenAddedCertificate 3 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_1 (v : Fin 10) :
    PetersenAddedCertificate 3 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_2 (v : Fin 10) :
    PetersenAddedCertificate 3 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_3 (v : Fin 10) :
    PetersenAddedCertificate 3 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_4 (v : Fin 10) :
    PetersenAddedCertificate 3 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_5 (v : Fin 10) :
    PetersenAddedCertificate 3 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_6 (v : Fin 10) :
    PetersenAddedCertificate 3 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_7 (v : Fin 10) :
    PetersenAddedCertificate 3 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_8 (v : Fin 10) :
    PetersenAddedCertificate 3 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_3_9 (v : Fin 10) :
    PetersenAddedCertificate 3 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_0 (v : Fin 10) :
    PetersenAddedCertificate 4 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_1 (v : Fin 10) :
    PetersenAddedCertificate 4 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_2 (v : Fin 10) :
    PetersenAddedCertificate 4 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_3 (v : Fin 10) :
    PetersenAddedCertificate 4 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_4 (v : Fin 10) :
    PetersenAddedCertificate 4 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_5 (v : Fin 10) :
    PetersenAddedCertificate 4 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_6 (v : Fin 10) :
    PetersenAddedCertificate 4 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_7 (v : Fin 10) :
    PetersenAddedCertificate 4 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_8 (v : Fin 10) :
    PetersenAddedCertificate 4 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_4_9 (v : Fin 10) :
    PetersenAddedCertificate 4 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_0 (v : Fin 10) :
    PetersenAddedCertificate 5 0 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_1 (v : Fin 10) :
    PetersenAddedCertificate 5 1 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_2 (v : Fin 10) :
    PetersenAddedCertificate 5 2 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_3 (v : Fin 10) :
    PetersenAddedCertificate 5 3 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_4 (v : Fin 10) :
    PetersenAddedCertificate 5 4 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_5 (v : Fin 10) :
    PetersenAddedCertificate 5 5 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_6 (v : Fin 10) :
    PetersenAddedCertificate 5 6 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_7 (v : Fin 10) :
    PetersenAddedCertificate 5 7 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_8 (v : Fin 10) :
    PetersenAddedCertificate 5 8 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem added_certificate_5_9 (v : Fin 10) :
    PetersenAddedCertificate 5 9 v := by
  unfold PetersenAddedCertificate IsPerfectMatching Joins
  fin_cases v <;> decide

private theorem petersenAddMatching_spec (i : Fin 6) :
    ∀ u v : Fin 10, u ≠ v → (∀ e, ¬ petersen.Joins e u v) →
      (petersenAddEdge u v).IsPerfectMatching (petersenAddMatching i u v) ∧
        (petersenAddMatching i u v ∩
          (petersenAddEdge u v).dangling (petersenMatchingShore i)).card = 3 := by
  intro u
  fin_cases i <;> fin_cases u
  · exact fun v ↦ added_certificate_0_0 v
  · exact fun v ↦ added_certificate_0_1 v
  · exact fun v ↦ added_certificate_0_2 v
  · exact fun v ↦ added_certificate_0_3 v
  · exact fun v ↦ added_certificate_0_4 v
  · exact fun v ↦ added_certificate_0_5 v
  · exact fun v ↦ added_certificate_0_6 v
  · exact fun v ↦ added_certificate_0_7 v
  · exact fun v ↦ added_certificate_0_8 v
  · exact fun v ↦ added_certificate_0_9 v
  · exact fun v ↦ added_certificate_1_0 v
  · exact fun v ↦ added_certificate_1_1 v
  · exact fun v ↦ added_certificate_1_2 v
  · exact fun v ↦ added_certificate_1_3 v
  · exact fun v ↦ added_certificate_1_4 v
  · exact fun v ↦ added_certificate_1_5 v
  · exact fun v ↦ added_certificate_1_6 v
  · exact fun v ↦ added_certificate_1_7 v
  · exact fun v ↦ added_certificate_1_8 v
  · exact fun v ↦ added_certificate_1_9 v
  · exact fun v ↦ added_certificate_2_0 v
  · exact fun v ↦ added_certificate_2_1 v
  · exact fun v ↦ added_certificate_2_2 v
  · exact fun v ↦ added_certificate_2_3 v
  · exact fun v ↦ added_certificate_2_4 v
  · exact fun v ↦ added_certificate_2_5 v
  · exact fun v ↦ added_certificate_2_6 v
  · exact fun v ↦ added_certificate_2_7 v
  · exact fun v ↦ added_certificate_2_8 v
  · exact fun v ↦ added_certificate_2_9 v
  · exact fun v ↦ added_certificate_3_0 v
  · exact fun v ↦ added_certificate_3_1 v
  · exact fun v ↦ added_certificate_3_2 v
  · exact fun v ↦ added_certificate_3_3 v
  · exact fun v ↦ added_certificate_3_4 v
  · exact fun v ↦ added_certificate_3_5 v
  · exact fun v ↦ added_certificate_3_6 v
  · exact fun v ↦ added_certificate_3_7 v
  · exact fun v ↦ added_certificate_3_8 v
  · exact fun v ↦ added_certificate_3_9 v
  · exact fun v ↦ added_certificate_4_0 v
  · exact fun v ↦ added_certificate_4_1 v
  · exact fun v ↦ added_certificate_4_2 v
  · exact fun v ↦ added_certificate_4_3 v
  · exact fun v ↦ added_certificate_4_4 v
  · exact fun v ↦ added_certificate_4_5 v
  · exact fun v ↦ added_certificate_4_6 v
  · exact fun v ↦ added_certificate_4_7 v
  · exact fun v ↦ added_certificate_4_8 v
  · exact fun v ↦ added_certificate_4_9 v
  · exact fun v ↦ added_certificate_5_0 v
  · exact fun v ↦ added_certificate_5_1 v
  · exact fun v ↦ added_certificate_5_2 v
  · exact fun v ↦ added_certificate_5_3 v
  · exact fun v ↦ added_certificate_5_4 v
  · exact fun v ↦ added_certificate_5_5 v
  · exact fun v ↦ added_certificate_5_6 v
  · exact fun v ↦ added_certificate_5_7 v
  · exact fun v ↦ added_certificate_5_8 v
  · exact fun v ↦ added_certificate_5_9 v

/-- The explicit matching construction behind Lemma 2.8 for a canonical Petersen cut. -/
theorem petersenAddEdge_exists_crossing_three_canonical (i : Fin 6) (u v : Fin 10)
    (hne : u ≠ v) (hnew : ∀ e, ¬ petersen.Joins e u v) :
    ∃ M, (petersenAddEdge u v).IsPerfectMatching M ∧
      (M ∩ (petersenAddEdge u v).dangling (petersenMatchingShore i)).card = 3 :=
  ⟨petersenAddMatching i u v, petersenAddMatching_spec i u v hne hnew⟩

end GraphPuzzles.LoopMultigraph
