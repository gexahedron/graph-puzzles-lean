import GraphPuzzles.Cuts.CrossingTightCut
import GraphPuzzles.Bricks.BrickConnectivity

/-! Opposite single attachments of a cohesive crossing pair give a two-vertex separation. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The two attachment alternatives in Proposition 6.1 contradict
connectivity after deleting the attachment vertices. -/
theorem IsCohesiveCuts.not_connectedAfterDeletingPairs_of_opposite_attachments
    {X Y : Finset V} (hc : H.IsCohesiveCuts {X, Y})
    (hcross : CutsCross X Y) (ho : Odd (X ∩ Y).card)
    {i j : V} (hi : i ∈ X ∩ Y)
    (hj : j ∈ (Finset.univ \ X) ∩ (Finset.univ \ Y))
    (hI : ∀ a ∈ X ∩ Y, ∀ w, w ∉ Y → ∀ e, H.Joins e w a → a = i)
    (hJ : ∀ a ∈ (Finset.univ \ X) ∩ (Finset.univ \ Y), ∀ w,
      w ∉ Finset.univ \ Y → ∀ e, H.Joins e w a → a = j) :
    ¬ H.ConnectedAfterDeletingPairs := by
  classical
  intro hconn
  have hiX := (Finset.mem_inter.mp hi).1
  have hiY := (Finset.mem_inter.mp hi).2
  have hjX := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).1).2
  have hjY := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).2).2
  have hij : i ≠ j := fun h ↦ hjY (h ▸ hiY)
  have hz := hc.edgesBetween_eq_empty (by simp : X ∈ ({X, Y} : Finset (Finset V)))
    (by simp : Y ∈ ({X, Y} : Finset (Finset V))) ho
  have no_cross (e : E) (a b : V) (he : H.Joins e a b)
      (haY : a ∈ Y) (hbY : b ∉ Y)
      (ha : a ∉ ({i, j} : Finset V)) (hb : b ∉ ({i, j} : Finset V)) : False := by
    by_cases haX : a ∈ X
    · have hai := hI a (Finset.mem_inter.mpr ⟨haX, haY⟩) b hbY e (H.joins_comm.mp he)
      exact ha (by simp [hai])
    · by_cases hbX : b ∈ X
      · have hem : e ∈ H.edgesBetween (X \ Y) (Y \ X) := by
          rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
            simp [edgesBetween, h0, h1, haY, haX, hbY, hbX]
        exact Finset.notMem_empty e (hz ▸ hem)
      · have hbj := hJ b (by simp [hbX, hbY]) a (by simp [haY]) e he
        exact hb (by simp [hbj])
  let c : V → Bool := fun v ↦ decide (v ∈ Y)
  have hedge (e : E) (h0 : H.endAt e 0 ∉ ({i, j} : Finset V))
      (h1 : H.endAt e 1 ∉ ({i, j} : Finset V)) :
      c (H.endAt e 0) = c (H.endAt e 1) := by
    by_cases he0 : H.endAt e 0 ∈ Y <;> by_cases he1 : H.endAt e 1 ∈ Y
    · simp [c, he0, he1]
    · exact (no_cross e _ _ (Or.inl ⟨rfl, rfl⟩) he0 he1 h0 h1).elim
    · exact (no_cross e _ _ (Or.inr ⟨rfl, rfl⟩) he1 he0 h1 h0).elim
    · simp [c, he0, he1]
  obtain ⟨a, ha⟩ := hcross.2.2.1
  obtain ⟨b, hb⟩ := hcross.2.1
  obtain ⟨haY, haX⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hbX, hbY⟩ := Finset.mem_sdiff.mp hb
  have haij : a ∉ ({i, j} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ haX (h.symm ▸ hiX), fun h ↦ hjY (h ▸ haY)⟩
  have hbij : b ∉ ({i, j} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ hbY (h.symm ▸ hiY), fun h ↦ hjX (h ▸ hbX)⟩
  have hh := hconn i j hij c hedge a haij b hbij
  simp [c, haY, hbY] at hh

end GraphPuzzles.LoopMultigraph
