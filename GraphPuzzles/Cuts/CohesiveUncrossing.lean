import GraphPuzzles.Cuts.CutOrder

/-! The modularity and cohesiveness assertions of Campos--Lucchesi Lemma 4.6. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Complementing all shore representatives leaves cohesiveness unchanged. -/
theorem IsCohesiveCuts.compls {C : Finset (Finset V)} (hc : H.IsCohesiveCuts C) :
    H.IsCohesiveCuts (C.image fun X ↦ Finset.univ \ X) := by
  intro e
  obtain ⟨M, hM, he, hm⟩ := hc e
  refine ⟨M, hM, he, ?_⟩
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
  simpa only [dangling_compl] using hm X hX

/-- Cohesiveness eliminates the edges between the two opposite difference regions. -/
theorem IsCohesiveCuts.edgesBetween_eq_empty {C : Finset (Finset V)}
    (hc : H.IsCohesiveCuts C) {X Y : Finset V} (hX : X ∈ C) (hY : Y ∈ C)
    (hI : Odd (X ∩ Y).card) : H.edgesBetween (X \ Y) (Y \ X) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨M, hM, heM, hm⟩ := hc e
  have htX : H.cutWeight (matchingVector M) X = 1 := by
    rw [cutWeight_matchingVector, hm X hX]
    norm_num
  have htY : H.cutWeight (matchingVector M) Y = 1 := by
    rw [cutWeight_matchingVector, hm Y hY]
    norm_num
  have hz := (hM.isFractional.uncross (hM.odd_of_crossing_one (hm X hX))
    (hM.odd_of_crossing_one (hm Y hY)) hI htX htY).2.2
  have hle := Finset.single_le_sum (fun f (_ : f ∈ H.edgesBetween (X \ Y) (Y \ X)) ↦
    hM.isFractional.nonneg f) he
  rw [hz] at hle
  norm_num [matchingVector, heM] at hle

/-- The cut identity becomes modular for arbitrary edge weights. -/
theorem IsCohesiveCuts.cutWeight_modular {C : Finset (Finset V)}
    (hc : H.IsCohesiveCuts C) {X Y : Finset V} (hX : X ∈ C) (hY : Y ∈ C)
    (hI : Odd (X ∩ Y).card) (x : E → ℚ) :
    H.cutWeight x X + H.cutWeight x Y =
      H.cutWeight x (X ∩ Y) + H.cutWeight x (X ∪ Y) := by
  have hh := LoopMultigraph.cutWeight_modular (H := H) x X Y
  simpa only [hc.edgesBetween_eq_empty hX hY hI, Finset.sum_empty, mul_zero, add_zero] using hh

/-- Campos--Lucchesi Lemma 4.6(i), with no matching assumption on the edge set. -/
theorem IsCohesiveCuts.crossing_modular {C : Finset (Finset V)}
    (hc : H.IsCohesiveCuts C) {X Y : Finset V} (hX : X ∈ C) (hY : Y ∈ C)
    (hI : Odd (X ∩ Y).card) (F : Finset E) :
    (F ∩ H.dangling X).card + (F ∩ H.dangling Y).card =
      (F ∩ H.dangling (X ∩ Y)).card + (F ∩ H.dangling (X ∪ Y)).card := by
  have hh := hc.cutWeight_modular hX hY hI (matchingVector F)
  simp only [cutWeight_matchingVector] at hh
  exact_mod_cast hh

/-- Campos--Lucchesi Lemma 4.6(ii): adjoining the odd intersection and union preserves
cohesiveness, including every other cut already in the collection. -/
theorem IsCohesiveCuts.uncross {C : Finset (Finset V)} (hc : H.IsCohesiveCuts C)
    {X Y : Finset V} (hX : X ∈ C) (hY : Y ∈ C) (hI : Odd (X ∩ Y).card) :
    H.IsCohesiveCuts (insert (X ∩ Y) (insert (X ∪ Y) C)) := by
  intro e
  obtain ⟨M, hM, he, hm⟩ := hc e
  have htX : H.cutWeight (matchingVector M) X = 1 := by
    rw [cutWeight_matchingVector, hm X hX]
    norm_num
  have htY : H.cutWeight (matchingVector M) Y = 1 := by
    rw [cutWeight_matchingVector, hm Y hY]
    norm_num
  obtain ⟨hi, hu, _⟩ := hM.isFractional.uncross (hM.odd_of_crossing_one (hm X hX))
    (hM.odd_of_crossing_one (hm Y hY)) hI htX htY
  simp only [cutWeight_matchingVector] at hi hu
  refine ⟨M, hM, he, ?_⟩
  intro Z hZ
  rcases Finset.mem_insert.mp hZ with rfl | hZ
  · exact_mod_cast hi
  · rcases Finset.mem_insert.mp hZ with rfl | hZ
    · exact_mod_cast hu
    · exact hm Z hZ

end GraphPuzzles.LoopMultigraph
