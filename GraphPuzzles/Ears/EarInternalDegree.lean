import GraphPuzzles.Ears.ClosedOddEar
import GraphPuzzles.Ears.LastOddEar
import GraphPuzzles.Bricks.BrickEdgeConnectivity

/-! The incidence alternatives for an internal vertex of the last nonmatching ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every internal vertex has precisely two incidences in the labelled ear,
whether its attachment vertices agree or are distinct. -/
theorem OddEar.degree_two_of_internal {S : Finset V} (A : H.OddEar S)
    {es : List E} (hw : H.EdgeChain A.start es (A.interior ++ [A.finish]))
    {w : V} (hwA : w ∈ A.interior) : H.degreeIn es.toFinset w = 2 := by
  have hn₁ : (A.start :: A.interior).Nodup := List.nodup_cons.mpr
    ⟨fun h ↦ A.avoids A.start h A.start_mem, A.nodup⟩
  have hn₂ : (A.interior ++ [A.finish]).Nodup := List.nodup_append.mpr
    ⟨A.nodup, by simp, fun x hx y hy hxy ↦
      A.avoids x hx (by rw [hxy, List.mem_singleton.mp hy]; exact A.finish_mem)⟩
  rw [hw.degreeIn_eq_counts (A.labels_nodup hw),
    List.count_eq_one_of_mem hn₁ (List.mem_cons_of_mem _ hwA),
    List.count_eq_one_of_mem hn₂ (List.mem_append_left _ hwA)]

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

/-- The old prefix has no incidence at an internal vertex of the marked ear. -/
theorem old_degree_zero_of_internal {w : V} (hw : w ∈ L.ear.interior) :
    H.degreeIn L.oldEdges w = 0 := by
  apply degreeIn_eq_zero_of
  intro e he k hkw
  exact L.ear.avoids w hw (hkw ▸ (mem_edgesIn.mp (L.earlier.forget.edgesIn he)) k)

/-- The third incidence at an internal vertex either leads to the hub or
belongs to a matching-tail edge. This is the degree step in Proposition 5.9. -/
theorem internal_hub_or_tail {v w : V} (hT : T = Finset.univ.erase v)
    (hG : G = H.edgesIn (Finset.univ.erase v)) (hw : w ∈ L.ear.interior)
    (hd : 3 ≤ H.degree w) :
    (∃ e, H.Joins e v w) ∨
      ∃ e ∈ G \ (L.oldEdges ∪ L.labels.toFinset), ∃ k, H.endAt e k = w := by
  have hdeg := L.ear.degree_two_of_internal L.walk hw
  have hsum := degreeIn_add_compl (H := H) L.labels.toFinset w
  have hpos : 0 < H.degreeIn (Finset.univ \ L.labels.toFinset) w := by omega
  obtain ⟨e, he, k, hk⟩ := (H.mem_edgeSupport_iff).mp
    ((H.degreeIn_pos_iff_mem_edgeSupport _ w).mp hpos)
  have hwv : w ≠ v := by
    have hh : w ∈ T := L.vertices_eq ▸
      Finset.mem_union_right L.oldVertices (List.mem_toFinset.mpr hw)
    exact (Finset.mem_erase.mp (hT ▸ hh)).1
  by_cases hv : H.endAt e (Fin.rev k) = v
  · left
    refine ⟨e, ?_⟩
    fin_cases k
    · exact Or.inr ⟨hk, hv⟩
    · exact Or.inl ⟨hv, hk⟩
  · right
    refine ⟨e, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, k, hk⟩
    · rw [hG]
      apply mem_edgesIn.mpr
      intro i
      have hneq : H.endAt e i ≠ v := by
        fin_cases k <;> fin_cases i
        · exact fun h ↦ hwv (hk.symm.trans h)
        · exact hv
        · exact hv
        · exact fun h ↦ hwv (hk.symm.trans h)
      simp [hneq]
    · intro hin
      rcases Finset.mem_union.mp hin with ho | hl
      · exact L.ear.avoids w hw (hk ▸ (mem_edgesIn.mp (L.earlier.forget.edgesIn ho)) k)
      · exact (Finset.mem_sdiff.mp he).2 hl

end LastOutsideOddEar
end GraphPuzzles.LoopMultigraph
