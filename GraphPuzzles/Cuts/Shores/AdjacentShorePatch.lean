import GraphPuzzles.Cuts.Shores.AdjacentShoreAttachments

/-! Combining the two orientations of the adjacent-shore matching patch. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {Y Z : Finset V}

/-- Connectivity chooses a usable orientation of Proposition 6.6. -/
theorem BipartiteRestorationShore.exists_adjacent_patch
    (P : H.BipartiteRestorationShore e Y) (Q : H.BipartiteRestorationShore e Z)
    (hbic : H.IsBicritical) (hconn : H.ConnectedAfterDeletingPairs)
    (hYZ : Disjoint Y Z) (hYcard : 2 ≤ Y.card)
    (hout : (Finset.univ \ (Y ∪ Z)).Nonempty)
    {v w a b x y : V} (he : H.Joins e v w) (hv : v ∈ P.small) (hw : w ∈ Q.small)
    (haout : a ∉ Y ∪ Z) (hbout : b ∉ Y ∪ Z)
    (hxout : x ∉ Y ∪ Z) (hyout : y ∉ Y ∪ Z)
    (hab : a ≠ b) (hxy : x ≠ y) (hd : Disjoint ({a, b} : Finset V) {x, y})
    (ha : ∃ s ∈ Y, ∃ f, H.Joins f s a) (hb : ∃ t ∈ Y, ∃ g, H.Joins g t b)
    (hx : ∃ s ∈ Z, ∃ f, H.Joins f s x) (hy : ∃ t ∈ Z, ∃ g, H.Joins g t y)
    (hbdY : ∀ f k, H.endAt f k ∈ Y → H.endAt f (Fin.rev k) ∉ Y ∪ Z →
      H.endAt f (Fin.rev k) ∈ ({a, b} : Finset V))
    (hbdZ : ∀ f k, H.endAt f k ∈ Z → H.endAt f (Fin.rev k) ∉ Y ∪ Z →
      H.endAt f (Fin.rev k) ∈ ({x, y} : Finset V)) :
    ∃ M, H.IsPerfectMatchingOn (Y ∪ Z ∪ {a, b, x, y}) M ∧
      e ∈ M ∧ (M ∩ H.dangling (Y ∪ Z)).card = 4 := by
  have hvY : v ∈ Y := P.union_eq ▸ Finset.mem_union_left _ hv
  have hwZ : w ∈ Z := Q.union_eq ▸ Finset.mem_union_left _ hw
  have heYZ : ∀ k, H.endAt e k ∈ Y ∪ Z := by
    intro k
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases k
    · exact h0.symm ▸ Finset.mem_union_left Z hvY
    · exact h1.symm ▸ Finset.mem_union_right Y hwZ
    · exact h0.symm ▸ Finset.mem_union_right Y hwZ
    · exact h1.symm ▸ Finset.mem_union_left Z hvY
  have hwY : w ∉ Y := fun hh ↦ Finset.disjoint_left.mp hYZ hh hwZ
  have hvZ : v ∉ Z := fun hh ↦ Finset.disjoint_left.mp hYZ hvY hh
  have heY : e ∈ H.dangling Y := by
    rw [mem_dangling]
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1, hvY, hwY]
  have heZ : e ∈ H.dangling Z := by
    rw [mem_dangling]
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1, hwZ, hvZ]
  have hattach := P.distinct_large_attachments Q hconn hYZ hYcard hout heYZ
    haout hbout hxout hyout ha hb hx hy hbdY hbdZ
  rcases hattach with ⟨s, hs, t, ht, hst, f, g, hf, hg⟩ | ⟨s, hs, t, ht, hst, f, g, hf, hg⟩
  · obtain ⟨M, hM, heM, hMY, hMZ, hcommon⟩ :=
      P.exists_matchingOn_adjacent_shores Q hbic hYZ he hv hw hs ht hst hf hg
        haout hbout hxout hyout hab hd (by
          intro r _ k hi hZ hY
          exact hbdZ r k hi (fun hh ↦ (Finset.mem_union.mp hh).elim hY hZ))
    refine ⟨M, ?_, heM, crossing_union_eq_four_of_three hYZ hMY hMZ heM heY heZ hcommon⟩
    have hu : Y ∪ Z ∪ {x, y, a, b} = Y ∪ Z ∪ {a, b, x, y} := by
      ext u
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hu ▸ hM
  · obtain ⟨M, hM, heM, hMZ, hMY, hcommon⟩ :=
      Q.exists_matchingOn_adjacent_shores P hbic hYZ.symm he.symm hw hv hs ht hst hf hg
        (by simpa only [Finset.union_comm Z Y] using hxout)
        (by simpa only [Finset.union_comm Z Y] using hyout)
        (by simpa only [Finset.union_comm Z Y] using haout)
        (by simpa only [Finset.union_comm Z Y] using hbout) hxy hd.symm (by
          intro r _ k hi hY hZ
          exact hbdY r k hi (fun hh ↦ (Finset.mem_union.mp hh).elim hY hZ))
    refine ⟨M, ?_, heM, ?_⟩
    · have hu : Z ∪ Y ∪ {a, b, x, y} = Y ∪ Z ∪ {a, b, x, y} := by rw [Finset.union_comm Z Y]
      exact hu ▸ hM
    · exact crossing_union_eq_four_of_three hYZ hMY hMZ heM heY heZ
        (fun r hr hy hz ↦ hcommon r hr hz hy)

end GraphPuzzles.LoopMultigraph
