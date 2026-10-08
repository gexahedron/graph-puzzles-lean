import GraphPuzzles.Ears.LabeledEar
import GraphPuzzles.Ears.OddEarExistence
import GraphPuzzles.Matching.MatchingOnRestriction

/-! Odd-ear decompositions covering every original vertex and labelled edge. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A finite odd-ear decomposition starting at `r`, recording both the
vertices and the original labelled edges already used. Each new ear is
disjoint from all earlier edges. -/
inductive HasOddEarDecomposition (H : LoopMultigraph V E) (r : V) :
    Finset V → Finset E → Prop
  | start : HasOddEarDecomposition H r {r} ∅
  | attach {S : Finset V} {F : Finset E} (old : HasOddEarDecomposition H r S F)
      (ear : H.OddEar S) (es : List E)
      (walk : H.EdgeChain ear.start es (ear.interior ++ [ear.finish]))
      (fresh : Disjoint F es.toFinset) :
      HasOddEarDecomposition H r ear.vertices (F ∪ es.toFinset)

namespace HasOddEarDecomposition

variable {r : V} {S : Finset V} {F : Finset E}

theorem root_mem (h : H.HasOddEarDecomposition r S F) : r ∈ S := by
  induction h with
  | start => exact Finset.mem_singleton_self _
  | attach _ _ _ _ _ ih => exact Finset.mem_union_left _ ih

theorem edgesIn (h : H.HasOddEarDecomposition r S F) : F ⊆ H.edgesIn S := by
  induction h with
  | start => exact Finset.empty_subset _
  | attach _ ear es hw _ ih =>
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact mem_edgesIn.mpr fun k ↦ Finset.mem_union_left _ ((mem_edgesIn.mp (ih he)) k)
    · exact ear.labels_edgesIn hw he

theorem vertex_construction (h : H.HasOddEarDecomposition r S F) :
    H.HasOddEarConstruction S := by
  induction h with
  | start => exact .singleton _
  | attach _ ear _ _ _ ih => exact ih.attach ear

theorem isFactorCritical (h : H.HasOddEarDecomposition r S F) : H.IsFactorCritical S :=
  h.vertex_construction.isFactorCritical

/-- Each intermediate graph is factor-critical using only the recorded
edges of its own decomposition prefix. -/
theorem isFactorCritical_restrictEdges (h : H.HasOddEarDecomposition r S F) :
    (H.restrictEdges F).IsFactorCritical S := by
  induction h with
  | start =>
    intro v hv
    have hvr := Finset.mem_singleton.mp hv
    subst v
    exact ⟨∅, by simp [IsPerfectMatchingOn]⟩
  | @attach S F _ ear es hw _ ih =>
    let A := ear.restrictEdges (F ∪ es.toFinset) hw Finset.subset_union_right
    exact A.isFactorCritical (ih.restrictEdges_mono Finset.subset_union_left)

end HasOddEarDecomposition

/-- The existence direction of the factor-critical odd-ear theorem, with
an arbitrary starting vertex and coverage of every labelled edge. Once all
vertices have been reached, unused edges are added as one-edge ears. -/
theorem IsFactorCritical.hasOddEarDecomposition (hfc : H.IsFactorCritical Finset.univ)
    (r : V) : H.HasOddEarDecomposition r Finset.univ Finset.univ := by
  classical
  obtain ⟨M, hM⟩ := hfc r (Finset.mem_univ _)
  let C : Finset (Finset V × Finset E) := Finset.univ.filter fun p ↦
    H.HasOddEarDecomposition r p.1 p.2 ∧
      ∀ a b, (∃ e ∈ M, H.Joins e a b) → (a ∈ p.1 ↔ b ∈ p.1)
  have hstart : ({r}, ∅) ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, .start, ?_⟩
    intro a b hab
    obtain ⟨e, heM, heab⟩ := hab
    obtain ⟨i, hi⟩ := heab.exists_end
    obtain ⟨j, hj⟩ := (H.joins_comm.mp heab).exists_end
    have har : a ≠ r := fun hh ↦
      (Finset.mem_erase.mp (hM.1 e heM i)).1 (hi.trans hh)
    have hbr : b ≠ r := fun hh ↦
      (Finset.mem_erase.mp (hM.1 e heM j)).1 (hj.trans hh)
    simp [har, hbr]
  obtain ⟨⟨S, F⟩, hSF, hmax⟩ := C.exists_max_image (fun p ↦ p.1.card + p.2.card)
    ⟨({r}, ∅), hstart⟩
  obtain ⟨hD, hclosed⟩ := (Finset.mem_filter.mp hSF).2
  have hS : S = Finset.univ := by
    by_contra hS
    have hp : (Finset.univ \ S).Nonempty := Finset.sdiff_nonempty.mpr fun h ↦
      hS (Finset.Subset.antisymm (Finset.subset_univ _) h)
    obtain ⟨A, hSA, hAclosed⟩ := hfc.exists_oddEar_closed hM hD.root_mem hclosed hp
    obtain ⟨es, hes⟩ := A.exists_labels
    have hne : A.interior ≠ [] := by
      intro hh
      have hv : A.vertices = S := by simp [OddEar.vertices, hh]
      rw [hv] at hSA
      exact (lt_irrefl S) hSA
    have hnew := hD.attach A es hes (A.labels_disjoint_old hD.edgesIn hne hes)
    have hAC : (A.vertices, F ∪ es.toFinset) ∈ C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew, hAclosed⟩
    have hhi := hmax _ hAC
    have hlo : S.card < A.vertices.card := Finset.card_lt_card hSA
    have hFle : F.card ≤ (F ∪ es.toFinset).card := Finset.card_le_card Finset.subset_union_left
    change A.vertices.card + (F ∪ es.toFinset).card ≤ S.card + F.card at hhi
    omega
  subst S
  have hF : F = Finset.univ := by
    by_contra hF
    obtain ⟨e, he⟩ := Finset.sdiff_nonempty.mpr (show ¬ Finset.univ ⊆ F from fun h ↦
      hF (Finset.Subset.antisymm (Finset.subset_univ _) h))
    have heF := (Finset.mem_sdiff.mp he).2
    let A : H.OddEar Finset.univ := {
      start := H.endAt e 0
      finish := H.endAt e 1
      interior := []
      start_mem := Finset.mem_univ _
      finish_mem := Finset.mem_univ _
      nodup := by simp
      avoids := by simp
      even := by simp
      chain := List.isChain_cons_cons.mpr ⟨⟨e, Or.inl ⟨rfl, rfl⟩⟩, .singleton _⟩ }
    have hw : H.EdgeChain A.start [e] (A.interior ++ [A.finish]) :=
      .cons (Or.inl ⟨rfl, rfl⟩) (.nil _)
    have hd : Disjoint F ([e] : List E).toFinset := by simp [heF]
    have hnew := hD.attach A [e] hw hd
    have hAC : (A.vertices, F ∪ ([e] : List E).toFinset) ∈ C :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew, fun _ _ _ ↦ by simp [A, OddEar.vertices]⟩
    have hhi := hmax _ hAC
    change A.vertices.card + (F ∪ ([e] : List E).toFinset).card ≤
      (Finset.univ : Finset V).card + F.card at hhi
    simp [A, OddEar.vertices, Finset.card_insert_of_notMem heF] at hhi
  exact hF ▸ hD

/-- The full odd-ear characterization, including all labelled edges. -/
theorem isFactorCritical_iff_hasOddEarDecomposition (r : V) :
    H.IsFactorCritical Finset.univ ↔ H.HasOddEarDecomposition r Finset.univ Finset.univ :=
  ⟨fun h ↦ h.hasOddEarDecomposition r, HasOddEarDecomposition.isFactorCritical⟩

end GraphPuzzles.LoopMultigraph
