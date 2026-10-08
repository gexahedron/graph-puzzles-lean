import GraphPuzzles.Ears.OddEarDecomposition
import GraphPuzzles.Ears.OddEarMatching

/-! Odd-ear decompositions indexed by their last ear outside a specified edge set. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- An odd-ear decomposition with `n` ears, of which the last ear not
contained in `M` is at position `q`. The index is zero if all ears lie in `M`. -/
inductive HasIndexedOddEarDecomposition (H : LoopMultigraph V E) (M : Finset E) (r : V) :
    ℕ → ℕ → Finset V → Finset E → Prop
  | start : HasIndexedOddEarDecomposition H M r 0 0 {r} ∅
  | attach_mem {n q : ℕ} {S : Finset V} {F : Finset E}
      (old : HasIndexedOddEarDecomposition H M r n q S F)
      (ear : H.OddEar S) (es : List E)
      (walk : H.EdgeChain ear.start es (ear.interior ++ [ear.finish]))
      (fresh : Disjoint F es.toFinset) (mem : es.toFinset ⊆ M) :
      HasIndexedOddEarDecomposition H M r (n + 1) q ear.vertices (F ∪ es.toFinset)
  | attach_outside {n q : ℕ} {S : Finset V} {F : Finset E}
      (old : HasIndexedOddEarDecomposition H M r n q S F)
      (ear : H.OddEar S) (es : List E)
      (walk : H.EdgeChain ear.start es (ear.interior ++ [ear.finish]))
      (fresh : Disjoint F es.toFinset) (outside : ¬ es.toFinset ⊆ M) :
      HasIndexedOddEarDecomposition H M r (n + 1) (n + 1) ear.vertices (F ∪ es.toFinset)

namespace HasIndexedOddEarDecomposition

variable {M F : Finset E} {r : V} {n q : ℕ} {S : Finset V}

theorem forget (h : H.HasIndexedOddEarDecomposition M r n q S F) :
    H.HasOddEarDecomposition r S F := by
  induction h with
  | start => exact .start
  | attach_mem _ A es hw hf _ ih => exact ih.attach A es hw hf
  | attach_outside _ A es hw hf _ ih => exact ih.attach A es hw hf

theorem index_le_count (h : H.HasIndexedOddEarDecomposition M r n q S F) : q ≤ n := by
  induction h with
  | start => exact le_rfl
  | attach_mem _ _ _ _ _ _ ih => omega
  | attach_outside => exact le_rfl

theorem count_zero (h : H.HasIndexedOddEarDecomposition M r 0 q S F) :
    S = {r} ∧ F = ∅ := by
  cases h
  exact ⟨rfl, rfl⟩

theorem count_le_card (h : H.HasIndexedOddEarDecomposition M r n q S F) : n ≤ F.card := by
  induction h with
  | start => simp
  | attach_mem _ A es hw hf _ ih | attach_outside _ A es hw hf _ ih =>
    have ho := A.labels_odd_length hw
    have hn := A.labels_nodup hw
    rw [Nat.odd_iff] at ho
    rw [Finset.card_union_of_disjoint hf, List.toFinset_card_of_nodup hn]
    omega

theorem index_eq_zero_iff (h : H.HasIndexedOddEarDecomposition M r n q S F) :
    q = 0 ↔ F ⊆ M := by
  induction h with
  | start => simp
  | attach_mem _ _ _ _ _ hm ih => simpa only [Finset.union_subset_iff, hm, and_true] using ih
  | attach_outside _ _ _ _ _ hm _ => simp [Finset.union_subset_iff, hm]

/-- A decomposition entirely contained in a matching can never grow beyond
its starting vertex. -/
theorem vertices_eq_singleton_of_index_zero
    (h : H.HasIndexedOddEarDecomposition M r n q S F) (hq : q = 0)
    (hd : ∀ w ∈ S, H.degreeIn M w ≤ 1) : S = {r} := by
  induction h with
  | start => rfl
  | attach_outside => omega
  | attach_mem _ A es hw _ hm ih =>
    have hAS := A.vertices_eq_of_labels_subset hw hm (fun w hw ↦
      hd w (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)))
    exact hAS.trans (ih hq (fun w hw ↦ hd w (Finset.mem_union_left _ hw)))

/-- Append a one-edge ear without changing the last nonmatching index. -/
theorem append_matching_edge (h : H.HasIndexedOddEarDecomposition M r n q S F)
    {e : E} (heS : e ∈ H.edgesIn S) (heF : e ∉ F) (heM : e ∈ M) :
    H.HasIndexedOddEarDecomposition M r (n + 1) q S (insert e F) := by
  simpa using h.attach_mem (OddEar.single S e heS) [e]
    (OddEar.single_walk S e heS) (by simp [heF]) (by simpa)

/-- Appending a one-edge ear outside the matching sets the index to its position. -/
theorem append_outside_edge (h : H.HasIndexedOddEarDecomposition M r n q S F)
    {e : E} (heS : e ∈ H.edgesIn S) (heF : e ∉ F) (heM : e ∉ M) :
    H.HasIndexedOddEarDecomposition M r (n + 1) (n + 1) S (insert e F) := by
  simpa using h.attach_outside (OddEar.single S e heS) [e]
    (OddEar.single_walk S e heS) (by simp [heF]) (by simpa)

/-- Any ordering of fresh matching edges internal to the existing shore
can be appended. In particular, permuting the matching tail preserves the index. -/
theorem append_matching_edges (h : H.HasIndexedOddEarDecomposition M r n q S F)
    (es : List E) (hn : es.Nodup) (hf : Disjoint F es.toFinset)
    (hs : es.toFinset ⊆ H.edgesIn S) (hm : es.toFinset ⊆ M) :
    H.HasIndexedOddEarDecomposition M r (n + es.length) q S (F ∪ es.toFinset) := by
  induction es generalizing n F with
  | nil => simpa using h
  | cons e es ih =>
    have heF : e ∉ F := fun he ↦ Finset.disjoint_left.mp hf he (by simp)
    have hnext := h.append_matching_edge (hs (by simp)) heF (hm (by simp))
    have htail := ih hnext (List.nodup_cons.mp hn).2 (by
      apply Finset.disjoint_left.mpr
      intro f hfi hfl
      rcases Finset.mem_insert.mp hfi with rfl | hfi
      · exact (List.nodup_cons.mp hn).1 (List.mem_toFinset.mp hfl)
      · exact Finset.disjoint_left.mp hf hfi (by simp [List.mem_toFinset.mp hfl]))
      (fun f hf ↦ hs (by simp [List.mem_toFinset.mp hf]))
      (fun f hf ↦ hm (by simp [List.mem_toFinset.mp hf]))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

end HasIndexedOddEarDecomposition

/-- Recording the last nonmatching position adds no assumption to an ear decomposition. -/
theorem HasOddEarDecomposition.indexed {r : V} {S : Finset V} {F : Finset E}
    (h : H.HasOddEarDecomposition r S F) (M : Finset E) :
    ∃ n q, H.HasIndexedOddEarDecomposition M r n q S F := by
  classical
  induction h with
  | start => exact ⟨0, 0, .start⟩
  | attach _ A es hw hf ih =>
    obtain ⟨n, q, hD⟩ := ih
    by_cases hm : es.toFinset ⊆ M
    · exact ⟨n + 1, q, hD.attach_mem A es hw hf hm⟩
    · exact ⟨n + 1, n + 1, hD.attach_outside A es hw hf hm⟩

/-- Maximality ranges over every root and every full decomposition of the
specified vertex and edge sets. -/
def IsMaximumOddEarIndex (H : LoopMultigraph V E) (M : Finset E)
    (S : Finset V) (F : Finset E) (q : ℕ) : Prop :=
  (∃ r n, H.HasIndexedOddEarDecomposition M r n q S F) ∧
    ∀ r n q', H.HasIndexedOddEarDecomposition M r n q' S F → q' ≤ q

/-- The index has a maximum, since the number of ears is bounded by the
number of original edge labels, independently of the chosen root. -/
theorem HasOddEarDecomposition.exists_maximum_index {r : V} {S : Finset V} {F : Finset E}
    (h : H.HasOddEarDecomposition r S F) (M : Finset E) :
    ∃ q, H.IsMaximumOddEarIndex M S F q := by
  classical
  let Q := (Finset.range (F.card + 1)).filter fun q ↦
    ∃ r n, H.HasIndexedOddEarDecomposition M r n q S F
  obtain ⟨n, q, hD⟩ := h.indexed M
  have hq : q ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (by have := hD.index_le_count; have := hD.count_le_card; omega), r, n, hD⟩
  obtain ⟨p, hp, hmax⟩ := Q.exists_max_image id ⟨q, hq⟩
  refine ⟨p, (Finset.mem_filter.mp hp).2, ?_⟩
  intro r' n' q' hD'
  exact hmax q' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (by have := hD'.index_le_count; have := hD'.count_le_card; omega), r', n', hD'⟩)

end GraphPuzzles.LoopMultigraph
