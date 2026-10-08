import GraphPuzzles.Reduction.Removable.EdgeRestriction
import GraphPuzzles.Circuits.OrdinaryCircuit

/-! Matchings covering every vertex other than a distinguished hub once. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A `v`-matching in the terminology of Campos–Lucchesi: every vertex other
than `v` has exactly one incidence in the edge set. -/
def IsVertexMatching (H : LoopMultigraph V E) (v : V) (M : Finset E) : Prop :=
  ∀ w, w ≠ v → H.degreeIn M w = 1

omit [DecidableEq E] in
theorem IsPerfectMatching.isVertexMatching {M : Finset E} (hM : H.IsPerfectMatching M)
    (v : V) : H.IsVertexMatching v M := fun w _ ↦ hM w

omit [DecidableEq E] in
/-- On an even vertex set the hub degree of a vertex matching is odd. -/
theorem IsVertexMatching.odd_hub_degree {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V)) :
    Odd (H.degreeIn M v) := by
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hs : (∑ w ∈ Finset.univ.erase v, H.degreeIn M w) = Fintype.card V - 1 := by
    calc
      _ = ∑ _w ∈ Finset.univ.erase v, 1 := Finset.sum_congr rfl fun w hw ↦
        hM w (Finset.mem_erase.mp hw).1
      _ = _ := by simp
  have hh := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun w ↦ H.degreeIn M w) (Finset.mem_univ v)
  rw [hs, H.sum_degreeIn] at hh
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff]
  omega

omit [DecidableEq E] in
theorem IsVertexMatching.odd_degrees {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V)) (w : V) :
    Odd (H.degreeIn M w) := by
  by_cases hw : w = v
  · exact hw ▸ hM.odd_hub_degree heven
  · rw [hM w hw]
    decide

/-- Every odd shore has an odd number of edges of a vertex matching crossing
it, even when the shore contains the hub. -/
theorem IsVertexMatching.odd_crossing {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V))
    {Q : Finset V} (hQ : Odd Q.card) : Odd (M ∩ H.dangling Q).card := by
  have hp := sum_degreeIn_mod_two (K := H) Q M
  have hs := Finset.odd_sum_iff_odd_card_odd (s := Q) (fun w ↦ H.degreeIn M w)
  rw [Finset.filter_true_of_mem (fun w _ ↦ hM.odd_degrees heven w)] at hs
  have ho := hs.mpr hQ
  rw [Nat.odd_iff] at ho ⊢
  omega

/-- A spanning edge restriction containing the edge set preserves a vertex
matching. -/
theorem IsVertexMatching.exists_restrictEdges {v : V} {M S : Finset E}
    (hM : H.IsVertexMatching v M) (hMS : M ⊆ S) :
    ∃ N, (H.restrictEdges S).IsVertexMatching v N ∧ N.image Subtype.val = M := by
  let N : Finset S := Finset.univ.filter fun e ↦ e.1 ∈ M
  have heq : N.image Subtype.val = M := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hf).2
    · intro he
      exact Finset.mem_image.mpr ⟨⟨e, hMS he⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  refine ⟨N, fun w hw ↦ ?_, heq⟩
  rw [← restrictEdges_degreeIn, heq]
  exact hM w hw

end GraphPuzzles.LoopMultigraph
