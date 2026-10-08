import GraphPuzzles.Bricks.BrickSplicing

/-! A degree bound on surviving cut labels rules out a two-vertex separator. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- Two vertices cannot cover more labels than their total incidence degree. -/
theorem exists_edge_avoiding_pair_of_degree_sum {F : Finset E} (u v : V) (huv : u ≠ v)
    (hF : H.degreeIn F u + H.degreeIn F v < F.card) :
    ∃ e ∈ F, ∀ k, H.endAt e k ∉ ({u, v} : Finset V) := by
  by_contra hn
  push Not at hn
  have hends : ∀ e ∈ F, 1 ≤ H.endsIn {u, v} e := by
    intro e he
    obtain ⟨k, hk⟩ := hn e he
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hsum : F.card ≤ H.degreeIn F u + H.degreeIn F v := by
    calc
      F.card = ∑ _e ∈ F, 1 := by simp
      _ ≤ ∑ e ∈ F, H.endsIn {u, v} e := Finset.sum_le_sum hends
      _ = ∑ w ∈ ({u, v} : Finset V), H.degreeIn F w := (H.sum_degreeIn_eq _ _).symm
      _ = H.degreeIn F u + H.degreeIn F v := Finset.sum_pair huv
  omega

/-- Five surviving cut labels of maximum degree two suffice to splice
two brick contractions into a brick. -/
theorem IsMatchingCovered.isBrick_of_brick_contractions_cut_degree_two
    (hm : H.IsMatchingCovered) {X : Finset V}
    (hl : (H.contract X).IsBrick) (hr : (H.contract (Finset.univ \ X)).IsBrick)
    {F : Finset E} (hFX : F ⊆ H.dangling X)
    (hd : ∀ w, H.degreeIn F w ≤ 2) (hF : 5 ≤ F.card) : H.IsBrick := by
  apply hm.isBrick_of_brick_contractions hl hr
  intro u v huv
  obtain ⟨e, he, huv'⟩ := exists_edge_avoiding_pair_of_degree_sum (H := H) (F := F) u v huv
    (by have hu := hd u; have hv := hd v; omega)
  exact ⟨e, hFX he, huv'⟩

end GraphPuzzles.LoopMultigraph
