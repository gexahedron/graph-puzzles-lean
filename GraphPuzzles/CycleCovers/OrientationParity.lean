import GraphPuzzles.CycleCovers.TJoin

/-! Prescribed orientation parity, constructed with the binary T-join theorem. -/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (H : LoopMultigraph V E)

/-- Parity of the number of edges directed out of a vertex. A loop contributes once. -/
def outParity (F : Finset E) (tail : E → Fin 2) (v : V) : F₂ :=
  ∑ e ∈ F, if H.endAt e (tail e) = v then 1 else 0

/-- Outgoing parity is the parity of the outgoing half-edge count. -/
theorem outParity_eq_card_halfEdges (F : Finset E) (tail : E → Fin 2) (v : V) :
    H.outParity F tail v =
      ((Finset.univ.filter fun h : H.halfEdgesAt v ↦
        h.1.1 ∈ F ∧ h.1.2 = tail h.1.1).card : F₂) := by
  have hcard : (Finset.univ.filter fun h : H.halfEdgesAt v ↦
      h.1.1 ∈ F ∧ h.1.2 = tail h.1.1).card =
      (F.filter fun e ↦ H.endAt e (tail e) = v).card := by
    apply Finset.card_bij (fun h _ ↦ h.1.1)
    · intro h hh
      obtain ⟨he, hi⟩ := (Finset.mem_filter.mp hh).2
      exact Finset.mem_filter.mpr ⟨he, hi ▸ h.2⟩
    · intro x hx y hy hxy
      have hxi := (Finset.mem_filter.mp hx).2.2
      have hyi := (Finset.mem_filter.mp hy).2.2
      exact Subtype.ext (Prod.ext hxy (hxi.trans ((congrArg tail hxy).trans hyi.symm)))
    · intro e he
      obtain ⟨heF, hev⟩ := Finset.mem_filter.mp he
      exact ⟨⟨(e, tail e), hev⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heF, rfl⟩, rfl⟩
  rw [hcard]
  simp only [outParity, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Reversing a set of edges changes outgoing parity by its binary boundary. -/
theorem outParity_flip (F J : Finset E) (hJF : J ⊆ F) (v : V) :
    H.outParity F (fun e ↦ if e ∈ J then 1 else 0) v =
      H.outParity F (fun _ ↦ 0) v + H.boundary J v := by
  unfold outParity
  calc
    (∑ e ∈ F, if H.endAt e (if e ∈ J then 1 else 0) = v then 1 else 0) =
        ∑ e ∈ F, ((if H.endAt e 0 = v then 1 else 0) +
          (if e ∈ J then H.edgeIncidence v e else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ J
      · simp only [he, if_true, edgeIncidence]
        rw [← add_assoc, F₂_add_self, zero_add]
      · simp [he]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hJF]
      rfl

omit [DecidableEq E] in
/-- The weighted outgoing parity counts each directed edge at its tail. -/
theorem sum_mul_outParity (F : Finset E) (tail : E → Fin 2) (c : V → F₂) :
    ∑ v, c v * H.outParity F tail v = ∑ e ∈ F, c (H.endAt e (tail e)) := by
  unfold outParity
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

/-- An edge orientation with specified outgoing parity exists when the condition holds on
every union of components. The condition is expressed without choosing components. -/
theorem exists_orientation_of_parity (F : Finset E) (target : V → F₂)
    (hcut : ∀ c : V → F₂,
      (∀ e ∈ F, c (H.endAt e 0) = c (H.endAt e 1)) →
        ∑ v, c v * target v = ∑ e ∈ F, c (H.endAt e 0)) :
    ∃ tail : E → Fin 2, ∀ v, H.outParity F tail v = target v := by
  let d : V → F₂ := fun v ↦ target v + H.outParity F (fun _ ↦ 0) v
  obtain ⟨J, hJF, hJ⟩ := H.exists_boundary_eq F d (by
    intro c hc
    simp only [d, mul_add, Finset.sum_add_distrib]
    rw [hcut c hc, H.sum_mul_outParity]
    exact F₂_add_self _)
  refine ⟨fun e ↦ if e ∈ J then 1 else 0, ?_⟩
  intro v
  rw [H.outParity_flip F J hJF, hJ]
  dsimp [d]
  rw [add_comm (target v), ← add_assoc, F₂_add_self, zero_add]

end LoopMultigraph
end GraphPuzzles
