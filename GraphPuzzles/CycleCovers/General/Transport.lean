import GraphPuzzles.CycleCovers.General.Upstream

/-! Transport the eight even layers, restoring loops in the first two layers. -/

namespace GraphPuzzles.CycleDoubleCoverProof

open scoped BigOperators

open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {H : LoopMultigraph V E}

/-- The eight binary triples, in the indexing convention of the existing cover API. -/
noncomputable def gammaIndex : Fin 8 ≃ CDCLean.Gamma :=
  Fintype.equivOfCardEq (by simp [CDCLean.Gamma])

private theorem binary_zero_or_one (a : CDCLean.F₂) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Non-loop membership comes from the checked cover; each loop goes in layers zero and one. -/
noncomputable def layerMember (D : (nonLoopGraph H).IndexedEvenDoubleCover)
    (i : Fin 8) (e : E) : Prop :=
  if h : H.endAt e 0 ≠ H.endAt e 1 then D.member (gammaIndex i) ⟨e, h⟩ = 1
  else i = 0 ∨ i = 1

omit [DecidableEq E] in
theorem layer_even (D : (nonLoopGraph H).IndexedEvenDoubleCover) (i : Fin 8) :
    H.IsEvenEdgeSet (Finset.univ.filter (layerMember D i)) := by
  classical
  intro w
  let q : E → CDCLean.F₂ := fun e ↦
    if h : H.endAt e 0 ≠ H.endAt e 1 then
      (if H.endAt e 0 = w then D.member (gammaIndex i) ⟨e, h⟩ else 0) +
      (if H.endAt e 1 = w then D.member (gammaIndex i) ⟨e, h⟩ else 0)
    else 0
  have hpoint (e : E) : (if layerMember D i e then H.edgeIncidence w e else 0) = q e := by
    by_cases h : H.endAt e 0 ≠ H.endAt e 1
    · rcases binary_zero_or_one (D.member (gammaIndex i) ⟨e, h⟩) with hz | ho
      · simp [layerMember, q, h, hz]
      · simp [layerMember, q, h, ho, LoopMultigraph.edgeIncidence]
    · have hl : H.endAt e 0 = H.endAt e 1 := not_ne_iff.mp h
      have hz : H.edgeIncidence w e = 0 := by
        simpa using H.singleton_loop_even e hl w
      simp [q, h, hz]
  rw [Finset.sum_filter]
  calc
    (∑ e : E, if layerMember D i e then H.edgeIncidence w e else 0) = ∑ e : E, q e :=
      Finset.sum_congr rfl (fun e _ ↦ hpoint e)
    _ = ∑ e : {e : E // H.endAt e 0 ≠ H.endAt e 1}, q e.1 := by
      calc
        (∑ e : E, q e) = ∑ e ∈ Finset.univ.filter
            (fun e ↦ H.endAt e 0 ≠ H.endAt e 1), q e := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro e _
          by_cases h : H.endAt e 0 ≠ H.endAt e 1 <;> simp [q, h]
        _ = _ := Finset.sum_subtype _ (fun e ↦ by simp) q
    _ = 0 := by
      have hq (e : {e : E // H.endAt e 0 ≠ H.endAt e 1}) : q e.1 =
          (if H.endAt e.1 0 = w then D.member (gammaIndex i) e else 0) +
          (if H.endAt e.1 1 = w then D.member (gammaIndex i) e else 0) := by
        simp only [q, dif_pos e.2]
      simp_rw [hq]
      exact D.vertexEven (gammaIndex i) w

/-- A checked cover in the upstream representation gives an eight-cycle double cover
in the endpoint-multigraph representation, including all deleted loops. -/
noncomputable def toEightCover (D : (nonLoopGraph H).IndexedEvenDoubleCover) :
    H.CycleDoubleCover 8 where
  cycles i := ⟨Finset.univ.filter (layerMember D i), layer_even D i⟩
  coveredTwice e := by
    classical
    by_cases h : H.endAt e 0 ≠ H.endAt e 1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, layerMember, dif_pos h]
      rw [Finset.card_filter]
      have hs := gammaIndex.sum_comp
        (fun s ↦ if D.member s ⟨e, h⟩ = 1 then (1 : ℕ) else 0)
      exact hs.trans (by simpa only [Finset.card_filter] using D.coveredTwice ⟨e, h⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, layerMember, dif_neg h]
      have heq : (Finset.univ.filter fun i : Fin 8 ↦ i = 0 ∨ i = 1) = {0, 1} := by
        ext i
        simp
      rw [heq]
      decide

end GraphPuzzles.CycleDoubleCoverProof
