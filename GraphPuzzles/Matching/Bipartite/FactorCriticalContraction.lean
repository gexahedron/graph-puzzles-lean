import GraphPuzzles.Cuts.Contraction.ContractionBarrierLift
import GraphPuzzles.Matching.Barriers.VertexMatchingBarrier
import GraphPuzzles.Matching.Bipartite.FactorCriticalBipartite
import GraphPuzzles.Cuts.CutWitness

/-! Campos–Lucchesi Proposition 5.11: contracting the complement of a
factor-critical odd shore of a brick gives a bicritical matching-covered graph. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A matching supported on a retained shore is unchanged by contraction. -/
theorem IsPerfectMatchingOn.contract_shore {X S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn S M) (hS : S ⊆ X) :
    (H.contract X).IsPerfectMatchingOn (contractShore X S) (H.contractMatching X M) := by
  constructor
  · intro e he k
    have hk := hM.1 e.1 ((mem_contractMatching X M e).mp he) k
    rw [contract_endAt, dif_pos (hS hk), some_mem_contractShore]
    exact hk
  · intro w hw
    cases w with
    | none => exact (none_not_mem_contractShore X S hw).elim
    | some w =>
      rw [contractMatching, contract_degreeIn_some]
      exact hM.2 w.1 ((some_mem_contractShore X S w).mp hw)

/-- Factor-criticality of the retained shore is factor-criticality after
deleting the contraction pole. -/
theorem IsFactorCritical.contract {X : Finset V} (hfc : H.IsFactorCritical X) :
    (H.contract X).IsFactorCritical (Finset.univ.erase none) := by
  intro w hw
  cases w with
  | none => simp at hw
  | some w =>
    obtain ⟨M, hM⟩ := hfc w.1 w.2
    refine ⟨H.contractMatching X M, ?_⟩
    have heq : contractShore X (X.erase w.1) =
        (Finset.univ.erase (none : Option X)).erase (some w) := contractShore_erase X w
    rw [← heq]
    exact hM.contract_shore (Finset.erase_subset _ _)

/-- In a connected graph, factor-criticality after deleting a
non-isolated hub supplies a perfect matching. -/
theorem IsFactorCritical.exists_perfectMatching_of_connected {v w : V}
    (hfc : H.IsFactorCritical (Finset.univ.erase v)) (hc : H.IsConnected) (hw : w ≠ v) :
    ∃ M, H.IsPerfectMatching M := by
  obtain ⟨e, he⟩ := hc.dangling_nonempty (X := {v}) (Finset.singleton_nonempty v)
    ⟨w, by simp [hw]⟩
  have hend : ∃ k, H.endAt e k ∈ ({v} : Finset V) ∧
      H.endAt e (Fin.rev k) ∉ ({v} : Finset V) := by
    have hh := mem_dangling.mp he
    by_cases h0 : H.endAt e 0 ∈ ({v} : Finset V)
    · exact ⟨0, h0, by simpa using (show H.endAt e 1 ∉ ({v} : Finset V) from by tauto)⟩
    · exact ⟨1, by tauto, by simpa using h0⟩
  obtain ⟨k, hk, hn⟩ := hend
  have hkv : H.endAt e k = v := Finset.mem_singleton.mp hk
  have hrv : H.endAt e (Fin.rev k) ≠ v := fun h ↦ hn (by simp [h])
  obtain ⟨M, hM⟩ := hfc (H.endAt e (Fin.rev k)) (by simp [hrv])
  refine ⟨insert e M, hM.insert_perfect ?_ hrv.symm⟩
  fin_cases k
  · exact Or.inl ⟨hkv, rfl⟩
  · exact Or.inr ⟨rfl, hkv⟩

/-- Bicriticality and connectivity make every non-loop edge admissible. -/
theorem IsBicritical.isMatchingCovered (hb : H.IsBicritical) (hc : H.IsConnected)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : H.IsMatchingCovered := by
  refine ⟨hc, fun e ↦ ?_⟩
  obtain ⟨M, hM⟩ := hb (H.endAt e 0) (H.endAt e 1) (hl e)
  exact ⟨insert e M, hM.insert_perfect (Or.inl ⟨rfl, rfl⟩) (hl e),
    Finset.mem_insert_self _ _⟩

/-- All nontrivial barriers are excluded: a barrier avoiding the pole
lifts to the original bicritical graph, while one containing the pole
contradicts factor-criticality after deleting it. -/
theorem IsBicritical.contract_of_factorCritical (hb : H.IsBicritical)
    {X : Finset V} (hX : (Finset.univ \ X).Nonempty)
    (ho : Odd (Finset.univ \ X).card) (hfc : H.IsFactorCritical X)
    {M : Finset (H.meets X)} (hM : (H.contract X).IsPerfectMatching M) :
    (H.contract X).IsBicritical := by
  apply (isBicritical_iff_barrier_card_le_one hM).mpr
  intro B F hB
  by_contra hn
  have hnB : none ∈ B := hB.pole_mem_of_bicritical F hb hX ho (by omega)
  obtain ⟨w, hw, hne⟩ : ∃ w ∈ B, w ≠ none := by
    by_contra h
    push Not at h
    have hh : B ⊆ {none} := fun w hw ↦ Finset.mem_singleton.mpr (h w hw)
    have hcard := Finset.card_le_card hh
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨P, hP⟩ := hfc.contract w (by simp [hne])
  exact hB.not_pairMatching F hnB hw hne.symm hP

/-- Campos–Lucchesi Proposition 5.11, in the original brick context.
The retained shore is nonempty and odd, and its complement is nonempty. -/
theorem IsBrick.contract_matchingCovered_bicritical_of_factorCritical (hb : H.IsBrick)
    {X : Finset V} (ho : Odd X.card) (hX : (Finset.univ \ X).Nonempty)
    (hfc : H.IsFactorCritical X) :
    (H.contract X).IsMatchingCovered ∧ (H.contract X).IsBicritical := by
  have hc := hb.matchingCovered.1.contract X hX
  have hl := contract_loopless X hb.matchingCovered.loopless
  obtain ⟨w, hw⟩ := Finset.card_pos.mp ho.pos
  obtain ⟨M, hM⟩ := hfc.contract.exists_perfectMatching_of_connected hc
    (show (some (⟨w, hw⟩ : X)) ≠ none by simp)
  obtain ⟨e, _⟩ := hb.matchingCovered.1.dangling_nonempty ⟨w, hw⟩ hX
  obtain ⟨P, hP, _⟩ := hb.matchingCovered.2 e
  have hcV := hP.isFractional.card_even
  have hcomp : Odd (Finset.univ \ X).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_univ]
    have hle := Finset.card_le_univ X
    rw [Nat.even_iff] at hcV
    rw [Nat.odd_iff] at ho ⊢
    omega
  have hbi := (hb.isBicritical hb.matchingCovered.loopless).contract_of_factorCritical
    hX hcomp hfc hM
  exact ⟨hbi.isMatchingCovered hc hl, hbi⟩

/-- A nonempty factor-critical shore has odd order. -/
theorem IsFactorCritical.card_odd_of_nonempty {X : Finset V}
    (hfc : H.IsFactorCritical X) (hX : X.Nonempty) : Odd X.card := by
  obtain ⟨v, hv⟩ := hX
  obtain ⟨M, hM⟩ := hfc v hv
  have he := hM.card_even
  rw [Finset.card_erase_of_mem hv, Nat.even_iff] at he
  have hp := Finset.card_pos.mpr ⟨v, hv⟩
  rw [Nat.odd_iff]
  omega

/-- The final step of the long-ear case: two nontrivial factor-critical
shores give a strictly separating cut, so the brick is not solid. -/
theorem IsBrick.not_solid_of_factorCritical_shores (hb : H.IsBrick)
    {X : Finset V} (hX : IsNontrivialCut X)
    (hl : H.IsFactorCritical X) (hr : H.IsFactorCritical (Finset.univ \ X)) :
    ¬ H.IsSolid := by
  have hne : X.Nonempty := Finset.card_pos.mp (by have := hX.1; omega)
  have hnec : (Finset.univ \ X).Nonempty :=
    Finset.card_pos.mp (by have := hX.2; omega)
  have hleft := hb.contract_matchingCovered_bicritical_of_factorCritical
    (hl.card_odd_of_nonempty hne) hnec hl
  have hright := hb.contract_matchingCovered_bicritical_of_factorCritical
    (hr.card_odd_of_nonempty hnec)
    (by simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hne) hr
  intro hs
  apply hs X
  refine ⟨⟨hleft.1, hright.1⟩, ?_, ?_⟩
  · intro hp
    have hh := hl.card_le_one_of_bipartiteOn hp.induced_of_contract
    have := hX.1
    omega
  · intro hp
    have hh := hr.card_le_one_of_bipartiteOn hp.induced_of_contract
    have := hX.2
    omega

end GraphPuzzles.LoopMultigraph
