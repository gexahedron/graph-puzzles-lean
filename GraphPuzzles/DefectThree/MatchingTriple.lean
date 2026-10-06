import GraphPuzzles.CycleCovers.CircuitExtensionCorollaries

/-!
# Matching triples, cores and colouring defect

The defect relation is stated by an attaining triple and a lower bound for every triple.
It therefore has its usual minimum meaning, including when no perfect matching exists:
in that case no finite defect is asserted.
-/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Three indexed perfect matchings. Repetitions are allowed. -/
structure MatchingTriple (H : LoopMultigraph V E) where
  matching : Fin 3 → Finset E
  perfect : ∀ i, H.IsPerfectMatching (matching i)

namespace MatchingTriple

variable (M : H.MatchingTriple)

/-- How many of the three indexed matchings contain an edge. -/
def multiplicity (e : E) : ℕ := (Finset.univ.filter fun i ↦ e ∈ M.matching i).card

/-- The edges covered exactly `n` times. -/
def edgesOfMultiplicity (n : ℕ) : Finset E := Finset.univ.filter fun e ↦ M.multiplicity e = n

/-- Edges omitted by the matching triple. -/
def uncovered : Finset E := M.edgesOfMultiplicity 0

/-- The core consists of all edges that are not covered exactly once. -/
def core : Finset E := Finset.univ.filter fun e ↦ M.multiplicity e ≠ 1

/-- A regular triple has no triply covered edge. -/
def IsRegular : Prop := ∀ e, M.multiplicity e ≤ 2

/-- Optimality minimizes the number of uncovered edges among all matching triples. -/
def IsOptimal : Prop := ∀ N : H.MatchingTriple, M.uncovered.card ≤ N.uncovered.card

@[simp]
theorem mem_edgesOfMultiplicity (n : ℕ) (e : E) :
    e ∈ M.edgesOfMultiplicity n ↔ M.multiplicity e = n := by
  simp [edgesOfMultiplicity]

@[simp]
theorem mem_uncovered (e : E) : e ∈ M.uncovered ↔ M.multiplicity e = 0 := by
  simp [uncovered]

@[simp]
theorem mem_core (e : E) : e ∈ M.core ↔ M.multiplicity e ≠ 1 := by
  simp [core]

theorem multiplicity_le_three (e : E) : M.multiplicity e ≤ 3 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem multiplicity_eq_one_iff (e : E) :
    M.multiplicity e = 1 ↔ ∃! i, e ∈ M.matching i := by
  rw [multiplicity, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hm : ∀ j, e ∈ M.matching j ↔ j = i := by
      intro j
      have := Finset.ext_iff.mp hi j
      simpa using this
    exact ⟨i, (hm i).mpr rfl, fun j hj ↦ (hm j).mp hj⟩
  · rintro ⟨i, hi, hu⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj ↦ hu j hj, fun h ↦ h ▸ hi⟩

theorem core_eq_union :
    M.core = M.uncovered ∪ M.edgesOfMultiplicity 2 ∪ M.edgesOfMultiplicity 3 := by
  ext e
  simp only [mem_core, Finset.mem_union, mem_uncovered, mem_edgesOfMultiplicity]
  have := M.multiplicity_le_three e
  omega

/-- The existing core-colouring construction applies to the actual matching-triple core. -/
theorem exists_fiveCycleDoubleCover_of_core_subset (hCubic : ∀ v, H.degree v = 3)
    (C : H.OrdinaryCircuit) (hcore : M.core ⊆ C.edges) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  apply C.exists_fiveCycleDoubleCover_of_matchings hCubic M.matching M.perfect
  intro e he
  apply (M.multiplicity_eq_one_iff e).mp
  by_contra hm
  exact he (hcore ((M.mem_core e).mpr hm))

/-- The core is a single nonempty connected circuit in the ordinary graph-theoretic sense. -/
def IsCircuitCore : Prop := ∃ C : H.OrdinaryCircuit, C.edges = M.core

theorem IsCircuitCore.exists_fiveCycleDoubleCover {M : H.MatchingTriple}
    (h : M.IsCircuitCore) (hCubic : ∀ v, H.degree v = 3) :
    ∃ D : H.CycleDoubleCover 5, D.Contains M.core := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨D, hD⟩ := M.exists_fiveCycleDoubleCover_of_core_subset hCubic C (by rw [hC])
  exact ⟨D, hC ▸ hD⟩

end MatchingTriple

/-- Colouring defect `d`: an optimal matching triple leaves precisely `d` edges uncovered. -/
def HasColoringDefect (H : LoopMultigraph V E) (d : ℕ) : Prop :=
  ∃ M : H.MatchingTriple, M.uncovered.card = d ∧ M.IsOptimal

theorem HasColoringDefect.unique {d d' : ℕ}
    (hd : H.HasColoringDefect d) (hd' : H.HasColoringDefect d') : d = d' := by
  obtain ⟨M, hM, hoptM⟩ := hd
  obtain ⟨N, hN, hoptN⟩ := hd'
  have h₁ := hoptM N
  have h₂ := hoptN M
  omega

/-- Every triple attaining the numerical defect is optimal. -/
theorem MatchingTriple.isOptimal_of_defect {d : ℕ} (M : H.MatchingTriple)
    (hd : H.HasColoringDefect d) (hM : M.uncovered.card = d) : M.IsOptimal := by
  obtain ⟨N, hN, hopt⟩ := hd
  intro P
  rw [hM, ← hN]
  exact hopt P

end LoopMultigraph
end GraphPuzzles
