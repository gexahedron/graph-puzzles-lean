import GraphPuzzles.Results.TwoCircuitFourMatchings

namespace GraphPuzzles.Claims

open LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- A family of `k` perfect matchings covering all edges; occurrences may repeat. -/
def HasPerfectMatchingCover (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  ∃ M : Fin k → Finset E, (∀ i, H.IsPerfectMatching (M i)) ∧ ∀ e, ∃ i, e ∈ M i

/-- The least size of a perfect-matching cover is `k`. -/
def PerfectMatchingIndexEq (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  HasPerfectMatchingCover H k ∧ ∀ j < k, ¬ HasPerfectMatchingCover H j

/-- Paper Theorem 1.1, retaining the complementary matching of the specified factor. -/
theorem two_circuit_four_matchings_prescribed (F : H.TwoCircuitFactor)
    (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    ∃ M : Fin 4 → Finset E, M 0 = F.compl ∧
      (∀ i, H.IsPerfectMatching (M i)) ∧ ∀ e, ∃ i, e ∈ M i := by
  obtain ⟨M₁, M₂, M₃, h₁, h₂, h₃, hcover⟩ :=
    F.exists_fourCover_of_properSnark' hs hnotP
  refine ⟨![F.compl, M₁, M₂, M₃], rfl, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact F.compl_perfect hs.cubic
    · exact h₁
    · exact h₂
    · exact h₃
  · intro e
    have he : e ∈ F.compl ∪ M₁ ∪ M₂ ∪ M₃ := by
      rw [hcover]
      exact Finset.mem_univ e
    simp only [Finset.mem_union] at he
    rcases he with ((h | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

/-- Four covering perfect matchings, without an external theorem hypothesis. -/
theorem two_circuit_four_matchings (F : H.TwoCircuitFactor)
    (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    HasPerfectMatchingCover H 4 := by
  obtain ⟨M, _, hM, hcover⟩ := two_circuit_four_matchings_prescribed F hs hnotP
  exact ⟨M, hM, hcover⟩

/-- Three covering perfect matchings supply a proper three-edge-colouring. -/
theorem colourable_of_three_matchings (h : HasPerfectMatchingCover H 3) :
    ∃ g : E → Color, H.ProperOff ∅ g := by
  classical
  obtain ⟨M, hM, hcover⟩ := h
  choose c hc using hcover
  refine ⟨fun e ↦ choiceColor (c e), fun e _ ↦ choiceColor_ne_zero (c e), ?_⟩
  intro w _ x y _ _ hcol
  have hi : c x.1.1 = c y.1.1 := choiceColor_injective _ _ hcol
  by_contra hne
  have htwo := H.two_le_degreeIn_of_ne x y hne (hc x.1.1) (hi.symm ▸ hc y.1.1)
  rw [hM (c x.1.1) w] at htwo
  omega

/-- Paper Theorem 1.1: the perfect matching index is exactly four. -/
theorem two_circuit_perfect_matching_index_four (F : H.TwoCircuitFactor)
    (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    PerfectMatchingIndexEq H 4 := by
  refine ⟨two_circuit_four_matchings F hs hnotP, ?_⟩
  intro k hk ⟨M, hM, hcover⟩
  obtain ⟨e, _⟩ := F.A.nonempty
  obtain ⟨j, _⟩ := hcover e
  have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  let N : Fin 3 → Finset E := fun i ↦
    if h : i.val < k then M ⟨i.val, h⟩ else M ⟨0, hpos⟩
  apply hs.notColourable
  apply colourable_of_three_matchings
  refine ⟨N, ?_, ?_⟩
  · intro i
    dsimp [N]
    split_ifs <;> apply hM
  · intro f
    obtain ⟨i, hi⟩ := hcover f
    have hi3 : i.val < 3 := by omega
    refine ⟨⟨i.val, hi3⟩, ?_⟩
    simpa only [N, dif_pos i.isLt] using hi

/-- Paper Corollary 1.2, for each chosen factor consisting of two induced circuits. -/
theorem permutation_four_matchings (F : H.TwoCircuitFactor) (_hF : F.IsInduced)
    (hs : H.IsProperSnark) (hnotP : ¬ H.IsPetersen) :
    PerfectMatchingIndexEq H 4 ∧
      ∃ M : Fin 4 → Finset E, M 0 = F.compl ∧
        (∀ i, H.IsPerfectMatching (M i)) ∧ ∀ e, ∃ i, e ∈ M i :=
  ⟨two_circuit_perfect_matching_index_four F hs hnotP,
    two_circuit_four_matchings_prescribed F hs hnotP⟩

/-- Karabáš–Máčajová's Hamiltonian cubic three-pole theorem, proved in Lean. -/
theorem karabas_macajova : KMThreePole.{u, v} := kmThreePole

/-- The Campos–Lucchesi brick theorem, proved in Lean. -/
theorem campos_lucchesi : CamposLucchesi.{u, v} := camposLucchesi

end GraphPuzzles.Claims
