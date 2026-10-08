import GraphPuzzles.Petersen.PetersenMatching
import GraphPuzzles.Ears.ClosedOddEar
import Mathlib.Data.ZMod.Defs

/-! Two pentagons joined by a permutation matching. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

/-- Two labelled five-cycles, joined by the permutation `σ`. -/
def pentagonalPair (σ : Equiv.Perm (Fin 5)) :
    LoopMultigraph (Fin 2 × Fin 5) (Fin 3 × Fin 5) :=
  ⟨fun e k ↦ if e.1 = 0 then (0, if k = 0 then e.2 else e.2 + 1)
    else if e.1 = 1 then (if k = 0 then (0, e.2) else (1, σ e.2))
    else (1, if k = 0 then e.2 else e.2 + 1)⟩

/-- The outer pentagon is the selected shore. -/
def pentagonalPairShore : Finset (Fin 2 × Fin 5) :=
  Finset.univ.filter (fun v ↦ v.1 = 0)

/-- Rim edges stay in their own layer, and each spoke has its own outer endpoint. -/
theorem pentagonalPair_isSimple (σ : Equiv.Perm (Fin 5)) :
    (pentagonalPair σ).IsSimple := by
  constructor
  · rintro ⟨a, i⟩
    fin_cases a <;> fin_cases i <;> simp [pentagonalPair]
  · rintro ⟨a, i⟩ ⟨b, j⟩
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [Joins, pentagonalPair]

/-- Adjacency in the labelled five-cycle. -/
def PentagonAdjacent (a b : Fin 5) : Prop := b = a + 1 ∨ a = b + 1

private theorem pentagon_nonneighbor (a b : Fin 5) (hne : a ≠ b)
    (hn : ¬ PentagonAdjacent a b) : b = a + 2 ∨ b = a + 3 := by
  revert a b
  unfold PentagonAdjacent
  decide

private theorem pentagon_no_backtrack (a b c s : Fin 5) (hs : s = 2 ∨ s = 3)
    (hab : b = a + s) (hbc : b ≠ c) (hac : a ≠ c)
    (hn : ¬ PentagonAdjacent b c) : c = b + s := by
  revert a b c s
  unfold PentagonAdjacent
  decide

/-- The two orientations of a pentagram, after a cyclic shift. -/
def pentagramPermutation (a : Fin 5) (b : Bool) : Equiv.Perm (Fin 5) where
  toFun i := a + (if b then 2 else 3) * i
  invFun j := (if b then 3 else 2) * (j - a)
  left_inv := by
    fin_cases a <;> cases b <;> decide
  right_inv := by
    fin_cases a <;> cases b <;> decide

/-- If adjacent outer vertices never have adjacent inner partners, the
permutation is one of the two pentagram orientations, up to an inner rotation. -/
theorem eq_pentagramPermutation_of_no_common_adjacent (σ : Equiv.Perm (Fin 5))
    (hn : ∀ i, ¬ PentagonAdjacent (σ i) (σ (i + 1))) :
    ∃ b : Bool, σ = pentagramPermutation (σ 0) b := by
  letI : CommRing (Fin 5) := Fin.instCommRing 5
  have step (s : Fin 5) (hs : s = 2 ∨ s = 3) (h1 : σ 1 = σ 0 + s) :
      ∀ i : Fin 5, σ i = σ 0 + s * i := by
    have h2 : σ 2 = σ 1 + s := pentagon_no_backtrack _ _ _ s hs h1
      (σ.injective.ne (by decide : (1 : Fin 5) ≠ 2))
      (σ.injective.ne (by decide : (0 : Fin 5) ≠ 2)) (hn 1)
    have h3 : σ 3 = σ 2 + s := pentagon_no_backtrack _ _ _ s hs h2
      (σ.injective.ne (by decide : (2 : Fin 5) ≠ 3))
      (σ.injective.ne (by decide : (1 : Fin 5) ≠ 3)) (hn 2)
    have h4 : σ 4 = σ 3 + s := pentagon_no_backtrack _ _ _ s hs h3
      (σ.injective.ne (by decide : (3 : Fin 5) ≠ 4))
      (σ.injective.ne (by decide : (2 : Fin 5) ≠ 4)) (hn 3)
    intro i
    fin_cases i
    · change σ 0 = σ 0 + s * 0
      ring
    · change σ 1 = σ 0 + s * 1
      rw [h1]; ring
    · change σ 2 = σ 0 + s * 2
      rw [h2, h1]; ring
    · change σ 3 = σ 0 + s * 3
      rw [h3, h2, h1]; ring
    · change σ 4 = σ 0 + s * 4
      rw [h4, h3, h2, h1]; ring
  rcases pentagon_nonneighbor (σ 0) (σ 1)
      (σ.injective.ne (by decide : (0 : Fin 5) ≠ 1)) (hn 0) with h | h
  · exact ⟨true, Equiv.ext (step 2 (Or.inl rfl) h)⟩
  · exact ⟨false, Equiv.ext (step 3 (Or.inr rfl) h)⟩

private def pentagonalThreeMatching (i j : Fin 5) : Finset (Fin 3 × Fin 5) :=
  {(0, i), (2, j), (1, i + 2), (1, i + 3), (1, i + 4)}

private theorem pentagonalPair_outer_joins (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    (pentagonalPair σ).Joins (0, i) (0, i) (0, i + 1) := Or.inl ⟨rfl, rfl⟩

private theorem pentagonalPair_spoke_joins (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    (pentagonalPair σ).Joins (1, i) (0, i) (1, σ i) := Or.inl ⟨rfl, rfl⟩

private theorem degreeIn_sum_singletons {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E) (M : Finset E) (v : V) :
    H.degreeIn M v = ∑ e ∈ M, H.degreeIn {e} v := by
  simp only [degreeIn, Finset.card_filter, Finset.sum_product]
  simp

private theorem pentagonalThreeMatching_isPerfectMatching (σ : Equiv.Perm (Fin 5))
    (i j : Fin 5) (hj : (pentagonalPair σ).Joins (2, j) (1, σ i) (1, σ (i + 1))) :
    (pentagonalPair σ).IsPerfectMatching (pentagonalThreeMatching i j) := by
  have ho := fun i v ↦ (pentagonalPair_outer_joins σ i).degreeIn_singleton_eq v
  have hs := fun i v ↦ (pentagonalPair_spoke_joins σ i).degreeIn_singleton_eq v
  have hi := hj.degreeIn_singleton_eq
  rintro ⟨a, b⟩
  rw [degreeIn_sum_singletons]
  fin_cases a
  · fin_cases i <;> fin_cases b <;> simp [pentagonalThreeMatching, ho, hs, hi]
  · obtain ⟨b, rfl⟩ := σ.surjective b
    fin_cases i <;> fin_cases b <;>
      simp [pentagonalThreeMatching, ho, hs, hi]

private theorem pentagonalPair_dangling (σ : Equiv.Perm (Fin 5)) :
    (pentagonalPair σ).dangling pentagonalPairShore =
      Finset.univ.filter (fun e : Fin 3 × Fin 5 ↦ e.1 = 1) := by
  ext ⟨a, i⟩
  fin_cases a <;> simp [mem_dangling, pentagonalPairShore, pentagonalPair]

private theorem pentagonalThreeMatching_crossing (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    (pentagonalThreeMatching i j ∩ (pentagonalPair σ).dangling pentagonalPairShore).card = 3 := by
  rw [pentagonalPair_dangling]
  fin_cases i <;> fin_cases j <;> decide

/-- A common adjacent pair leaves exactly three matching spokes. -/
theorem pentagonalPair_exists_three_of_common_adjacent (σ : Equiv.Perm (Fin 5))
    {i : Fin 5} (hi : PentagonAdjacent (σ i) (σ (i + 1))) :
    ∃ M, (pentagonalPair σ).IsPerfectMatching M ∧
      (M ∩ (pentagonalPair σ).dangling pentagonalPairShore).card = 3 := by
  rcases hi with h | h
  · refine ⟨pentagonalThreeMatching i (σ i), ?_, pentagonalThreeMatching_crossing σ _ _⟩
    apply pentagonalThreeMatching_isPerfectMatching
    exact Or.inl ⟨rfl, congrArg (fun j : Fin 5 ↦ ((1 : Fin 2), j)) h.symm⟩
  · refine ⟨pentagonalThreeMatching i (σ (i + 1)), ?_, pentagonalThreeMatching_crossing σ _ _⟩
    apply pentagonalThreeMatching_isPerfectMatching
    exact Or.inr ⟨rfl, congrArg (fun j : Fin 5 ↦ ((1 : Fin 2), j)) h.symm⟩

private def pentagonalLayerPerm {n : ℕ} (π : Fin n → Equiv.Perm (Fin 5)) :
    Equiv.Perm (Fin n × Fin 5) where
  toFun v := (v.1, π v.1 v.2)
  invFun v := (v.1, (π v.1).symm v.2)
  left_inv v := by rcases v with ⟨a, i⟩; simp
  right_inv v := by rcases v with ⟨a, i⟩; simp

/-- An explicit endpoint isomorphism from either pentagram orientation. -/
def pentagonalPair_pentagramIso (a : Fin 5) (b : Bool) :
    EndpointIso (pentagonalPair (pentagramPermutation a b)) petersen where
  vertexEquiv := (pentagonalLayerPerm fun i : Fin 2 ↦
    if i = 0 then Equiv.refl _ else (pentagramPermutation a b).symm).trans finProdFinEquiv
  edgeEquiv := (pentagonalLayerPerm fun i : Fin 3 ↦
    if i = 2 then (if b then (Equiv.addRight (1 : Fin 5)).trans (pentagramPermutation a b).symm
      else (pentagramPermutation a b).symm) else Equiv.refl _).trans finProdFinEquiv
  endEquiv e := if e.1 = 2 ∧ b = true then Equiv.swap 0 1 else Equiv.refl _
  map_endAt := by
    fin_cases a <;> cases b <;> rintro ⟨c, i⟩ k <;>
      fin_cases c <;> fin_cases i <;> fin_cases k <;> decide

/-- Every pair of pentagons with a matching between them is Petersen or has
an explicit perfect matching crossing between the pentagons three times. -/
theorem pentagonalPair_three_or_petersen (σ : Equiv.Perm (Fin 5)) :
    (∃ M, (pentagonalPair σ).IsPerfectMatching M ∧
      (M ∩ (pentagonalPair σ).dangling pentagonalPairShore).card = 3) ∨
      (pentagonalPair σ).IsPetersen := by
  classical
  by_cases h : ∃ i, PentagonAdjacent (σ i) (σ (i + 1))
  · obtain ⟨i, hi⟩ := h
    exact Or.inl (pentagonalPair_exists_three_of_common_adjacent σ hi)
  · have hn : ∀ i, ¬ PentagonAdjacent (σ i) (σ (i + 1)) := by
      simpa only [not_exists] using h
    obtain ⟨b, heq⟩ := eq_pentagramPermutation_of_no_common_adjacent σ hn
    exact Or.inr ⟨heq.symm ▸ pentagonalPair_pentagramIso (σ 0) b⟩

end GraphPuzzles.LoopMultigraph
