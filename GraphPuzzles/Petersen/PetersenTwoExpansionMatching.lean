import GraphPuzzles.Petersen.PetersenExpansionGluing
import GraphPuzzles.Matching.MatchingCommonEdge
import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixTwo

/-! The nonadjacent two-expanded-vertices branch of Section 6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- Two local restoration matchings share the restored edge. Their union
and a lifted Petersen matching cross the selected cut exactly three times. -/
theorem exists_three_crossing_two_expansions
    (R : (H.deleteEdge e).PetersenFiberModel X) {p q : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (Q : H.BipartiteRestorationShore e (R.canonicalFiber q))
    (hbic : H.IsBicritical)
    (hsingle : ∀ r, r ≠ p → r ≠ q → (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small) (hw : w ∈ Q.small)
    (hqp : q ≠ p) (hp : p ∈ R.canonicalCut) (hq : q ∈ R.canonicalCut)
    (hadj : ∀ f, ¬ LoopMultigraph.petersen.Joins f p q) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  obtain ⟨x₁, y₁, z₁, x₂, y₂, z₂, N, hxy₁, hxz₁, hyz₁, hxy₂, hxz₂, hyz₂,
      hdxy, hf₁, hf₂, hc₁, hc₂, hN, hcount⟩ :=
    R.canonical_cut_separating.petersen_two_expansion_patch R.canonical_cut_nontrivial
      hp hq hqp.symm hadj
  have hav {r : Fin 10} {S : Finset (Fin 10)} (hd : Disjoint S {p, q}) (hr : r ∈ S) :
      r ≠ p ∧ r ≠ q := by
    constructor
    · exact fun h ↦ Finset.disjoint_left.mp hd hr (by simp [h])
    · exact fun h ↦ Finset.disjoint_left.mp hd hr (by simp [h])
  have hs₁ : ∀ r ∈ ({x₁, y₁, z₁} : Finset (Fin 10)), (R.canonicalFiber r).card ≤ 1 :=
    fun r hr ↦ hsingle r (hav hf₁ hr).1 (hav hf₁ hr).2
  have hs₂ : ∀ r ∈ ({x₂, y₂, z₂} : Finset (Fin 10)), (R.canonicalFiber r).card ≤ 1 :=
    fun r hr ↦ hsingle r (hav hf₂ hr).1 (hav hf₂ hr).2
  have hvY : v ∈ R.canonicalFiber p := P.union_eq ▸ Finset.mem_union_left _ hv
  have hwY : w ∈ R.canonicalFiber q := Q.union_eq ▸ Finset.mem_union_left _ hw
  have hvp := (R.mem_canonicalFiber p v).mp hvY
  have hwq := (R.mem_canonicalFiber q w).mp hwY
  obtain ⟨M₁, hM₁, he₁, hC₁⟩ := R.local_expansion_matching P hbic hs₁ he hv hwq hqp
    hp hq hxy₁ hxz₁ hyz₁ hf₁ hc₁
  have hf₂' : Disjoint ({x₂, y₂, z₂} : Finset (Fin 10)) {q, p} := by
    simpa only [Finset.pair_comm q p] using hf₂
  obtain ⟨M₂, hM₂, he₂, hC₂⟩ := R.local_expansion_matching Q hbic hs₂ he.symm hw hvp hqp.symm
    hq hp hxy₂ hxz₂ hyz₂ hf₂' hc₂
  let S₁ := R.canonicalFiber p ∪ {R.canonicalRepresentative x₁, R.canonicalRepresentative y₁, w}
  let S₂ := R.canonicalFiber q ∪ {R.canonicalRepresentative x₂, R.canonicalRepresentative y₂, v}
  have hnames : Disjoint ({p, x₁, y₁} : Finset (Fin 10)) {q, x₂, y₂} := by
    apply Finset.disjoint_left.mpr
    intro r hr₁ hr₂
    have hpq := hqp.symm
    have h₁ := hav hf₁ (by simp : x₁ ∈ ({x₁, y₁, z₁} : Finset (Fin 10)))
    have h₂ := hav hf₁ (by simp : y₁ ∈ ({x₁, y₁, z₁} : Finset (Fin 10)))
    have h₃ := hav hf₂ (by simp : x₂ ∈ ({x₂, y₂, z₂} : Finset (Fin 10)))
    have h₄ := hav hf₂ (by simp : y₂ ∈ ({x₂, y₂, z₂} : Finset (Fin 10)))
    have hd := Finset.disjoint_left.mp hdxy
    clear * - hr₁ hr₂ hpq h₁ h₂ h₃ h₄ hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    rcases hr₁ with rfl | rfl | rfl <;> rcases hr₂ with h | h | h
    all_goals first | exact hpq h | exact h₁.2 h | exact h₂.2 h |
      exact h₃.1 h.symm | exact h₄.1 h.symm |
      exact hd (Or.inl rfl) (Or.inl h) | exact hd (Or.inl rfl) (Or.inr h) |
      exact hd (Or.inr rfl) (Or.inl h) | exact hd (Or.inr rfl) (Or.inr h)
  have hST : S₁ ∩ S₂ ⊆ ({v, w} : Finset V) := by
    intro u hu
    by_contra hn
    have huv : u ≠ v := fun h ↦ hn (by simp [h])
    have huw : u ≠ w := fun h ↦ hn (by simp [h])
    obtain ⟨hu₁, hu₂⟩ := Finset.mem_inter.mp hu
    have h₁ : R.canonicalVertex u ∈ ({p, x₁, y₁} : Finset (Fin 10)) := by
      simp only [S₁, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu₁
      rcases hu₁ with hu | rfl | rfl | hu
      · simp [(R.mem_canonicalFiber p u).mp hu]
      · simp
      · simp
      · exact (huw hu).elim
    have h₂ : R.canonicalVertex u ∈ ({q, x₂, y₂} : Finset (Fin 10)) := by
      simp only [S₂, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hu₂
      rcases hu₂ with hu | rfl | rfl | hu
      · simp [(R.mem_canonicalFiber q u).mp hu]
      · simp
      · simp
      · exact (huv hu).elim
    exact Finset.disjoint_left.mp hnames h₁ h₂
  have heends : ({v, w} : Finset V) = {H.endAt e 0, H.endAt e 1} := by
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [h0, h1]
    · simp only [h0, h1, Finset.pair_comm]
  have hST' : S₁ ∩ S₂ ⊆ {H.endAt e 0, H.endAt e 1} := by rwa [← heends]
  have hM := hM₁.union_of_common_edge hM₂ he₁ he₂ hST'
  have hvX : v ∈ X := (R.mem_canonicalCut v).mp (hvp.symm ▸ hp)
  have hwX : w ∈ X := (R.mem_canonicalCut w).mp (hwq.symm ▸ hq)
  have heX : e ∉ H.dangling X := by
    rw [mem_dangling]
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1, hvX, hwX]
  have hMC := hM₁.crossing_union_of_common_edge hM₂ he₁ hST' X heX
  rw [hC₁, hC₂] at hMC
  let T : Finset (Fin 10) := {p, q, x₁, y₁, x₂, y₂}
  have hT : R.canonicalPreimage T = S₁ ∪ S₂ := by
    simp only [T, canonicalPreimage_insert, ← canonicalFiber_preimage_singleton,
      R.canonicalFiber_eq_singleton (hs₁ x₁ (by simp)),
      R.canonicalFiber_eq_singleton (hs₁ y₁ (by simp)),
      R.canonicalFiber_eq_singleton (hs₂ x₂ (by simp)),
      R.canonicalFiber_eq_singleton (hs₂ y₂ (by simp))]
    ext u
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    clear * - hvY hwY
    constructor
    · tauto
    · rintro ((hu | hu | hu | rfl) | (hu | hu | hu | rfl))
      all_goals tauto
  have hM' : H.IsPerfectMatchingOn (R.canonicalPreimage T) (M₁ ∪ M₂) := hT.symm ▸ hM
  have hNs : ∀ r ∈ Finset.univ \ T, (R.canonicalFiber r).card ≤ 1 := by
    intro r hr
    have hn := (Finset.mem_sdiff.mp hr).2
    exact hsingle r (fun h ↦ hn (by simp [T, h])) (fun h ↦ hn (by simp [T, h]))
  apply R.complete_expansion_matching hM' hN hNs
  have hU : ({x₁, y₁, x₂, y₂} : Finset (Fin 10)) = {x₁, y₁} ∪ {x₂, y₂} := by
    ext r
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hd : Disjoint (({x₁, y₁} : Finset (Fin 10)) \ R.canonicalCut)
      ({x₂, y₂} \ R.canonicalCut) := hdxy.mono Finset.sdiff_subset Finset.sdiff_subset
  rw [hU, Finset.union_sdiff_distrib, Finset.card_union_of_disjoint hd] at hcount
  rw [hMC]
  omega

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
