import GraphPuzzles.Petersen.PetersenExpansionGluing
import GraphPuzzles.Petersen.PetersenFiberNeighbors
import GraphPuzzles.Cuts.Shores.AdjacentShorePatch
import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixAdjacent

/-! The adjacent two-expanded-vertices branch of Section 6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- Adjacent expansion fibers have the four-boundary-edge local patch;
the remaining Petersen matching contributes the third selected crossing. -/
theorem exists_three_crossing_adjacent_expansions
    (R : (H.deleteEdge e).PetersenFiberModel X) {p q : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (Q : H.BipartiteRestorationShore e (R.canonicalFiber q))
    (hbic : H.IsBicritical) (hconn : H.ConnectedAfterDeletingPairs)
    (hpcard : 2 ≤ (R.canonicalFiber p).card)
    (hsingle : ∀ r, r ≠ p → r ≠ q → (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small) (hw : w ∈ Q.small)
    (hqp : q ≠ p) (hp : p ∈ R.canonicalCut) (hq : q ∈ R.canonicalCut)
    (hadj : ∃ f, LoopMultigraph.petersen.Joins f p q) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  obtain ⟨x₁, y₁, x₂, y₂, N, hxy₁, hxy₂, hdxy, hfresh, hc₁, hc₂, hN, hcount, hNC⟩ :=
    R.canonical_cut_separating.petersen_adjacent_expansion_patch R.canonical_cut_nontrivial
      hp hq hqp.symm hadj
  let A : Finset (Fin 10) := {x₁, y₁, x₂, y₂}
  let Y := R.canonicalFiber p
  let Z := R.canonicalFiber q
  let a := R.canonicalRepresentative x₁
  let b := R.canonicalRepresentative y₁
  let x := R.canonicalRepresentative x₂
  let y := R.canonicalRepresentative y₂
  have hav {r : Fin 10} (hr : r ∈ A) : r ≠ p ∧ r ≠ q := by
    constructor
    · exact fun h ↦ Finset.disjoint_left.mp hfresh hr (by simp [h])
    · exact fun h ↦ Finset.disjoint_left.mp hfresh hr (by simp [h])
  have hsingleA : ∀ r ∈ A, (R.canonicalFiber r).card ≤ 1 :=
    fun r hr ↦ hsingle r (hav hr).1 (hav hr).2
  have hrepro {r : Fin 10} (hr : r ∈ A) : R.canonicalRepresentative r ∉ Y ∪ Z := by
    have hh := hav hr
    simpa only [Y, Z, Finset.mem_union, mem_canonicalFiber, canonicalVertex_representative,
      not_or] using hh
  have ha : a ∉ Y ∪ Z := hrepro (by simp [A])
  have hb : b ∉ Y ∪ Z := hrepro (by simp [A])
  have hx : x ∉ Y ∪ Z := hrepro (by simp [A])
  have hy : y ∉ Y ∪ Z := hrepro (by simp [A])
  have hYZ : Disjoint Y Z := R.canonicalFiber_disjoint hqp.symm
  have hout : (Finset.univ \ (Y ∪ Z)).Nonempty := ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hvY : v ∈ Y := by
    change v ∈ R.canonicalFiber p
    exact P.union_eq ▸ Finset.mem_union_left _ hv
  have hwZ : w ∈ Z := by
    change w ∈ R.canonicalFiber q
    exact Q.union_eq ▸ Finset.mem_union_left _ hw
  have heYZ : ∀ k, H.endAt e k ∈ Y ∪ Z := by
    intro k
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases k
    · exact h0.symm ▸ Finset.mem_union_left Z hvY
    · exact h1.symm ▸ Finset.mem_union_right Y hwZ
    · exact h0.symm ▸ Finset.mem_union_right Y hwZ
    · exact h1.symm ▸ Finset.mem_union_left Z hvY
  have neighbor {r s : Fin 10} (hr : r ∈ A)
      (hmem : r ∈ petersenClosedNeighborhood s) (hne : r ≠ s) :
      ∃ u ∈ R.canonicalFiber s, ∃ f, H.Joins f u (R.canonicalRepresentative r) := by
    obtain hh | hh := (petersen_mem_closedNeighborhood s r).mp hmem
    · exact (hne hh).elim
    obtain ⟨u, hu, f, hf⟩ := R.canonical_exists_join_representative hh (hsingleA r hr)
    exact ⟨u, hu, f.1, hf⟩
  have na : ∃ u ∈ Y, ∃ f, H.Joins f u a :=
    neighbor (by simp [A]) (by rw [hc₁]; simp) (hav (by simp [A] : x₁ ∈ A)).1
  have nb : ∃ u ∈ Y, ∃ f, H.Joins f u b :=
    neighbor (by simp [A]) (by rw [hc₁]; simp) (hav (by simp [A] : y₁ ∈ A)).1
  have nx : ∃ u ∈ Z, ∃ f, H.Joins f u x :=
    neighbor (by simp [A]) (by rw [hc₂]; simp) (hav (by simp [A] : x₂ ∈ A)).2
  have ny : ∃ u ∈ Z, ∃ f, H.Joins f u y :=
    neighbor (by simp [A]) (by rw [hc₂]; simp) (hav (by simp [A] : y₂ ∈ A)).2
  have boundary {s r t : Fin 10} (hs : s = p ∨ s = q)
      (hclosed : petersenClosedNeighborhood s ⊆ ({p, q, r, t} : Finset (Fin 10)))
      (hr : r ∈ A) (ht : t ∈ A) : ∀ f k, H.endAt f k ∈ R.canonicalFiber s →
      H.endAt f (Fin.rev k) ∉ Y ∪ Z →
      H.endAt f (Fin.rev k) ∈ ({R.canonicalRepresentative r, R.canonicalRepresentative t} : Finset V) := by
    intro f k hi ho
    have hfe : f ≠ e := fun h ↦ ho (h.symm ▸ heYZ (Fin.rev k))
    let f' : Finset.univ.erase e := ⟨f, by simp [hfe]⟩
    have hj : (H.deleteEdge e).Joins f' (H.endAt f k) (H.endAt f (Fin.rev k)) := by
      fin_cases k
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    have hos : H.endAt f (Fin.rev k) ∉ R.canonicalFiber s := by
      intro hh
      rcases hs with rfl | rfl
      · exact ho (Finset.mem_union_left _ hh)
      · exact ho (Finset.mem_union_right _ hh)
    have hn := hclosed (R.canonical_neighbor_of_boundary hj hi hos)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn | hn | hn
    · exact (ho (Finset.mem_union_left _ ((R.mem_canonicalFiber p _).mpr hn))).elim
    · exact (ho (Finset.mem_union_right _ ((R.mem_canonicalFiber q _).mpr hn))).elim
    · exact Finset.mem_insert.mpr (Or.inl (R.canonicalFiber_subsingleton
        (hsingleA r hr) hn (R.canonicalVertex_representative r)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (R.canonicalFiber_subsingleton (hsingleA t ht) hn (R.canonicalVertex_representative t))))
  have hdabxy : Disjoint ({a, b} : Finset V) {x, y} := by
    simpa only [Finset.image_insert, Finset.image_singleton] using
      (Finset.disjoint_image R.canonicalRepresentative_injective).mpr hdxy
  obtain ⟨M, hM, _, hMYZ⟩ := P.exists_adjacent_patch Q hbic hconn hYZ hpcard hout he hv hw
    ha hb hx hy (R.canonicalRepresentative_injective.ne hxy₁)
    (R.canonicalRepresentative_injective.ne hxy₂) hdabxy na nb nx ny
    (boundary (Or.inl rfl) (by rw [hc₁]) (by simp [A]) (by simp [A]))
    (boundary (Or.inr rfl) (by rw [hc₂]) (by simp [A]) (by simp [A]))
  let W := A.image R.canonicalRepresentative
  have hW : W = ({a, b, x, y} : Finset V) := by
    simp only [W, A, Finset.image_insert, Finset.image_singleton, a, b, x, y]
  have hM' : H.IsPerfectMatchingOn ((Y ∪ Z) ∪ W) M := by simpa only [hW] using hM
  have hdW : Disjoint (Y ∪ Z) W := by
    apply Finset.disjoint_right.mpr
    intro u hu huYZ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    exact hrepro hr huYZ
  have hAu : A = ({x₁, y₁} : Finset (Fin 10)) ∪ {x₂, y₂} := by
    ext r
    simp only [A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hWcard : W.card = 4 := by
    rw [Finset.card_image_of_injective _ R.canonicalRepresentative_injective,
      hAu, Finset.card_union_of_disjoint hdxy]
    simp [hxy₁, hxy₂]
  have hsubset : Y ∪ Z ⊆ X := by
    intro u hu
    apply (R.mem_canonicalCut u).mp
    rcases Finset.mem_union.mp hu with hu | hu
    · rw [(R.mem_canonicalFiber p u).mp hu]; exact hp
    · rw [(R.mem_canonicalFiber q u).mp hu]; exact hq
  have hMC := hM'.crossing_of_saturated_boundary hdW (hMYZ.trans hWcard.symm) hsubset
  rw [R.card_representatives_outside] at hMC
  have hMC' : (M ∩ H.dangling X).card = 2 := hMC.trans hcount
  let T := insert p (insert q A)
  have hT : R.canonicalPreimage T = (Y ∪ Z) ∪ W := by
    rw [canonicalPreimage_insert, canonicalPreimage_insert, R.canonicalPreimage_eq_image hsingleA]
    exact (Finset.union_assoc _ _ _).symm
  have hPM : H.IsPerfectMatchingOn (R.canonicalPreimage T) M := hT.symm ▸ hM'
  have hNs : ∀ r ∈ Finset.univ \ T, (R.canonicalFiber r).card ≤ 1 := by
    intro r hr
    have hn := (Finset.mem_sdiff.mp hr).2
    exact hsingle r (fun h ↦ hn (by simp [T, h])) (fun h ↦ hn (by simp [T, h]))
  exact R.complete_expansion_matching hPM hN hNs (by rw [hMC', hNC])

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
