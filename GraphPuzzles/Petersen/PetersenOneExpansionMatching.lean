import GraphPuzzles.Petersen.PetersenFiberTransport
import GraphPuzzles.Cuts.Shores.DeletedShoreMatching
import GraphPuzzles.Matching.MatchingBoundarySaturation
import GraphPuzzles.Petersen.CaseSix.PetersenCaseSixOne

/-! Assembling the one-expanded-vertex matching in Section 6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- Glue a canonical finite patch to the local matching supplied by
Proposition 6.5. The restored exterior endpoint may lie on either side
of the selected cut; its contribution is counted in the finite certificate. -/
theorem assemble_one_expansion
    (R : (H.deleteEdge e).PetersenFiberModel X) {p q x y z : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (hbic : H.IsBicritical)
    (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small)
    (hw : R.canonicalVertex w = q) (hqp : q ≠ p) (hp : p ∈ R.canonicalCut)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfresh : Disjoint ({x, y, z} : Finset (Fin 10)) {p, q})
    (hclosed : petersenClosedNeighborhood p = {p, x, y, z})
    {N : Finset (Fin 15)}
    (hN : GraphPuzzles.LoopMultigraph.petersen.IsPerfectMatchingOn (Finset.univ \ {p, q, x, y}) N)
    (hcount : (N ∩ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut).card +
      (({x, y, q} : Finset (Fin 10)) \ R.canonicalCut).card = 3) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  let Y := R.canonicalFiber p
  let a := R.canonicalRepresentative x
  let b := R.canonicalRepresentative y
  let c := R.canonicalRepresentative z
  have havoid {r : Fin 10} (hr : r ∈ ({x, y, z} : Finset (Fin 10))) : r ≠ p ∧ r ≠ q := by
    constructor
    · intro h
      exact Finset.disjoint_left.mp hfresh hr (by simp [h])
    · intro h
      exact Finset.disjoint_left.mp hfresh hr (by simp [h])
  have hxp := (havoid (by simp : x ∈ ({x, y, z} : Finset (Fin 10)))).1
  have hyp := (havoid (by simp : y ∈ ({x, y, z} : Finset (Fin 10)))).1
  have hzp := (havoid (by simp : z ∈ ({x, y, z} : Finset (Fin 10)))).1
  have hxq := (havoid (by simp : x ∈ ({x, y, z} : Finset (Fin 10)))).2
  have hyq := (havoid (by simp : y ∈ ({x, y, z} : Finset (Fin 10)))).2
  have hab : a ≠ b := R.canonicalRepresentative_injective.ne hxy
  have hac : a ≠ c := R.canonicalRepresentative_injective.ne hxz
  have hbc : b ≠ c := R.canonicalRepresentative_injective.ne hyz
  have haY : a ∉ Y := by simpa [Y, a] using hxp
  have hbY : b ∉ Y := by simpa [Y, b] using hyp
  have hcY : c ∉ Y := by simpa [Y, c] using hzp
  have hwY : w ∉ Y := by simpa [Y, hw] using hqp
  have hwa : w ≠ a := by
    intro h
    have hh := congrArg R.canonicalVertex h
    simp only [hw, a, canonicalVertex_representative] at hh
    exact hxq hh.symm
  have hwb : w ≠ b := by
    intro h
    have hh := congrArg R.canonicalVertex h
    simp only [hw, b, canonicalVertex_representative] at hh
    exact hyq hh.symm
  have hboundary : ∀ f, f ≠ e → ∀ k, H.endAt f k ∈ Y →
      H.endAt f (Fin.rev k) ∉ Y → H.endAt f (Fin.rev k) ∈ ({a, b, c} : Finset V) := by
    intro f hfe k hi ho
    let f' : Finset.univ.erase e := ⟨f, by simp [hfe]⟩
    have hj : (H.deleteEdge e).Joins f' (H.endAt f k) (H.endAt f (Fin.rev k)) := by
      fin_cases k
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    have hh := R.canonical_neighbor_of_boundary hj hi ho
    rw [hclosed] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh
    · exact (ho ((R.mem_canonicalFiber p _).mpr hh)).elim
    · have ha := R.canonicalFiber_subsingleton (hsingle x hxp) hh (R.canonicalVertex_representative x)
      exact Finset.mem_insert.mpr (Or.inl ha)
    · have hb := R.canonicalFiber_subsingleton (hsingle y hyp) hh (R.canonicalVertex_representative y)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hb)))
    · have hc := R.canonicalFiber_subsingleton (hsingle z hzp) hh (R.canonicalVertex_representative z)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr hc))))
  obtain ⟨M, hM, _, hMY⟩ := P.exists_matchingOn_three_neighbors hbic he hv
    hwY haY hbY hcY hac hbc hwa hwb hboundary
  let Z : Finset V := {a, b, w}
  have hM' : H.IsPerfectMatchingOn (Y ∪ Z) M := hM
  have hdYZ : Disjoint Y Z := by
    apply Finset.disjoint_right.mpr
    intro u hu huY
    rcases Finset.mem_insert.mp hu with h | h
    · exact haY (h ▸ huY)
    · rcases Finset.mem_insert.mp h with h | h
      · exact hbY (h ▸ huY)
      · exact hwY ((Finset.mem_singleton.mp h) ▸ huY)
  have hZcard : Z.card = 3 := by
    simp [Z, hab, hwa.symm, hwb.symm]
  have hYX : Y ⊆ X := by
    intro u hu
    apply (R.mem_canonicalCut u).mp
    rw [(R.mem_canonicalFiber p u).mp hu]
    exact hp
  have hMcount := hM'.crossing_of_saturated_boundary hdYZ (hMY.trans hZcard.symm) hYX
  have hww : w = R.canonicalRepresentative q := R.canonicalFiber_subsingleton
    (hsingle q hqp) hw (R.canonicalVertex_representative q)
  have hZimage : Z = ({x, y, q} : Finset (Fin 10)).image R.canonicalRepresentative := by
    simp only [Z, Finset.image_insert, Finset.image_singleton, a, b, hww]
  rw [hZimage, R.card_representatives_outside] at hMcount
  let T : Finset (Fin 10) := {p, q, x, y}
  have hT : R.canonicalPreimage T = Y ∪ Z := by
    simp only [T, canonicalPreimage_insert, ← canonicalFiber_preimage_singleton,
      R.canonicalFiber_eq_singleton (hsingle q hqp),
      R.canonicalFiber_eq_singleton (hsingle x hxp),
      R.canonicalFiber_eq_singleton (hsingle y hyp)]
    ext u
    simp only [Y, Z, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, a, b, hww]
    tauto
  have hNs : ∀ r ∈ Finset.univ \ T, (R.canonicalFiber r).card ≤ 1 := by
    intro r hr
    apply hsingle r
    intro h
    have hn := (Finset.mem_sdiff.mp hr).2
    exact hn (by simp [T, h])
  have hL₀ := (R.canonicalLift_matchingOn hN hNs).of_restrictEdges
  have hL : H.IsPerfectMatchingOn (Finset.univ \ (Y ∪ Z))
      ((R.canonicalLift N).image Subtype.val) := by
    change H.IsPerfectMatchingOn (R.canonicalPreimage (Finset.univ \ T))
      ((R.canonicalLift N).image Subtype.val) at hL₀
    simpa only [R.canonicalPreimage_compl, hT] using hL₀
  have hLC : ((R.canonicalLift N).image Subtype.val ∩ H.dangling X).card =
      (N ∩ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut).card :=
    (restrictEdges_crossing (H := H) (Finset.univ.erase e) (R.canonicalLift N) X).trans
      (R.canonicalLift_crossing N)
  have hdS : Disjoint (Y ∪ Z) (Finset.univ \ (Y ∪ Z)) := by
    exact Finset.disjoint_left.mpr (fun _ hu hv ↦ (Finset.mem_sdiff.mp hv).2 hu)
  have hglue := hM'.union hL hdS
  have hU : (Y ∪ Z) ∪ (Finset.univ \ (Y ∪ Z)) = Finset.univ := by ext u; simp
  rw [hU] at hglue
  refine ⟨_, hglue.of_univ, ?_⟩
  have hdM := hM'.disjoint hL hdS
  have hdC : Disjoint (M ∩ H.dangling X)
      ((R.canonicalLift N).image Subtype.val ∩ H.dangling X) :=
    hdM.mono Finset.inter_subset_left Finset.inter_subset_left
  rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdC, hMcount, hLC]
  omega

/-- The one-expanded-vertex, nonadjacent-endpoint branch of Case 6. -/
theorem exists_three_crossing_one_expansion
    (R : (H.deleteEdge e).PetersenFiberModel X) {p q : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (hbic : H.IsBicritical)
    (hsingle : ∀ r, r ≠ p → (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small)
    (hw : R.canonicalVertex w = q) (hqp : q ≠ p)
    (hp : p ∈ R.canonicalCut) (hq : q ∈ R.canonicalCut)
    (hadj : ∀ f, ¬ GraphPuzzles.LoopMultigraph.petersen.Joins f p q) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  obtain ⟨x, y, z, N, hxy, hxz, hyz, hd, hc, hN, hn⟩ :=
    R.canonical_cut_separating.petersen_one_expansion_patch R.canonical_cut_nontrivial
      hp hq hqp.symm hadj
  apply R.assemble_one_expansion P hbic hsingle he hv hw hqp hp hxy hxz hyz hd hc hN
  have heq : ({x, y, q} : Finset (Fin 10)) \ R.canonicalCut =
      {x, y} \ R.canonicalCut := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hn⟩
      rcases ht with ht | ht | ht
      · exact ⟨Or.inl ht, hn⟩
      · exact ⟨Or.inr ht, hn⟩
      · exact (hn (ht.symm ▸ hq)).elim
    · rintro ⟨ht, hn⟩
      exact ⟨ht.imp_right Or.inl, hn⟩
  simpa only [heq] using hn

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
