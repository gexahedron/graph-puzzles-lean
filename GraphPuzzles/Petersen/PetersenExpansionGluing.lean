import GraphPuzzles.Petersen.PetersenFiberTransport
import GraphPuzzles.Cuts.Shores.DeletedShoreMatching
import GraphPuzzles.Matching.MatchingBoundarySaturation

/-! Local patches and final complement gluing for Petersen expansions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- A restoration shore and three singleton neighbors supply the local
matching of Proposition 6.5, with its contribution to the selected cut. -/
theorem local_expansion_matching
    (R : (H.deleteEdge e).PetersenFiberModel X) {p q x y z : Fin 10}
    (P : H.BipartiteRestorationShore e (R.canonicalFiber p))
    (hbic : H.IsBicritical)
    (hsingle : ∀ r ∈ ({x, y, z} : Finset (Fin 10)), (R.canonicalFiber r).card ≤ 1)
    {v w : V} (he : H.Joins e v w) (hv : v ∈ P.small)
    (hw : R.canonicalVertex w = q) (hqp : q ≠ p)
    (hp : p ∈ R.canonicalCut) (hq : q ∈ R.canonicalCut)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfresh : Disjoint ({x, y, z} : Finset (Fin 10)) {p, q})
    (hclosed : petersenClosedNeighborhood p = {p, x, y, z}) :
    ∃ M, H.IsPerfectMatchingOn
      (R.canonicalFiber p ∪ {R.canonicalRepresentative x, R.canonicalRepresentative y, w}) M ∧
      e ∈ M ∧ (M ∩ H.dangling X).card =
        (({x, y} : Finset (Fin 10)) \ R.canonicalCut).card := by
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
    · have ha := R.canonicalFiber_subsingleton (hsingle x (by simp)) hh (R.canonicalVertex_representative x)
      exact Finset.mem_insert.mpr (Or.inl ha)
    · have hb := R.canonicalFiber_subsingleton (hsingle y (by simp)) hh (R.canonicalVertex_representative y)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hb)))
    · have hc := R.canonicalFiber_subsingleton (hsingle z (by simp)) hh (R.canonicalVertex_representative z)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr hc))))
  obtain ⟨M, hM, heM, hMY⟩ := P.exists_matchingOn_three_neighbors hbic he hv
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
  have hwX : w ∈ X := (R.mem_canonicalCut w).mp (hw.symm ▸ hq)
  have hZX : Z \ X = ({x, y} : Finset (Fin 10)).image R.canonicalRepresentative \ X := by
    ext u
    simp only [Z, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.image_insert, Finset.image_singleton, a, b]
    clear * - hwX
    constructor
    · rintro ⟨hu | hu | hu, hn⟩
      · exact ⟨Or.inl hu, hn⟩
      · exact ⟨Or.inr hu, hn⟩
      · exact (hn (hu.symm ▸ hwX)).elim
    · rintro ⟨hu, hn⟩
      exact ⟨hu.imp_right Or.inl, hn⟩
  refine ⟨M, hM, heM, ?_⟩
  rw [hMcount, hZX, R.card_representatives_outside]

/-- Complete a patch on expanded vertices by lifting a perfect matching
on the complementary singleton Petersen fibers. -/
theorem complete_expansion_matching
    (R : (H.deleteEdge e).PetersenFiberModel X)
    {T : Finset (Fin 10)} {M : Finset E} {N : Finset (Fin 15)}
    (hM : H.IsPerfectMatchingOn (R.canonicalPreimage T) M)
    (hN : LoopMultigraph.petersen.IsPerfectMatchingOn (Finset.univ \ T) N)
    (hsingle : ∀ r ∈ Finset.univ \ T, (R.canonicalFiber r).card ≤ 1)
    (hcount : (M ∩ H.dangling X).card +
      (N ∩ LoopMultigraph.petersen.dangling R.canonicalCut).card = 3) :
    ∃ L, H.IsPerfectMatching L ∧ (L ∩ H.dangling X).card = 3 := by
  have hL₀ := (R.canonicalLift_matchingOn hN hsingle).of_restrictEdges
  have hL : H.IsPerfectMatchingOn (Finset.univ \ R.canonicalPreimage T)
      ((R.canonicalLift N).image Subtype.val) := by
    simpa only [R.canonicalPreimage_compl] using hL₀
  have hLC : ((R.canonicalLift N).image Subtype.val ∩ H.dangling X).card =
      (N ∩ LoopMultigraph.petersen.dangling R.canonicalCut).card :=
    (restrictEdges_crossing (H := H) (Finset.univ.erase e) (R.canonicalLift N) X).trans
      (R.canonicalLift_crossing N)
  have hdS : Disjoint (R.canonicalPreimage T) (Finset.univ \ R.canonicalPreimage T) :=
    Finset.disjoint_left.mpr (fun _ hu hv ↦ (Finset.mem_sdiff.mp hv).2 hu)
  have hglue := hM.union hL hdS
  have hU : R.canonicalPreimage T ∪ (Finset.univ \ R.canonicalPreimage T) = Finset.univ := by
    ext u
    simp
  rw [hU] at hglue
  refine ⟨_, hglue.of_univ, ?_⟩
  have hdM := hM.disjoint hL hdS
  have hdC : Disjoint (M ∩ H.dangling X)
      ((R.canonicalLift N).image Subtype.val ∩ H.dangling X) :=
    hdM.mono Finset.inter_subset_left Finset.inter_subset_left
  rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdC, hLC]
  exact hcount

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
