import GraphPuzzles.Petersen.PetersenBoundaryFibers
import GraphPuzzles.Cuts.Shores.DeletedShoreMatching
import GraphPuzzles.Cuts.SeparatingCutMatchingPatch

/-! Restoring a matching-cut edge in a Petersen expansion. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- If the selected cut is a perfect matching, the two expanded endpoint
fibers are adjacent across the canonical Petersen cut. -/
theorem restored_endpoints_adjacent_of_matching_cut
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hC : H.IsPerfectMatching (H.dangling X)) (he : e ∈ H.dangling X) :
    ∃ d ∈ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut,
      GraphPuzzles.LoopMultigraph.petersen.Joins d
        (R.canonicalVertex (H.endAt e 0)) (R.canonicalVertex (H.endAt e 1)) := by
  let p := R.canonicalVertex (H.endAt e 0)
  let q := R.canonicalVertex (H.endAt e 1)
  let Y := R.canonicalFiber p
  have hY : Y ∈ R.nonsingletonFibers := (R.mem_nonsingletonFibers _).mpr
    ⟨R.reduction.vertexEquiv.symm p, R.two_le_fiber_of_matching_cut_endpoint hC he 0, rfl⟩
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hY
  have hthree := P.crossing_three_of_covers_shore (fun w _ ↦ hC w) he
  have hPM := R.canonical_cut_separating.petersen_dangling_isPerfectMatching
    R.canonical_cut_nontrivial
  have hpos : 0 < GraphPuzzles.LoopMultigraph.petersen.degreeIn
      (GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut) p := by rw [hPM p]; decide
  obtain ⟨⟨d, i⟩, hdi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hdi, hip⟩ := Finset.mem_filter.mp hdi
  have hd := (Finset.mem_product.mp hdi).1
  let r := GraphPuzzles.LoopMultigraph.petersen.endAt d (Fin.rev i)
  have hj : GraphPuzzles.LoopMultigraph.petersen.Joins d p r := by
    fin_cases i
    · exact Or.inl ⟨hip, rfl⟩
    · exact Or.inr ⟨rfl, hip⟩
  have hrp : r ≠ p := by
    intro hh
    have hc := mem_dangling.mp hd
    rw [hh] at hj
    rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp_all
  have hrq : r = q := by
    by_contra hn
    have hs := R.singleton_away_from_restored_endpoints hb hr hm hbi hrp hn
    let B := (H.dangling X ∩ H.dangling Y).erase e
    have hB : 2 ≤ B.card := by
      by_cases heB : e ∈ H.dangling X ∩ H.dangling Y
      · change 2 ≤ ((H.dangling X ∩ H.dangling Y).erase e).card
        rw [Finset.card_erase_of_mem heB, hthree]
      · change 2 ≤ ((H.dangling X ∩ H.dangling Y).erase e).card
        rw [Finset.erase_eq_of_notMem heB, hthree]
        decide
    have through {f : E} (hf : f ∈ B) :
        ∃ j, H.endAt f j = R.canonicalRepresentative r := by
      obtain ⟨hfe, hf⟩ := Finset.mem_erase.mp hf
      obtain ⟨hfC, hfY⟩ := Finset.mem_inter.mp hf
      have hex : ∃ k, H.endAt f k ∈ Y := by
        have hh := mem_dangling.mp hfY
        by_cases h0 : H.endAt f 0 ∈ Y
        · exact ⟨0, h0⟩
        · exact ⟨1, by tauto⟩
      obtain ⟨k, hk⟩ := hex
      have hfj : H.Joins f (H.endAt f k) (H.endAt f (Fin.rev k)) := by
        fin_cases k
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      have hcan := R.canonical_cut_neighbor hd hj hfe hfC hfj
        ((R.mem_canonicalFiber p _).mp hk)
      exact ⟨Fin.rev k, R.canonicalFiber_subsingleton hs hcan
        (R.canonicalVertex_representative r)⟩
    have hle : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro f hf g hg
      obtain ⟨j, hj⟩ := through hf
      obtain ⟨k, hk⟩ := through hg
      exact congrArg Prod.fst (eq_incidence_of_degreeIn_one (hC (R.canonicalRepresentative r))
        (Finset.mem_inter.mp (Finset.mem_erase.mp hf).2).1
        (Finset.mem_inter.mp (Finset.mem_erase.mp hg).2).1 hj hk)
    omega
  refine ⟨d, hd, ?_⟩
  change GraphPuzzles.LoopMultigraph.petersen.Joins d p q
  rwa [hrq] at hj

/-- The two expanded fibers are covered by the original matching cut.
A separating Petersen matching covers the remaining fibers without
crossing the selected cut, giving exactly three crossings after restoration. -/
theorem exists_three_crossing_of_matching_cut
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hC : H.IsPerfectMatching (H.dangling X)) (he : e ∈ H.dangling X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  let p := R.canonicalVertex (H.endAt e 0)
  let q := R.canonicalVertex (H.endAt e 1)
  let Y := R.canonicalFiber p
  let Z := R.canonicalFiber q
  let S := Y ∪ Z
  obtain ⟨d, hd, hdj⟩ := R.restored_endpoints_adjacent_of_matching_cut hb hr hm hbi hC he
  have hpq : p ≠ q := by
    intro hh
    apply mem_dangling.mp he
    rw [← R.mem_canonicalCut (H.endAt e 0), ← R.mem_canonicalCut (H.endAt e 1)]
    change (p ∈ R.canonicalCut ↔ q ∈ R.canonicalCut)
    rw [hh]
  have hS : R.canonicalPreimage {p, q} = S := by
    rw [R.canonicalPreimage_insert, ← R.canonicalFiber_preimage_singleton]
  have hends (k : Fin 2) : H.endAt e k ∈ S := by
    fin_cases k
    · exact Finset.mem_union_left _ ((R.mem_canonicalFiber p _).mpr rfl)
    · exact Finset.mem_union_right _ ((R.mem_canonicalFiber q _).mpr rfl)
  have hclosed : ∀ f ∈ H.dangling X, ∀ k,
      H.endAt f k ∈ S → H.endAt f (Fin.rev k) ∈ S := by
    intro f hf k hk
    by_cases hfe : f = e
    · subst f
      exact hends _
    have hfj : H.Joins f (H.endAt f k) (H.endAt f (Fin.rev k)) := by
      fin_cases k
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    rcases Finset.mem_union.mp hk with hk | hk
    · have hh := R.canonical_cut_neighbor hd hdj hfe hf hfj ((R.mem_canonicalFiber p _).mp hk)
      exact Finset.mem_union_right _ ((R.mem_canonicalFiber q _).mpr hh)
    · have hh := R.canonical_cut_neighbor hd
        (GraphPuzzles.LoopMultigraph.petersen.joins_comm.mp hdj) hfe hf hfj
        ((R.mem_canonicalFiber q _).mp hk)
      exact Finset.mem_union_left _ ((R.mem_canonicalFiber p _).mpr hh)
  let M := H.dangling X ∩ H.edgesIn S
  have hM : H.IsPerfectMatchingOn S M := hC.on_univ.restrict (Finset.subset_univ _) hclosed
  have heM : e ∈ M := Finset.mem_inter.mpr ⟨he, mem_edgesIn.mpr hends⟩
  have hY : Y ∈ R.nonsingletonFibers := (R.mem_nonsingletonFibers _).mpr
    ⟨R.reduction.vertexEquiv.symm p, R.two_le_fiber_of_matching_cut_endpoint hC he 0, rfl⟩
  obtain ⟨P⟩ := R.deleted_shore_restoration hb hr hm hbi hY
  have hthree := P.crossing_three_of_covers_shore
    (fun w hw ↦ hM.2 w (Finset.mem_union_left _ hw)) heM
  have hMY : M ∩ H.dangling Y = M := by
    apply Finset.inter_eq_left.mpr
    intro f hf
    have hmem (k : Fin 2) : R.canonicalVertex (H.endAt f k) = p ∨
        R.canonicalVertex (H.endAt f k) = q := by
      have hh := (R.mem_canonicalPreimage {p, q} _).mp (hS.symm ▸ hM.1 f hf k)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    apply mem_dangling.mpr
    intro hy
    have h0 := hmem 0
    have h1 := hmem 1
    change (H.endAt f 0 ∈ R.canonicalFiber p ↔ H.endAt f 1 ∈ R.canonicalFiber p) at hy
    simp only [R.mem_canonicalFiber] at hy
    have hh : R.canonicalVertex (H.endAt f 0) = R.canonicalVertex (H.endAt f 1) := by
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp_all
    apply mem_dangling.mp (Finset.mem_inter.mp hf).1
    rw [← R.mem_canonicalCut (H.endAt f 0), ← R.mem_canonicalCut (H.endAt f 1), hh]
  have hMC : M ∩ H.dangling X = M := Finset.inter_eq_left.mpr Finset.inter_subset_left
  have hMC3 : (M ∩ H.dangling X).card = 3 := by
    rw [hMY] at hthree
    simpa only [hMC] using hthree
  have hNex : ∃ N, GraphPuzzles.LoopMultigraph.petersen.IsPerfectMatchingOn
      (Finset.univ \ {p, q}) N ∧
      (N ∩ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut).card = 0 := by
    have hcut : ¬ (p ∈ R.canonicalCut ↔ q ∈ R.canonicalCut) := by
      simpa only [p, q, R.mem_canonicalCut] using mem_dangling.mp he
    by_cases hp : p ∈ R.canonicalCut
    · exact R.canonical_cut_separating.exists_zero_crossing_matchingOn hp
        (fun hq ↦ hcut (by simp [hp, hq])) hdj
    · have hq : q ∈ R.canonicalCut := by tauto
      simpa only [Finset.pair_comm] using
        R.canonical_cut_separating.exists_zero_crossing_matchingOn hq hp
          (GraphPuzzles.LoopMultigraph.petersen.joins_comm.mp hdj)
  obtain ⟨N, hN, hN0⟩ := hNex
  have hsingle : ∀ r ∈ Finset.univ \ {p, q}, (R.canonicalFiber r).card ≤ 1 := by
    intro r hr'
    have hh : r ≠ p ∧ r ≠ q := by simpa using hr'
    exact R.singleton_away_from_restored_endpoints hb hr hm hbi hh.1 hh.2
  have hL₀ := (R.canonicalLift_matchingOn hN hsingle).of_restrictEdges
  have hL : H.IsPerfectMatchingOn (Finset.univ \ S)
      ((R.canonicalLift N).image Subtype.val) := by
    simpa only [R.canonicalPreimage_compl, hS] using hL₀
  have hLC : ((R.canonicalLift N).image Subtype.val ∩ H.dangling X).card = 0 :=
    (restrictEdges_crossing (H := H) (Finset.univ.erase e) (R.canonicalLift N) X).trans
      ((R.canonicalLift_crossing N).trans hN0)
  have hdisj : Disjoint S (Finset.univ \ S) :=
    Finset.disjoint_left.mpr (fun _ hs ht ↦ (Finset.mem_sdiff.mp ht).2 hs)
  have hglue := hM.union hL hdisj
  have hU : S ∪ (Finset.univ \ S) = Finset.univ := by ext w; simp
  rw [hU] at hglue
  refine ⟨_, hglue.of_univ, ?_⟩
  have hdC := (hM.disjoint hL hdisj).mono
    (Finset.inter_subset_left (s₁ := M) (s₂ := H.dangling X))
    (Finset.inter_subset_left (s₁ := (R.canonicalLift N).image Subtype.val) (s₂ := H.dangling X))
  rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdC, hMC3, hLC]

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
