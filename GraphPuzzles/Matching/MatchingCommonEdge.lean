import GraphPuzzles.Matching.MatchingOn

/-! Gluing local perfect matchings that share one prescribed edge. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {S T : Finset V} {M N : Finset E} {e : E}

/-- Removing an edge from a local matching exposes exactly its two ends. -/
theorem IsPerfectMatchingOn.erase_edge (hM : H.IsPerfectMatchingOn S M) (he : e ∈ M) :
    H.IsPerfectMatchingOn (S \ {H.endAt e 0, H.endAt e 1}) (M.erase e) := by
  constructor
  · intro f hf k
    obtain ⟨hfne, hfM⟩ := Finset.mem_erase.mp hf
    apply Finset.mem_sdiff.mpr
    refine ⟨hM.1 f hfM k, ?_⟩
    intro hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact hfne (congrArg Prod.fst (eq_incidence_of_degreeIn_one
        (hM.2 _ (hM.1 e he 0)) hfM he hk rfl))
    · exact hfne (congrArg Prod.fst (eq_incidence_of_degreeIn_one
        (hM.2 _ (hM.1 e he 1)) hfM he (Finset.mem_singleton.mp hk) rfl))
  · intro v hv
    have hv0 : v ≠ H.endAt e 0 := fun h ↦ (Finset.mem_sdiff.mp hv).2
      (Finset.mem_insert.mpr (Or.inl h))
    have hv1 : v ≠ H.endAt e 1 := fun h ↦ (Finset.mem_sdiff.mp hv).2
      (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr h))
    have hz : H.degreeIn {e} v = 0 := degreeIn_singleton_eq_zero (fun k hk ↦ by
      fin_cases k
      · exact hv0 hk.symm
      · exact hv1 hk.symm)
    have hdisj : Disjoint ({e} : Finset E) (M.erase e) := by simp
    have hu : ({e} : Finset E) ∪ M.erase e = M := by
      simpa only [Finset.singleton_union] using Finset.insert_erase he
    have hh := degreeIn_union_of_disjoint (H := H) hdisj v
    rw [hu, hM.2 _ (Finset.mem_sdiff.mp hv).1, hz, zero_add] at hh
    exact hh.symm

/-- If the shores overlap only at the ends of a common matching edge,
the union is again a perfect matching on the union of the shores. -/
theorem IsPerfectMatchingOn.union_of_common_edge
    (hM : H.IsPerfectMatchingOn S M) (hN : H.IsPerfectMatchingOn T N)
    (heM : e ∈ M) (heN : e ∈ N)
    (hST : S ∩ T ⊆ {H.endAt e 0, H.endAt e 1}) :
    H.IsPerfectMatchingOn (S ∪ T) (M ∪ N) := by
  have hd : Disjoint S (T \ {H.endAt e 0, H.endAt e 1}) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 (hST (Finset.mem_inter.mpr ⟨hvS,
      (Finset.mem_sdiff.mp hvT).1⟩))
  have hglue := hM.union (hN.erase_edge heN) hd
  have hu : S ∪ (T \ {H.endAt e 0, H.endAt e 1}) = S ∪ T := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    have h0 := hM.1 e heM 0
    have h1 := hM.1 e heM 1
    constructor
    · tauto
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hv : v ∈ S
        · exact Or.inl hv
        · exact Or.inr ⟨h, fun hh ↦ hh.elim (fun he ↦ hv (he.symm ▸ h0))
            (fun he ↦ hv (he.symm ▸ h1))⟩
  have heq : M ∪ N.erase e = M ∪ N := by
    ext f
    by_cases hfe : f = e
    · subst f
      simp [heM]
    · simp [hfe]
  rwa [hu, heq] at hglue

/-- The common edge is the only possible overlap of the two edge sets. -/
theorem IsPerfectMatchingOn.inter_subset_common_edge
    (hM : H.IsPerfectMatchingOn S M) (hN : H.IsPerfectMatchingOn T N)
    (heM : e ∈ M) (hST : S ∩ T ⊆ {H.endAt e 0, H.endAt e 1}) :
    M ∩ N ⊆ {e} := by
  intro f hf
  obtain ⟨hfM, hfN⟩ := Finset.mem_inter.mp hf
  have hh := hST (Finset.mem_inter.mpr ⟨hM.1 f hfM 0, hN.1 f hfN 0⟩)
  apply Finset.mem_singleton.mpr
  rcases Finset.mem_insert.mp hh with hh | hh
  · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one
      (hM.2 _ (hM.1 e heM 0)) hfM heM hh rfl)
  · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one
      (hM.2 _ (hM.1 e heM 1)) hfM heM (Finset.mem_singleton.mp hh) rfl)

/-- Crossing counts add when the only common matching edge is internal
to the selected shore or to its complement. -/
theorem IsPerfectMatchingOn.crossing_union_of_common_edge
    (hM : H.IsPerfectMatchingOn S M) (hN : H.IsPerfectMatchingOn T N)
    (heM : e ∈ M) (hST : S ∩ T ⊆ {H.endAt e 0, H.endAt e 1})
    (X : Finset V) (heX : e ∉ H.dangling X) :
    ((M ∪ N) ∩ H.dangling X).card =
      (M ∩ H.dangling X).card + (N ∩ H.dangling X).card := by
  rw [Finset.union_inter_distrib_right]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro f hf hg
  have hfe := Finset.mem_singleton.mp (hM.inter_subset_common_edge hN heM hST
    (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hf).1, (Finset.mem_inter.mp hg).1⟩))
  exact heX (hfe ▸ (Finset.mem_inter.mp hf).2)

end GraphPuzzles.LoopMultigraph
