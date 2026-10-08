import GraphPuzzles.Matching.MatchingInduced

/-! Restriction, disjoint gluing and single-edge extension of matchings on vertex sets. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem eq_incidence_of_degreeIn_one {M : Finset E} {v : V} (hd : H.degreeIn M v = 1)
    {e f : E} {i j : Fin 2} (he : e ∈ M) (hf : f ∈ M)
    (hi : H.endAt e i = v) (hj : H.endAt f j = v) : (e, i) = (f, j) := by
  apply Finset.card_le_one_iff.mp hd.le
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, hi⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf, Finset.mem_univ _⟩, hj⟩

omit [DecidableEq E] in
theorem IsPerfectMatchingOn.degree_zero {S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn S M) {v : V} (hv : v ∉ S) : H.degreeIn M v = 0 :=
  degreeIn_eq_zero_of fun e he k hk ↦ hv (hk ▸ hM.1 e he k)

omit [DecidableEq E] in
theorem IsPerfectMatchingOn.disjoint {S T : Finset V} {M N : Finset E}
    (hM : H.IsPerfectMatchingOn S M) (hN : H.IsPerfectMatchingOn T N) (hST : Disjoint S T) :
    Disjoint M N := by
  apply Finset.disjoint_left.mpr
  intro e heM heN
  exact Finset.disjoint_left.mp hST (hM.1 e heM 0) (hN.1 e heN 0)

/-- Matchings on disjoint vertex sets glue by taking their union. -/
theorem IsPerfectMatchingOn.union {S T : Finset V} {M N : Finset E}
    (hM : H.IsPerfectMatchingOn S M) (hN : H.IsPerfectMatchingOn T N) (hST : Disjoint S T) :
    H.IsPerfectMatchingOn (S ∪ T) (M ∪ N) := by
  constructor
  · intro e he k
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (hM.1 e he k)
    · exact Finset.mem_union_right _ (hN.1 e he k)
  · intro v hv
    rw [degreeIn_union_of_disjoint (hM.disjoint hN hST)]
    rcases Finset.mem_union.mp hv with hv | hv
    · rw [hM.2 v hv, hN.degree_zero (Finset.disjoint_left.mp hST hv), add_zero]
    · rw [hN.2 v hv, hM.degree_zero (Finset.disjoint_right.mp hST hv), zero_add]

/-- Disjoint families of vertex sets allow all their matchings to be glued at once. -/
theorem IsPerfectMatchingOn.biUnion {I : Type*} [DecidableEq I] (s : Finset I)
    (S : I → Finset V) (M : I → Finset E)
    (hm : ∀ i ∈ s, H.IsPerfectMatchingOn (S i) (M i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    H.IsPerfectMatchingOn (s.biUnion S) (s.biUnion M) := by
  induction s using Finset.induction_on with
  | empty => simp [IsPerfectMatchingOn, degreeIn]
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.biUnion_insert]
    apply (hm i (Finset.mem_insert_self _ _)).union
    · apply ih
      · exact fun j hj ↦ hm j (Finset.mem_insert_of_mem hj)
      · exact fun j hj k hk hne ↦ hd j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hne
    · apply Finset.disjoint_left.mpr
      intro v hv hvU
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvU
      exact Finset.disjoint_left.mp (hd i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun he ↦ hi (he.symm ▸ hj))) hv hvj

/-- Restrict a matching to any vertex set closed under its edges. -/
theorem IsPerfectMatchingOn.restrict {S T : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn T M) (hST : S ⊆ T)
    (hc : ∀ e ∈ M, ∀ k, H.endAt e k ∈ S → H.endAt e (Fin.rev k) ∈ S) :
    H.IsPerfectMatchingOn S (M ∩ H.edgesIn S) := by
  constructor
  · intro e he k
    exact (mem_edgesIn.mp (Finset.mem_inter.mp he).2) k
  · intro v hv
    have hdeg : H.degreeIn (M ∩ H.edgesIn S) v = H.degreeIn M v := by
      unfold degreeIn
      congr 1
      ext ⟨e, k⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_inter]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · rintro ⟨he, hk⟩
        have hkS : H.endAt e k ∈ S := hk ▸ hv
        have hrS := hc e he k hkS
        refine ⟨⟨he, mem_edgesIn.mpr ?_⟩, hk⟩
        intro j
        fin_cases k <;> fin_cases j <;> assumption
    exact hdeg.trans (hM.2 v (hST hv))

omit [DecidableEq E] in
theorem IsPerfectMatching.on_univ {M : Finset E} (hM : H.IsPerfectMatching M) :
    H.IsPerfectMatchingOn Finset.univ M := ⟨fun _ _ _ ↦ Finset.mem_univ _, fun v _ ↦ hM v⟩

omit [DecidableEq E] in
theorem IsPerfectMatchingOn.of_univ {M : Finset E}
    (hM : H.IsPerfectMatchingOn Finset.univ M) : H.IsPerfectMatching M :=
  fun v ↦ hM.2 v (Finset.mem_univ _)

/-- Removing a matching edge leaves a perfect matching on the other vertices. -/
theorem IsPerfectMatching.erase_edge {M : Finset E} (hM : H.IsPerfectMatching M)
    {e : E} (he : e ∈ M) :
    H.IsPerfectMatchingOn (Finset.univ \ {H.endAt e 0, H.endAt e 1}) (M.erase e) := by
  constructor
  · intro f hf k
    obtain ⟨hfne, hfM⟩ := Finset.mem_erase.mp hf
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact hfne (congrArg Prod.fst (eq_incidence_of_degreeIn_one (hM _) hfM he hk rfl))
    · have hk' := Finset.mem_singleton.mp hk
      exact hfne (congrArg Prod.fst (eq_incidence_of_degreeIn_one (hM _) hfM he hk' rfl))
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
    rw [hu, hM, hz, zero_add] at hh
    exact hh.symm

omit [DecidableEq E] in
/-- The singleton edge is a perfect matching on its two distinct ends. -/
theorem Joins.isPerfectMatchingOn {e : E} {a b : V} (he : H.Joins e a b) (hab : a ≠ b) :
    H.IsPerfectMatchingOn {a, b} {e} := by
  constructor
  · intro f hf k
    have hfe := Finset.mem_singleton.mp hf
    rw [hfe]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he.endAt_mem k
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact degreeIn_singleton_of_joins he hab
    · rw [Finset.mem_singleton.mp hv]
      exact degreeIn_singleton_of_joins (H.joins_comm.mp he) hab.symm

/-- Extend a factor-critical component matching through a chosen edge to an exterior vertex. -/
theorem IsPerfectMatchingOn.insert_boundary {Q : Finset V} {M : Finset E} {a b : V}
    (hM : H.IsPerfectMatchingOn (Q.erase a) M) (ha : a ∈ Q) (hb : b ∉ Q)
    {e : E} (he : H.Joins e a b) : H.IsPerfectMatchingOn (insert b Q) (insert e M) := by
  have hab : a ≠ b := fun h ↦ hb (h ▸ ha)
  have hd : Disjoint ({a, b} : Finset V) (Q.erase a) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (Finset.mem_erase.mp hvQ).1 rfl
    · exact hb ((Finset.mem_singleton.mp hv) ▸ (Finset.mem_erase.mp hvQ).2)
  have hh := (he.isPerfectMatchingOn hab).union hM hd
  have hS : ({a, b} : Finset V) ∪ Q.erase a = insert b Q := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ((rfl | rfl) | ⟨_, hv⟩)
      · exact Or.inr ha
      · exact Or.inl rfl
      · exact Or.inr hv
    · rintro (rfl | hv)
      · exact Or.inl (Or.inr rfl)
      · by_cases hva : v = a
        · exact Or.inl (Or.inl hva)
        · exact Or.inr ⟨hva, hv⟩
  simpa only [hS, Finset.singleton_union] using hh

end GraphPuzzles.LoopMultigraph
