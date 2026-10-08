import GraphPuzzles.Cuts.Shores.DeletedShoreMatching

/-! The adjacent-shore matching extension in Proposition 6.6. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {Y Z : Finset V}

open scoped BigOperators

/-- A matching edge between disjoint shores is counted at both boundaries;
all other union-boundary edges are counted once. -/
theorem crossing_union_card_of_disjoint (hYZ : Disjoint Y Z) (M : Finset E) :
    (M ∩ H.dangling Y).card + (M ∩ H.dangling Z).card =
      (M ∩ H.dangling (Y ∪ Z)).card + 2 * (M ∩ H.dangling Y ∩ H.dangling Z).card := by
  have hedge (r : E) :
      (if r ∈ H.dangling Y then (1 : ℕ) else 0) + (if r ∈ H.dangling Z then 1 else 0) =
      (if r ∈ H.dangling (Y ∪ Z) then 1 else 0) +
        2 * (if r ∈ H.dangling Y ∧ r ∈ H.dangling Z then 1 else 0) := by
    have hd0 : H.endAt r 0 ∈ Y → H.endAt r 0 ∉ Z := fun hh ↦ Finset.disjoint_left.mp hYZ hh
    have hd1 : H.endAt r 1 ∈ Y → H.endAt r 1 ∉ Z := fun hh ↦ Finset.disjoint_left.mp hYZ hh
    by_cases hY0 : H.endAt r 0 ∈ Y <;> by_cases hY1 : H.endAt r 1 ∈ Y <;>
      by_cases hZ0 : H.endAt r 0 ∈ Z <;> by_cases hZ1 : H.endAt r 1 ∈ Z <;>
      simp_all [mem_dangling, Finset.mem_union]
  have hfilter : (M.filter fun r ↦ r ∈ H.dangling Y ∧ r ∈ H.dangling Z) =
      M ∩ H.dangling Y ∩ H.dangling Z := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact and_assoc.symm
  have hh := Finset.sum_congr (s₁ := M) rfl (fun r _ ↦ hedge r)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    hfilter, Finset.filter_mem_eq_inter, Nat.cast_id] using hh

theorem crossing_union_eq_four_of_three {M : Finset E} (hYZ : Disjoint Y Z)
    (hY : (M ∩ H.dangling Y).card = 3) (hZ : (M ∩ H.dangling Z).card = 3)
    (he : e ∈ M) (heY : e ∈ H.dangling Y) (heZ : e ∈ H.dangling Z)
    (hcommon : ∀ r ∈ M, r ∈ H.dangling Y → r ∈ H.dangling Z → r = e) :
    (M ∩ H.dangling (Y ∪ Z)).card = 4 := by
  have hinter : M ∩ H.dangling Y ∩ H.dangling Z = {e} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨he, heY⟩, heZ⟩, ?_⟩
    intro r hr
    obtain ⟨hrMY, hrZ⟩ := Finset.mem_inter.mp hr
    obtain ⟨hrM, hrY⟩ := Finset.mem_inter.mp hrMY
    exact hcommon r hrM hrY hrZ
  have hh := crossing_union_card_of_disjoint (H := H) hYZ M
  rw [hY, hZ, hinter, Finset.card_singleton] at hh
  omega

namespace BipartiteRestorationShore

/-- Two adjacent restored shores can be covered together with their four
old exterior neighbours. The two prescribed edges at the first shore expose
two large-side vertices for a bicritical matching. -/
theorem exists_matchingOn_adjacent_shores
    (P : H.BipartiteRestorationShore e Y) (Q : H.BipartiteRestorationShore e Z)
    (hbic : H.IsBicritical) (hYZ : Disjoint Y Z)
    {v w a b x y s t : V} {f g : E}
    (he : H.Joins e v w) (hv : v ∈ P.small) (hw : w ∈ Q.small)
    (hs : s ∈ P.large) (ht : t ∈ P.large) (hst : s ≠ t)
    (hf : H.Joins f s a) (hg : H.Joins g t b)
    (ha : a ∉ Y ∪ Z) (hb : b ∉ Y ∪ Z)
    (hx : x ∉ Y ∪ Z) (hy : y ∉ Y ∪ Z)
    (hab : a ≠ b) (haxy : Disjoint ({a, b} : Finset V) {x, y})
    (hboundary : ∀ r, r ≠ e → ∀ k, H.endAt r k ∈ Z →
      H.endAt r (Fin.rev k) ∉ Z → H.endAt r (Fin.rev k) ∉ Y →
      H.endAt r (Fin.rev k) ∈ ({x, y} : Finset V)) :
    ∃ M, H.IsPerfectMatchingOn (Y ∪ Z ∪ {x, y, a, b}) M ∧ e ∈ M ∧
      (M ∩ H.dangling Y).card = 3 ∧ (M ∩ H.dangling Z).card = 3 ∧
      ∀ r ∈ M, r ∈ H.dangling Y → r ∈ H.dangling Z → r = e := by
  have hsmall (A : Finset V) (R : H.BipartiteRestorationShore e A) : R.small ⊆ A := by
    intro z hz
    exact R.union_eq ▸ Finset.mem_union_left _ hz
  have hlarge (A : Finset V) (R : H.BipartiteRestorationShore e A) : R.large ⊆ A := by
    intro z hz
    exact R.union_eq ▸ Finset.mem_union_right _ hz
  have hvY := hsmall Y P hv
  have hwZ := hsmall Z Q hw
  have hsY := hlarge Y P hs
  have htY := hlarge Y P ht
  have hYnotZ {z : V} (hz : z ∈ Y) : z ∉ Z := Finset.disjoint_left.mp hYZ hz
  have hZnotY {z : V} (hz : z ∈ Z) : z ∉ Y := Finset.disjoint_right.mp hYZ hz
  have joined_cut {r : E} {u z : V} {A : Finset V}
      (hr : H.Joins r u z) (hu : u ∈ A) (hz : z ∉ A) : r ∈ H.dangling A := by
    rcases hr with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [mem_dangling, h0, h1, hu, hz]
  have crossing {r : E} {A : Finset V} {k : Fin 2}
      (hi : H.endAt r k ∈ A) (ho : H.endAt r (Fin.rev k) ∉ A) : r ∈ H.dangling A := by
    clear * - hi ho
    fin_cases k <;> simp_all [mem_dangling]
  have heY : e ∈ H.dangling Y := joined_cut he hvY (hZnotY hwZ)
  have heZ : e ∈ H.dangling Z := joined_cut he.symm hwZ (hYnotZ hvY)
  obtain ⟨N, hN₀⟩ := hbic s t hst
  have hN : H.IsPerfectMatchingOn (Finset.univ \ {s, t}) N := by
    convert hN₀ using 1
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, and_true, not_or]
    exact and_comm
  obtain ⟨heN, hNY⟩ := P.crossing_one_of_delete_two_large hs ht hst hN
  have only_e {r : E} (hr : r ∈ N) (hrY : r ∈ H.dangling Y) : r = e := by
    have hh := Finset.card_le_one.mp hNY.le
    exact hh r (Finset.mem_inter.mpr ⟨hr, hrY⟩) e (Finset.mem_inter.mpr ⟨heN, heY⟩)
  have ends_avoid {r : E} (hr : r ∈ N) (k : Fin 2) :
      H.endAt r k ≠ s ∧ H.endAt r k ≠ t := by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hN.1 r hr k
  have hcoverZ : ∀ z ∈ Z, H.degreeIn N z = 1 := by
    intro z hz
    exact hN.2 z (by simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]; exact
        ⟨ne_of_mem_of_not_mem hz (hYnotZ hsY), ne_of_mem_of_not_mem hz (hYnotZ htY)⟩)
  have hNZ := Q.crossing_three_of_covers_shore hcoverZ heN
  let T := (N ∩ H.dangling Z).erase e
  have hTcard : T.card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨heN, heZ⟩), hNZ]
  have hxyout {q : V} (hq : q ∉ Y ∪ Z) : q ≠ s ∧ q ≠ t :=
    ⟨fun h ↦ hq (h.symm ▸ Finset.mem_union_left _ hsY),
      fun h ↦ hq (h.symm ▸ Finset.mem_union_left _ htY)⟩
  have hdegx : H.degreeIn N x = 1 := hN.2 x (by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hxyout hx)
  have hdegy : H.degreeIn N y = 1 := hN.2 y (by
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hxyout hy)
  have outside_xy {r : E} (hr : r ∈ N) (hre : r ≠ e) {k : Fin 2}
      (hi : H.endAt r k ∈ Z) (ho : H.endAt r (Fin.rev k) ∉ Z) :
      H.endAt r (Fin.rev k) ∈ ({x, y} : Finset V) := by
    apply hboundary r hre k hi ho
    intro hY
    apply hre
    apply only_e hr
    exact crossing hY (by
      simpa only [Fin.rev_rev] using hZnotY hi)
  have cut_ends {r : E} (hr : r ∈ T) :
      ∃ k, (H.endAt r k = x ∨ H.endAt r k = y) ∧ H.endAt r (Fin.rev k) ∈ Z := by
    have hrev0 : Fin.rev (0 : Fin 2) = 1 := by decide
    have hrev1 : Fin.rev (1 : Fin 2) = 0 := by decide
    obtain ⟨hre, hrNZ⟩ := Finset.mem_erase.mp hr
    obtain ⟨hrN, hrZ⟩ := Finset.mem_inter.mp hrNZ
    have hd := mem_dangling.mp hrZ
    by_cases h0 : H.endAt r 0 ∈ Z
    · have h1 : H.endAt r 1 ∉ Z := fun h ↦ hd ⟨fun _ ↦ h, fun _ ↦ h0⟩
      exact ⟨1, (by simpa only [Finset.mem_insert, Finset.mem_singleton, hrev0, hrev1] using
        (outside_xy hrN hre h0 h1)), h0⟩
    · have h1 : H.endAt r 1 ∈ Z := by
        clear * - hd h0
        tauto
      exact ⟨0, (by simpa only [Finset.mem_insert, Finset.mem_singleton, hrev0, hrev1] using
        (outside_xy hrN hre h1 h0)), h1⟩
  have through {q r : V} (hdeg : H.degreeIn N r = 1)
      (hcover : ∀ f ∈ T, ∃ k, H.endAt f k = q ∨ H.endAt f k = r) :
      ∃ f ∈ T, ∃ k, H.endAt f k = q := by
    by_contra hn
    push Not at hn
    have hr (f : E) (hf : f ∈ T) : ∃ k, H.endAt f k = r := by
      obtain ⟨k, hk⟩ := hcover f hf
      exact ⟨k, hk.resolve_left (hn f hf k)⟩
    have hc : T.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro f hf g hg
      obtain ⟨i, hi⟩ := hr f hf
      obtain ⟨j, hj⟩ := hr g hg
      exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hdeg
        (Finset.mem_inter.mp (Finset.mem_of_mem_erase hf)).1
        (Finset.mem_inter.mp (Finset.mem_of_mem_erase hg)).1 hi hj)
    omega
  have hthroughx := through hdegy (fun r hr ↦ by
    obtain ⟨k, hk, _⟩ := cut_ends hr
    exact ⟨k, hk⟩)
  have hthroughy := through hdegx (fun r hr ↦ by
    obtain ⟨k, hk, _⟩ := cut_ends hr
    exact ⟨k, hk.symm⟩)
  have partner_inside {q : V} (hq : q ∉ Y ∪ Z) (hdeg : H.degreeIn N q = 1)
      (hthrough : ∃ f ∈ T, ∃ k, H.endAt f k = q)
      {r : E} (hr : r ∈ N) {j : Fin 2} (hj : H.endAt r j = q) :
      H.endAt r (Fin.rev j) ∈ Z := by
    obtain ⟨f, hf, k, hk⟩ := hthrough
    have hfN := (Finset.mem_inter.mp (Finset.mem_of_mem_erase hf)).1
    have hfk : H.endAt f (Fin.rev k) ∈ Z := by
      have hd := mem_dangling.mp (Finset.mem_inter.mp (Finset.mem_of_mem_erase hf)).2
      have hkn : H.endAt f k ∉ Z := fun h ↦ hq (Finset.mem_union_right _ (hk ▸ h))
      fin_cases k
      · exact of_not_not (fun h ↦ hd ⟨fun hh ↦ (hkn hh).elim, fun hh ↦ (h hh).elim⟩)
      · exact of_not_not (fun h ↦ hd ⟨fun hh ↦ (h hh).elim, fun hh ↦ (hkn hh).elim⟩)
    have hh := eq_incidence_of_degreeIn_one hdeg hr hfN hj hk
    exact (congrArg (fun p : E × Fin 2 ↦ H.endAt p.1 (Fin.rev p.2)) hh).symm ▸ hfk
  let S := ((Y ∪ Z) \ {s, t}) ∪ ({x, y} : Finset V)
  have hST : S ⊆ Finset.univ \ {s, t} := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hq).2⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] using hxyout hx
      · rw [Finset.mem_singleton.mp hq]
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] using hxyout hy
  have he_inside (k : Fin 2) : H.endAt e k ∈ Y ∪ Z := by
    rcases he.endAt_mem k with hh | hh
    · exact hh.symm ▸ Finset.mem_union_left _ hvY
    · exact hh.symm ▸ Finset.mem_union_right _ hwZ
  have hclosed : ∀ r ∈ N, ∀ k, H.endAt r k ∈ S → H.endAt r (Fin.rev k) ∈ S := by
    intro r hr k hk
    have hav := ends_avoid hr (Fin.rev k)
    have add_inner (hi : H.endAt r (Fin.rev k) ∈ Y ∪ Z) : H.endAt r (Fin.rev k) ∈ S :=
      Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hav⟩)
    rcases Finset.mem_union.mp hk with hk | hk
    · have hin := (Finset.mem_sdiff.mp hk).1
      by_cases ho : H.endAt r (Fin.rev k) ∈ Y ∪ Z
      · exact add_inner ho
      · apply Finset.mem_union_right
        have hre : r ≠ e := fun h ↦ ho (h.symm ▸ he_inside (Fin.rev k))
        rcases Finset.mem_union.mp hin with hY | hZ
        · exact (hre (only_e hr (crossing hY
            (fun h ↦ ho (Finset.mem_union_left _ h))))).elim
        · exact outside_xy hr hre hZ (fun h ↦ ho (Finset.mem_union_right _ h))
    · rcases Finset.mem_insert.mp hk with hk | hk
      · exact add_inner (Finset.mem_union_right _ (partner_inside hx hdegx hthroughx hr hk))
      · exact add_inner (Finset.mem_union_right _
          (partner_inside hy hdegy hthroughy hr (Finset.mem_singleton.mp hk)))
  have hNS := hN.restrict hST hclosed
  have hsa : s ≠ a := ne_of_mem_of_not_mem (Finset.mem_union_left _ hsY) ha
  have htb : t ≠ b := ne_of_mem_of_not_mem (Finset.mem_union_left _ htY) hb
  have hpair : Disjoint ({s, a} : Finset V) {t, b} := by
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨hst, ne_of_mem_of_not_mem (Finset.mem_union_left _ hsY) hb⟩,
      ⟨(ne_of_mem_of_not_mem (Finset.mem_union_left _ htY) ha).symm, hab⟩⟩
  have hfg := (hf.isPerfectMatchingOn hsa).union (hg.isPerfectMatchingOn htb) hpair
  have hdisj : Disjoint S (({s, a} : Finset V) ∪ {t, b}) := by
    apply Finset.disjoint_left.mpr
    intro q hq hp
    have hp' : q = s ∨ q = t ∨ q ∈ ({a, b} : Finset V) := by
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
      clear * - hp
      tauto
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨hi, ho⟩ := Finset.mem_sdiff.mp hq
      rcases hp' with h | h | h
      · exact ho (Finset.mem_insert.mpr (Or.inl h))
      · exact ho (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
      · rcases Finset.mem_insert.mp h with h | h
        · exact ha (h ▸ hi)
        · exact hb ((Finset.mem_singleton.mp h) ▸ hi)
    · rcases hp' with hqs | hqt | h
      · have hqY : q ∈ Y ∪ Z := hqs.symm ▸ Finset.mem_union_left _ hsY
        rcases Finset.mem_insert.mp hq with hq | hq
        · exact hx (hq ▸ hqY)
        · exact hy ((Finset.mem_singleton.mp hq) ▸ hqY)
      · have hqY : q ∈ Y ∪ Z := hqt.symm ▸ Finset.mem_union_left _ htY
        rcases Finset.mem_insert.mp hq with hq | hq
        · exact hx (hq ▸ hqY)
        · exact hy ((Finset.mem_singleton.mp hq) ▸ hqY)
      · exact Finset.disjoint_left.mp haxy h hq
  have hglue := hNS.union hfg hdisj
  have hU : S ∪ ({s, a} ∪ {t, b}) = Y ∪ Z ∪ {x, y, a, b} := by
    ext q
    by_cases hqs : q = s
    · subst q
      simp [S, hsY]
    by_cases hqt : q = t
    · subst q
      simp [S, htY]
    simp only [S, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, hqs, hqt, false_or, or_false, not_false_eq_true, and_true]
    clear * - hqs hqt
    tauto
  rw [hU] at hglue
  have heS : e ∈ H.edgesIn S := by
    apply mem_edgesIn.mpr
    intro k
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he_inside k, by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ends_avoid heN k⟩)
  have heM : e ∈ (N ∩ H.edgesIn S) ∪ ({f} ∪ {g}) :=
    Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨heN, heS⟩)
  refine ⟨_, hglue, heM, P.crossing_three_of_covers_shore (fun q hq ↦
    hglue.2 q (Finset.mem_union_left _ (Finset.mem_union_left _ hq))) heM,
    Q.crossing_three_of_covers_shore (fun q hq ↦
      hglue.2 q (Finset.mem_union_left _ (Finset.mem_union_right _ hq))) heM, ?_⟩
  intro r hr hrY hrZ
  rcases Finset.mem_union.mp hr with hr | hr
  · exact only_e (Finset.mem_inter.mp hr).1 hrY
  · have hfZ : f ∉ H.dangling Z := by
      intro hh
      have h0 := hYnotZ hsY
      have h1 : a ∉ Z := fun h ↦ ha (Finset.mem_union_right _ h)
      rcases hf with ⟨hf0, hf1⟩ | ⟨hf0, hf1⟩ <;>
        simp only [mem_dangling, hf0, hf1, h0, h1, iff_self, not_true_eq_false] at hh
    have hgZ : g ∉ H.dangling Z := by
      intro hh
      have h0 := hYnotZ htY
      have h1 : b ∉ Z := fun h ↦ hb (Finset.mem_union_right _ h)
      rcases hg with ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩ <;>
        simp only [mem_dangling, hg0, hg1, h0, h1, iff_self, not_true_eq_false] at hh
    rcases Finset.mem_union.mp hr with hr | hr
    · exact (hfZ ((Finset.mem_singleton.mp hr) ▸ hrZ)).elim
    · exact (hgZ ((Finset.mem_singleton.mp hr) ▸ hrZ)).elim

end BipartiteRestorationShore

end GraphPuzzles.LoopMultigraph
