import GraphPuzzles.Factorization.FactorHeredity

/-!
# The projected cut (Chladný–Škoviera, Proposition 9.4)

Let `A` be an atom and `Y ⊇ A` a non-associated cycle-separating shore.  In the factor `B₀` of
the complement of `A`, the shore `Y \ A` (join case) or `Y \ A` together with the two fresh
vertices (cap case) is cycle-separating: its boundary has four edges, its complement is the
old complement of `Y`, and if it were acyclic then `Y \ A` would have at most two vertices,
which the counting lemmas exclude.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph}

/-- The boundary of `Y \ A` for `A ⊆ Y` in a closed graph. -/
theorem bd_sdiff_eq (_hcl : Δ.IsClosed) {A Y : Finset ℕ} (hAY : A ⊆ Y) :
    Δ.bd (Y \ A) = (Δ.bd A \ Δ.bd Y) ∪ (Δ.bd Y \ Δ.bd A) := by
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff, mem_bd]
  have i0 : Δ.ends e 0 ∈ A → Δ.ends e 0 ∈ Y := fun h ↦ hAY h
  have i1 : Δ.ends e 1 ∈ A → Δ.ends e 1 ∈ Y := fun h ↦ hAY h
  by_cases he : e ∈ Δ.Es
  · simp only [he, true_and]
    by_cases a0 : Δ.ends e 0 ∈ A <;> by_cases a1 : Δ.ends e 1 ∈ A <;>
      by_cases y0 : Δ.ends e 0 ∈ Y <;> by_cases y1 : Δ.ends e 1 ∈ Y <;>
      simp only [a0, a1, y0, y1] <;> tauto
  · simp [he]

section Projection

variable {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ)
include hG hΔ

omit hG hΔ in
/-- The boundary of an old vertex set together with both fresh vertices of a cap. -/
theorem cap_bd_insert_both {W : Finset ℕ} (hP : (Δ.pole W).IsPole4) (m : Fin 3)
    (_hW : W ⊆ Δ.Vs) {Z : Finset ℕ} (hZ : Z ⊆ W) :
    (cap hP m).bd (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) Z)) =
      (Δ.bd Z \ Δ.bd W) ∪ (Δ.bd W \ Δ.bd Z) := by
  ext e
  rw [mem_bd, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
  simp only [Finset.mem_insert, cap_Es]
  have hu : freshV (Δ.pole W) ∉ Z := fun h ↦ freshV_notMem (hZ h)
  have hw : freshV (Δ.pole W) + 1 ∉ Z := fun h ↦ freshV_succ_notMem (hZ h)
  have hwu : freshV (Δ.pole W) + 1 ≠ freshV (Δ.pole W) := by omega
  have hdang : (Δ.pole W).dangling = Δ.bd W := dangling_pole W
  constructor
  · rintro ⟨he, hiff⟩
    rcases he with rfl | he
    · exfalso
      apply hiff
      have h0 : (cap hP m).ends (freshE (Δ.pole W)) 0 = freshV (Δ.pole W) := by
        rw [cap_ends_new]; simp
      have h1 : (cap hP m).ends (freshE (Δ.pole W)) 1 = freshV (Δ.pole W) + 1 := by
        rw [cap_ends_new]; simp
      rw [h0, h1]
      simp
    · have heΔ : e ∈ Δ.Es := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.elim (fun h ↦ edgesIn_subset W h) (fun h ↦ bd_subset W h)
      by_cases hd : e ∈ (Δ.pole W).dangling
      · right
        refine ⟨hdang ▸ hd, ?_⟩
        rw [mem_bd_of_dangling hP hZ hd]
        obtain ⟨h1, h2, hi, -⟩ := cap_ends_dangling hP m hd
        intro hin
        apply hiff
        rcases dangling_idx_cases hP hd with ⟨hii, -⟩ | ⟨hii, -⟩
        · rw [hii] at h1 h2 hin
          rw [Iso.rev_zero'] at h2
          rw [h1, h2]
          split_ifs <;> simp [hin]
        · rw [hii] at h1 h2 hin
          rw [Iso.rev_one'] at h2
          rw [h1, h2]
          split_ifs <;> simp [hin]
      · left
        have hin : ∀ i, Δ.ends e i ∈ W := by
          intro i
          by_contra h
          exact hd (mem_dangling.mpr ⟨he, i, h⟩)
        refine ⟨mem_bd.mpr ⟨heΔ, fun h ↦ hiff ?_⟩, hdang ▸ hd⟩
        rw [cap_ends_inner hP m he hin, cap_ends_inner hP m he hin]
        have h0 : (Δ.pole W).ends e 0 ≠ freshV (Δ.pole W) := fun h' ↦ freshV_notMem (h' ▸ hin 0)
        have h1 : (Δ.pole W).ends e 1 ≠ freshV (Δ.pole W) := fun h' ↦ freshV_notMem (h' ▸ hin 1)
        have h0' : (Δ.pole W).ends e 0 ≠ freshV (Δ.pole W) + 1 :=
          fun h' ↦ freshV_succ_notMem (h' ▸ hin 0)
        have h1' : (Δ.pole W).ends e 1 ≠ freshV (Δ.pole W) + 1 :=
          fun h' ↦ freshV_succ_notMem (h' ▸ hin 1)
        simp only [h0, h1, h0', h1', false_or]
        exact h
  · rintro (⟨hb, hnb⟩ | ⟨hb, hnb⟩)
    · have he : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side hb
        exact mem_edgesIn_or_bd (bd_subset Z hb) (hZ hi)
      have hd : e ∉ (Δ.pole W).dangling := by rw [hdang]; exact hnb
      have hin : ∀ i, Δ.ends e i ∈ W := by
        intro i
        by_contra h
        exact hd (mem_dangling.mpr ⟨he, i, h⟩)
      refine ⟨Or.inr he, ?_⟩
      rw [cap_ends_inner hP m he hin, cap_ends_inner hP m he hin]
      have h0 : (Δ.pole W).ends e 0 ≠ freshV (Δ.pole W) := fun h' ↦ freshV_notMem (h' ▸ hin 0)
      have h1 : (Δ.pole W).ends e 1 ≠ freshV (Δ.pole W) := fun h' ↦ freshV_notMem (h' ▸ hin 1)
      have h0' : (Δ.pole W).ends e 0 ≠ freshV (Δ.pole W) + 1 :=
        fun h' ↦ freshV_succ_notMem (h' ▸ hin 0)
      have h1' : (Δ.pole W).ends e 1 ≠ freshV (Δ.pole W) + 1 :=
        fun h' ↦ freshV_succ_notMem (h' ▸ hin 1)
      simp only [h0, h1, h0', h1', false_or]
      exact (mem_bd.mp hb).2
    · have hd : e ∈ (Δ.pole W).dangling := by rw [hdang]; exact hb
      have he := (mem_dangling.mp hd).1
      refine ⟨Or.inr he, ?_⟩
      have hnin : Δ.ends e (innerIdx hP hd) ∉ Z := fun h ↦ hnb ((mem_bd_of_dangling hP hZ hd).mpr h)
      obtain ⟨h1, h2, hi, -⟩ := cap_ends_dangling hP m hd
      have hZu : Δ.ends e (innerIdx hP hd) ≠ freshV (Δ.pole W) := fun h ↦ freshV_notMem (h ▸ hi)
      have hZw : Δ.ends e (innerIdx hP hd) ≠ freshV (Δ.pole W) + 1 :=
        fun h ↦ freshV_succ_notMem (h ▸ hi)
      rcases dangling_idx_cases hP hd with ⟨hii, -⟩ | ⟨hii, -⟩
      · rw [hii] at h1 h2 hnin hZu hZw
        rw [Iso.rev_zero'] at h2
        rw [h1, h2]
        split_ifs <;> simp [hnin, hZu, hZw]
      · rw [hii] at h1 h2 hnin hZu hZw
        rw [Iso.rev_one'] at h2
        rw [h1, h2]
        split_ifs <;> simp [hnin, hZu, hZw]

omit hG hΔ in
/-- For a boundary edge of `A ⊆ Y`, its end outside `A` lies in `Y \ A` iff the edge is not a
boundary edge of `Y`. -/
theorem innerEnd_compl_mem_iff (hcl : Δ.IsClosed) {A Y : Finset ℕ} (hAY : A ⊆ Y)
    (hPAc : (Δ.pole (Δ.Vs \ A)).IsPole4) {a : ℕ} (ha : a ∈ (Δ.pole (Δ.Vs \ A)).dangling) :
    innerEnd hPAc a ∈ Y \ A ↔ a ∉ Δ.bd Y := by
  have haE : a ∈ Δ.Es := bd_subset _ (dangling_pole _ ▸ ha)
  have hin : Δ.ends a (innerIdx hPAc ha) ∈ Δ.Vs \ A := (innerIdx_spec hPAc ha).1
  have hout : Δ.ends a (Fin.rev (innerIdx hPAc ha)) ∉ Δ.Vs \ A := (innerIdx_spec hPAc ha).2
  have hotherA : Δ.ends a (Fin.rev (innerIdx hPAc ha)) ∈ A := by
    by_contra h
    exact hout (Finset.mem_sdiff.mpr ⟨hcl a haE _, h⟩)
  have hotherY := hAY hotherA
  rw [← ends_innerIdx hPAc ha]
  show Δ.ends a (innerIdx hPAc ha) ∈ Y \ A ↔ a ∉ Δ.bd Y
  rw [Finset.mem_sdiff, mem_bd]
  constructor
  · rintro ⟨hY, -⟩ ⟨-, h⟩
    apply h
    rcases dangling_idx_cases hPAc ha with ⟨hi, -⟩ | ⟨hi, -⟩
    · rw [hi] at hY hotherY
      rw [Iso.rev_zero'] at hotherY
      exact ⟨fun _ ↦ hotherY, fun _ ↦ hY⟩
    · rw [hi] at hY hotherY
      rw [Iso.rev_one'] at hotherY
      exact ⟨fun _ ↦ hY, fun _ ↦ hotherY⟩
  · intro h
    refine ⟨?_, (Finset.mem_sdiff.mp hin).2⟩
    by_contra hY
    apply h
    refine ⟨haE, fun hiff ↦ ?_⟩
    rcases dangling_idx_cases hPAc ha with ⟨hi, -⟩ | ⟨hi, -⟩
    · rw [hi] at hY hotherY
      rw [Iso.rev_zero'] at hotherY
      exact hY (hiff.mpr hotherY)
    · rw [hi] at hY hotherY
      rw [Iso.rev_one'] at hotherY
      exact hY (hiff.mp hotherY)

/-- **Chladný–Škoviera, Proposition 9.4.**  The projection of a non-associated cut into the
factor of the complement of the atom is cycle-separating. -/
theorem projected_cycSep {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hnq : ¬ Δ.IsQuasiatomic A Y) (hPAc : (Δ.pole (Δ.Vs \ A)).IsPole4) (m : Fin 3) :
    (IsoWith hPAc m → P (cap hPAc m) → (cap hPAc m).CycSep
      (insert (freshV (Δ.pole (Δ.Vs \ A))) (insert (freshV (Δ.pole (Δ.Vs \ A)) + 1) (Y \ A)))) ∧
    (HetWith hPAc m → P (join hPAc m) → (join hPAc m).CycSep (Y \ A)) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  have hc4 := hG.cyc4 Δ hΔ
  have hYV := hY.1
  have hAV := hA.1.1
  have hAc := cycSep_compl hcl hA.1
  have hPA := hA.1.isPole4 hcub
  have hc3 := IsAtom.card_inter_ne_three hcl hcub hg hc4 hA hY
  have hcle2 := card_inter_le_two hG hΔ hA hY hAY hne
  have hKne : (Y \ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h) hAY)
  have hKsub : Y \ A ⊆ Δ.Vs \ A := Finset.sdiff_subset_sdiff hYV (Finset.Subset.refl _)
  have hsmall : ¬ (Y \ A).card ≤ 2 := by
    intro hle
    have hpos := Finset.card_pos.mpr hKne
    have h12 : (Y \ A).card = 1 ∨ (Y \ A).card = 2 := by omega
    rcases h12 with h1 | h2
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
      exact not_singleton_sdiff hcl hcub hg hc4 hA.1 hY hAY hv hc3
    · obtain ⟨v₁, v₂, hv, hK⟩ := Finset.card_eq_two.mp h2
      exact hnq (quasiatomic_of_pair hcl hcub hg hc4 hA.1 hY hAY hv hK hc3 hne)
  have hbdK : Δ.bd (Y \ A) = (Δ.bd A \ Δ.bd Y) ∪ (Δ.bd Y \ Δ.bd A) := bd_sdiff_eq hcl hAY
  have hbdAc : Δ.bd (Δ.Vs \ A) = Δ.bd A := bd_compl hcl A
  have hYc_cyc : Δ.HasCycle (Δ.Vs \ Y) := hY.2.2.2
  have hYc_sub : Δ.Vs \ Y ⊆ Δ.Vs \ A := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hAY
  constructor
  · -- cap case
    intro hiso hPmem
    set Q := cap hPAc m with hQ
    have hQcl := hG.closed Q hPmem
    have hQcub := hG.cubic Q hPmem
    set Y' := insert (freshV (Δ.pole (Δ.Vs \ A)))
      (insert (freshV (Δ.pole (Δ.Vs \ A)) + 1) (Y \ A)) with hY'
    have hY'Q : Y' ⊆ Q.Vs := by
      intro v hv
      rw [hY', Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · exact freshV_mem_cap hPAc m
      · exact freshV_succ_mem_cap hPAc m
      · exact mem_cap_Vs_of_old hPAc m (hKsub hv)
    have hbd : (Q.bd Y').card = 4 := by
      rw [hQ, hY', cap_bd_insert_both hPAc m Finset.sdiff_subset hKsub, hbdAc, hbdK]
      have e : ((Δ.bd A \ Δ.bd Y) ∪ (Δ.bd Y \ Δ.bd A)) \ Δ.bd A ∪
          (Δ.bd A \ ((Δ.bd A \ Δ.bd Y) ∪ (Δ.bd Y \ Δ.bd A))) = Δ.bd Y := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      rw [e]
      exact hY.2.1
    have hcompl : Q.Vs \ Y' = Δ.Vs \ Y := by
      ext v
      rw [hQ, cap_Vs, hY']
      simp only [Finset.mem_sdiff, Finset.mem_insert, pole_Vs]
      constructor
      · rintro ⟨h1, h2⟩
        rw [not_or, not_or] at h2
        rcases h1 with rfl | rfl | ⟨h1, h1'⟩
        · exact absurd rfl h2.1
        · exact absurd rfl h2.2.1
        · exact ⟨h1, fun hY ↦ h2.2.2 ⟨hY, h1'⟩⟩
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr (Or.inr ⟨h1, fun h ↦ h2 (hAY h)⟩), ?_⟩
        rw [not_or, not_or]
        refine ⟨fun h ↦ freshV_notMem (P := Δ.pole (Δ.Vs \ A)) ?_,
          fun h ↦ freshV_succ_notMem (P := Δ.pole (Δ.Vs \ A)) ?_, fun h ↦ h2 h.1⟩
        · rw [← h]; exact Finset.mem_sdiff.mpr ⟨h1, fun h' ↦ h2 (hAY h')⟩
        · rw [← h]; exact Finset.mem_sdiff.mpr ⟨h1, fun h' ↦ h2 (hAY h')⟩
    refine ⟨hY'Q, hbd, ?_, ?_⟩
    · by_contra hno
      have h1 := card_add_two_le_card_bd hQcub hY'Q (Finset.insert_nonempty _ _) hno
      rw [hbd, hY', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at h1
      · have := Finset.card_pos.mpr hKne
        omega
      · intro h
        exact freshV_succ_notMem (P := Δ.pole (Δ.Vs \ A)) (hKsub h)
      · rw [Finset.mem_insert, not_or]
        exact ⟨by omega, fun h ↦ freshV_notMem (P := Δ.pole (Δ.Vs \ A)) (hKsub h)⟩
    · rw [hcompl]
      exact cap_hasCycle_of hPAc m hYc_sub Finset.sdiff_subset hYc_cyc
  · -- join case
    intro hhet hPmem
    set Q := join hPAc m with hQ
    have hQcl := hG.closed Q hPmem
    have hQcub := hG.cubic Q hPmem
    have hKQ : Y \ A ⊆ Q.Vs := by rw [hQ, join_Vs, pole_Vs]; exact hKsub
    -- the `A`-pole is isochromatic with the same pairing
    have hisoA : IsoWith hPA m := by
      have hcolA := hG.pole_colourable Δ hΔ A hA.1
      have hcolAc := hG.pole_colourable Δ hΔ _ hAc
      obtain ⟨m', hm'⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPA hPAc hcolA hcolAc
      rcases hm' with ⟨hiso', hhet'⟩ | ⟨-, hiso'⟩
      · rw [HetWith.unique hPAc hcolAc hhet' hhet] at hiso'
        exact hiso'
      · exact absurd hiso' (fun h ↦ not_isoWith_hetWith hPAc hcolAc h hhet)
    have hemb : ∀ k, bdEmb hPA k = bdEmb hPAc k :=
      bdEmb_congr hPA hPAc (by rw [dangling_pole, dangling_pole, hbdAc])
    -- no couple of `∂A` lies in `∂Y`
    have hnocouple : ∀ k, bdEmb hPAc k ∈ Δ.bd Y → bdEmb hPAc (pairing m k) ∈ Δ.bd Y → False := by
      intro k h₁ h₂
      rw [← hemb] at h₁ h₂
      exact not_couple_of_bdA hG hΔ hA hY hAY hne hPA (hY.isPole4 hcub) (pairing_ne m k).symm h₁ h₂
        (Or.inl hisoA) rfl
    have hbd : (Q.bd (Y \ A)).card = 4 := by
      rw [hQ, join_bd_old hPAc m hKsub Finset.sdiff_subset, hbdAc]
      have hf₁ : freshE (Δ.pole (Δ.Vs \ A)) ∉ Δ.bd (Y \ A) := by
        intro h
        refine freshE_notMem (P := Δ.pole (Δ.Vs \ A)) ?_
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset _ h) (hKsub hi)
      have hf₂ : freshE (Δ.pole (Δ.Vs \ A)) + 1 ∉ Δ.bd (Y \ A) := by
        intro h
        refine freshE_succ_notMem (P := Δ.pole (Δ.Vs \ A)) ?_
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset _ h) (hKsub hi)
      rw [Finset.card_union_of_disjoint]
      · have e1 : ((Δ.bd (Y \ A)).filter fun e ↦ e ∉ Δ.bd A).card =
            4 - (Δ.bd A ∩ Δ.bd Y).card := by
          have e : (Δ.bd (Y \ A)).filter (fun e ↦ e ∉ Δ.bd A) = Δ.bd Y \ Δ.bd A := by
            rw [hbdK]
            ext e
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
            tauto
          rw [e]
          have := Finset.card_sdiff_add_card_inter (Δ.bd Y) (Δ.bd A)
          rw [Finset.inter_comm] at this
          have hY4 := hY.2.1
          omega
        have hcross : ∀ k, (k = 0 ∨ k = other m) →
            ((¬ ((join hPAc m).ends (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).1 0 ∈ Y \ A ↔
              (join hPAc m).ends (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).1 1 ∈ Y \ A)) ↔
            (bdEmb hPAc k ∈ Δ.bd Y ∨ bdEmb hPAc (pairing m k) ∈ Δ.bd Y)) := by
          intro k hk
          have h0 : (join hPAc m).ends (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).1 0 =
              innerEnd hPAc (bdEmb hPAc k) := by
            have := join_ends_newHalf hPAc m k
            have hk0 : (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).2 = 0 := by
              rcases hk with rfl | rfl
              · rw [newHalf_zero]
              · rw [newHalf_other]
            rw [hk0] at this
            exact this
          have h1 : (join hPAc m).ends (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).1 1 =
              innerEnd hPAc (bdEmb hPAc (pairing m k)) := by
            have := join_ends_newHalf hPAc m (pairing m k)
            have hk1 : (newHalf (P := Δ.pole (Δ.Vs \ A)) m (pairing m k)).1 =
                (newHalf (P := Δ.pole (Δ.Vs \ A)) m k).1 :=
              (newHalf_pairing (Q := Δ.pole (Δ.Vs \ A)) m k).1
            have hk2 : (newHalf (P := Δ.pole (Δ.Vs \ A)) m (pairing m k)).2 = 1 := by
              rw [(newHalf_pairing (Q := Δ.pole (Δ.Vs \ A)) m k).2]
              rcases hk with rfl | rfl
              · rw [newHalf_zero]; exact Iso.rev_zero'
              · rw [newHalf_other]; exact Iso.rev_zero'
            rw [hk1, hk2] at this
            exact this
          rw [h0, h1, innerEnd_compl_mem_iff hcl hAY hPAc (bdEmb_mem hPAc k),
            innerEnd_compl_mem_iff hcl hAY hPAc (bdEmb_mem hPAc _)]
          constructor
          · intro h
            by_contra hc
            rw [not_or] at hc
            exact h ⟨fun _ ↦ hc.2, fun _ ↦ hc.1⟩
          · rintro (h | h) hiff
            · by_cases hc : bdEmb hPAc (pairing m k) ∈ Δ.bd Y
              · exact hnocouple k h hc
              · exact (hiff.mpr hc) h
            · by_cases hc : bdEmb hPAc k ∈ Δ.bd Y
              · exact hnocouple k hc h
              · exact (hiff.mp hc) h
        have e2 : (({freshE (Δ.pole (Δ.Vs \ A)), freshE (Δ.pole (Δ.Vs \ A)) + 1} : Finset ℕ).filter
            fun f ↦ ¬ ((join hPAc m).ends f 0 ∈ Y \ A ↔ (join hPAc m).ends f 1 ∈ Y \ A)).card =
              (Δ.bd A ∩ Δ.bd Y).card := by
          have hc' : (Δ.bd A ∩ Δ.bd Y).card = (Δ.bd Y ∩ Δ.bd (Δ.Vs \ A)).card := by
            rw [hbdAc, Finset.inter_comm]
          rw [hc', card_inter_eq_card_filter hPAc, Finset.card_filter, Finset.card_filter,
            sum_couples m, Finset.sum_pair (by omega)]
          have c₁ := hcross 0 (Or.inl rfl)
          have c₂ := hcross (other m) (Or.inr rfl)
          rw [newHalf_zero_fst] at c₁
          rw [newHalf_other_fst] at c₂
          have n₁ := hnocouple 0
          have n₂ := hnocouple (other m)
          by_cases a0 : bdEmb hPAc 0 ∈ Δ.bd Y <;>
            by_cases a1 : bdEmb hPAc (pairing m 0) ∈ Δ.bd Y <;>
            by_cases a2 : bdEmb hPAc (other m) ∈ Δ.bd Y <;>
            by_cases a3 : bdEmb hPAc (pairing m (other m)) ∈ Δ.bd Y <;>
            simp only [a0, a1, a2, a3, or_true, or_false, c₁, c₂, if_true, if_false] <;>
            first | rfl | exact absurd a1 (n₁ a0) | exact absurd a3 (n₂ a2)
        omega
      · rw [Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_filter] at h1 h2
        rw [Finset.mem_insert, Finset.mem_singleton] at h2
        rcases h2.1 with rfl | rfl
        · exact hf₁ h1.1
        · exact hf₂ h1.1
    have hcompl : Q.Vs \ (Y \ A) = Δ.Vs \ Y := by
      rw [hQ, join_Vs, pole_Vs]
      ext v
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun h ↦ h3 ⟨h, h2⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun h ↦ h2 (hAY h)⟩, fun h ↦ h2 h.1⟩
    refine ⟨hKQ, hbd, ?_, ?_⟩
    · by_contra hno
      have h1 := card_add_two_le_card_bd hQcub hKQ hKne hno
      rw [hbd] at h1
      exact hsmall (by omega)
    · rw [hcompl]
      exact join_hasCycle_of hPAc m hYc_sub Finset.sdiff_subset hYc_cyc

end Projection

end FinGraph
end GraphPuzzles
