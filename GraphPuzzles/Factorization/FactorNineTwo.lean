import GraphPuzzles.Factorization.FactorTransport

/-!
# Chladný–Škoviera, Lemma 9.2

Let `A ⊆ Y` be cycle-separating shores of a graph of a good class with `|∂A ∩ ∂Y| = 2`.  Then
the two common edges do not form a couple of the `Y`-cut.  Otherwise the factor of `Y` would
contain a cycle-separating `2`-cut (join case) or `3`-cut (cap case) around `A`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph}

/-- The inner end (with respect to `Y`) of an edge of `∂A ∩ ∂Y` lies in `A ⊆ Y`. -/
theorem innerEnd_mem_of_mem_inter {A Y : Finset ℕ} (hAY : A ⊆ Y) (hPY : (Δ.pole Y).IsPole4)
    {a : ℕ} (ha : a ∈ Δ.bd A) (haY : a ∈ (Δ.pole Y).dangling) :
    innerEnd hPY a ∈ A := by
  rw [← ends_innerIdx hPY haY]
  have hout : Δ.ends a (Fin.rev (innerIdx hPY haY)) ∉ Y := (innerIdx_spec hPY haY).2
  obtain ⟨i, hi, hi'⟩ := bd_side ha
  by_cases h : i = innerIdx hPY haY
  · rw [← h]
    exact hi
  · have hrev : i = Fin.rev (innerIdx hPY haY) := fin2_eq_rev_of_ne h
    rw [hrev] at hi
    exact absurd (hAY hi) hout

/-- The inner end (with respect to `Y`) of an edge of `∂Y \ ∂A` lies outside `A`. -/
theorem innerEnd_notMem_of_notMem {A Y : Finset ℕ} (hAY : A ⊆ Y) (hPY : (Δ.pole Y).IsPole4)
    {a : ℕ} (ha : a ∉ Δ.bd A) (haY : a ∈ (Δ.pole Y).dangling) :
    innerEnd hPY a ∉ A := by
  intro h
  apply ha
  rw [mem_bd]
  refine ⟨bd_subset Y (dangling_pole Y ▸ haY), ?_⟩
  rw [← ends_innerIdx hPY haY] at h
  have hout : Δ.ends a (Fin.rev (innerIdx hPY haY)) ∉ Y := (innerIdx_spec hPY haY).2
  have hout' : Δ.ends a (Fin.rev (innerIdx hPY haY)) ∉ A := fun h' ↦ hout (hAY h')
  rcases dangling_idx_cases hPY haY with ⟨hi, -⟩ | ⟨hi, -⟩
  · rw [hi] at h hout'
    rw [Iso.rev_zero'] at hout'
    exact fun hiff ↦ hout' (hiff.mp h)
  · rw [hi] at h hout'
    rw [Iso.rev_one'] at hout'
    exact fun hiff ↦ hout' (hiff.mpr h)

/-- The boundary of an old set together with the second fresh vertex. -/
theorem cap_bd_insert_w {Y : Finset ℕ} (hP : (Δ.pole Y).IsPole4) (m : Fin 3) (_hcl : Δ.IsClosed)
    (_hY : Y ⊆ Δ.Vs) {Z : Finset ℕ} (hZ : Z ⊆ Y) :
    (cap hP m).bd (insert (freshV (Δ.pole Y) + 1) Z) =
      insert (freshE (Δ.pole Y)) ((Δ.bd Z \ couple₂ hP m) ∪ (couple₂ hP m \ Δ.bd Z)) := by
  ext e
  rw [mem_bd]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, cap_Es]
  have hu : freshV (Δ.pole Y) ∉ Z := fun h ↦ freshV_notMem (hZ h)
  have hw : freshV (Δ.pole Y) + 1 ∉ Z := fun h ↦ freshV_succ_notMem (hZ h)
  have hwu : freshV (Δ.pole Y) ≠ freshV (Δ.pole Y) + 1 := by omega
  have key_d : ∀ (hd : e ∈ (Δ.pole Y).dangling),
      (¬ (((cap hP m).ends e 0 = freshV (Δ.pole Y) + 1 ∨ (cap hP m).ends e 0 ∈ Z) ↔
        ((cap hP m).ends e 1 = freshV (Δ.pole Y) + 1 ∨ (cap hP m).ends e 1 ∈ Z))) ↔
      (e ∈ couple₂ hP m ↔ Δ.ends e (innerIdx hP hd) ∉ Z) := by
    intro hd
    obtain ⟨h1, h2, hi, -⟩ := cap_ends_dangling hP m hd
    have hZw : Δ.ends e (innerIdx hP hd) ≠ freshV (Δ.pole Y) + 1 :=
      fun h ↦ freshV_succ_notMem (h ▸ hi)
    rw [mem_couple₂_iff hP m hd]
    rcases dangling_idx_cases hP hd with ⟨hii, -⟩ | ⟨hii, -⟩
    · rw [hii] at h1 h2 hZw ⊢
      rw [Iso.rev_zero'] at h2
      rw [h1, h2]
      by_cases hc : e ∈ couple₁ hP m
      · rw [if_pos hc]
        simp only [hc, hZw, false_or, not_true_eq_false, false_iff, hwu, hu]
        tauto
      · rw [if_neg hc]
        simp only [hc, hZw, false_or, not_false_eq_true, true_iff, true_or]
        tauto
    · rw [hii] at h1 h2 hZw ⊢
      rw [Iso.rev_one'] at h2
      rw [h1, h2]
      by_cases hc : e ∈ couple₁ hP m
      · rw [if_pos hc]
        simp only [hc, hZw, false_or, not_true_eq_false, false_iff, hwu, hu]
      · rw [if_neg hc]
        simp only [hc, hZw, false_or, not_false_eq_true, true_iff, true_or]
  have key_i : ∀ (he : e ∈ (Δ.pole Y).Es), e ∉ (Δ.pole Y).dangling →
      ((¬ (((cap hP m).ends e 0 = freshV (Δ.pole Y) + 1 ∨ (cap hP m).ends e 0 ∈ Z) ↔
        ((cap hP m).ends e 1 = freshV (Δ.pole Y) + 1 ∨ (cap hP m).ends e 1 ∈ Z))) ↔
      ¬ (Δ.ends e 0 ∈ Z ↔ Δ.ends e 1 ∈ Z)) := by
    intro he hd
    have hin : ∀ i, Δ.ends e i ∈ Y := by
      intro i
      by_contra h
      exact hd (mem_dangling.mpr ⟨he, i, h⟩)
    rw [cap_ends_inner hP m he hin, cap_ends_inner hP m he hin]
    have h0 : (Δ.pole Y).ends e 0 ≠ freshV (Δ.pole Y) + 1 :=
      fun h' ↦ freshV_succ_notMem (h' ▸ hin 0)
    have h1 : (Δ.pole Y).ends e 1 ≠ freshV (Δ.pole Y) + 1 :=
      fun h' ↦ freshV_succ_notMem (h' ▸ hin 1)
    simp only [h0, h1, false_or]
    rfl
  constructor
  · rintro ⟨he, hiff⟩
    rcases he with rfl | he
    · exact Or.inl rfl
    · right
      by_cases hd : e ∈ (Δ.pole Y).dangling
      · have h := (key_d hd).mp hiff
        by_cases hc : e ∈ couple₂ hP m
        · exact Or.inr ⟨hc, fun hb ↦ (h.mp hc) ((mem_bd_of_dangling hP hZ hd).mp hb)⟩
        · exact Or.inl ⟨(mem_bd_of_dangling hP hZ hd).mpr (by by_contra hz; exact hc (h.mpr hz)),
            hc⟩
      · have h := (key_i he hd).mp hiff
        have heΔ : e ∈ Δ.Es := by
          rw [pole_Es, Finset.mem_union] at he
          exact he.elim (fun h ↦ edgesIn_subset Y h) (fun h ↦ bd_subset Y h)
        exact Or.inl ⟨mem_bd.mpr ⟨heΔ, h⟩, fun hc ↦ hd (couple₂_subset_dangling hP m hc)⟩
  · rintro (rfl | ⟨hb, hc⟩ | ⟨hc, hb⟩)
    · refine ⟨Or.inl rfl, ?_⟩
      have h0 : (cap hP m).ends (freshE (Δ.pole Y)) 0 = freshV (Δ.pole Y) := by
        rw [cap_ends_new]; simp
      have h1 : (cap hP m).ends (freshE (Δ.pole Y)) 1 = freshV (Δ.pole Y) + 1 := by
        rw [cap_ends_new]; simp
      rw [h0, h1]
      simp [hu]
    · have he : e ∈ (Δ.pole Y).Es := by
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side hb
        exact mem_edgesIn_or_bd (bd_subset Z hb) (hZ hi)
      refine ⟨Or.inr he, ?_⟩
      by_cases hd : e ∈ (Δ.pole Y).dangling
      · rw [key_d hd]
        exact ⟨fun h ↦ absurd h hc, fun h ↦ absurd ((mem_bd_of_dangling hP hZ hd).mp hb) h⟩
      · rw [key_i he hd]
        exact (mem_bd.mp hb).2
    · have hd := couple₂_subset_dangling hP m hc
      have he := (mem_dangling.mp hd).1
      refine ⟨Or.inr he, ?_⟩
      rw [key_d hd]
      exact ⟨fun _ ↦ fun hz ↦ hb ((mem_bd_of_dangling hP hZ hd).mpr hz), fun _ ↦ hc⟩

section NineTwo

variable {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ)
include hG hΔ

/-- **Chladný–Škoviera, Lemma 9.2.**  If `A ⊆ Y` are cycle-separating shores, `Y ≠ A`, and the
two edges of `∂A ∩ ∂Y` form a couple of the `Y`-cut, we reach a contradiction. -/
theorem no_couple_in_cut {A Y : Finset ℕ} (hA : Δ.CycSep A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hPY : (Δ.pole Y).IsPole4) {k₁ k₂ : Fin 4}
    (h₁ : bdEmb hPY k₁ ∈ Δ.bd A) (h₂ : bdEmb hPY k₂ ∈ Δ.bd A)
    (hcard : (Δ.bd A ∩ Δ.bd Y).card = 2) {m : Fin 3} (hm : IsoWith hPY m ∨ HetWith hPY m)
    (hpair : pairing m k₁ = k₂) : False := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hYV := hY.1
  have hcolY := hG.pole_colourable Δ hΔ Y hY
  have hk : k₁ ≠ k₂ := fun h ↦ pairing_ne m k₁ (h ▸ hpair)
  -- the couple positions are `{0, pairing m 0}` or `{other m, pairing m (other m)}`
  have hcouple : ({bdEmb hPY k₁, bdEmb hPY k₂} : Finset ℕ) = couple₁ hPY m ∨
      ({bdEmb hPY k₁, bdEmb hPY k₂} : Finset ℕ) = couple₂ hPY m := by
    rcases four_positions m k₁ with rfl | rfl | rfl | rfl
    · left; unfold couple₁; rw [hpair]
    · left; unfold couple₁
      rw [← hpair, pairing_involutive, Finset.pair_comm]
    · right; unfold couple₂; rw [hpair]
    · right; unfold couple₂
      rw [← hpair, pairing_involutive, Finset.pair_comm]
  -- `K = Y \ A` is nonempty
  have hKne : (Y \ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (Finset.sdiff_eq_empty_iff_subset.mp h |> fun h ↦ Finset.Subset.antisymm h hAY)
  have hA4 : (Δ.bd A).card = 4 := hA.2.1
  have hbd_sdiff : (Δ.bd A \ Δ.bd Y).card = 2 := by
    have := Finset.card_sdiff_add_card_inter (Δ.bd A) (Δ.bd Y)
    omega
  have hd₁ : bdEmb hPY k₁ ∈ (Δ.pole Y).dangling := bdEmb_mem hPY k₁
  have hd₂ : bdEmb hPY k₂ ∈ (Δ.pole Y).dangling := bdEmb_mem hPY k₂
  have hinter : Δ.bd A ∩ Δ.bd Y = {bdEmb hPY k₁, bdEmb hPY k₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨h₁, bd_subset Y (dangling_pole Y ▸ hd₁) |> fun _ ↦
          dangling_pole Y ▸ hd₁⟩
      · exact Finset.mem_inter.mpr ⟨h₂, dangling_pole Y ▸ hd₂⟩
    · rw [hcard, Finset.card_pair (fun h ↦ hk (bdEmb_injective hPY h))]
  have hother : ∀ k, k ≠ k₁ → k ≠ k₂ → bdEmb hPY k ∉ Δ.bd A := by
    intro k hk₁ hk₂ h
    have : bdEmb hPY k ∈ Δ.bd A ∩ Δ.bd Y :=
      Finset.mem_inter.mpr ⟨h, dangling_pole Y ▸ bdEmb_mem hPY k⟩
    rw [hinter, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h'
    · exact hk₁ (bdEmb_injective hPY h')
    · exact hk₂ (bdEmb_injective hPY h')
  have hYc := cycSep_compl hcl hY
  have hPYc := hYc.isPole4 hcub
  have hcolYc := hG.pole_colourable Δ hΔ _ hYc
  have hKV : Y \ A ⊆ Δ.Vs := Finset.sdiff_subset.trans hYV
  have hKpos := Finset.card_pos.mpr hKne
  rcases hm with hiso | hhet
  · -- cap case: `A` together with the fresh vertex of the couple is a `3`-cut of the cap
    have hQP : P (cap hPY m) := by
      obtain ⟨m', hm'⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPY hPYc hcolY hcolYc
      rcases hm' with ⟨hiso', hhet'⟩ | ⟨hhet', -⟩
      · have := IsoWith.unique hPY hcolY hiso hiso'
        subst this
        exact hG.cap_mem Δ hΔ Y m hPY ⟨hY, ⟨hPY, hiso⟩, ⟨hPYc, hhet'⟩⟩
      · exact absurd hhet' (fun h ↦ not_isoWith_hetWith hPY hcolY hiso h)
    set Q := cap hPY m with hQ
    have hQcl := hG.closed Q hQP
    have hQcub := hG.cubic Q hQP
    have hQc4 := hG.cyc4 Q hQP
    have hAQ : A ⊆ Q.Vs := fun v hv ↦ mem_cap_Vs_of_old hPY m (hAY hv)
    have hcycA : Q.HasCycle A := cap_hasCycle_of hPY m hAY hYV hA.2.2.1
    -- the common argument for either fresh vertex
    have key : ∀ (x x' : ℕ) (C : Finset ℕ), x ∈ Q.Vs → x ∉ Y → x' ∉ Y → x ≠ x' →
        C = {bdEmb hPY k₁, bdEmb hPY k₂} →
        Q.bd (insert x A) = insert (freshE (Δ.pole Y)) ((Δ.bd A \ C) ∪ (C \ Δ.bd A)) →
        Q.Vs \ insert x A = insert x' (Y \ A) → False := by
      intro x x' C hxQ hxY hx'Y hxx' hC hbd hcompl
      have hCsub : C ⊆ Δ.bd A := by
        rw [hC]
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact h₁
        · exact h₂
      have hC2 : C.card = 2 := by
        rw [hC, Finset.card_pair (fun h ↦ hk (bdEmb_injective hPY h))]
      have hfresh : freshE (Δ.pole Y) ∉ Δ.bd A := by
        intro h
        refine freshE_notMem (P := Δ.pole Y) ?_
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset A h) (hAY hi)
      have hcard3 : (Q.bd (insert x A)).card = 3 := by
        rw [hbd, Finset.card_insert_of_notMem, Finset.sdiff_eq_empty_iff_subset.mpr hCsub,
          Finset.union_empty, Finset.card_sdiff_of_subset hCsub, hA4, hC2]
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, not_or]
        exact ⟨fun h ↦ hfresh h.1, fun h ↦ hfresh (hCsub h.1)⟩
      have hZQ : insert x A ⊆ Q.Vs := Finset.insert_subset hxQ hAQ
      have hcycZ : Q.HasCycle (insert x A) := hcycA.mono (Finset.subset_insert _ _)
      have hne' : (Q.Vs \ insert x A).Nonempty := by
        rw [hcompl]
        exact Finset.insert_nonempty _ _
      by_cases hcyc : Q.HasCycle (Q.Vs \ insert x A)
      · have := hQc4 _ hZQ hcycZ hcyc
        omega
      · have h1 := card_add_two_le_card_bd hQcub Finset.sdiff_subset hne' hcyc
        rw [bd_compl hQcl, hcard3, hcompl, Finset.card_insert_of_notMem
          (fun h ↦ hx'Y (Finset.mem_sdiff.mp h).1)] at h1
        omega
    have hu : freshV (Δ.pole Y) ∉ Y := freshV_notMem
    have hw : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem
    rcases hcouple with hC | hC
    · apply key (freshV (Δ.pole Y)) (freshV (Δ.pole Y) + 1) (couple₁ hPY m) (freshV_mem_cap hPY m)
        hu hw (by omega) hC.symm (cap_bd_insert_u hPY m hcl hYV hAY)
      ext v
      rw [cap_Vs]
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rw [not_or] at h2
        rcases h1 with rfl | rfl | h1
        · exact absurd rfl h2.1
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2.2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inr (Or.inl rfl), fun h ↦ h.elim (fun h ↦ by omega) (fun h ↦ hw (hAY h))⟩
        · exact ⟨Or.inr (Or.inr h1), fun h ↦ h.elim (fun h ↦ hu (h ▸ h1)) h2⟩
    · apply key (freshV (Δ.pole Y) + 1) (freshV (Δ.pole Y)) (couple₂ hPY m)
        (freshV_succ_mem_cap hPY m) hw hu (by omega) hC.symm (cap_bd_insert_w hPY m hcl hYV hAY)
      ext v
      rw [cap_Vs]
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rw [not_or] at h2
        rcases h1 with rfl | rfl | h1
        · exact Or.inl rfl
        · exact absurd rfl h2.1
        · exact Or.inr ⟨h1, h2.2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, fun h ↦ h.elim (fun h ↦ by omega) (fun h ↦ hu (hAY h))⟩
        · exact ⟨Or.inr (Or.inr h1), fun h ↦ h.elim (fun h ↦ hw (h ▸ h1)) h2⟩
  · -- join case: `A` is a `2`-cut of the join
    have hQP : P (join hPY m) := by
      obtain ⟨m', hm'⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPY hPYc hcolY hcolYc
      rcases hm' with ⟨hiso', -⟩ | ⟨hhet', hiso'⟩
      · exact absurd hiso' (fun h ↦ not_isoWith_hetWith hPY hcolY h hhet)
      · have := HetWith.unique hPY hcolY hhet hhet'
        subst this
        have e : Δ.Vs \ (Δ.Vs \ Y) = Y := Finset.sdiff_sdiff_eq_self hYV
        have hP' : (Δ.pole (Δ.Vs \ (Δ.Vs \ Y))).IsPole4 := by rw [e]; exact hPY
        have := hG.join_mem Δ hΔ (Δ.Vs \ Y) m hP' ⟨hYc, ⟨hPYc, hiso'⟩, ⟨hP', by
          have hh := hhet
          exact (by
            have key : ∀ (X₁ X₂ : Finset ℕ) (h : X₁ = X₂) (hP₁ : (Δ.pole X₁).IsPole4)
                (hP₂ : (Δ.pole X₂).IsPole4), HetWith hP₁ m → HetWith hP₂ m := by
              intro X₁ X₂ h hP₁ hP₂ hk
              subst h
              exact hk
            exact key _ _ e.symm hPY hP' hh)⟩⟩
        rw [join_congr e hP' hPY rfl] at this
        exact this
    set Q := join hPY m with hQ
    have hQcl := hG.closed Q hQP
    have hQcub := hG.cubic Q hQP
    have hQc4 := hG.cyc4 Q hQP
    have hAQ : A ⊆ Q.Vs := by rw [hQ, join_Vs, pole_Vs]; exact hAY
    have hcycA : Q.HasCycle A := join_hasCycle_of hPY m hAY hYV hA.2.2.1
    -- neither new edge crosses `A`
    have hends : ∀ k, (innerEnd hPY (bdEmb hPY k) ∈ A ↔ k = k₁ ∨ k = k₂) := by
      intro k
      constructor
      · intro h
        by_contra hc
        rw [not_or] at hc
        exact innerEnd_notMem_of_notMem hAY hPY (hother k hc.1 hc.2) (bdEmb_mem hPY k) h
      · rintro (rfl | rfl)
        · exact innerEnd_mem_of_mem_inter hAY hPY h₁ hd₁
        · exact innerEnd_mem_of_mem_inter hAY hPY h₂ hd₂
    have hpairs : ∀ k, (k = k₁ ∨ k = k₂) ↔ (pairing m k = k₁ ∨ pairing m k = k₂) := by
      intro k
      constructor
      · rintro (rfl | rfl)
        · exact Or.inr hpair
        · left
          rw [← hpair, pairing_involutive]
      · rintro (h | h)
        · right
          have := congrArg (pairing m) h
          rw [pairing_involutive, hpair] at this
          exact this
        · left
          have := congrArg (pairing m) h
          rw [pairing_involutive, ← hpair, pairing_involutive] at this
          exact this
    have hnocross : ∀ f ∈ ({freshE (Δ.pole Y), freshE (Δ.pole Y) + 1} : Finset ℕ),
        (Q.ends f 0 ∈ A ↔ Q.ends f 1 ∈ A) := by
      intro f hf
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · rw [join_ends_new₁, join_ends_new₁]
        simp only [if_true, one_ne_zero, if_false]
        rw [hends, hends, hpairs 0]
      · rw [join_ends_new₂, join_ends_new₂]
        simp only [if_true, one_ne_zero, if_false]
        rw [hends, hends, hpairs (other m)]
    have hbdA : Q.bd A = Δ.bd A \ Δ.bd Y := by
      rw [hQ, join_bd_old hPY m hAY hYV]
      have : (({freshE (Δ.pole Y), freshE (Δ.pole Y) + 1} : Finset ℕ).filter fun f ↦
          ¬ ((join hPY m).ends f 0 ∈ A ↔ (join hPY m).ends f 1 ∈ A)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro f hf h
        exact h (hnocross f hf)
      rw [this, Finset.union_empty]
      ext e
      simp [Finset.mem_filter, Finset.mem_sdiff]
    have hcard2 : (Q.bd A).card = 2 := by rw [hbdA, hbd_sdiff]
    have hcompl : Q.Vs \ A = Y \ A := by rw [hQ, join_Vs, pole_Vs]
    by_cases hcyc : Q.HasCycle (Q.Vs \ A)
    · have := hQc4 _ hAQ hcycA hcyc
      omega
    · have h1 := card_add_two_le_card_bd hQcub Finset.sdiff_subset (by rw [hcompl]; exact hKne) hcyc
      rw [bd_compl hQcl, hcard2, hcompl] at h1
      omega

end NineTwo

end FinGraph
end GraphPuzzles
