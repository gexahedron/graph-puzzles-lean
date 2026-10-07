import GraphPuzzles.FinGraph.FinGraphTypes

/-!
# Colour-open poles

The boundary edges of a `4`-pole are listed in label order, so every colouring has a boundary
vector in `Fin 4 → Color`.  The Kempe lemma shows that a colourable `4`-pole has boundary vectors
of at least two types.  If a closed cubic graph is uncolourable and both poles of a `4`-edge-cut
are colourable, their type sets are disjoint, so by the finite type combinatorics one pole is
isochromatic and the other heterochromatic for the same pairing (Chladný–Škoviera,
Proposition 3.5).  The pairing and the side are uniquely determined.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

set_option maxRecDepth 100000

variable {Γ : FinGraph}

section Boundary

/-- The boundary edges of a `4`-pole in label order. -/
noncomputable def bdEmb (hP : Γ.IsPole4) : Fin 4 ↪o ℕ :=
  Γ.dangling.orderEmbOfFin hP.card_dangling

theorem bdEmb_mem (hP : Γ.IsPole4) (i : Fin 4) : bdEmb hP i ∈ Γ.dangling :=
  Finset.orderEmbOfFin_mem _ _ i

theorem bdEmb_injective (hP : Γ.IsPole4) : Function.Injective (bdEmb hP) := (bdEmb hP).injective

theorem dangling_eq_image (hP : Γ.IsPole4) : Γ.dangling = Finset.univ.image (bdEmb hP) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact bdEmb_mem hP i
  · rw [hP.card_dangling, Finset.card_image_of_injective _ (bdEmb_injective hP)]
    simp

theorem exists_bdEmb_eq (hP : Γ.IsPole4) {e : ℕ} (he : e ∈ Γ.dangling) : ∃ i, bdEmb hP i = e := by
  rw [dangling_eq_image hP] at he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  exact ⟨i, hi⟩

/-- Two poles with the same dangling edges list them in the same order. -/
theorem bdEmb_congr {Γ₁ Γ₂ : FinGraph} (hP₁ : Γ₁.IsPole4) (hP₂ : Γ₂.IsPole4)
    (h : Γ₁.dangling = Γ₂.dangling) (i : Fin 4) : bdEmb hP₁ i = bdEmb hP₂ i := by
  have := Finset.orderEmbOfFin_unique' hP₂.card_dangling (f := bdEmb hP₁)
    (fun x ↦ h ▸ bdEmb_mem hP₁ x)
  exact congrArg (fun f : Fin 4 ↪o ℕ ↦ f i) this

/-- The boundary vector of a colouring. -/
noncomputable def tvec (hP : Γ.IsPole4) (c : ℕ → Color) : Fin 4 → Color := fun i ↦ c (bdEmb hP i)

/-- The boundary vectors of the colourings of a pole. -/
def Col (hP : Γ.IsPole4) : Set (Fin 4 → Color) := {t | ∃ c, Γ.IsColouring c ∧ tvec hP c = t}

/-- The pairing `m` is isochromatic: every colouring gives equal colours to paired boundary
edges. -/
def IsoWith (hP : Γ.IsPole4) (m : Fin 3) : Prop := ∀ t ∈ Col hP, ∀ i, t i = t (pairing m i)

/-- The pairing `m` is heterochromatic: every colouring gives distinct colours to paired
boundary edges. -/
def HetWith (hP : Γ.IsPole4) (m : Fin 3) : Prop := ∀ t ∈ Col hP, ∀ i, t i ≠ t (pairing m i)

open Classical in
/-- The types of the boundary vectors of colourings. -/
noncomputable def types (hP : Γ.IsPole4) : Finset (Option (Fin 3)) :=
  Finset.univ.filter fun τ ↦ ∃ t ∈ Col hP, ptype t = τ

theorem mem_types (hP : Γ.IsPole4) {τ : Option (Fin 3)} :
    τ ∈ types hP ↔ ∃ t ∈ Col hP, ptype t = τ := by
  simp [types]

theorem tvec_nonzero (hP : Γ.IsPole4) {c : ℕ → Color} (hc : Γ.IsColouring c) :
    Nonzero4 (tvec hP c) := fun i ↦ hc.1 _ (a_mem_Es (bdEmb_mem hP i))

theorem tvec_valid (hP : Γ.IsPole4) {c : ℕ → Color} (hc : Γ.IsColouring c) :
    Valid (tvec hP c) := by
  apply valid_of_even_counts _ (tvec_nonzero hP hc)
  intro κ hκ
  have h := hc.even_card_dangling_color hP hκ
  rw [dangling_eq_image hP, Finset.filter_image,
    Finset.card_image_of_injective _ (bdEmb_injective hP)] at h
  exact h

theorem Col.valid (hP : Γ.IsPole4) {t : Fin 4 → Color} (ht : t ∈ Col hP) : Valid t := by
  obtain ⟨c, hc, rfl⟩ := ht
  exact tvec_valid hP hc

theorem Col.nonzero (hP : Γ.IsPole4) {t : Fin 4 → Color} (ht : t ∈ Col hP) : Nonzero4 t := by
  obtain ⟨c, hc, rfl⟩ := ht
  exact tvec_nonzero hP hc

end Boundary

section TwoTypes

theorem index_cases (m : Fin 3) (j : Fin 4) (hj0 : j ≠ 0) (hjp : j ≠ pairing m 0) :
    ∀ i, i = 0 ∨ i = pairing m 0 ∨ i = j ∨ i = pairing m j := by
  revert m j
  decide


/-- The combinatorial core of the Kempe argument: a swap that changes the first boundary colour
to `β`, where `β` is the other colour used by `t` (or arbitrary if `t` is constant), and changes
at most boundary edges with pairwise distinct colours besides the first, changes the type. -/
theorem ptype_ne_of_swap (t t' : Fin 4 → Color) (hv : Valid t) (hv' : Valid t') {α β : Color}
    (hα : t 0 = α) (hβ : β ≠ α) (h0 : t' 0 = β)
    (_hsw : ∀ i, t' i = t i ∨ t' i = swapC α β (t i))
    (hdist : ∀ i j, i ≠ 0 → j ≠ 0 → t' i ≠ t i → t' j ≠ t j → i ≠ j → t i ≠ t j)
    (hβ' : (∃ j, t j = β) ∨ ∀ j, t j = α) : ptype t' ≠ ptype t := by
  intro heq
  rcases hβ' with ⟨j, hj⟩ | hall
  · -- `t` has type `some m`
    have hne' : ¬ ∀ i, t i = t 0 := by
      intro h
      apply hβ
      rw [← hj, h j, hα]
    obtain ⟨m, hm⟩ : ∃ m, ptype t = some m := by
      cases h : ptype t with
      | none => exact absurd ((ptype_none_iff t).mp h) hne'
      | some m => exact ⟨m, rfl⟩
    have hpat := ((ptype_some_iff t hv m).mp hm).1
    rw [hm] at heq
    have hpat' := ((ptype_some_iff t' hv' m).mp heq).1
    have hnc' := ((ptype_some_iff t' hv' m).mp heq).2
    set p := pairing m 0 with hp
    have hp0 : p ≠ 0 := pairing_ne m 0
    have htp : t p = α := by rw [hp, ← hpat 0, hα]
    have hj0 : j ≠ 0 := fun h ↦ hβ (by rw [← hj, h, hα])
    have hjp : j ≠ p := fun h ↦ hβ (by rw [← hj, h, htp])
    set r := pairing m j with hr
    have hrj : r ≠ j := pairing_ne m j
    have hr0 : r ≠ 0 := by
      intro h
      apply hjp
      rw [hp, ← h, hr, pairing_involutive]
    have hrp : r ≠ p := by
      intro h
      apply hj0
      have := congrArg (pairing m) h
      rw [hr, pairing_involutive, hp, pairing_involutive] at this
      exact this
    have htr : t r = β := by rw [hr, ← hpat j, hj]
    -- `p` changes
    have hp' : t' p ≠ t p := by rw [htp, ← hpat' 0, h0]; exact hβ
    -- `j` and `r` change: `t' j = t' r`, and not all of `t'` equals `t' 0`
    have hjr' : t' j = t' r := hpat' j
    have hj' : t' j ≠ t j := by
      intro h
      apply hnc'
      intro i
      -- every index is `0`, `p`, `j` or `r`
      have hi : i = 0 ∨ i = p ∨ i = j ∨ i = r := index_cases m j hj0 hjp i
      rcases hi with rfl | rfl | rfl | rfl
      · rfl
      · rw [← hpat' 0]
      · rw [h, hj, h0]
      · rw [← hjr', h, hj, h0]
    have hr' : t' r ≠ t r := by
      intro h
      apply hj'
      rw [hjr', h, htr, hj]
    exact hdist j r hj0 hr0 hj' hr' (Ne.symm hrj) (by rw [hj, htr])
  · -- `t` is constant: `ptype t = none`
    have hnone : ptype t = none := (ptype_none_iff t).mpr fun i ↦ by rw [hall i, hall 0]
    rw [hnone, ptype_none_iff] at heq
    have h1 : t' 1 ≠ t 1 := by rw [heq 1, h0, hall 1]; exact hβ
    have h2 : t' 2 ≠ t 2 := by rw [heq 2, h0, hall 2]; exact hβ
    exact hdist 1 2 (by decide) (by decide) h1 h2 (by decide) (by rw [hall 1, hall 2])

theorem exists_ne_color (α : Color) : ∃ β : Color, β ≠ 0 ∧ β ≠ α := by
  revert α
  decide

/-- **A colourable `4`-pole has at least two types** (Kempe chains). -/
theorem exists_other_type (hP : Γ.IsPole4) {c : ℕ → Color} (hc : Γ.IsColouring c) :
    ∃ t' ∈ Col hP, ptype t' ≠ ptype (tvec hP c) := by
  set t := tvec hP c with ht
  set a := bdEmb hP 0 with ha
  have haD : a ∈ Γ.dangling := bdEmb_mem hP 0
  have hα : t 0 = c a := rfl
  -- choose the second colour
  obtain ⟨β, hβ0, hβa, hβ'⟩ : ∃ β : Color, β ≠ 0 ∧ β ≠ c a ∧
      ((∃ j, t j = β) ∨ ∀ j, t j = c a) := by
    by_cases h : ∃ j, t j ≠ c a
    · obtain ⟨j, hj⟩ := h
      exact ⟨t j, tvec_nonzero hP hc j, hj, Or.inl ⟨j, rfl⟩⟩
    · push Not at h
      obtain ⟨β, hβ0, hβa⟩ := exists_ne_color (c a)
      exact ⟨β, hβ0, hβa, Or.inr h⟩
  obtain ⟨c', hc', hc'a, hsw, v, hv⟩ := exists_kempe hP hc haD hβ0
  refine ⟨tvec hP c', ⟨c', hc', rfl⟩, ?_⟩
  apply ptype_ne_of_swap t (tvec hP c') (tvec_valid hP hc) (tvec_valid hP hc') hα hβa
    (by show c' a = β; exact hc'a) (fun i ↦ hsw _) ?_ hβ'
  intro i j hi hj hi' hj' hij
  -- both changed dangling edges are attached to `v`, so their colours are distinct
  obtain ⟨ki, hki, hki'⟩ := hP.exists_unique_inner (bdEmb_mem hP i)
  obtain ⟨kj, hkj, hkj'⟩ := hP.exists_unique_inner (bdEmb_mem hP j)
  have hia : bdEmb hP i ≠ a := fun h ↦ hi (bdEmb_injective hP h)
  have hja : bdEmb hP j ≠ a := fun h ↦ hj (bdEmb_injective hP h)
  have hvi := hv _ (bdEmb_mem hP i) hia hi' ki hki
  have hvj := hv _ (bdEmb_mem hP j) hja hj' kj hkj
  intro heq
  have h1 : (bdEmb hP i, ki) ∈ Γ.halfEdgesIn Γ.Es v :=
    mem_halfEdgesIn.mpr ⟨a_mem_Es (bdEmb_mem hP i), hvi⟩
  have h2 : (bdEmb hP j, kj) ∈ Γ.halfEdgesIn Γ.Es v :=
    mem_halfEdgesIn.mpr ⟨a_mem_Es (bdEmb_mem hP j), hvj⟩
  have := hc.unique_halfEdge (hvi ▸ hki) h1 h2 heq
  exact hij (bdEmb_injective hP (congrArg Prod.fst this))

theorem two_types (hP : Γ.IsPole4) (_hcol : Γ.Colourable) :
    ∀ τ ∈ types hP, ∃ τ' ∈ types hP, τ' ≠ τ := by
  intro τ hτ
  obtain ⟨t, ⟨c, hc, rfl⟩, rfl⟩ := (mem_types hP).mp hτ
  obtain ⟨t', ht', hne⟩ := exists_other_type hP hc
  exact ⟨ptype t', (mem_types hP).mpr ⟨t', ht', rfl⟩, hne⟩

theorem types_nonempty (hP : Γ.IsPole4) (hcol : Γ.Colourable) : ∃ τ, τ ∈ types hP := by
  obtain ⟨c, hc⟩ := hcol
  exact ⟨ptype (tvec hP c), (mem_types hP).mpr ⟨tvec hP c, ⟨c, hc, rfl⟩, rfl⟩⟩

end TwoTypes

section Perm

theorem swapC_zero {α β : Color} (hα : α ≠ 0) (hβ : β ≠ 0) : swapC α β 0 = 0 := by
  unfold swapC
  rw [if_neg (Ne.symm hα), if_neg (Ne.symm hβ)]

theorem swapC_right (α β : Color) : swapC α β β = α := by
  unfold swapC
  by_cases h : β = α
  · rw [if_pos h, h]
  · rw [if_neg h, if_pos rfl]

theorem swapC_of_ne {α β κ : Color} (h1 : κ ≠ α) (h2 : κ ≠ β) : swapC α β κ = κ := by
  unfold swapC
  rw [if_neg h1, if_neg h2]

theorem eq_zero_or_pairing_of_eq (m : Fin 3) (t : Fin 4 → Color)
    (hpat : ∀ i, t i = t (pairing m i)) (hnc : ¬ ∀ i, t i = t 0) :
    ∀ i, t i = t 0 → i = 0 ∨ i = pairing m 0 := by
  revert m t
  decide

theorem eq_of_ne_zero (m : Fin 3) (t : Fin 4 → Color)
    (hpat : ∀ i, t i = t (pairing m i)) :
    ∀ i j, t i ≠ t 0 → t j ≠ t 0 → t i = t j := by
  revert m t
  decide

/-- Boundary vectors of the same type differ by a permutation of the nonzero colours. -/
theorem exists_perm (t t' : Fin 4 → Color) (hv : Valid t) (hv' : Valid t') (hn : Nonzero4 t)
    (hn' : Nonzero4 t') (h : ptype t = ptype t') :
    ∃ σ : Color → Color, Function.Injective σ ∧ σ 0 = 0 ∧ ∀ i, σ (t i) = t' i := by
  cases hτ : ptype t with
  | none =>
    rw [hτ] at h
    have hc := (ptype_none_iff t).mp hτ
    have hc' := (ptype_none_iff t').mp h.symm
    refine ⟨swapC (t 0) (t' 0), swapC_injective _ _, swapC_zero (hn 0) (hn' 0), fun i ↦ ?_⟩
    rw [hc i, hc' i, swapC_left]
  | some m =>
    rw [hτ] at h
    obtain ⟨hpat, hnc⟩ := (ptype_some_iff t hv m).mp hτ
    obtain ⟨hpat', hnc'⟩ := (ptype_some_iff t' hv' m).mp h.symm
    push Not at hnc
    obtain ⟨j₀, hj₀⟩ := hnc
    have hnc'' : ¬ ∀ i, t i = t 0 := fun h ↦ hj₀ (h j₀)
    have hj₀' : t' j₀ ≠ t' 0 := by
      intro h
      rcases eq_zero_or_pairing_of_eq m t' hpat' hnc' j₀ h with h | h
      · exact hj₀ (by rw [h])
      · exact hj₀ (by rw [h, ← hpat 0])
    have hαα' : swapC (t 0) (t' 0) (t j₀) ≠ t' 0 := by
      intro h
      unfold swapC at h
      by_cases h1 : t j₀ = t 0
      · exact hj₀ h1
      · rw [if_neg h1] at h
        by_cases h2 : t j₀ = t' 0
        · rw [if_pos h2] at h
          exact hj₀ (h2.trans h.symm)
        · rw [if_neg h2] at h
          exact h2 h
    have hδ₁0 : swapC (t 0) (t' 0) (t j₀) ≠ 0 := swapC_ne_zero (hn 0) (hn' 0) (hn j₀)
    refine ⟨fun κ ↦ swapC (swapC (t 0) (t' 0) (t j₀)) (t' j₀) (swapC (t 0) (t' 0) κ),
      (swapC_injective _ _).comp (swapC_injective _ _), ?_, fun i ↦ ?_⟩
    · show swapC (swapC (t 0) (t' 0) (t j₀)) (t' j₀) (swapC (t 0) (t' 0) 0) = 0
      rw [swapC_zero (hn 0) (hn' 0), swapC_zero hδ₁0 (hn' j₀)]
    · show swapC (swapC (t 0) (t' 0) (t j₀)) (t' j₀) (swapC (t 0) (t' 0) (t i)) = t' i
      by_cases hi : t i = t 0
      · rw [hi, swapC_left, swapC_of_ne (Ne.symm hαα') (Ne.symm hj₀')]
        rcases eq_zero_or_pairing_of_eq m t hpat hnc'' i hi with h | h
        · rw [h]
        · rw [h, ← hpat' 0]
      · have hiδ : t i = t j₀ := eq_of_ne_zero m t hpat i j₀ hi hj₀
        have hi' : t' i ≠ t' 0 := by
          intro h
          rcases eq_zero_or_pairing_of_eq m t' hpat' hnc' i h with h | h
          · exact hi (by rw [h])
          · exact hi (by rw [h, ← hpat 0])
        have hiδ' : t' i = t' j₀ := eq_of_ne_zero m t' hpat' i j₀ hi' hj₀'
        rw [hiδ, hiδ', swapC_left]

end Perm

section Combine

/-- An edge with an end in `X` lies inside `X` or on its boundary. -/
theorem mem_edgesIn_or_bd {X : Finset ℕ} {e : ℕ} (he : e ∈ Γ.Es) {i : Fin 2}
    (hi : Γ.ends e i ∈ X) : e ∈ Γ.edgesIn X ∨ e ∈ Γ.bd X := by
  by_cases h : ∀ j, Γ.ends e j ∈ X
  · exact Or.inl (mem_edgesIn.mpr ⟨he, h⟩)
  · refine Or.inr (mem_bd.mpr ⟨he, fun hiff ↦ h fun j ↦ ?_⟩)
    have hi0 : i = 0 ∨ i = 1 := by omega
    have hj0 : j = 0 ∨ j = 1 := by omega
    rcases hi0 with rfl | rfl <;> rcases hj0 with rfl | rfl
    · exact hi
    · exact hiff.mp hi
    · exact hiff.mpr hi
    · exact hi

/-- **Combining colourings of the two sides.**  If a closed graph is cut by a `4`-edge-cut and
the two poles have colourings with boundary vectors of the same type, the graph is colourable. -/
theorem colourable_of_same_type (hcl : Γ.IsClosed) {X : Finset ℕ} (hP : (Γ.pole X).IsPole4)
    (hP' : (Γ.pole (Γ.Vs \ X)).IsPole4) {c c' : ℕ → Color} (hc : (Γ.pole X).IsColouring c)
    (hc' : (Γ.pole (Γ.Vs \ X)).IsColouring c')
    (h : ptype (tvec hP c) = ptype (tvec hP' c')) : Γ.Colourable := by
  obtain ⟨σ, hσinj, hσ0, hσ⟩ := exists_perm _ _ (tvec_valid hP hc) (tvec_valid hP' hc')
    (tvec_nonzero hP hc) (tvec_nonzero hP' hc') h
  have hbd : ∀ i, bdEmb hP i = bdEmb hP' i :=
    bdEmb_congr hP hP' (by rw [dangling_pole, dangling_pole, bd_compl hcl])
  -- the two colourings agree on the boundary after relabelling
  have hagree : ∀ e ∈ Γ.bd X, σ (c e) = c' e := by
    intro e he
    obtain ⟨i, hi⟩ := exists_bdEmb_eq hP (by rw [dangling_pole]; exact he)
    have := hσ i
    unfold tvec at this
    rw [hi, ← hbd i, hi] at this
    exact this
  refine ⟨fun e ↦ if e ∈ Γ.edgesIn X ∪ Γ.bd X then σ (c e) else c' e, fun e he ↦ ?_,
    fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  · dsimp only
    split_ifs with hmem
    · intro h0
      have := hc.1 e hmem
      rw [← hσ0] at h0
      exact this (hσinj h0)
    · have hmem' : e ∈ Γ.edgesIn (Γ.Vs \ X) ∪ Γ.bd (Γ.Vs \ X) := by
        rw [Finset.mem_union, mem_edgesIn]
        refine Or.inl ⟨he, fun i ↦ Finset.mem_sdiff.mpr ⟨hcl e he i, fun hi ↦ hmem ?_⟩⟩
        exact Finset.mem_union.mpr (mem_edgesIn_or_bd he hi)
      exact hc'.1 e hmem'
  · have h₁' := mem_halfEdgesIn.mp h₁m
    have h₂' := mem_halfEdgesIn.mp h₂m
    by_cases hvX : v ∈ X
    · have m₁ : h₁ ∈ (Γ.pole X).halfEdgesIn (Γ.pole X).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₁'.1 (h₁'.2 ▸ hvX), h₁'.2⟩
      have m₂ : h₂ ∈ (Γ.pole X).halfEdgesIn (Γ.pole X).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₂'.1 (h₂'.2 ▸ hvX), h₂'.2⟩
      have e₁ : h₁.1 ∈ Γ.edgesIn X ∪ Γ.bd X := (mem_halfEdgesIn.mp m₁).1
      have e₂ : h₂.1 ∈ Γ.edgesIn X ∪ Γ.bd X := (mem_halfEdgesIn.mp m₂).1
      dsimp only at heq
      rw [if_pos e₁, if_pos e₂] at heq
      exact hc.unique_halfEdge hvX m₁ m₂ (hσinj heq)
    · have hvX' : v ∈ Γ.Vs \ X := Finset.mem_sdiff.mpr ⟨hv, hvX⟩
      have m₁ : h₁ ∈ (Γ.pole (Γ.Vs \ X)).halfEdgesIn (Γ.pole (Γ.Vs \ X)).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₁'.1 (h₁'.2 ▸ hvX'), h₁'.2⟩
      have m₂ : h₂ ∈ (Γ.pole (Γ.Vs \ X)).halfEdgesIn (Γ.pole (Γ.Vs \ X)).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₂'.1 (h₂'.2 ▸ hvX'), h₂'.2⟩
      -- on the edges at `v`, the combined colouring is `c'`
      have key : ∀ h ∈ Γ.halfEdgesIn Γ.Es v,
          (if h.1 ∈ Γ.edgesIn X ∪ Γ.bd X then σ (c h.1) else c' h.1) = c' h.1 := by
        intro h hm
        have hm' := mem_halfEdgesIn.mp hm
        split_ifs with hmem
        · rw [Finset.mem_union] at hmem
          rcases hmem with hmem | hmem
          · exact absurd ((mem_edgesIn.mp hmem).2 h.2) (hm'.2 ▸ hvX)
          · exact hagree _ hmem
        · rfl
      dsimp only at heq
      rw [key h₁ h₁m, key h₂ h₂m] at heq
      exact hc'.unique_halfEdge hvX' m₁ m₂ heq

/-- The type sets of the two sides of a cut of an uncolourable graph are disjoint. -/
theorem types_disjoint (hcl : Γ.IsClosed) (hnc : ¬ Γ.Colourable) {X : Finset ℕ}
    (hP : (Γ.pole X).IsPole4) (hP' : (Γ.pole (Γ.Vs \ X)).IsPole4) :
    ∀ τ ∈ types hP, τ ∉ types hP' := by
  intro τ hτ hτ'
  obtain ⟨t, ⟨c, hc, rfl⟩, rfl⟩ := (mem_types hP).mp hτ
  obtain ⟨t', ⟨c', hc', rfl⟩, h⟩ := (mem_types hP').mp hτ'
  exact hnc (colourable_of_same_type hcl hP hP' hc hc' h.symm)

/-- **Chladný–Škoviera, Proposition 3.5.**  If a closed cubic uncolourable graph is cut by a
`4`-edge-cut into two colourable poles, then for a unique pairing one pole is isochromatic and
the other heterochromatic. -/
theorem exists_pairing (hcl : Γ.IsClosed) (hnc : ¬ Γ.Colourable) {X : Finset ℕ}
    (hP : (Γ.pole X).IsPole4) (hP' : (Γ.pole (Γ.Vs \ X)).IsPole4)
    (hM : (Γ.pole X).Colourable) (hN : (Γ.pole (Γ.Vs \ X)).Colourable) :
    ∃ m, (IsoWith hP m ∧ HetWith hP' m) ∨ (HetWith hP m ∧ IsoWith hP' m) := by
  have hsplit := types_split (types hP) (types hP') ⟨types_disjoint hcl hnc hP hP',
    types_nonempty hP hM, types_nonempty hP' hN, two_types hP hM, two_types hP' hN⟩
  obtain ⟨m, hm⟩ := hsplit
  refine ⟨m, ?_⟩
  have iso : ∀ {Γ' : FinGraph} (hQ : Γ'.IsPole4), (∀ τ ∈ types hQ, τ ∈ isoTypes m) →
      IsoWith hQ m := by
    intro Γ' hQ h t ht
    exact (valid_iso_iff t (Col.valid hQ ht) m).mpr (h _ ((mem_types hQ).mpr ⟨t, ht, rfl⟩))
  have het : ∀ {Γ' : FinGraph} (hQ : Γ'.IsPole4), (∀ τ ∈ types hQ, τ ∈ hetTypes m) →
      HetWith hQ m := by
    intro Γ' hQ h t ht
    exact (valid_het_iff t (Col.valid hQ ht) m).mpr (h _ ((mem_types hQ).mpr ⟨t, ht, rfl⟩))
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨iso hP h1, het hP' h2⟩
  · exact Or.inr ⟨het hP h2, iso hP' h1⟩

end Combine

section Unique

theorem const_of_iso_iso (m m' : Fin 3) (t : Fin 4 → Color) (hmm : m ≠ m')
    (h1 : ∀ i, t i = t (pairing m i)) (h2 : ∀ i, t i = t (pairing m' i)) : ∀ i, t i = t 0 := by
  revert m m' t
  decide

theorem ptype_of_iso_het (m m' : Fin 3) (t : Fin 4 → Color) (hv : Valid t)
    (h1 : ∀ i, t i = t (pairing m i)) (h2 : ∀ i, t i ≠ t (pairing m' i)) : ptype t = some m := by
  revert m m' t
  decide

/-- The third pairing. -/
def third (m m' : Fin 3) : Fin 3 := if m = 0 then (if m' = 1 then 2 else 1) else
  if m = 1 then (if m' = 0 then 2 else 0) else (if m' = 0 then 1 else 0)

theorem ptype_of_het_het (m m' : Fin 3) (t : Fin 4 → Color) (hv : Valid t) (hmm : m ≠ m')
    (h1 : ∀ i, t i ≠ t (pairing m i)) (h2 : ∀ i, t i ≠ t (pairing m' i)) :
    ptype t = some (third m m') := by
  revert m m' t
  decide

/-- Two colourings of a colourable pole have distinct types for some pair. -/
theorem exists_two_types (hP : Γ.IsPole4) (hcol : Γ.Colourable) :
    ∃ t ∈ Col hP, ∃ t' ∈ Col hP, ptype t ≠ ptype t' := by
  obtain ⟨c, hc⟩ := hcol
  obtain ⟨t', ht', hne⟩ := exists_other_type hP hc
  exact ⟨tvec hP c, ⟨c, hc, rfl⟩, t', ht', hne.symm⟩

theorem IsoWith.unique (hP : Γ.IsPole4) (hcol : Γ.Colourable) {m m' : Fin 3}
    (h1 : IsoWith hP m) (h2 : IsoWith hP m') : m = m' := by
  by_contra hmm
  obtain ⟨t, ht, t', ht', hne⟩ := exists_two_types hP hcol
  apply hne
  rw [(ptype_none_iff t).mpr (const_of_iso_iso m m' t hmm (h1 t ht) (h2 t ht)),
    (ptype_none_iff t').mpr (const_of_iso_iso m m' t' hmm (h1 t' ht') (h2 t' ht'))]

theorem HetWith.unique (hP : Γ.IsPole4) (hcol : Γ.Colourable) {m m' : Fin 3}
    (h1 : HetWith hP m) (h2 : HetWith hP m') : m = m' := by
  by_contra hmm
  obtain ⟨t, ht, t', ht', hne⟩ := exists_two_types hP hcol
  apply hne
  rw [ptype_of_het_het m m' t (Col.valid hP ht) hmm (h1 t ht) (h2 t ht),
    ptype_of_het_het m m' t' (Col.valid hP ht') hmm (h1 t' ht') (h2 t' ht')]

theorem not_isoWith_hetWith (hP : Γ.IsPole4) (hcol : Γ.Colourable) {m m' : Fin 3}
    (h1 : IsoWith hP m) (h2 : HetWith hP m') : False := by
  obtain ⟨t, ht, t', ht', hne⟩ := exists_two_types hP hcol
  apply hne
  rw [ptype_of_iso_het m m' t (Col.valid hP ht) (h1 t ht) (h2 t ht),
    ptype_of_iso_het m m' t' (Col.valid hP ht') (h1 t' ht') (h2 t' ht')]

end Unique

end FinGraph
end GraphPuzzles
