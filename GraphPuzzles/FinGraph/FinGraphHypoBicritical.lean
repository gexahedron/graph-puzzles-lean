import GraphPuzzles.FinGraph.FinGraphCycleCut

/-!
# Hypohamiltonian cubic graphs are bicritical

For distinct `x`, `y`, a Hamilton cycle of `Γ - x` through `y`, minus the two edges at `y`, is
a Hamilton path of `Γ - {x, y}`; colour it alternately, give the two edges at `y` (dangling in
the pole) the colours missing at their inner ends, and the third colour to everything else.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- **Hypohamiltonian cubic graphs are bicritical.** -/
theorem IsHypohamiltonian.isBicritical (_hcl : Γ.IsClosed) (hcub : Γ.IsCubic)
    (h4 : 4 ≤ Γ.Vs.card) (hH : Γ.IsHypohamiltonian) : Γ.IsBicritical := by
  classical
  intro x hx y hy hxy
  obtain ⟨C, hC⟩ := hH.2 x hx
  have hS3 : 3 ≤ (Γ.Vs.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
  have hloop := hC.no_loop (by omega)
  have hCE : C ⊆ Γ.Es := hC.subset.trans (edgesIn_subset _)
  have hyS : y ∈ Γ.Vs.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  -- the two edges of `C` at `y`
  obtain ⟨e₁, i₁, e₂, i₂, hne, hset⟩ := halfEdges_two (hC.deg y hyS)
  have hm₁ : (e₁, i₁) ∈ Γ.halfEdgesIn C y := by rw [hset]; exact Finset.mem_insert_self _ _
  have hm₂ : (e₂, i₂) ∈ Γ.halfEdgesIn C y := by
    rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [mem_halfEdgesIn] at hm₁ hm₂
  dsimp only at hm₁ hm₂
  obtain ⟨he₁, hi₁⟩ := hm₁
  obtain ⟨he₂, hi₂⟩ := hm₂
  have he12 : e₁ ≠ e₂ := by
    rintro rfl
    exact hne (Prod.ext rfl (idx_eq_of_ends_eq_single (hloop e₁ he₁) (hi₁.trans hi₂.symm)))
  -- an edge of `C` at `y` is `e₁` or `e₂`
  have haty : ∀ f ∈ C, ∀ j, Γ.ends f j = y → f = e₁ ∨ f = e₂ := by
    intro f hf j hj
    have : (f, j) ∈ Γ.halfEdgesIn C y := mem_halfEdgesIn.mpr ⟨hf, hj⟩
    rw [hset, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk.injEq] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  -- the other ends
  set y₁ := Γ.ends e₁ (Fin.rev i₁) with hy₁def
  set y₂ := Γ.ends e₂ (Fin.rev i₂) with hy₂def
  have hy₁y : y₁ ≠ y := by
    intro h
    exact fin2_rev_ne i₁ (idx_eq_of_ends_eq_single (hloop e₁ he₁) (h.trans hi₁.symm))
  have hy₂y : y₂ ≠ y := by
    intro h
    exact fin2_rev_ne i₂ (idx_eq_of_ends_eq_single (hloop e₂ he₂) (h.trans hi₂.symm))
  have hy₁S : y₁ ∈ Γ.Vs.erase x := (mem_edgesIn.mp (hC.subset he₁)).2 _
  have hy₂S : y₂ ∈ Γ.Vs.erase x := (mem_edgesIn.mp (hC.subset he₂)).2 _
  -- the ends of `e₁` are `y` and `y₁`
  have hends₁ : ∀ j, Γ.ends e₁ j = y ∨ Γ.ends e₁ j = y₁ := by
    intro j
    by_cases h : j = i₁
    · exact Or.inl (h ▸ hi₁)
    · exact Or.inr (by rw [fin2_eq_rev_of_ne h])
  have hends₂ : ∀ j, Γ.ends e₂ j = y ∨ Γ.ends e₂ j = y₂ := by
    intro j
    by_cases h : j = i₂
    · exact Or.inl (h ▸ hi₂)
    · exact Or.inr (by rw [fin2_eq_rev_of_ne h])
  -- `y₁ ≠ y₂`: otherwise `{e₁, e₂}` is the whole cycle
  have hy12 : y₁ ≠ y₂ := by
    intro h
    have hj₁ : Γ.Joins e₁ y y₁ := by
      have hi0 : i₁ = 0 ∨ i₁ = 1 := by omega
      rcases hi0 with rfl | rfl
      · exact Or.inl ⟨hi₁, by rw [hy₁def, Iso.rev_zero']⟩
      · exact Or.inr ⟨by rw [hy₁def, Iso.rev_one'], hi₁⟩
    have hj₂ : Γ.Joins e₂ y y₁ := by
      rw [h]
      have hi0 : i₂ = 0 ∨ i₂ = 1 := by omega
      rcases hi0 with rfl | rfl
      · exact Or.inl ⟨hi₂, by rw [hy₂def, Iso.rev_zero']⟩
      · exact Or.inr ⟨by rw [hy₂def, Iso.rev_one'], hi₂⟩
    have hD : ({e₁, e₂} : Finset ℕ) = C := by
      apply hC.eq_of_subset
      · intro f hf
        rw [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl <;> assumption
      · exact ⟨e₁, Finset.mem_insert_self _ _⟩
      · intro v _
        rw [degIn_eq_sum, Finset.sum_pair he12, endCount_of_joins hj₁ hy₁y.symm,
          endCount_of_joins hj₂ hy₁y.symm]
        split_ifs <;> simp
    have := hC.card_eq
    rw [← hD, Finset.card_pair he12] at this
    omega
  -- the Hamilton path
  have hconn₁ := isConnected_erase_of_cycle hC.subset hC.deg hC.connected hloop he₁
  have hdeg₁y : Γ.degIn (C.erase e₁) y = 1 := by
    have := degIn_erase_of_ends he₁ (hloop e₁ he₁) i₁
    rw [hi₁, hC.deg y hyS] at this; omega
  have he₂' : e₂ ∈ C.erase e₁ := Finset.mem_erase.mpr ⟨he12.symm, he₂⟩
  have hconnP : Γ.IsConnected ((C.erase e₁).erase e₂) :=
    isConnected_erase_pendant hconn₁ he₂' (i := i₂) (by rw [hi₂]; exact hdeg₁y)
  have hPC : (C.erase e₁).erase e₂ ⊆ C :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hPne₁ : ∀ f ∈ (C.erase e₁).erase e₂, f ≠ e₁ := fun f hf ↦
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hf)).1
  have hPne₂ : ∀ f ∈ (C.erase e₁).erase e₂, f ≠ e₂ := fun f hf ↦ (Finset.mem_erase.mp hf).1
  -- degrees on the path
  have hdegPy₁ : Γ.degIn ((C.erase e₁).erase e₂) y₁ = 1 := by
    rw [degIn_erase_of_not_ends he₂' (fun j hj ↦ ?_)]
    · have := degIn_erase_of_ends he₁ (hloop e₁ he₁) (Fin.rev i₁)
      rw [← hy₁def, hC.deg y₁ hy₁S] at this; omega
    · rcases hends₂ j with h | h
      · exact hy₁y (hj.symm.trans h)
      · exact hy12 (hj.symm.trans h)
  have hdegPy₂ : Γ.degIn ((C.erase e₁).erase e₂) y₂ = 1 := by
    have h1 : Γ.degIn (C.erase e₁) y₂ = 2 := by
      rw [degIn_erase_of_not_ends he₁ (fun j hj ↦ ?_)]
      · exact hC.deg y₂ hy₂S
      · rcases hends₁ j with h | h
        · exact hy₂y (hj.symm.trans h)
        · exact hy12 (h.symm.trans hj)
    have := degIn_erase_of_ends he₂' (hloop e₂ he₂) (Fin.rev i₂)
    rw [← hy₂def, h1] at this; omega
  -- the path avoids `y`
  have hPsub : (C.erase e₁).erase e₂ ⊆ Γ.edgesIn (Γ.Vs \ {x, y}) := by
    intro f hf
    have hfC := hPC hf
    have hfin := mem_edgesIn.mp (hC.subset hfC)
    rw [mem_edgesIn]
    refine ⟨hfin.1, fun j ↦ ?_⟩
    have hj := hfin.2 j
    rw [Finset.mem_erase] at hj
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨hj.2, ?_⟩
    rintro (h | h)
    · exact hj.1 h
    · rcases haty f hfC j h with rfl | rfl
      · exact hPne₁ f hf rfl
      · exact hPne₂ f hf rfl
  have hy₁W : y₁ ∈ Γ.Vs \ {x, y} := by
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨(Finset.mem_erase.mp hy₁S).2, ?_⟩
    rintro (h | h)
    · exact (Finset.mem_erase.mp hy₁S).1 h
    · exact hy₁y h
  have hy₂W : y₂ ∈ Γ.Vs \ {x, y} := by
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨(Finset.mem_erase.mp hy₂S).2, ?_⟩
    rintro (h | h)
    · exact (Finset.mem_erase.mp hy₂S).1 h
    · exact hy₂y h
  obtain ⟨c₂, hprop, -⟩ := exists_two_colouring ((C.erase e₁).erase e₂).card _ rfl hPsub
    (fun v hv ↦ (degIn_mono hPC v).trans (hC.deg v (by
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hv
      exact Finset.mem_erase.mpr ⟨fun h ↦ hv.2 (Or.inl h), hv.1⟩)).le)
    hconnP (fun f hf ↦ hloop f (hPC hf)) y₁ y₂ hy₁W hy₂W hy12 hdegPy₁ hdegPy₂
  -- the path edges at `y₁`, `y₂`
  obtain ⟨⟨g₁, k₁⟩, hg₁⟩ : (Γ.halfEdgesIn ((C.erase e₁).erase e₂) y₁).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdegPy₁]; omega
  obtain ⟨⟨g₂, k₂⟩, hg₂⟩ : (Γ.halfEdgesIn ((C.erase e₁).erase e₂) y₂).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdegPy₂]; omega
  rw [mem_halfEdgesIn] at hg₁ hg₂
  dsimp only at hg₁ hg₂
  refine ⟨fun f ↦ if f ∈ (C.erase e₁).erase e₂ then twoColor (c₂ f) else
    if f = e₁ then twoColor (1 - c₂ g₁) else if f = e₂ then twoColor (1 - c₂ g₂) else (1, 1),
    ?_, ?_⟩
  · intro f _
    dsimp only
    split_ifs
    · exact twoColor_ne_zero _
    · exact twoColor_ne_zero _
    · exact twoColor_ne_zero _
    · decide
  · intro v hv h₁ h₁m h₂ h₂m heq
    have hv' : v ∈ Γ.Vs \ {x, y} := hv
    rw [halfEdgesIn_pole_eq hv'] at h₁m h₂m
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hv'
    have hvS : v ∈ Γ.Vs.erase x := Finset.mem_erase.mpr ⟨fun h ↦ hv'.2 (Or.inl h), hv'.1⟩
    have hvy : v ≠ y := fun h ↦ hv'.2 (Or.inr h)
    dsimp only at heq
    rw [mem_halfEdgesIn] at h₁m h₂m
    obtain ⟨f, j⟩ := h₁
    obtain ⟨f', j'⟩ := h₂
    simp only at h₁m h₂m heq
    obtain ⟨t, jt, htE, htC, hjt, huniq⟩ := third_halfEdge hcub hv'.1 hCE (hC.deg v hvS)
    -- classification of a half-edge at `v`
    have classify : ∀ (f : ℕ) (j : Fin 2), f ∈ Γ.Es → Γ.ends f j = v →
        f ∈ (C.erase e₁).erase e₂ ∨ (f = e₁ ∧ v = y₁) ∨ (f = e₂ ∧ v = y₂) ∨ (f, j) = (t, jt) := by
      intro f j hf hj
      by_cases hfC : f ∈ C
      · by_cases hf₁ : f = e₁
        · subst hf₁
          rcases hends₁ j with h | h
          · exact absurd (hj.symm.trans h) hvy
          · exact Or.inr (Or.inl ⟨rfl, hj.symm.trans h⟩)
        · by_cases hf₂ : f = e₂
          · subst hf₂
            rcases hends₂ j with h | h
            · exact absurd (hj.symm.trans h) hvy
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, hj.symm.trans h⟩))
          · exact Or.inl (Finset.mem_erase.mpr ⟨hf₂, Finset.mem_erase.mpr ⟨hf₁, hfC⟩⟩)
      · exact Or.inr (Or.inr (Or.inr (huniq f j hf hfC hj)))
    have hpath : ∀ (f : ℕ) (j : Fin 2) (f' : ℕ) (j' : Fin 2), f ∈ (C.erase e₁).erase e₂ →
        f' ∈ (C.erase e₁).erase e₂ → Γ.ends f j = v → Γ.ends f' j' = v →
        twoColor (c₂ f) = twoColor (c₂ f') → (f, j) = (f', j') := by
      intro f j f' j' hf hf' hj hj' hcol
      by_cases hff : f = f'
      · subst hff
        rw [idx_eq_of_ends_eq_single (hloop f (hPC hf)) (hj.trans hj'.symm)]
      · exfalso
        exact hprop f hf f' hf' hff ⟨hf, hf', j, j', hj.trans hj'.symm⟩ (twoColor_inj hcol)
    -- the path edge at `y₁` is `g₁`, at `y₂` is `g₂`
    have hat₁ : ∀ (f : ℕ) (j : Fin 2), f ∈ (C.erase e₁).erase e₂ → Γ.ends f j = y₁ → f = g₁ :=
      fun f j hf hj ↦ (eq_of_degIn_eq_one hdegPy₁ hf hg₁.1 hj hg₁.2).1
    have hat₂ : ∀ (f : ℕ) (j : Fin 2), f ∈ (C.erase e₁).erase e₂ → Γ.ends f j = y₂ → f = g₂ :=
      fun f j hf hj ↦ (eq_of_degIn_eq_one hdegPy₂ hf hg₂.1 hj hg₂.2).1
    have hne₁ : ∀ f ∈ (C.erase e₁).erase e₂, f ≠ e₁ ∧ f ≠ e₂ := fun f hf ↦ ⟨hPne₁ f hf, hPne₂ f hf⟩
    have hT₁ : t ≠ e₁ := fun h ↦ htC (h ▸ he₁)
    have hT₂ : t ≠ e₂ := fun h ↦ htC (h ▸ he₂)
    have hTP : t ∉ (C.erase e₁).erase e₂ := fun h ↦ htC (hPC h)
    have hE₁P : e₁ ∉ (C.erase e₁).erase e₂ := fun h ↦ hPne₁ e₁ h rfl
    have hE₂P : e₂ ∉ (C.erase e₁).erase e₂ := fun h ↦ hPne₂ e₂ h rfl
    rcases classify f j h₁m.1 h₁m.2 with hf | ⟨hf, hv₁⟩ | ⟨hf, hv₂⟩ | hf <;>
      rcases classify f' j' h₂m.1 h₂m.2 with hf' | ⟨hf', hv₁'⟩ | ⟨hf', hv₂'⟩ | hf'
    · rw [if_pos hf, if_pos hf'] at heq
      exact hpath f j f' j' hf hf' h₁m.2 h₂m.2 heq
    · exfalso
      subst hf'
      rw [if_pos hf, if_neg hE₁P, if_pos rfl] at heq
      rw [hat₁ f j hf (h₁m.2.trans hv₁')] at heq
      exact twoColor_sub_ne _ heq.symm
    · exfalso
      subst hf'
      rw [if_pos hf, if_neg hE₂P, if_neg he12.symm, if_pos rfl] at heq
      rw [hat₂ f j hf (h₁m.2.trans hv₂')] at heq
      exact twoColor_sub_ne _ heq.symm
    · exfalso
      rw [Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_pos hf, if_neg hTP, if_neg hT₁, if_neg hT₂] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      subst hf
      rw [if_pos hf', if_neg hE₁P, if_pos rfl] at heq
      rw [hat₁ f' j' hf' (h₂m.2.trans hv₁)] at heq
      exact twoColor_sub_ne _ heq
    · subst f; subst f'
      rw [idx_eq_of_ends_eq_single (hloop e₁ he₁) (h₁m.2.trans h₂m.2.symm)]
    · exfalso
      exact hy12 (hv₁.symm.trans hv₂')
    · exfalso
      subst hf
      rw [Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_neg hE₁P, if_pos rfl, if_neg hTP, if_neg hT₁, if_neg hT₂] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      subst hf
      rw [if_pos hf', if_neg hE₂P, if_neg he12.symm, if_pos rfl] at heq
      rw [hat₂ f' j' hf' (h₂m.2.trans hv₂)] at heq
      exact twoColor_sub_ne _ heq
    · exfalso
      exact hy12 (hv₁'.symm.trans hv₂)
    · subst f; subst f'
      rw [idx_eq_of_ends_eq_single (hloop e₂ he₂) (h₁m.2.trans h₂m.2.symm)]
    · exfalso
      subst hf
      rw [Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_neg hE₂P, if_neg he12.symm, if_pos rfl, if_neg hTP, if_neg hT₁, if_neg hT₂] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      rw [Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [if_neg hTP, if_neg hT₁, if_neg hT₂, if_pos hf'] at heq
      exact twoColor_ne_third _ heq.symm
    · exfalso
      rw [Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst hf'
      rw [if_neg hTP, if_neg hT₁, if_neg hT₂, if_neg hE₁P, if_pos rfl] at heq
      exact twoColor_ne_third _ heq.symm
    · exfalso
      rw [Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst hf'
      rw [if_neg hTP, if_neg hT₁, if_neg hT₂, if_neg hE₂P, if_neg he12.symm, if_pos rfl] at heq
      exact twoColor_ne_third _ heq.symm
    · rw [hf, hf']

end FinGraph
end GraphPuzzles
