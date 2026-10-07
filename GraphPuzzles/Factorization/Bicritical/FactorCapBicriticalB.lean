import GraphPuzzles.Factorization.Bicritical.FactorCapBicriticalA

/-!
# Bicriticality of the cap factor, II: the non-adjacent case

For a cut edge `d` with outer end `y`, and a vertex `x` of the shore not adjacent to the new
vertex attached to `d`, any colouring of the pole avoiding `x` and `y` colours the couple not
containing `d` with two distinct colours: otherwise the join factor would be colourable
(Chladný–Škoviera, Theorem 4.8, Case 2).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Couples

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

theorem eq_partner_of_couple₁ {a d : ℕ} (ha : a ∈ couple₁ hP m) (hd : d ∈ couple₁ hP m)
    (hne : a ≠ d) : a = partner hP m d := by
  rw [couple₁, Finset.mem_insert, Finset.mem_singleton] at ha hd
  rcases ha with rfl | rfl <;> rcases hd with rfl | rfl
  · exact absurd rfl hne
  · rw [partner_bdEmb, pairing_involutive]
  · rw [partner_bdEmb]
  · exact absurd rfl hne

theorem eq_partner_of_couple₂ {a d : ℕ} (ha : a ∈ couple₂ hP m) (hd : d ∈ couple₂ hP m)
    (hne : a ≠ d) : a = partner hP m d := by
  rw [couple₂, Finset.mem_insert, Finset.mem_singleton] at ha hd
  rcases ha with rfl | rfl <;> rcases hd with rfl | rfl
  · exact absurd rfl hne
  · rw [partner_bdEmb, pairing_involutive]
  · rw [partner_bdEmb]
  · exact absurd rfl hne

theorem newHalf_fst_of_couple₁ {k : Fin 4} (hk : bdEmb hP k ∈ couple₁ hP m) :
    (newHalf (P := P) m k).1 = freshE P := by
  rw [couple₁, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with hk | hk
  · rw [bdEmb_injective hP hk, newHalf_zero]
  · rw [bdEmb_injective hP hk, newHalf_pairing_zero]

theorem newHalf_fst_of_couple₂ {k : Fin 4} (hk : bdEmb hP k ∈ couple₂ hP m) :
    (newHalf (P := P) m k).1 = freshE P + 1 := by
  rw [couple₂, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with hk | hk
  · rw [bdEmb_injective hP hk, newHalf_other]
  · rw [bdEmb_injective hP hk, newHalf_pairing_other]

end Couples

section Nonadjacent

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hcub : Δ.IsCubic)
  (hg5 : Δ.Girth5) (hY : Y ⊆ Δ.Vs) (hind : Δ.IsIndependentCut Y)
  (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)
  (hhet : HetWith hPYc m)
include hcl hcub hg5 hY hind hhet

omit hY in
/-- **The non-adjacent case.** -/
theorem other_couple_ne_of_nonadjacent {d x : ℕ} (hd : d ∈ Δ.bd Y) (hx : x ∈ Y)
    (hx₁ : x ≠ innerEnd hPY d) (hx₂ : x ≠ innerEnd hPY (partner hPY m d)) {c : ℕ → Color}
    (hc : (Δ.pole (Δ.Vs \ {x, innerEnd hPYc d})).IsColouring c) :
    (d ∈ couple₁ hPY m → c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m)))) ∧
      (d ∉ couple₁ hPY m → c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0))) := by
  classical
  have hloop : ∀ e ∈ Δ.Es, Δ.ends e 0 ≠ Δ.ends e 1 := fun e he ↦ hg5.no_loop he (hcl e he 0)
  have hemb : ∀ k, bdEmb hPY k = bdEmb hPYc k := bdEmb_eq_compl hcl hPY hPYc
  set y := innerEnd hPYc d with hydef
  set W := Δ.Vs \ {x, y} with hWdef
  have hyV : y ∈ Δ.Vs \ Y := innerEnd_compl_mem hcl hPYc hd
  have hxy : x ≠ y := fun h ↦ (Finset.mem_sdiff.mp hyV).2 (h ▸ hx)
  have hdE : d ∈ Δ.Es := bd_subset Y hd
  have hdc : d ∈ Δ.bd (Δ.Vs \ Y) := by rw [bd_compl hcl]; exact hd
  have hindc : Δ.IsIndependentCut (Δ.Vs \ Y) := hind.compl hcl
  have hdd : d ∈ (Δ.pole Y).dangling := mem_dangling_Y hd
  have hpd : partner hPY m d ∈ Δ.bd Y := by
    have := partner_mem hPY m hdd
    rw [dangling_pole] at this; exact this
  have hpdne : partner hPY m d ≠ d := partner_ne hPY m hdd
  obtain ⟨jy, hjy⟩ := ends_innerEnd_compl hcl hPYc hd
  -- the two other edges at `y` and the boundary of `(Vs \ Y).erase y`
  obtain ⟨g₁, g₂, hg₁, hg₂, h12, h1d, h2d, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, hbd⟩ :=
    bd_erase_of_cut hcub hloop Finset.sdiff_subset hindc hdc (j := jy) (hjy ▸ hyV)
  rw [hjy] at hi₁ hi₂ hbd
  rw [bd_compl hcl] at hbd
  have hg₁E : g₁ ∈ Δ.Es := edgesIn_subset _ hg₁
  have hg₂E : g₂ ∈ Δ.Es := edgesIn_subset _ hg₂
  have hall : ∀ e ∈ Δ.Es, ∀ j, Δ.ends e j = y → e = d ∨ e = g₁ ∨ e = g₂ := by
    obtain ⟨x₃, hx₃, ⟨k, hk⟩, h31, h32, hall'⟩ :=
      third_edge hcub hloop (Finset.mem_sdiff.mp hyV).1 hg₁E hg₂E h12 hi₁ hi₂
    have hd3 : d = x₃ := by
      rcases hall' d hdE jy hjy with h | h | h
      · exact absurd h.symm h1d
      · exact absurd h.symm h2d
      · exact h
    intro e he j hj
    rcases hall' e he j hj with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (h.trans hd3.symm)
  -- the other ends of `g₁`, `g₂` lie in `W`
  have hother : ∀ g ∈ Δ.edgesIn (Δ.Vs \ Y), ∀ i, Δ.ends g i = y → g ∈ (Δ.pole W).Es := by
    intro g hg i hi
    rw [mem_edgesIn] at hg
    have hne : Δ.ends g (Fin.rev i) ≠ y := by
      intro h
      have := idx_eq_of_ends_eq hloop hg.1 (h.trans hi.symm)
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hi0 with rfl | rfl <;> simp at this
    rw [pole_Es, Finset.mem_union]
    apply mem_edgesIn_or_bd hg.1 (i := Fin.rev i)
    have := hg.2 (Fin.rev i)
    rw [Finset.mem_sdiff] at this
    rw [hWdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨this.1, by rintro (h | h); exact this.2 (h ▸ hx); exact hne h⟩
  have hg₁W : g₁ ∈ (Δ.pole W).Es := hother g₁ hg₁ i₁ hi₁
  have hg₂W : g₂ ∈ (Δ.pole W).Es := hother g₂ hg₂ i₂ hi₂
  -- the parity of the pole `(Vs \ Y).erase y`
  have hsub : (Δ.Vs \ Y).erase y ⊆ W := by
    intro v hv
    rw [Finset.mem_erase, Finset.mem_sdiff] at hv
    rw [hWdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hv.2.1, by rintro (rfl | rfl); exact hv.2.2 hx; exact hv.1 rfl⟩
  have hsum := (hc.restrict hsub).sum_bd_eq_zero hcub
    ((Finset.erase_subset y _).trans Finset.sdiff_subset)
  have hg₁bd : g₁ ∉ Δ.bd Y := fun h ↦
    Finset.disjoint_left.mp (disjoint_edgesIn_bd (Δ.Vs \ Y)) hg₁ (by rw [bd_compl hcl]; exact h)
  have hg₂bd : g₂ ∉ Δ.bd Y := fun h ↦
    Finset.disjoint_left.mp (disjoint_edgesIn_bd (Δ.Vs \ Y)) hg₂ (by rw [bd_compl hcl]; exact h)
  rw [hbd, Finset.sum_insert (by
      rw [Finset.mem_insert, Finset.mem_erase]; rintro (h | ⟨-, h⟩); exact h12 h; exact hg₁bd h),
    Finset.sum_insert (by rw [Finset.mem_erase]; rintro ⟨-, h⟩; exact hg₂bd h)] at hsum
  have htot := Finset.add_sum_erase (Δ.bd Y) c hd
  rw [sum_bd_four m hPY] at htot
  -- the cut edges other than `d` are edges of the pole `W`
  have hcut : ∀ a ∈ Δ.bd Y, a ≠ d → a ∈ (Δ.pole W).Es :=
    fun a ha had ↦ cut_mem_pole hcl hPYc hind hd ha had hx
  -- the position of `d`
  obtain ⟨kd, hkd⟩ := exists_bdEmb_eq hPYc (mem_dangling_compl hcl hd)
  have hkd' : bdEmb hPY kd = d := by rw [hemb]; exact hkd
  -- the new half-edges at `y` all come from `d`
  have hnewy : ∀ h ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es y,
      (h.1 = freshE (Δ.pole (Δ.Vs \ Y)) ∨ h.1 = freshE (Δ.pole (Δ.Vs \ Y)) + 1) →
      h = newHalf (P := Δ.pole (Δ.Vs \ Y)) m kd := by
    intro h hh hnew
    rw [mem_halfEdgesIn] at hh
    have hjoin : (join hPYc m).ends h.1 h.2 =
        innerEnd hPYc (bdEmb hPYc (newPos (Δ.pole (Δ.Vs \ Y)) m h)) := by
      conv_lhs => rw [← newHalf_newPos m h hnew]
      exact join_ends_newHalf hPYc m _
    rw [hh.2] at hjoin
    have hbk : bdEmb hPYc (newPos (Δ.pole (Δ.Vs \ Y)) m h) ∈ Δ.bd Y := by
      rw [← bd_compl hcl, ← dangling_pole]; exact bdEmb_mem hPYc _
    have := innerEnd_compl_inj hcl hPYc hind hbk hd hjoin.symm
    rw [← hkd] at this
    rw [← newHalf_newPos m h hnew, bdEmb_injective hPYc this]
  -- the old half-edges at `y` are the two other edges
  have holdy : ∀ h ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es y,
      ¬ (h.1 = freshE (Δ.pole (Δ.Vs \ Y)) ∨ h.1 = freshE (Δ.pole (Δ.Vs \ Y)) + 1) →
      h.1 ∈ (Δ.pole (Δ.Vs \ Y)).Es ∧ (h.1 = g₁ ∨ h.1 = g₂) ∧ Δ.ends h.1 h.2 = y := by
    intro h hh hnew
    rw [mem_halfEdgesIn, join_Es, Finset.mem_insert, Finset.mem_insert] at hh
    obtain ⟨he, hend⟩ := hh
    rcases he with h1 | h1 | h1
    · exact absurd (Or.inl h1) hnew
    · exact absurd (Or.inr h1) hnew
    · rw [Finset.mem_sdiff] at h1
      rw [join_ends_old hPYc m h1.1] at hend
      have hend' : Δ.ends h.1 h.2 = y := hend
      refine ⟨h1.1, ?_, hend'⟩
      have heΔ : h.1 ∈ Δ.Es := by
        rw [pole_Es, Finset.mem_union] at h1
        exact h1.1.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
      rcases hall h.1 heΔ h.2 hend' with h2 | h2 | h2
      · exact absurd (h2 ▸ mem_dangling_compl hcl hd) h1.2
      · exact Or.inl h2
      · exact Or.inr h2
  -- properness at `y`, given the colour of the new edge at `y` and the parity identity
  have hspy : ∀ γ₁ γ₂ : Color,
      joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m kd).1 =
        c (partner hPY m d) →
      c g₁ + c g₂ + c (partner hPY m d) = 0 →
      ∀ h₁ ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es y,
      ∀ h₂ ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es y,
      joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ h₁.1 = joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ h₂.1 →
      h₁ = h₂ := by
    intro γ₁ γ₂ hnewcol hsum3 h₁ h₁m h₂ h₂m heq
    have hn1 : c g₁ ≠ 0 := hc.1 g₁ hg₁W
    have hn2 : c g₂ ≠ 0 := hc.1 g₂ hg₂W
    have hnp : c (partner hPY m d) ≠ 0 := hc.1 _ (hcut _ hpd hpdne)
    have h12c : c g₁ ≠ c g₂ := by
      apply ne_of_add_three_eq_zero hnp hn1 hn2
      linear_combination hsum3
    have h1p : c g₁ ≠ c (partner hPY m d) := by
      apply ne_of_add_three_eq_zero hn2 hn1 hnp
      linear_combination hsum3
    have h2p : c g₂ ≠ c (partner hPY m d) := by
      apply ne_of_add_three_eq_zero hn1 hn2 hnp
      linear_combination hsum3
    by_cases hn₁ : h₁.1 = freshE (Δ.pole (Δ.Vs \ Y)) ∨ h₁.1 = freshE (Δ.pole (Δ.Vs \ Y)) + 1 <;>
      by_cases hn₂ : h₂.1 = freshE (Δ.pole (Δ.Vs \ Y)) ∨ h₂.1 = freshE (Δ.pole (Δ.Vs \ Y)) + 1
    · rw [hnewy h₁ h₁m hn₁, hnewy h₂ h₂m hn₂]
    · exfalso
      rw [hnewy h₁ h₁m hn₁, hnewcol] at heq
      obtain ⟨he₂, hg, -⟩ := holdy h₂ h₂m hn₂
      rw [joinCol_old he₂] at heq
      rcases hg with hg | hg <;> rw [hg] at heq
      · exact h1p heq.symm
      · exact h2p heq.symm
    · exfalso
      rw [hnewy h₂ h₂m hn₂, hnewcol] at heq
      obtain ⟨he₁, hg, -⟩ := holdy h₁ h₁m hn₁
      rw [joinCol_old he₁] at heq
      rcases hg with hg | hg <;> rw [hg] at heq
      · exact h1p heq
      · exact h2p heq
    · obtain ⟨he₁, hg₁', hend₁⟩ := holdy h₁ h₁m hn₁
      obtain ⟨he₂, hg₂', hend₂⟩ := holdy h₂ h₂m hn₂
      rw [joinCol_old he₁, joinCol_old he₂] at heq
      have hsame : h₁.1 = h₂.1 := by
        rcases hg₁' with hg₁' | hg₁' <;> rcases hg₂' with hg₂' | hg₂' <;>
          rw [hg₁', hg₂'] at heq ⊢ <;>
          first
          | rfl
          | exact absurd heq h12c
          | exact absurd heq.symm h12c
      obtain ⟨e₁, i₁'⟩ := h₁
      obtain ⟨e₂, i₂'⟩ := h₂
      simp only at hsame hend₁ hend₂
      subst hsame
      have heΔ : e₁ ∈ Δ.Es := by
        rw [pole_Es, Finset.mem_union] at he₁
        exact he₁.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
      rw [idx_eq_of_ends_eq hloop heΔ (hend₁.trans hend₂.symm)]
  -- the edges inside `Vs \ Y` with an end outside `W` would be loops at `y`
  have hnz : ∀ e ∈ (Δ.pole (Δ.Vs \ Y)).Es \ (Δ.pole (Δ.Vs \ Y)).dangling,
      (∀ i, Δ.ends e i ∈ Δ.Vs \ Y → Δ.ends e i ∉ W) → c e ≠ 0 := by
    intro e he hall'
    exfalso
    rw [Finset.mem_sdiff, dangling_pole, pole_Es, Finset.mem_union] at he
    have hin : e ∈ Δ.edgesIn (Δ.Vs \ Y) := he.1.resolve_right he.2
    rw [mem_edgesIn] at hin
    have hy' : ∀ i, Δ.ends e i = y := by
      intro i
      have := hall' i (hin.2 i)
      rw [hWdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at this
      push Not at this
      rcases this (hin.2 i |> Finset.mem_sdiff.mp |>.1) with h | h
      · exact absurd (h ▸ hx) (Finset.mem_sdiff.mp (hin.2 i)).2
      · exact h
    exact hloop e hin.1 ((hy' 0).trans (hy' 1).symm)
  -- the vertices of `Vs \ Y` outside `W` are `y`
  have hspv : ∀ v ∈ Δ.Vs \ Y, v ∉ W → v = y := by
    intro v hv hvW
    rw [hWdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hvW
    push Not at hvW
    rcases hvW (Finset.mem_sdiff.mp hv).1 with h | h
    · exact absurd (h ▸ hv) (fun h' ↦ (Finset.mem_sdiff.mp h').2 hx)
    · exact h
  -- the colouring of the join contradicts heterochromaticity
  have hjoin : ∀ γ₁ γ₂ : Color, γ₁ ≠ 0 → γ₂ ≠ 0 →
      (∀ k, (k = 0 ∨ k = pairing m 0) → innerEnd hPYc (bdEmb hPYc k) ∈ Δ.Vs \ Y →
        innerEnd hPYc (bdEmb hPYc k) ∈ W → c (bdEmb hPYc k) = γ₁) →
      (∀ k, (k = other m ∨ k = pairing m (other m)) → innerEnd hPYc (bdEmb hPYc k) ∈ Δ.Vs \ Y →
        innerEnd hPYc (bdEmb hPYc k) ∈ W → c (bdEmb hPYc k) = γ₂) →
      joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m kd).1 =
        c (partner hPY m d) →
      c g₁ + c g₂ + c (partner hPY m d) = 0 → False := by
    intro γ₁ γ₂ hγ₁ hγ₂ hc₁ hc₂ hnewcol hsum3
    apply not_colourable_join_of_hetWith hPYc m hhet
    refine ⟨joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂, ?_⟩
    rw [IsClosed.isColouring_iff (join_isClosed hPYc m)]
    refine join_colouring hPYc m hc (Z := Δ.Vs \ Y) subset_rfl hγ₁ hγ₂ hc₁ hc₂ ?_ hnz
    intro v hv hvW
    rw [hspv v hv hvW]
    exact hspy γ₁ γ₂ hnewcol hsum3
  have hneq_d : ∀ k, innerEnd hPYc (bdEmb hPYc k) ∈ W → bdEmb hPY k ≠ d := by
    intro k hk h
    rw [hemb] at h
    rw [h] at hk
    rw [hWdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hk
    exact hk.2 (Or.inr rfl)
  refine ⟨fun hd₁ heq ↦ ?_, fun hd₁ heq ↦ ?_⟩
  · -- `d` in the first couple: the new edge at `y` is the first new edge
    have hkd₁ : bdEmb hPYc kd ∈ couple₁ hPYc m := by
      rw [hkd, couple₁, ← hemb, ← hemb]; exact hd₁
    have hβ : c (bdEmb hPY (other m)) ≠ 0 :=
      hc.1 _ (hcut _ (by rw [← dangling_pole]; exact bdEmb_mem hPY _)
        (fun h ↦ bdEmb_other_notMem_couple₁ m hPY (h ▸ hd₁)))
    have hγ₁ : c (partner hPY m d) ≠ 0 := hc.1 _ (hcut _ hpd hpdne)
    apply hjoin (c (partner hPY m d)) (c (bdEmb hPY (other m))) hγ₁ hβ
    · intro k hk hZ hW'
      have hne := hneq_d k hW'
      rw [← hemb]
      congr 1
      apply eq_partner_of_couple₁ hPY m _ hd₁ hne
      rw [couple₁, Finset.mem_insert, Finset.mem_singleton]
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro k hk _ _
      rw [← hemb]
      rcases hk with rfl | rfl
      · rfl
      · exact heq.symm
    · rw [newHalf_fst_of_couple₁ hPYc m hkd₁, joinCol_new₁]
    · rw [couple₁, Finset.mem_insert, Finset.mem_singleton] at hd₁
      rcases hd₁ with rfl | rfl
      · rw [partner_bdEmb]
        linear_combination hsum - htot - heq -
          color_add_self (c (bdEmb hPY (pairing m (other m))))
      · rw [partner_bdEmb, pairing_involutive]
        linear_combination hsum - htot - heq -
          color_add_self (c (bdEmb hPY (pairing m (other m))))
  · -- `d` in the second couple
    have hd₂ : d ∈ couple₂ hPY m := (mem_couple₂_iff hPY m hdd).mpr hd₁
    have hkd₂ : bdEmb hPYc kd ∈ couple₂ hPYc m := by
      rw [hkd, couple₂, ← hemb, ← hemb]; exact hd₂
    have hβ : c (bdEmb hPY 0) ≠ 0 :=
      hc.1 _ (hcut _ (by rw [← dangling_pole]; exact bdEmb_mem hPY _)
        (fun h ↦ hd₁ (h ▸ Finset.mem_insert_self _ _)))
    have hγ₂ : c (partner hPY m d) ≠ 0 := hc.1 _ (hcut _ hpd hpdne)
    apply hjoin (c (bdEmb hPY 0)) (c (partner hPY m d)) hβ hγ₂
    · intro k hk _ _
      rw [← hemb]
      rcases hk with rfl | rfl
      · rfl
      · exact heq.symm
    · intro k hk hZ hW'
      have hne := hneq_d k hW'
      rw [← hemb]
      congr 1
      apply eq_partner_of_couple₂ hPY m _ hd₂ hne
      rw [couple₂, Finset.mem_insert, Finset.mem_singleton]
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [newHalf_fst_of_couple₂ hPYc m hkd₂, joinCol_new₂]
    · rw [couple₂, Finset.mem_insert, Finset.mem_singleton] at hd₂
      rcases hd₂ with rfl | rfl
      · rw [partner_bdEmb]
        linear_combination hsum - htot - heq - color_add_self (c (bdEmb hPY (pairing m 0)))
      · rw [partner_bdEmb, pairing_involutive]
        linear_combination hsum - htot - heq - color_add_self (c (bdEmb hPY (pairing m 0)))

end Nonadjacent

end FinGraph
end GraphPuzzles
