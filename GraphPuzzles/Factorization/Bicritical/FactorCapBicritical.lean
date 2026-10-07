import GraphPuzzles.Factorization.Bicritical.FactorCapBicriticalB

/-!
# The cap factor of a bicritical snark is bicritical

Chladný–Škoviera, Theorems 4.6 and 4.8 (the "`H`" side).  Pairs of old vertices use the
heterochromatic complementary pole; the pair of new vertices leaves the pole of `Y`; a new vertex
with an old one is handled by the adjacent and non-adjacent cases.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hcub : Δ.IsCubic)
  (hnc : ¬ Δ.Colourable) (hb : Δ.IsBicritical) (hg5 : Δ.Girth5) (hc4 : Δ.Cyc4Conn)
  (hY : Δ.CycSep Y) (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)
  (hhet : HetWith hPYc m)

section Pairs

include hcl hcub hb hg5 hY hhet in
omit hcub hg5 in
/-- Two old vertices. -/
theorem capPole_pair_Y {a b : ℕ} (ha : a ∈ Y) (hb' : b ∈ Y) (hab : a ≠ b) :
    ((cap hPY m).pole ((cap hPY m).Vs \ {a, b})).Colourable := by
  have hYV : Y ⊆ Δ.Vs := hY.1
  have hemb : ∀ k, bdEmb hPY k = bdEmb hPYc k := bdEmb_eq_compl hcl hPY hPYc
  obtain ⟨c, hc⟩ := hb a (hYV ha) b (hYV hb') hab
  have hcc : (Δ.pole (Δ.Vs \ Y)).IsColouring c := hc.restrict (by
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨hv.1, ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hv.2 ha
    · exact hv.2 hb')
  have ht : tvec hPYc c ∈ Col hPYc := ⟨c, hcc, rfl⟩
  have htn := Col.nonzero hPYc ht
  have htv := Col.valid hPYc ht
  have hth := hhet _ ht
  have hsum := het_sum m _ htv htn hth
  have hval : ∀ k, c (bdEmb hPY k) = tvec hPYc c k := fun k ↦ by simp [tvec, hemb]
  set u := freshV (Δ.pole Y) with hudef
  set w := freshV (Δ.pole Y) + 1 with hwdef
  have huY : u ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : w ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have hshore : ({u, w} : Finset ℕ) ∪ (Y \ {a, b}) = (cap hPY m).Vs \ {a, b} := by
    rw [cap_Vs]
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff]
    constructor
    · rintro ((rfl | rfl) | ⟨hv, hv'⟩)
      · exact ⟨Or.inl rfl, by rintro (rfl | rfl); exact huY ha; exact huY hb'⟩
      · exact ⟨Or.inr (Or.inl rfl), by rintro (rfl | rfl); exact hwY ha; exact hwY hb'⟩
      · exact ⟨Or.inr (Or.inr hv), hv'⟩
    · rintro ⟨rfl | rfl | hv, hv'⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨hv, hv'⟩
  refine ⟨capCol (Δ.pole Y) c (tvec hPYc c 0 + tvec hPYc c (pairing m 0)), ?_⟩
  rw [← hshore]
  refine cap_colouring hPY m hc (Z₀ := Y \ {a, b}) (S := {u, w}) Finset.sdiff_subset
    (fun v hv ↦ Finset.mem_sdiff.mpr ⟨hYV (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩)
    subset_rfl (add_ne_of_ne (htn 0) (htn _) (hth 0)).1 ?_ ?_
  · intro _
    rw [hval, hval]
    exact ⟨htn 0, htn _, hth 0, rfl⟩
  · intro _
    rw [hval, hval]
    exact ⟨htn _, htn _, hth _, hsum⟩

include hcl hcub hb hg5 hY in
omit hcub in
/-- The two new vertices. -/
theorem capPole_uw :
    ((cap hPY m).pole ((cap hPY m).Vs \ {freshV (Δ.pole Y), freshV (Δ.pole Y) + 1})).Colourable := by
  have hYV : Y ⊆ Δ.Vs := hY.1
  have hloop : ∀ e ∈ Δ.Es, Δ.ends e 0 ≠ Δ.ends e 1 := fun e he ↦ hg5.no_loop he (hcl e he 0)
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have hshore : (cap hPY m).Vs \ {freshV (Δ.pole Y), freshV (Δ.pole Y) + 1} = Y := by
    rw [cap_Vs]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | hv, hv'⟩
      · exact absurd (Or.inl rfl) hv'
      · exact absurd (Or.inr rfl) hv'
      · exact hv
    · intro hv
      exact ⟨Or.inr (Or.inr hv), by rintro (rfl | rfl); exact huY hv; exact hwY hv⟩
  rw [hshore]
  have h2 : 2 ≤ (Δ.Vs \ Y).card := by
    rcases hY.2.2.2.exists_loop_or_two with ⟨e, he, -, hl⟩ | h
    · exact absurd hl (hloop e he)
    · exact h
  exact (capPoleIso hPY m hcl hYV subset_rfl).symm.colourable (hb.pole_colourable hYV h2)

end Pairs

section Assemble

variable {x y : ℕ} (hx : x ∈ Y) (hy : y ∉ Y) {c : ℕ → Color}
  (hc : (Δ.pole (Δ.Vs \ {x, y})).IsColouring c)
include hY hx hy hc

/-- Assembling a colouring of the pole avoiding `u` and `x` from the second couple. -/
theorem capPole_assemble_w (h0 : c (bdEmb hPY (other m)) ≠ 0)
    (h0' : c (bdEmb hPY (pairing m (other m))) ≠ 0)
    (hne : c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m)))) :
    ((cap hPY m).pole ((cap hPY m).Vs \ {freshV (Δ.pole Y), x})).Colourable := by
  have hYV : Y ⊆ Δ.Vs := hY.1
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have hshore : ({freshV (Δ.pole Y) + 1} : Finset ℕ) ∪ Y.erase x =
      (cap hPY m).Vs \ {freshV (Δ.pole Y), x} := by
    rw [cap_Vs]
    ext v
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert]
    constructor
    · rintro (rfl | ⟨hvx, hv⟩)
      · exact ⟨Or.inr (Or.inl rfl), by rintro (h | rfl); omega; exact hwY hx⟩
      · exact ⟨Or.inr (Or.inr hv), by rintro (rfl | rfl); exact huY hv; exact hvx rfl⟩
    · rintro ⟨rfl | rfl | hv, hv'⟩
      · exact absurd (Or.inl rfl) hv'
      · exact Or.inl rfl
      · exact Or.inr ⟨fun h ↦ hv' (Or.inr h), hv⟩
  refine ⟨capCol (Δ.pole Y) c (c (bdEmb hPY (other m)) + c (bdEmb hPY (pairing m (other m)))), ?_⟩
  rw [← hshore]
  refine cap_colouring hPY m hc (Z₀ := Y.erase x) (S := {freshV (Δ.pole Y) + 1})
    (Finset.erase_subset x Y) ?_ (by intro v hv; rw [Finset.mem_singleton] at hv; rw [hv]; simp)
    (add_ne_of_ne h0 h0' hne).1 ?_ ?_
  · intro v hv
    rw [Finset.mem_erase] at hv
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hYV hv.2, by rintro (rfl | rfl); exact hv.1 rfl; exact hy hv.2⟩
  · intro h
    rw [Finset.mem_singleton] at h
    omega
  · intro _
    exact ⟨h0, h0', hne, rfl⟩

/-- Assembling a colouring of the pole avoiding `w` and `x` from the first couple. -/
theorem capPole_assemble_u (h0 : c (bdEmb hPY 0) ≠ 0) (h0' : c (bdEmb hPY (pairing m 0)) ≠ 0)
    (hne : c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0))) :
    ((cap hPY m).pole ((cap hPY m).Vs \ {freshV (Δ.pole Y) + 1, x})).Colourable := by
  have hYV : Y ⊆ Δ.Vs := hY.1
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have hshore : ({freshV (Δ.pole Y)} : Finset ℕ) ∪ Y.erase x =
      (cap hPY m).Vs \ {freshV (Δ.pole Y) + 1, x} := by
    rw [cap_Vs]
    ext v
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert]
    constructor
    · rintro (rfl | ⟨hvx, hv⟩)
      · exact ⟨Or.inl rfl, by rintro (h | rfl); omega; exact huY hx⟩
      · exact ⟨Or.inr (Or.inr hv), by rintro (rfl | rfl); exact hwY hv; exact hvx rfl⟩
    · rintro ⟨rfl | rfl | hv, hv'⟩
      · exact Or.inl rfl
      · exact absurd (Or.inl rfl) hv'
      · exact Or.inr ⟨fun h ↦ hv' (Or.inr h), hv⟩
  refine ⟨capCol (Δ.pole Y) c (c (bdEmb hPY 0) + c (bdEmb hPY (pairing m 0))), ?_⟩
  rw [← hshore]
  refine cap_colouring hPY m hc (Z₀ := Y.erase x) (S := {freshV (Δ.pole Y)})
    (Finset.erase_subset x Y) ?_ (by intro v hv; rw [Finset.mem_singleton] at hv; rw [hv]; simp)
    (add_ne_of_ne h0 h0' hne).1 ?_ ?_
  · intro v hv
    rw [Finset.mem_erase] at hv
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hYV hv.2, by rintro (rfl | rfl); exact hv.1 rfl; exact hy hv.2⟩
  · intro _
    exact ⟨h0, h0', hne, rfl⟩
  · intro h
    rw [Finset.mem_singleton] at h
    omega

end Assemble

section NewOld

include hcl hcub hnc hb hg5 hc4 hY hhet in
/-- A new vertex with an old one. -/
theorem capPole_new_old {d x : ℕ} (hd : d ∈ Δ.bd Y) (hx : x ∈ Y) :
    ((cap hPY m).pole ((cap hPY m).Vs \
      {if d ∈ couple₁ hPY m then freshV (Δ.pole Y) else freshV (Δ.pole Y) + 1, x})).Colourable := by
  classical
  have hYV : Y ⊆ Δ.Vs := hY.1
  have hind : Δ.IsIndependentCut Y := hY.independent hcl hcub hg5 hc4
  have hdd : d ∈ (Δ.pole Y).dangling := mem_dangling_Y hd
  -- replace `d` by its partner when `x` is the inner end of the partner
  set d' := if x = innerEnd hPY (partner hPY m d) then partner hPY m d else d with hd'def
  have hd'bd : d' ∈ Δ.bd Y := by
    rw [hd'def]; split_ifs
    · have := partner_mem hPY m hdd; rwa [dangling_pole] at this
    · exact hd
  have hd'c : d' ∈ couple₁ hPY m ↔ d ∈ couple₁ hPY m := by
    rw [hd'def]; split_ifs
    · exact partner_mem_couple₁_iff hPY m hdd
    · exact Iff.rfl
  have hx₂ : x ≠ innerEnd hPY (partner hPY m d') := by
    rw [hd'def]; split_ifs with h
    · rw [partner_partner hPY m hdd]
      intro h'
      rw [h'] at h
      exact partner_ne hPY m hdd (innerEnd_Y_inj hPY hind (by
          have := partner_mem hPY m hdd; rwa [dangling_pole] at this) hd h.symm)
    · exact h
  set y := innerEnd hPYc d' with hydef
  have hyV : y ∈ Δ.Vs \ Y := innerEnd_compl_mem hcl hPYc hd'bd
  have hxy : x ≠ y := fun h ↦ (Finset.mem_sdiff.mp hyV).2 (h ▸ hx)
  obtain ⟨c, hc⟩ := hb x (hYV hx) y (Finset.mem_sdiff.mp hyV).1 hxy
  have hne : (d' ∈ couple₁ hPY m → c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m)))) ∧
      (d' ∉ couple₁ hPY m → c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0))) := by
    by_cases hx₁ : x = innerEnd hPY d'
    · rw [hx₁] at hc
      exact other_couple_ne_of_adjacent hcl hcub hnc hg5 hYV hind hPY hPYc m hd'bd hc
    · exact other_couple_ne_of_nonadjacent hcl hcub hg5 hind hPY hPYc m hhet hd'bd hx hx₁ hx₂ hc
  have hcut : ∀ a ∈ Δ.bd Y, a ≠ d' → c a ≠ 0 :=
    fun a ha had ↦ hc.1 a (cut_mem_pole hcl hPYc hind hd'bd ha had hx)
  have hbd : ∀ k, bdEmb hPY k ∈ Δ.bd Y := fun k ↦ by
    rw [← dangling_pole]; exact bdEmb_mem hPY k
  by_cases hd₁ : d ∈ couple₁ hPY m
  · rw [if_pos hd₁]
    have hd'₁ : d' ∈ couple₁ hPY m := hd'c.mpr hd₁
    exact capPole_assemble_w hY hPY m hx (Finset.mem_sdiff.mp hyV).2 hc
      (hcut _ (hbd _) (fun h ↦ bdEmb_other_notMem_couple₁ m hPY (h ▸ hd'₁)))
      (hcut _ (hbd _) (fun h ↦ bdEmb_pairing_other_notMem_couple₁ m hPY (h ▸ hd'₁)))
      (hne.1 hd'₁)
  · rw [if_neg hd₁]
    have hd'₁ : d' ∉ couple₁ hPY m := fun h ↦ hd₁ (hd'c.mp h)
    exact capPole_assemble_u hY hPY m hx (Finset.mem_sdiff.mp hyV).2 hc
      (hcut _ (hbd _) (fun h ↦ hd'₁ (h ▸ Finset.mem_insert_self _ _)))
      (hcut _ (hbd _) (fun h ↦ hd'₁ (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      (hne.2 hd'₁)

end NewOld

section Main

include hcl hcub hnc hb hg5 hc4 hY hhet in
/-- **The cap factor of a bicritical snark is bicritical.** -/
theorem cap_isBicritical : (cap hPY m).IsBicritical := by
  classical
  intro a ha b hb' hab
  have hbd0 : bdEmb hPY 0 ∈ Δ.bd Y := by rw [← dangling_pole]; exact bdEmb_mem hPY 0
  have hbdo : bdEmb hPY (other m) ∈ Δ.bd Y := by rw [← dangling_pole]; exact bdEmb_mem hPY _
  have hc0 : bdEmb hPY 0 ∈ couple₁ hPY m := Finset.mem_insert_self _ _
  have hco : bdEmb hPY (other m) ∉ couple₁ hPY m := bdEmb_other_notMem_couple₁ m hPY
  have hu : ∀ x ∈ Y, ((cap hPY m).pole ((cap hPY m).Vs \ {freshV (Δ.pole Y), x})).Colourable := by
    intro x hx
    have := capPole_new_old hcl hcub hnc hb hg5 hc4 hY hPY hPYc m hhet hbd0 hx
    rwa [if_pos hc0] at this
  have hw : ∀ x ∈ Y,
      ((cap hPY m).pole ((cap hPY m).Vs \ {freshV (Δ.pole Y) + 1, x})).Colourable := by
    intro x hx
    have := capPole_new_old hcl hcub hnc hb hg5 hc4 hY hPY hPYc m hhet hbdo hx
    rwa [if_neg hco] at this
  rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at ha hb'
  rcases ha with rfl | rfl | ha <;> rcases hb' with rfl | rfl | hb'
  · exact absurd rfl hab
  · exact capPole_uw hcl hb hg5 hY hPY m
  · exact hu b hb'
  · rw [Finset.pair_comm]; exact capPole_uw hcl hb hg5 hY hPY m
  · exact absurd rfl hab
  · exact hw b hb'
  · rw [Finset.pair_comm]; exact hu a ha
  · rw [Finset.pair_comm]; exact hw a ha
  · exact capPole_pair_Y hcl hb hY hPY hPYc m hhet ha hb' hab

end Main

end FinGraph
end GraphPuzzles
