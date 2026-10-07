import GraphPuzzles.FinGraph.FinGraphSmallCycles
import GraphPuzzles.Factorization.Diamond.FactorDblCommon
import GraphPuzzles.Factorization.FactorGlue

/-!
# Recognising a cap, and colourings of caps

* `recap_iso`: a closed graph whose vertex set is a shore `Z` together with two adjacent
  vertices, each sending its two other edges into `Z` as one couple of the pole at `Z`, is
  isomorphic to the cap of that pole.
* `cap_colourable_of_het`: a heterochromatic colouring of a pole extends to its cap; hence an
  uncolourable cap forces the pole to be isochromatic (`isoWith_of_cap_not_colourable`).
* `cap_short_cycle`, `join_parallel`: two dangling edges attached to adjacent inner vertices
  produce a short cycle in the cap (resp. a parallel edge in the join if they form a couple).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

set_option maxRecDepth 100000

section Recap

variable {Γ : FinGraph} (hcl : Γ.IsClosed) {Z : Finset ℕ} {x y g d₁ d₂ : ℕ}
  (hxy : x ≠ y) (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hV : Γ.Vs = insert x (insert y Z))
  (hg : g ∈ Γ.Es) (hgxy : Γ.Joins g x y) (hP : (Γ.pole Z).IsPole4) (m : Fin 3)
  (hx : ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i = x → e = g ∨ e ∈ Γ.bd Z)
  (hy : ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i = y → e = g ∨ e ∈ Γ.bd Z)
  (hd₁ : d₁ ∈ Γ.bd Z) (hd₂ : d₂ ∈ Γ.bd Z) (hdne : d₁ ≠ d₂) (hpd : partner hP m d₁ = d₂)
  (hXset : ∀ e ∈ Γ.bd Z, (∃ i, Γ.ends e i = x) ↔ (e = d₁ ∨ e = d₂))

/-- The vertex map of the recap isomorphism. -/
noncomputable def recapFv (v : ℕ) : ℕ :=
  if v = x then (if d₁ ∈ couple₁ hP m then freshV (Γ.pole Z) else freshV (Γ.pole Z) + 1)
  else if v = y then (if d₁ ∈ couple₁ hP m then freshV (Γ.pole Z) + 1 else freshV (Γ.pole Z))
  else v

include hcl hxy hxZ hyZ hV hg hgxy hx hy hd₁ hd₂ hdne hpd hXset in
omit hd₂ hdne in
/-- **Recap.** -/
theorem recap_iso : Nonempty (Iso Γ (cap hP m)) := by
  have hZV : Z ⊆ Γ.Vs := by
    rw [hV]; exact fun v hv ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)
  have hxV : x ∈ Γ.Vs := by rw [hV]; exact Finset.mem_insert_self _ _
  have hyV : y ∈ Γ.Vs := by rw [hV]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfu : freshV (Γ.pole Z) ∉ Z := freshV_notMem (P := Γ.pole Z)
  have hfw : freshV (Γ.pole Z) + 1 ∉ Z := freshV_succ_notMem (P := Γ.pole Z)
  have hgbd : g ∉ Γ.bd Z := by
    rw [mem_bd]
    rintro ⟨-, h⟩
    rcases hgxy with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] at h
    · exact h ⟨fun h' ↦ absurd h' hxZ, fun h' ↦ absurd h' hyZ⟩
    · exact h ⟨fun h' ↦ absurd h' hyZ, fun h' ↦ absurd h' hxZ⟩
  have hgin : g ∉ Γ.edgesIn Z := by
    rw [mem_edgesIn]
    rintro ⟨-, h⟩
    rcases hgxy with ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hxZ (h0 ▸ h 0)
    · exact hyZ (h0 ▸ h 0)
  have hgP : g ∉ (Γ.pole Z).Es := by
    rw [pole_Es, Finset.mem_union]
    rintro (h | h)
    · exact hgin h
    · exact hgbd h
  have hdang : (Γ.pole Z).dangling = Γ.bd Z := dangling_pole Z
  -- the edge set is the pole plus `g`
  have hEs : ∀ e ∈ Γ.Es, e = g ∨ e ∈ (Γ.pole Z).Es := by
    intro e he
    by_cases hin : ∃ i, Γ.ends e i ∈ Z
    · right
      obtain ⟨i, hi⟩ := hin
      exact mem_pole_Es_iff'.mpr ⟨he, i, hi⟩
    · push Not at hin
      have h0 : Γ.ends e 0 ∈ Γ.Vs := hcl e he 0
      rw [hV, Finset.mem_insert, Finset.mem_insert] at h0
      rcases h0 with h0 | h0 | h0
      · rcases hx e he 0 h0 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [pole_Es]; exact Finset.mem_union_right _ h)
      · rcases hy e he 0 h0 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [pole_Es]; exact Finset.mem_union_right _ h)
      · exact absurd h0 (hin 0)
  -- the outer end of a boundary edge is `x` or `y`
  have hout : ∀ e ∈ Γ.bd Z, ∀ i, Γ.ends e i ∉ Z → Γ.ends e i = x ∨ Γ.ends e i = y := by
    intro e he i hi
    have := hcl e (bd_subset Z he) i
    rw [hV, Finset.mem_insert, Finset.mem_insert] at this
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hi
  -- a boundary edge at `x` is not at `y`
  have hbdne : ∀ e ∈ Γ.bd Z, ∀ i j, Γ.ends e i = x → Γ.ends e j = y → False := by
    intro e he i j hi hj
    have hbd := he
    rw [mem_bd] at hbd
    have hi' : Γ.ends e i ∉ Z := hi ▸ hxZ
    have hj' : Γ.ends e j ∉ Z := hj ▸ hyZ
    have hij : i = 0 ∨ i = 1 := by omega
    have hij' : j = 0 ∨ j = 1 := by omega
    rcases hij with rfl | rfl <;> rcases hij' with rfl | rfl
    · exact hxy (hi.symm.trans hj)
    · exact hbd.2 ⟨fun h ↦ absurd h hi', fun h ↦ absurd h hj'⟩
    · exact hbd.2 ⟨fun h ↦ absurd h hj', fun h ↦ absurd h hi'⟩
    · exact hxy (hi.symm.trans hj)
  -- the couples: `{d₁, d₂}` and the rest
  have hcard : (Γ.bd Z).card = 4 := by rw [← hdang]; exact hP.card_dangling
  have hpd₂ : partner hP m d₂ = d₁ := by
    rw [← hpd, partner_partner hP m (hdang ▸ hd₁)]
  have hatX : ∀ e ∈ Γ.bd Z, (∃ i, Γ.ends e i = x) ↔ (partner hP m e = d₁ ∨ partner hP m e = d₂) := by
    intro e he
    have hed : e ∈ (Γ.pole Z).dangling := by rw [hdang]; exact he
    rw [hXset e he]
    constructor
    · rintro (h | h)
      · rw [h]; exact Or.inr hpd
      · rw [h]; exact Or.inl hpd₂
    · rintro (h | h)
      · right
        calc e = partner hP m (partner hP m e) := (partner_partner hP m hed).symm
          _ = partner hP m d₁ := by rw [h]
          _ = d₂ := hpd
      · left
        calc e = partner hP m (partner hP m e) := (partner_partner hP m hed).symm
          _ = partner hP m d₂ := by rw [h]
          _ = d₁ := hpd₂
  have key : ∀ e ∈ Γ.bd Z, (e ∈ couple₁ hP m ↔ d₁ ∈ couple₁ hP m) ↔
      ((∃ i, Γ.ends e i = x) ↔ True) := by
    intro e he
    have hed : e ∈ (Γ.pole Z).dangling := by rw [hdang]; exact he
    have hd₁d : d₁ ∈ (Γ.pole Z).dangling := by rw [hdang]; exact hd₁
    rw [same_couple_iff hP m hed hd₁d, iff_true, hXset e he]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        calc e = partner hP m (partner hP m e) := (partner_partner hP m hed).symm
          _ = partner hP m d₁ := by rw [h]
          _ = d₂ := hpd
    · rintro (h | h)
      · exact Or.inl h
      · rw [h]; exact Or.inr hpd₂
  -- membership of `x`/`y` boundary edges in the first couple
  have memc : ∀ e ∈ Γ.bd Z, ∀ i, Γ.ends e i = x →
      (e ∈ couple₁ hP m ↔ d₁ ∈ couple₁ hP m) := by
    intro e he i hi
    exact (key e he).mpr ⟨fun _ ↦ trivial, fun _ ↦ ⟨i, hi⟩⟩
  have memc' : ∀ e ∈ Γ.bd Z, ∀ i, Γ.ends e i = y →
      (e ∈ couple₁ hP m ↔ d₁ ∉ couple₁ hP m) := by
    intro e he i hi
    have hnx : ¬ ∃ j, Γ.ends e j = x := fun ⟨j, hj⟩ ↦ hbdne e he j i hj hi
    have := key e he
    rw [iff_true] at this
    constructor
    · intro h1 h2
      exact hnx (this.mp ⟨fun _ ↦ h2, fun _ ↦ h1⟩)
    · intro h1
      by_contra h2
      exact hnx (this.mp ⟨fun h ↦ absurd h h2, fun h ↦ absurd h h1⟩)
  -- the vertex map on `x` and `y`
  have fvx : recapFv (x := x) (y := y) (d₁ := d₁) hP m x =
      if d₁ ∈ couple₁ hP m then freshV (Γ.pole Z) else freshV (Γ.pole Z) + 1 := by
    unfold recapFv; rw [if_pos rfl]
  have fvy : recapFv (x := x) (y := y) (d₁ := d₁) hP m y =
      if d₁ ∈ couple₁ hP m then freshV (Γ.pole Z) + 1 else freshV (Γ.pole Z) := by
    unfold recapFv; rw [if_neg hxy.symm, if_pos rfl]
  have fvZ : ∀ v ∈ Z, recapFv (x := x) (y := y) (d₁ := d₁) hP m v = v := by
    intro v hv
    have h1 : v ≠ x := fun h ↦ hxZ (h ▸ hv)
    have h2 : v ≠ y := fun h ↦ hyZ (h ▸ hv)
    unfold recapFv
    rw [if_neg h1, if_neg h2]
  -- ends in the cap
  have endsC : ∀ e ∈ (Γ.pole Z).Es, ∀ i, (cap hP m).ends e i =
      if Γ.ends e i ∈ Z then Γ.ends e i
      else (if e ∈ couple₁ hP m then freshV (Γ.pole Z) else freshV (Γ.pole Z) + 1) := by
    intro e he i
    rw [cap_ends_eq hP m he, pole_ends, pole_Vs]
  refine ⟨Iso.mk'' hcl (recapFv (x := x) (y := y) (d₁ := d₁) hP m)
    (fun e ↦ if e = g then freshE (Γ.pole Z) else e) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro v hv
    rw [hV, Finset.mem_insert, Finset.mem_insert] at hv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert]
    rcases hv with rfl | rfl | hv
    · rw [fvx]; split_ifs <;> simp
    · rw [fvy]; split_ifs <;> simp
    · rw [fvZ v hv]; exact Or.inr (Or.inr hv)
  · intro v hv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · by_cases h : d₁ ∈ couple₁ hP m
      · exact ⟨x, hxV, by rw [fvx, if_pos h]⟩
      · exact ⟨y, hyV, by rw [fvy, if_neg h]⟩
    · by_cases h : d₁ ∈ couple₁ hP m
      · exact ⟨y, hyV, by rw [fvy, if_pos h]⟩
      · exact ⟨x, hxV, by rw [fvx, if_neg h]⟩
    · exact ⟨v, hZV hv, fvZ v hv⟩
  · intro u hu v hv huv
    rw [hV, Finset.mem_insert, Finset.mem_insert] at hu hv
    rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv
    · rfl
    · exfalso; rw [fvx, fvy] at huv; split_ifs at huv <;> omega
    · exfalso; rw [fvx, fvZ _ hv] at huv; split_ifs at huv
      · exact hfu (by rw [huv]; exact hv)
      · exact hfw (by rw [huv]; exact hv)
    · exfalso; rw [fvy, fvx] at huv; split_ifs at huv <;> omega
    · rfl
    · exfalso; rw [fvy, fvZ _ hv] at huv; split_ifs at huv
      · exact hfw (by rw [huv]; exact hv)
      · exact hfu (by rw [huv]; exact hv)
    · exfalso; rw [fvZ _ hu, fvx] at huv; split_ifs at huv
      · exact hfu (by rw [← huv]; exact hu)
      · exact hfw (by rw [← huv]; exact hu)
    · exfalso; rw [fvZ _ hu, fvy] at huv; split_ifs at huv
      · exact hfw (by rw [← huv]; exact hu)
      · exact hfu (by rw [← huv]; exact hu)
    · rw [fvZ _ hu, fvZ _ hv] at huv; exact huv
  · intro e he
    rw [cap_Es, Finset.mem_insert]
    by_cases h : e = g
    · rw [if_pos h]; exact Or.inl rfl
    · rw [if_neg h]; exact Or.inr ((hEs e he).resolve_left h)
  · intro e he
    rw [cap_Es, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact ⟨g, hg, by rw [if_pos rfl]⟩
    · have heΓ : e ∈ Γ.Es := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.elim (fun h ↦ edgesIn_subset Z h) (fun h ↦ bd_subset Z h)
      have h' : e ≠ g := fun h ↦ hgP (h ▸ he)
      exact ⟨e, heΓ, by rw [if_neg h']⟩
  · intro d hd e he hde
    by_cases h1 : d = g <;> by_cases h2 : e = g
    · rw [h1, h2]
    · rw [if_pos h1, if_neg h2] at hde
      exact absurd ((hEs e he).resolve_left h2) (fun h ↦ freshE_notMem (hde ▸ h))
    · rw [if_neg h1, if_pos h2] at hde
      exact absurd ((hEs d hd).resolve_left h1) (fun h ↦ freshE_notMem (hde.symm ▸ h))
    · rw [if_neg h1, if_neg h2] at hde; exact hde
  · intro e he
    by_cases h : e = g
    · subst h
      simp only [if_true]
      rw [cap_ends_new, cap_ends_new]
      simp only [if_true, one_ne_zero, if_false]
      rcases hgxy with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1, fvx, fvy]
      · split_ifs
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · split_ifs
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
    · simp only [if_neg h]
      have heP := (hEs e he).resolve_left h
      left
      have fin : ∀ i, (cap hP m).ends e i = recapFv (x := x) (y := y) (d₁ := d₁) hP m (Γ.ends e i) := by
        intro i
        rw [endsC e heP]
        by_cases hZ : Γ.ends e i ∈ Z
        · rw [if_pos hZ, fvZ _ hZ]
        · rw [if_neg hZ]
          have hbd : e ∈ Γ.bd Z := by
            rw [pole_Es, Finset.mem_union] at heP
            rcases heP with heP | heP
            · exact absurd ((mem_edgesIn.mp heP).2 i) hZ
            · exact heP
          rcases hout e hbd i hZ with hxe | hye
          · rw [hxe, fvx]
            have := memc e hbd i hxe
            by_cases h1 : e ∈ couple₁ hP m
            · rw [if_pos h1, if_pos (this.mp h1)]
            · rw [if_neg h1, if_neg (fun h' ↦ h1 (this.mpr h'))]
          · rw [hye, fvy]
            have := memc' e hbd i hye
            by_cases h1 : e ∈ couple₁ hP m
            · rw [if_pos h1, if_neg (this.mp h1)]
            · rw [if_neg h1, if_pos (by
                by_contra h'
                exact h1 (this.mpr h'))]
      exact ⟨fin 0, fin 1⟩

end Recap

section CapColouring

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

/-- A heterochromatic colouring of a pole extends to its cap. -/
theorem cap_colourable_of_het {c : ℕ → Color} (hc : P.IsColouring c)
    (hhet : ∀ i, tvec hP c i ≠ tvec hP c (pairing m i)) : (cap hP m).Colourable := by
  have htv := tvec_valid hP hc
  have htn := tvec_nonzero hP hc
  have hsum := het_sum m _ htv htn hhet
  have hε : ∀ e ∈ P.Es, e ≠ freshE P := fun e he h ↦ freshE_notMem (h ▸ he)
  have hcol : ∀ k, c (bdEmb hP k) = tvec hP c k := fun k ↦ rfl
  refine ⟨fun e ↦ if e = freshE P then tvec hP c 0 + tvec hP c (pairing m 0) else c e, ?_, ?_⟩
  · intro e he
    dsimp only
    split_ifs with h
    · exact (add_ne_of_ne (htn 0) (htn _) (hhet 0)).1
    · rw [cap_Es, Finset.mem_insert] at he
      exact hc.1 e (he.resolve_left h)
  · intro v hv h₁ h₁m h₂ h₂m heq
    dsimp only at heq
    have hcne : ∀ d ∈ P.dangling, d ≠ freshE P := fun d hd ↦ hε d (mem_dangling.mp hd).1
    have key : ∀ (k₀ : Fin 4) (C : Finset ℕ) (j : Fin 2),
        C = {bdEmb hP k₀, bdEmb hP (pairing m k₀)} →
        tvec hP c 0 + tvec hP c (pairing m 0) = tvec hP c k₀ + tvec hP c (pairing m k₀) →
        h₁ ∈ insert (freshE P, j) (C.image fun d ↦ (d, outerIdx hP d)) →
        h₂ ∈ insert (freshE P, j) (C.image fun d ↦ (d, outerIdx hP d)) →
        h₁ = h₂ := by
      intro k₀ C j hC hs hm₁ hm₂
      have hCd : ∀ d ∈ C, d ∈ P.dangling := by
        intro d hd
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> exact bdEmb_mem hP _
      have hne := add_ne_of_ne (htn k₀) (htn _) (hhet k₀)
      rw [← hs] at hne
      rw [Finset.mem_insert, Finset.mem_image] at hm₁ hm₂
      rcases hm₁ with rfl | ⟨d₁, hd₁, rfl⟩ <;> rcases hm₂ with rfl | ⟨d₂, hd₂, rfl⟩
      · rfl
      · exfalso
        simp only [if_true, hcne d₂ (hCd d₂ hd₂), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₂
        rcases hd₂ with rfl | rfl <;> rw [hcol] at heq
        · exact hne.2.1 heq
        · exact hne.2.2 heq
      · exfalso
        simp only [if_true, hcne d₁ (hCd d₁ hd₁), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁
        rcases hd₁ with rfl | rfl <;> rw [hcol] at heq
        · exact hne.2.1 heq.symm
        · exact hne.2.2 heq.symm
      · simp only [hcne d₁ (hCd d₁ hd₁), hcne d₂ (hCd d₂ hd₂), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁ hd₂
        rcases hd₁ with rfl | rfl <;> rcases hd₂ with rfl | rfl
        · rfl
        · rw [hcol, hcol] at heq
          exact absurd heq (hhet k₀)
        · rw [hcol, hcol] at heq
          exact absurd heq.symm (hhet k₀)
        · rfl
    rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · rw [cap_halfEdges_u] at h₁m h₂m
      exact key 0 (couple₁ hP m) 0 rfl rfl h₁m h₂m
    · rw [cap_halfEdges_w] at h₁m h₂m
      exact key (other m) (couple₂ hP m) 1 rfl hsum h₁m h₂m
    · rw [cap_halfEdges_old hP m hv] at h₁m h₂m
      have n₁ : h₁.1 ≠ freshE P := hε _ (mem_halfEdgesIn.mp h₁m).1
      have n₂ : h₂.1 ≠ freshE P := hε _ (mem_halfEdgesIn.mp h₂m).1
      simp only [n₁, n₂, if_false] at heq
      exact hc.unique_halfEdge hv h₁m h₂m heq

/-- A valid boundary vector is isochromatic or heterochromatic for every pairing. -/
theorem valid_iso_or_het (t : Fin 4 → Color) (hv : Valid t) (m : Fin 3) :
    (∀ i, t i = t (pairing m i)) ∨ (∀ i, t i ≠ t (pairing m i)) := by
  revert t m
  decide

/-- If the cap of a colourable pole is uncolourable, the pole is isochromatic. -/
theorem isoWith_of_cap_not_colourable (hnc : ¬ (cap hP m).Colourable) : IsoWith hP m := by
  intro t ht
  obtain ⟨c, hc, rfl⟩ := ht
  rcases valid_iso_or_het _ (tvec_valid hP hc) m with h | h
  · exact h
  · exact absurd (cap_colourable_of_het hP m hc h) hnc

end CapColouring

section Gadgets

variable {Γ : FinGraph} {W : Finset ℕ} (hP : (Γ.pole W).IsPole4) (m : Fin 3)
  {d₁ d₂ f v₁ v₂ : ℕ} (hd₁ : d₁ ∈ Γ.bd W) (hd₂ : d₂ ∈ Γ.bd W) (hne : d₁ ≠ d₂)
  (hv : v₁ ≠ v₂) (hi₁ : innerEnd hP d₁ = v₁) (hi₂ : innerEnd hP d₂ = v₂)
  (hf : f ∈ Γ.edgesIn W) (hfj : Γ.Joins f v₁ v₂)

include hd₁ hd₂ hne hv hi₁ hi₂ hf hfj in
/-- Two dangling edges at adjacent inner vertices give a short cycle in the cap. -/
theorem cap_short_cycle : ¬ (cap hP m).Girth5 := by
  intro hg
  have hd₁' : d₁ ∈ (Γ.pole W).dangling := dangling_pole W ▸ hd₁
  have hd₂' : d₂ ∈ (Γ.pole W).dangling := dangling_pole W ▸ hd₂
  have hfP : f ∈ (Γ.pole W).Es := by rw [pole_Es]; exact Finset.mem_union_left _ hf
  have hd₁P : d₁ ∈ (Γ.pole W).Es := (mem_dangling.mp hd₁').1
  have hd₂P : d₂ ∈ (Γ.pole W).Es := (mem_dangling.mp hd₂').1
  have hv₁W : v₁ ∈ W := by rw [← hi₁]; exact innerEnd_mem hP hd₁'
  have hv₂W : v₂ ∈ W := by rw [← hi₂]; exact innerEnd_mem hP hd₂'
  have hfd : f ∉ (Γ.pole W).dangling := by
    rw [dangling_pole, mem_bd]
    rintro ⟨-, h⟩
    have := (mem_edgesIn.mp hf).2
    exact h ⟨fun _ ↦ this 1, fun _ ↦ this 0⟩
  have hfd₁ : f ≠ d₁ := fun h ↦ hfd (h ▸ hd₁')
  have hfd₂ : f ≠ d₂ := fun h ↦ hfd (h ▸ hd₂')
  have hu : freshV (Γ.pole W) ∉ W := freshV_notMem (P := Γ.pole W)
  have hw : freshV (Γ.pole W) + 1 ∉ W := freshV_succ_notMem (P := Γ.pole W)
  -- the ends of the dangling edges in the cap
  have hends : ∀ (d : ℕ) (hd : d ∈ (Γ.pole W).dangling) (v : ℕ), innerEnd hP d = v →
      (cap hP m).Joins d v (if d ∈ couple₁ hP m then freshV (Γ.pole W) else freshV (Γ.pole W) + 1) := by
    intro d hd v hv
    have h1 := cap_ends_dangling hP m hd
    have h2 := ends_innerIdx hP hd
    rw [pole_ends] at h2
    rw [h2, hv] at h1
    rcases dangling_idx_cases hP hd with ⟨hi, -⟩ | ⟨hi, -⟩ <;> rw [hi] at h1
    · rw [Iso.rev_zero'] at h1
      exact Or.inl ⟨h1.1, h1.2.1⟩
    · rw [Iso.rev_one'] at h1
      exact Or.inr ⟨h1.2.1, h1.1⟩
  have hfC : (cap hP m).Joins f v₁ v₂ := by
    have e0 := cap_ends_old hP m hfP (i := 0) (by rw [pole_ends, pole_Vs]; exact (mem_edgesIn.mp hf).2 0)
    have e1 := cap_ends_old hP m hfP (i := 1) (by rw [pole_ends, pole_Vs]; exact (mem_edgesIn.mp hf).2 1)
    rw [pole_ends] at e0 e1
    unfold Joins
    rw [e0, e1]
    exact hfj
  have hfE : f ∈ (cap hP m).Es := by rw [cap_Es]; exact Finset.mem_insert_of_mem hfP
  have hd₁E : d₁ ∈ (cap hP m).Es := by rw [cap_Es]; exact Finset.mem_insert_of_mem hd₁P
  have hd₂E : d₂ ∈ (cap hP m).Es := by rw [cap_Es]; exact Finset.mem_insert_of_mem hd₂P
  have hnE : freshE (Γ.pole W) ∈ (cap hP m).Es := by rw [cap_Es]; exact Finset.mem_insert_self _ _
  have hnf : freshE (Γ.pole W) ≠ f := fun h ↦ freshE_notMem (P := Γ.pole W) (h ▸ hfP)
  have hnd₁ : freshE (Γ.pole W) ≠ d₁ := fun h ↦ freshE_notMem (P := Γ.pole W) (h ▸ hd₁P)
  have hnd₂ : freshE (Γ.pole W) ≠ d₂ := fun h ↦ freshE_notMem (P := Γ.pole W) (h ▸ hd₂P)
  have hnJ : (cap hP m).Joins (freshE (Γ.pole W)) (freshV (Γ.pole W)) (freshV (Γ.pole W) + 1) := by
    left
    rw [cap_ends_new, cap_ends_new]
    simp
  have j₁ := hends d₁ hd₁' v₁ hi₁
  have j₂ := hends d₂ hd₂' v₂ hi₂
  have hv₁u : v₁ ≠ freshV (Γ.pole W) := fun h ↦ hu (h ▸ hv₁W)
  have hv₁w : v₁ ≠ freshV (Γ.pole W) + 1 := fun h ↦ hw (h ▸ hv₁W)
  have hv₂u : v₂ ≠ freshV (Γ.pole W) := fun h ↦ hu (h ▸ hv₂W)
  have hv₂w : v₂ ≠ freshV (Γ.pole W) + 1 := fun h ↦ hw (h ▸ hv₂W)
  by_cases hc : (d₁ ∈ couple₁ hP m ↔ d₂ ∈ couple₁ hP m)
  · -- same fresh vertex: a triangle
    by_cases h1 : d₁ ∈ couple₁ hP m
    · rw [if_pos h1] at j₁
      rw [if_pos (hc.mp h1)] at j₂
      exact hg.no_triangle hfE hd₂E hd₁E hfd₂ hfd₁ hne.symm hv hv₂u hv₁u hfC j₂ j₁.symm
    · rw [if_neg h1] at j₁
      rw [if_neg (fun h ↦ h1 (hc.mpr h))] at j₂
      exact hg.no_triangle hfE hd₂E hd₁E hfd₂ hfd₁ hne.symm hv hv₂w hv₁w hfC j₂ j₁.symm
  · -- different fresh vertices: a quadrilateral through the fresh edge
    by_cases h1 : d₁ ∈ couple₁ hP m
    · rw [if_pos h1] at j₁
      rw [if_neg (fun h ↦ hc ⟨fun _ ↦ h, fun _ ↦ h1⟩)] at j₂
      exact hg.no_quad hd₁E hnE hd₂E hfE hnd₁.symm hne hfd₁.symm hnd₂ hnf hfd₂.symm
        hv₁u (by omega) hv₂w.symm hv hv₁w hv₂u.symm j₁ hnJ j₂.symm hfC.symm
    · rw [if_neg h1] at j₁
      rw [if_pos (by
        by_contra h
        exact hc ⟨fun h' ↦ absurd h' h1, fun h' ↦ absurd h' h⟩)] at j₂
      exact hg.no_quad hd₁E hnE hd₂E hfE hnd₁.symm hne hfd₁.symm hnd₂ hnf hfd₂.symm
        hv₁w (by omega) hv₂u.symm hv hv₁u hv₂w.symm j₁ hnJ.symm j₂.symm hfC.symm

include hd₁ hd₂ hne hv hi₁ hi₂ hf hfj in
omit hd₂ in
/-- Two coupled dangling edges at adjacent inner vertices give a parallel edge in the join. -/
theorem join_parallel (hpd : partner hP m d₁ = d₂) : ¬ (join hP m).Girth5 := by
  intro hg
  have hd₁' : d₁ ∈ (Γ.pole W).dangling := dangling_pole W ▸ hd₁
  have hfP : f ∈ (Γ.pole W).Es := by rw [pole_Es]; exact Finset.mem_union_left _ hf
  have hfd : f ∉ (Γ.pole W).dangling := by
    rw [dangling_pole, mem_bd]
    rintro ⟨-, h⟩
    have := (mem_edgesIn.mp hf).2
    exact h ⟨fun _ ↦ this 1, fun _ ↦ this 0⟩
  have hfJ : f ∈ (join hP m).Es := by
    rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
    exact Or.inr (Or.inr ⟨hfP, hfd⟩)
  have hfj' : (join hP m).Joins f v₁ v₂ := by
    unfold Joins
    rw [join_ends_eq hP m hfP, join_ends_eq hP m hfP, pole_ends]
    exact hfj
  -- the new edge of the couple of `d₁`
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd₁'
  rw [partner_bdEmb] at hpd
  have hn : ∀ n ∈ ({freshE (Γ.pole W), freshE (Γ.pole W) + 1} : Finset ℕ), n ≠ f := by
    intro n hn h
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact freshE_notMem (P := Γ.pole W) (h ▸ hfP)
    · exact freshE_succ_notMem (P := Γ.pole W) (h ▸ hfP)
  -- the couple of `k` is `{k, pairing m k}`; its new edge joins `v₁` and `v₂`
  have hnew : ∃ n ∈ ({freshE (Γ.pole W), freshE (Γ.pole W) + 1} : Finset ℕ),
      (join hP m).Joins n v₁ v₂ := by
    rcases four_positions m k with rfl | rfl | rfl | rfl
    · refine ⟨freshE (Γ.pole W), Finset.mem_insert_self _ _, Or.inl ?_⟩
      rw [join_ends_new₁, join_ends_new₁]
      simp only [if_true, one_ne_zero, if_false]
      rw [hi₁, hpd, hi₂]
      exact ⟨rfl, rfl⟩
    · refine ⟨freshE (Γ.pole W), Finset.mem_insert_self _ _, Or.inr ?_⟩
      rw [join_ends_new₁, join_ends_new₁]
      simp only [if_true, one_ne_zero, if_false]
      rw [pairing_involutive] at hpd
      rw [hpd, hi₂, hi₁]
      exact ⟨rfl, rfl⟩
    · refine ⟨freshE (Γ.pole W) + 1, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Or.inl ?_⟩
      rw [join_ends_new₂, join_ends_new₂]
      simp only [if_true, one_ne_zero, if_false]
      rw [hi₁, hpd, hi₂]
      exact ⟨rfl, rfl⟩
    · refine ⟨freshE (Γ.pole W) + 1, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Or.inr ?_⟩
      rw [join_ends_new₂, join_ends_new₂]
      simp only [if_true, one_ne_zero, if_false]
      rw [pairing_involutive] at hpd
      rw [hpd, hi₂, hi₁]
      exact ⟨rfl, rfl⟩
  obtain ⟨n, hnm, hnj⟩ := hnew
  have hnJ : n ∈ (join hP m).Es := by
    rw [join_Es, Finset.mem_insert, Finset.mem_insert]
    rw [Finset.mem_insert, Finset.mem_singleton] at hnm
    rcases hnm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  exact hg.no_two_cycle hnJ hfJ (hn n hnm) hv hnj hfj'

end Gadgets

end FinGraph
end GraphPuzzles
