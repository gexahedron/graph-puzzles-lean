import GraphPuzzles.Factorization.FactorQuasiHelpers

/-!
# A join along `∂W` is a cap along `∂Z` when `W = Z ∪ {x, y}` with `x ~ y`

This is the common core of both isomorphisms of Chladný–Škoviera, Proposition 8.2.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

theorem Joins.end_eq {Γ : FinGraph} {e a b : ℕ} (h : Γ.Joins e a b) (i : Fin 2) :
    Γ.ends e i = a ∨ Γ.ends e i = b := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hi with rfl | rfl
  · exact Or.inl h0
  · exact Or.inr h1
  · exact Or.inr h0
  · exact Or.inl h1

theorem Joins.exists_end {Γ : FinGraph} {e a b : ℕ} (h : Γ.Joins e a b) :
    ∃ i, Γ.ends e i = a := by
  rcases h with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

section JoinCap

variable {Δ : FinGraph} (hcl : Δ.IsClosed) {W Z : Finset ℕ} (hZW : Z ⊆ W) (hW : W ⊆ Δ.Vs)
  {x y f ax ay lx ly : ℕ} (hxy : x ≠ y) (hxZ : x ∉ Z) (hyZ : y ∉ Z)
  (hWeq : W = insert x (insert y Z)) (hf : f ∈ Δ.Es) (hfj : Δ.Joins f x y)
  (hax : ax ∈ Δ.bd Z) (haxv : ∃ i, Δ.ends ax i = x) (hay : ay ∈ Δ.bd Z) (hayv : ∃ i, Δ.ends ay i = y)
  (hlx : lx ∈ Δ.bd W) (hlxv : ∃ i, Δ.ends lx i = x) (hly : ly ∈ Δ.bd W) (hlyv : ∃ i, Δ.ends ly i = y)
  (hatx : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = x → e = f ∨ e = ax ∨ e = lx)
  (haty : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = y → e = f ∨ e = ay ∨ e = ly)
  (hPW : (Δ.pole W).IsPole4) (mW : Fin 3) (hPZ : (Δ.pole Z).IsPole4)
  (hno : ∀ k, bdEmb hPW k ∈ Δ.bd Z → bdEmb hPW (pairing mW k) ∈ Δ.bd Z → False)

include hcl hZW hW hxy hxZ hyZ hWeq hf hfj hax haxv hay hayv hlx hlxv hly hlyv hatx haty hno in
omit hcl in
/-- **A join along the outer cut is a cap along the inner cut.** -/
theorem join_is_cap : ∃ m, Nonempty (Iso (join hPW mW) (cap hPZ m)) := by
  have hxW : x ∈ W := by rw [hWeq]; exact Finset.mem_insert_self _ _
  have hyW : y ∈ W := by rw [hWeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hdangW : (Δ.pole W).dangling = Δ.bd W := dangling_pole W
  -- the partner function of the `W`-pole never maps `∂Z` into `∂Z`
  have hno' : ∀ d ∈ Δ.bd Z, d ∈ Δ.bd W → partner hPW mW d ∉ Δ.bd Z := by
    intro d hdZ hdW hpd
    have hd' : d ∈ (Δ.pole W).dangling := hdangW ▸ hdW
    obtain ⟨k, rfl⟩ := exists_bdEmb_eq hPW hd'
    rw [partner_bdEmb] at hpd
    exact hno k hdZ hpd
  have hWmem : ∀ v ∈ W, v = x ∨ v = y ∨ v ∈ Z := by
    intro v hv
    rw [hWeq, Finset.mem_insert, Finset.mem_insert] at hv
    exact hv
  -- `f` has both ends in `W \ Z`
  have hfends : ∀ i, Δ.ends f i ∈ W ∧ Δ.ends f i ∉ Z := by
    intro i
    rcases hfj.end_eq i with h | h <;> rw [h]
    · exact ⟨hxW, hxZ⟩
    · exact ⟨hyW, hyZ⟩
  have hfbdW : f ∉ Δ.bd W := by
    rw [mem_bd]; rintro ⟨-, h⟩; exact h ⟨fun _ ↦ (hfends 1).1, fun _ ↦ (hfends 0).1⟩
  have hfbdZ : f ∉ Δ.bd Z := by
    rw [mem_bd]; rintro ⟨-, h⟩
    exact h ⟨fun h' ↦ absurd h' (hfends 0).2, fun h' ↦ absurd h' (hfends 1).2⟩
  have hfW : f ∈ (Δ.pole W).Es := by
    rw [pole_Es, Finset.mem_union]; left
    exact mem_edgesIn.mpr ⟨hf, fun i ↦ (hfends i).1⟩
  have hfJ : f ∈ (join hPW mW).Es := by
    rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff, hdangW]
    exact Or.inr (Or.inr ⟨hfW, hfbdW⟩)
  -- the other end of a boundary edge of `Z` at a vertex outside `Z` lies in `Z`
  have bd_other : ∀ a ∈ Δ.bd Z, ∀ i, Δ.ends a i ∉ Z → Δ.ends a (Fin.rev i) ∈ Z := by
    intro a ha i hi
    rw [mem_bd] at ha
    have h1 : i = 0 ∨ i = 1 := by omega
    rcases h1 with rfl | rfl
    · rw [Iso.rev_zero']; by_contra h; exact ha.2 ⟨fun h' ↦ absurd h' hi, fun h' ↦ absurd h' h⟩
    · rw [Iso.rev_one']; by_contra h; exact ha.2 ⟨fun h' ↦ absurd h' h, fun h' ↦ absurd h' hi⟩
  -- the generic analysis at a vertex `z ∈ W \ Z`
  have atGen : ∀ (z az lz : ℕ), z ∈ W → z ∉ Z → az ∈ Δ.bd Z → (∃ i, Δ.ends az i = z) →
      lz ∈ Δ.bd W → (∃ i, Δ.ends lz i = z) →
      (∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = z → e = f ∨ e = az ∨ e = lz) →
      az ∉ Δ.bd W ∧ lz ∉ Δ.bd Z ∧ az ≠ lz ∧ f ≠ az ∧ f ≠ lz ∧ innerEnd hPW lz = z ∧
      az ∈ (Δ.pole W).Es ∧ (∀ d ∈ Δ.bd W, innerEnd hPW d = z → d = lz) := by
    intro z az lz hzW hzZ haz hazv hlz hlzv hatz
    obtain ⟨i, hi⟩ := hazv
    obtain ⟨j, hj⟩ := hlzv
    have hazo : Δ.ends az (Fin.rev i) ∈ Z := bd_other az haz i (hi ▸ hzZ)
    have hazW : az ∉ Δ.bd W := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at hazo; exact h ⟨fun _ ↦ hZW hazo, fun _ ↦ hi ▸ hzW⟩
      · rw [Iso.rev_one'] at hazo; exact h ⟨fun _ ↦ hi ▸ hzW, fun _ ↦ hZW hazo⟩
    have hlzo : Δ.ends lz (Fin.rev j) ∉ W := other_end_notMem hlz (hj ▸ hzW)
    have hlzZ : lz ∉ Δ.bd Z := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have hj0 : j = 0 ∨ j = 1 := by omega
      rcases hj0 with rfl | rfl
      · rw [Iso.rev_zero'] at hlzo
        exact h ⟨fun h' ↦ absurd h' (hj ▸ hzZ), fun h' ↦ absurd (hZW h') hlzo⟩
      · rw [Iso.rev_one'] at hlzo
        exact h ⟨fun h' ↦ absurd (hZW h') hlzo, fun h' ↦ absurd h' (hj ▸ hzZ)⟩
    refine ⟨hazW, hlzZ, fun h ↦ hazW (h ▸ hlz), fun h ↦ hfbdZ (h ▸ haz), fun h ↦ hfbdW (h ▸ hlz),
      innerEnd_eq_of_end hPW hlz (hj ▸ hzW) |>.trans hj, ?_, ?_⟩
    · rw [pole_Es, Finset.mem_union]; left
      refine mem_edgesIn.mpr ⟨bd_subset Z haz, fun k ↦ ?_⟩
      by_cases hk : k = i
      · rw [hk, hi]; exact hzW
      · have : k = Fin.rev i := by
          have h1 : k = 0 ∨ k = 1 := by omega
          have h2 : i = 0 ∨ i = 1 := by omega
          rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> rw [h2] at hk ⊢
          · exact absurd rfl hk
          · rw [Iso.rev_one']
          · rw [Iso.rev_zero']
          · exact absurd rfl hk
        rw [this]; exact hZW hazo
    · intro d hd hdz
      have hd' : d ∈ (Δ.pole W).dangling := hdangW ▸ hd
      have := ends_innerIdx hPW hd'
      rw [pole_ends, hdz] at this
      rcases hatz d (bd_subset W hd) _ this with h | h | h
      · exact absurd (h ▸ hd) hfbdW
      · exact absurd (h ▸ hd) hazW
      · exact h
  obtain ⟨haxW, hlxZ, haxlx, hfax, hflx, hilx, haxP, huniqx⟩ :=
    atGen x ax lx hxW hxZ hax haxv hlx hlxv hatx
  obtain ⟨hayW, hlyZ, hayly, hfay, hfly, hily, hayP, huniqy⟩ :=
    atGen y ay ly hyW hyZ hay hayv hly hlyv haty
  have hlxly : lx ≠ ly := by
    intro h
    have := hilx
    rw [h, hily] at this
    exact hxy this.symm
  have notbd : ∀ e ∈ Δ.Es, e ∉ Δ.bd Z → (Δ.ends e 0 ∈ Z ↔ Δ.ends e 1 ∈ Z) := by
    intro e he h
    by_contra h'
    exact h (mem_bd.mpr ⟨he, h'⟩)
  -- the boundary of `W` outside `∂Z` is `{lx, ly}`
  have hsdiff : ∀ e ∈ Δ.bd W, e ∉ Δ.bd Z → e = lx ∨ e = ly := by
    intro e he heZ
    obtain ⟨i, hi, hi'⟩ := bd_side he
    have hiff := notbd e (bd_subset W he) heZ
    have hiZ : Δ.ends e i ∉ Z := by
      intro h
      have h2 : Δ.ends e (Fin.rev i) ∉ Z := fun h' ↦ hi' (hZW h')
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at h2; exact h2 (hiff.mp h)
      · rw [Iso.rev_one'] at h2; exact h2 (hiff.mpr h)
    rcases hWmem _ hi with hx' | hy' | hz
    · rcases hatx e (bd_subset W he) i hx' with h | h | h
      · exact absurd (h ▸ he) hfbdW
      · exact absurd (h ▸ he) haxW
      · exact Or.inl h
    · rcases haty e (bd_subset W he) i hy' with h | h | h
      · exact absurd (h ▸ he) hfbdW
      · exact absurd (h ▸ he) hayW
      · exact Or.inr h
    · exact absurd hz hiZ
  -- the partners of `lx` and `ly` lie on `∂Z`
  have hcardW : (Δ.bd W).card = 4 := by rw [← hdangW]; exact hPW.card_dangling
  have hpartner : ∀ lz ∈ Δ.bd W, (lz = lx ∨ lz = ly) → partner hPW mW lz ∈ Δ.bd Z := by
    intro lz hlz hlz'
    by_contra hp
    have hpW : partner hPW mW lz ∈ Δ.bd W := hdangW ▸ partner_mem hPW mW (hdangW ▸ hlz)
    have hpne := partner_ne hPW mW (hdangW ▸ hlz)
    -- the couple of `lz` is `{lx, ly}`
    have hcouple : ∀ d, d = lx ∨ d = ly → partner hPW mW d = lx ∨ partner hPW mW d = ly := by
      have h1 := hsdiff _ hpW hp
      intro d hd
      have hpp : partner hPW mW (partner hPW mW lz) = lz := partner_partner hPW mW (hdangW ▸ hlz)
      rcases hlz' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases hd with rfl | rfl
      · exact absurd h1 hpne
      · exact absurd h1 hpne
      · exact Or.inr h1
      · left; rw [← h1, hpp]
      · right; rw [← h1, hpp]
      · exact Or.inl h1
      · exact absurd h1 hpne
      · exact absurd h1 hpne
    -- an edge of `∂W ∩ ∂Z` and its partner
    have hne : (Δ.bd W \ {lx, ly}).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset (by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl <;> assumption), hcardW, Finset.card_pair hlxly]
      omega
    obtain ⟨e', he'⟩ := hne
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at he'
    have he'Z : e' ∈ Δ.bd Z := by
      by_contra h
      exact he'.2 (hsdiff e' he'.1 h)
    have hpe'W : partner hPW mW e' ∈ Δ.bd W := hdangW ▸ partner_mem hPW mW (hdangW ▸ he'.1)
    have hpe'Z : partner hPW mW e' ∈ Δ.bd Z := by
      by_contra h
      have hpp : partner hPW mW (partner hPW mW e') = e' := partner_partner hPW mW (hdangW ▸ he'.1)
      rcases hsdiff _ hpe'W h with h' | h'
      · have hc := hcouple lx (Or.inl rfl)
        have he'' : e' = partner hPW mW lx := by rw [← h', hpp]
        rw [← he''] at hc
        exact he'.2 hc
      · have hc := hcouple ly (Or.inr rfl)
        have he'' : e' = partner hPW mW ly := by rw [← h', hpp]
        rw [← he''] at hc
        exact he'.2 hc
    exact hno' e' he'Z he'.1 hpe'Z
  have hplx := hpartner lx hlx (Or.inl rfl)
  have hply := hpartner ly hly (Or.inr rfl)
  -- the inner end of the partner of `lz` lies in `Z`
  have innerZ : ∀ lz ∈ Δ.bd W, partner hPW mW lz ∈ Δ.bd Z → innerEnd hPW (partner hPW mW lz) ∈ Z := by
    intro lz hlz hpZ
    have hpW : partner hPW mW lz ∈ Δ.bd W := hdangW ▸ partner_mem hPW mW (hdangW ▸ hlz)
    obtain ⟨i, hi, -⟩ := bd_side hpZ
    rw [innerEnd_eq_of_end hPW hpW (hZW hi)]
    exact hi
  -- the new edges attached to `x` and `y`
  set Γ' := join hPW mW with hΓ'
  have hclJ : Γ'.IsClosed := join_isClosed hPW mW
  have hbdJ := join_bd_Z hPW mW hW Z hZW
  have hdangJ : (Γ'.pole Z).dangling = Γ'.bd Z := dangling_pole Z
  have newGen : ∀ (z az lz : ℕ), z ∈ W → z ∉ Z → az ∈ Δ.bd Z → (∃ i, Δ.ends az i = z) →
      lz ∈ Δ.bd W → innerEnd hPW lz = z → az ∉ Δ.bd W → az ∈ (Δ.pole W).Es →
      partner hPW mW lz ∈ Δ.bd Z →
      (∀ d ∈ Δ.bd W, innerEnd hPW d = z → d = lz) →
      (∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = z → e = f ∨ e = az ∨ e = lz) →
      let nz := if lz ∈ couple₁ hPW mW then freshE (Δ.pole W) else freshE (Δ.pole W) + 1
      az ∈ Γ'.bd Z ∧ nz ∈ Γ'.bd Z ∧ az ≠ nz ∧ (∃ i, Γ'.ends az i = z) ∧ (∃ i, Γ'.ends nz i = z) ∧
      (∀ e ∈ Γ'.Es, ∀ i, Γ'.ends e i = z → e = f ∨ e = az ∨ e = nz) := by
    intro z az lz hzW hzZ haz hazv hlz hilz hazW hazP hpz huniq hatz nz
    have hlz' : lz ∈ (Δ.pole W).dangling := hdangW ▸ hlz
    have hnzJ := join_new_joins hPW mW hlz'
    rw [hilz] at hnzJ
    have hnzE : nz ∈ Γ'.Es := join_new_mem hPW mW
    have htZ := innerZ lz hlz hpz
    have hnzbd : nz ∈ Γ'.bd Z := by
      rw [mem_bd]
      refine ⟨hnzE, ?_⟩
      rcases hnzJ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
      · exact fun h ↦ hzZ (h.mpr htZ)
      · exact fun h ↦ hzZ (h.mp htZ)
    have hazbd : az ∈ Γ'.bd Z := by
      rw [hbdJ, Finset.mem_union, Finset.mem_filter]
      exact Or.inl ⟨haz, hazW⟩
    have hazne : az ≠ nz := by
      intro h
      have : nz ∈ (Δ.pole W).Es := h ▸ hazP
      unfold nz at this
      split_ifs at this
      · exact freshE_notMem this
      · exact freshE_succ_notMem this
    refine ⟨hazbd, hnzbd, hazne, ?_, hnzJ.exists_end, ?_⟩
    · obtain ⟨i, hi⟩ := hazv
      exact ⟨i, by rw [hΓ', join_ends_eq hPW mW hazP, pole_ends]; exact hi⟩
    · intro e he i hi
      rcases join_mem_Es_cases' hPW mW he with hn | hn | ⟨heP, hed⟩
      · -- a new edge
        obtain ⟨e', he', hne', hj⟩ := join_new_ends_cases hPW mW e (Or.inl hn)
        right; right
        rcases hj.end_eq i with h | h <;> rw [hi] at h
        · have := huniq e' (hdangW ▸ he') h.symm
          rw [hne', this]
        · have hpe' : partner hPW mW e' = lz := huniq _ (hdangW ▸ partner_mem hPW mW he') h.symm
          have : e' ∈ couple₁ hPW mW ↔ lz ∈ couple₁ hPW mW := by
            rw [← hpe', partner_mem_couple₁_iff hPW mW he']
          rw [hne']
          unfold nz
          by_cases hc : lz ∈ couple₁ hPW mW
          · rw [if_pos (this.mpr hc), if_pos hc]
          · rw [if_neg (fun h' ↦ hc (this.mp h')), if_neg hc]
      · obtain ⟨e', he', hne', hj⟩ := join_new_ends_cases hPW mW e (Or.inr hn)
        right; right
        rcases hj.end_eq i with h | h <;> rw [hi] at h
        · have := huniq e' (hdangW ▸ he') h.symm
          rw [hne', this]
        · have hpe' : partner hPW mW e' = lz := huniq _ (hdangW ▸ partner_mem hPW mW he') h.symm
          have : e' ∈ couple₁ hPW mW ↔ lz ∈ couple₁ hPW mW := by
            rw [← hpe', partner_mem_couple₁_iff hPW mW he']
          rw [hne']
          unfold nz
          by_cases hc : lz ∈ couple₁ hPW mW
          · rw [if_pos (this.mpr hc), if_pos hc]
          · rw [if_neg (fun h' ↦ hc (this.mp h')), if_neg hc]
      · rw [hΓ', join_ends_eq hPW mW heP, pole_ends] at hi
        have heΔ : e ∈ Δ.Es := by
          rw [pole_Es, Finset.mem_union] at heP
          exact heP.elim (fun h ↦ edgesIn_subset W h) (fun h ↦ bd_subset W h)
        rcases hatz e heΔ i hi with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd (h ▸ hlz') hed
  obtain ⟨haxbd, hnxbd, haxnx, haxz, hnxz, hatx'⟩ :=
    newGen x ax lx hxW hxZ hax haxv hlx hilx haxW haxP hplx huniqx hatx
  obtain ⟨haybd, hnybd, hayny, hayz, hnyz, haty'⟩ :=
    newGen y ay ly hyW hyZ hay hayv hly hily hayW hayP hply huniqy haty
  -- `f` is not on the boundary of `Z` in the join
  have hfbdJ : f ∉ Γ'.bd Z := by
    rw [mem_bd]
    rintro ⟨-, h⟩
    apply h
    rw [hΓ', join_ends_eq hPW mW hfW, join_ends_eq hPW mW hfW, pole_ends]
    exact ⟨fun h' ↦ absurd h' (hfends 0).2, fun h' ↦ absurd h' (hfends 1).2⟩
  -- the pole of `Z` in the join and its pairing
  have hP'' : (Γ'.pole Z).IsPole4 := (joinPoleIso hPW mW hW Z hZW hno).symm.isPole4 hPZ
  obtain ⟨k₁, hk₁⟩ := exists_bdEmb_eq hP'' (hdangJ ▸ haxbd)
  obtain ⟨k₂, hk₂⟩ := exists_bdEmb_eq hP'' (hdangJ ▸ hnxbd)
  have hk : k₁ ≠ k₂ := fun h ↦ haxnx (by rw [← hk₁, ← hk₂, h])
  have hpd : partner hP'' (pairOf k₁ k₂) ax =
      (if lx ∈ couple₁ hPW mW then freshE (Δ.pole W) else freshE (Δ.pole W) + 1) := by
    rw [← hk₁, partner_bdEmb, pairing_pairOf k₁ k₂ hk, hk₂]
  have hXset : ∀ e ∈ Γ'.bd Z, (∃ i, Γ'.ends e i = x) ↔
      (e = ax ∨ e = (if lx ∈ couple₁ hPW mW then freshE (Δ.pole W) else freshE (Δ.pole W) + 1)) := by
    intro e he
    constructor
    · rintro ⟨i, hi⟩
      rcases hatx' e (bd_subset Z he) i hi with h | h | h
      · exact absurd (h ▸ he) hfbdJ
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact haxz
      · exact hnxz
  have hV : Γ'.Vs = insert x (insert y Z) := by rw [hΓ', join_Vs, pole_Vs, hWeq]
  have hfj' : Γ'.Joins f x y := by
    unfold Joins
    rw [hΓ', join_ends_eq hPW mW hfW, join_ends_eq hPW mW hfW, pole_ends]
    exact hfj
  have hx' : ∀ e ∈ Γ'.Es, ∀ i, Γ'.ends e i = x → e = f ∨ e ∈ Γ'.bd Z := by
    intro e he i hi
    rcases hatx' e he i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ haxbd)
    · exact Or.inr (h ▸ hnxbd)
  have hy' : ∀ e ∈ Γ'.Es, ∀ i, Γ'.ends e i = y → e = f ∨ e ∈ Γ'.bd Z := by
    intro e he i hi
    rcases haty' e he i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ haybd)
    · exact Or.inr (h ▸ hnybd)
  obtain ⟨I⟩ := recap_iso hclJ hxy hxZ hyZ hV hfJ hfj' hP'' (pairOf k₁ k₂) hx' hy' haxbd hpd hXset
  exact ⟨_, ⟨I.trans (capIso (joinPoleIso hPW mW hW Z hZW hno) hP'' hPZ (pairOf k₁ k₂))⟩⟩

end JoinCap

end FinGraph
end GraphPuzzles
