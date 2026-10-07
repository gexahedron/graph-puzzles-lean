import GraphPuzzles.Factorization.Diamond.FactorDblJJ

/-!
# The double completion: join at `W`, then cap at `X`

For nested shores `X ⊆ W`, the join of the pole of `W` followed by the cap of the pole of
`W \ X` is isomorphic to the canonical double completion with a join gadget at `∂W` and a cap
gadget at `∂X`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section JC

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPW : (Δ.pole W).IsPole4) (mW : Fin 3) (hPX : (Δ.pole X).IsPole4) (mX : Fin 3)
  (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
  (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)
  (hQ : ((join hPW mW).pole (W \ X)).IsPole4) (m' : Fin 3)
  (hp' : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling,
    partner hQ m' c = joinPoleGe hPW mW X (partner hPX mX (joinPoleFe hPW mW X c)))

set_option quotPrecheck false in
local notation "n₀" => freshE (Δ.pole W)
set_option quotPrecheck false in
local notation "r₀" => bdEmb hPW 0
set_option quotPrecheck false in
local notation "r₁" => bdEmb hPW (other mW)
set_option quotPrecheck false in
local notation "pW" => partner hPW mW
set_option quotPrecheck false in
local notation "pX" => partner hPX mX
set_option quotPrecheck false in
local notation "cross₀" => (r₀ ∈ Δ.bd X ∨ pW r₀ ∈ Δ.bd X)
set_option quotPrecheck false in
local notation "cross₁" => (r₁ ∈ Δ.bd X ∨ pW r₁ ∈ Δ.bd X)
set_option quotPrecheck false in
local notation "QJ" => (join hPW mW).pole (W \ X)
set_option quotPrecheck false in
local notation "uX" => freshV ((join hPW mW).pole (W \ X))
set_option quotPrecheck false in
local notation "nX" => freshE ((join hPW mW).pole (W \ X))
set_option quotPrecheck false in
local notation "tX" => tokU Δ (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "eX" => tokE Δ (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "fX" => first (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "fe" => joinPoleFe hPW mW X
set_option quotPrecheck false in
local notation "ge" => joinPoleGe hPW mW X
set_option quotPrecheck false in
local notation "MM" => W \ X

/-- The canonical label of a first-stage edge with representative `r`. -/
noncomputable def jcLabel (j r : ℕ) : ℕ :=
  if r ∈ Δ.bd X ∨ pW r ∈ Δ.bd X then fe j else min r (pW r)

/-- The vertex map. -/
noncomputable def dblJCfv (v : ℕ) : ℕ :=
  if v = uX then (if fX ∈ couple₁ hQ m' then tX else tX + 1)
  else if v = uX + 1 then (if fX ∈ couple₁ hQ m' then tX + 1 else tX)
  else v

/-- The edge map. -/
noncomputable def dblJCfe (e : ℕ) : ℕ :=
  if e = nX then eX else if e = n₀ then jcLabel (X := X) hPW mW n₀ r₀
  else if e = n₀ + 1 then jcLabel (X := X) hPW mW (n₀ + 1) r₁ else e

include hcl hXW hW hnoX hnoW hp' in
/-- **The join-cap is the canonical double completion.** -/
theorem dblJC_iso : Nonempty (Iso (cap hQ m')
    (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true false)) := by
  have hneX := sdiffX_nonempty hPX mX hnoX
  have hneW := sdiffW_nonempty hPW mW hnoW
  have hn := n_notMem_poleW (Δ := Δ) (W := W)
  have hnX : nX ∉ (QJ).Es := freshE_notMem
  have huX : uX ∉ W \ X ∧ uX + 1 ∉ W \ X :=
    ⟨freshV_notMem (P := QJ), freshV_succ_notMem (P := QJ)⟩
  have hSXE : Δ.bd X ⊆ Δ.Es := bd_subset X
  have hSWE : Δ.bd W ⊆ Δ.Es := bd_subset W
  have hMV : W \ X ⊆ Δ.Vs := fun v hv ↦ hW (Finset.mem_sdiff.mp hv).1
  have htokM : ∀ v ∈ W \ X, v ≠ tX ∧ v ≠ tX + 1 := fun v hv ↦ tokU_notMem Δ (Δ.bd X) (Δ.bd W) v (hMV hv)
  have huXM : ∀ v ∈ W \ X, v ≠ uX ∧ v ≠ uX + 1 := by
    intro v hv
    exact ⟨fun h ↦ huX.1 (h ▸ hv), fun h ↦ huX.2 (h ▸ hv)⟩
  have hn0Q : n₀ ∈ (QJ).Es := (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hn1Q : n₀ + 1 ∈ (QJ).Es := (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hnXn : nX ≠ n₀ ∧ nX ≠ n₀ + 1 := ⟨fun h ↦ hnX (h ▸ hn0Q), fun h ↦ hnX (h ▸ hn1Q)⟩
  have memM : ∀ e ∈ Δ.edgesIn (W \ X), e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]; left
    rw [mem_edgesIn] at he ⊢
    exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
  have hr₀ : r₀ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW 0
  have hr₁ : r₁ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW _
  have hpr₀ : pW r₀ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW 0)
  have hpr₁ : pW r₁ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW _)
  have hfX : fX ∈ Δ.bd X \ Δ.bd W := first_mem _ _ hneX
  have hfXd : fX ∈ (QJ).dangling := by
    rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hfX
  have memBdW : ∀ c ∈ Δ.bd W \ Δ.bd X, c ∈ Δ.bd (W \ X) := fun c hc ↦ by
    rw [bd_middle hcl hXW]; exact Finset.mem_union_right _ hc
  -- the vertex map
  have fvX0 : dblJCfv hPW mW hQ m' uX = if fX ∈ couple₁ hQ m' then tX else tX + 1 := by
    unfold dblJCfv; rw [if_pos rfl]
  have fvX1 : dblJCfv hPW mW hQ m' (uX + 1) = if fX ∈ couple₁ hQ m' then tX + 1 else tX := by
    unfold dblJCfv; rw [if_neg (by omega), if_pos rfl]
  have fvM : ∀ v ∈ W \ X, dblJCfv hPW mW hQ m' v = v := by
    intro v hv
    have h := huXM v hv
    unfold dblJCfv
    rw [if_neg h.1, if_neg h.2]
  -- the token of an old dangling edge of `X`
  have tokOld : ∀ d ∈ Δ.bd X \ Δ.bd W,
      dblJCfv hPW mW hQ m' (if d ∈ couple₁ hQ m' then uX else uX + 1) =
        tok Δ (Δ.bd X) (Δ.bd W) pX d := by
    intro d hd
    have hdd : d ∈ (QJ).dangling := by
      rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hd
    have hiff : (d = fX ∨ partner hQ m' d = fX) ↔ (d = fX ∨ pX d = fX) := by
      rw [hp' d hdd, fe_old' hPW mW (sdiffX_mem_poleW hXW hd)]
      by_cases h : pX d ∈ Δ.bd W
      · have hge := ge_thru hPW mW (Finset.mem_inter.mpr ⟨pX_mem hPX mX (Finset.mem_sdiff.mp hd).1, h⟩)
        rw [hge]
        have h1 : ¬ ((if pX d ∈ couple₁ hPW mW then n₀ else n₀ + 1) = fX) := by
          split_ifs <;> intro h' <;> [exact hn.1 (h' ▸ sdiffX_mem_poleW hXW hfX);
            exact hn.2 (h' ▸ sdiffX_mem_poleW hXW hfX)]
        have h2 : pX d ≠ fX := fun h' ↦ (Finset.mem_sdiff.mp hfX).2 (h' ▸ h)
        simp only [h1, h2, or_false]
      · rw [ge_old hPW mW h]
    rw [← tok_eq_of_iff hQ m' pX hneX hdd hfXd hiff]
    by_cases h : d ∈ couple₁ hQ m'
    · rw [if_pos h, if_pos h]; exact fvX0
    · rw [if_neg h, if_neg h]; exact fvX1
  -- the token of a crossing new edge
  have tokNew : ∀ j ∈ (QJ).dangling, (j = n₀ ∨ j = n₀ + 1) → ∀ e ∈ Δ.bd X ∩ Δ.bd W, fe j = e →
      dblJCfv hPW mW hQ m' (if j ∈ couple₁ hQ m' then uX else uX + 1) =
        tok Δ (Δ.bd X) (Δ.bd W) pX e := by
    intro j hj hjn e he hfe
    have hiff : (j = fX ∨ partner hQ m' j = fX) ↔ (e = fX ∨ pX e = fX) := by
      rw [hp' j hj, hfe, ge_old hPW mW (hnoX e (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2)]
      have h1 : j ≠ fX := by
        rcases hjn with rfl | rfl
        · exact fun h' ↦ hn.1 (h' ▸ sdiffX_mem_poleW hXW hfX)
        · exact fun h' ↦ hn.2 (h' ▸ sdiffX_mem_poleW hXW hfX)
      have h2 : e ≠ fX := fun h' ↦ (Finset.mem_sdiff.mp hfX).2 (h' ▸ (Finset.mem_inter.mp he).2)
      simp only [h1, h2, false_or]
    rw [← tok_eq_of_iff hQ m' pX hneX hj hfXd hiff]
    by_cases h : j ∈ couple₁ hQ m'
    · rw [if_pos h, if_pos h]; exact fvX0
    · rw [if_neg h, if_neg h]; exact fvX1
  -- the value of the edge map
  have fe_nX : dblJCfe (X := X) hPW mW nX = eX := by unfold dblJCfe; rw [if_pos rfl]
  have fe_n₀ : dblJCfe (X := X) hPW mW n₀ = jcLabel (X := X) hPW mW n₀ r₀ := by
    unfold dblJCfe; rw [if_neg hnXn.1.symm, if_pos rfl]
  have fe_n₁ : dblJCfe (X := X) hPW mW (n₀ + 1) = jcLabel (X := X) hPW mW (n₀ + 1) r₁ := by
    unfold dblJCfe; rw [if_neg hnXn.2.symm, if_neg (by omega), if_pos rfl]
  have fe_old : ∀ e ∈ (Δ.pole W).Es, e ∈ (QJ).Es → dblJCfe (X := X) hPW mW e = e := by
    intro e he heQ
    have h1 : e ≠ nX := fun h ↦ hnX (h ▸ heQ)
    have h2 : e ≠ n₀ := fun h ↦ hn.1 (h ▸ he)
    have h3 : e ≠ n₀ + 1 := fun h ↦ hn.2 (h ▸ he)
    unfold dblJCfe
    rw [if_neg h1, if_neg h2, if_neg h3]
  -- ends in the cap
  have endsC : ∀ e ∈ (QJ).Es, ∀ i, (cap hQ m').ends e i =
      if (join hPW mW).ends e i ∈ W \ X then (join hPW mW).ends e i
      else (if e ∈ couple₁ hQ m' then uX else uX + 1) := by
    intro e he i
    rw [cap_ends_eq hQ m' he, pole_ends, pole_Vs]
  have e₀ := PJ_ends_n₀ hPW mW
  have e₁ := PJ_ends_n₁ hPW mW
  -- the pair label of a non-crossing first-stage edge
  have pairW : ∀ r ∈ Δ.bd W, r ∉ Δ.bd X → pW r ∉ Δ.bd X →
      min r (pW r) ∈ pairLabels (Δ.bd W) (Δ.bd X) pW ∧
      ((min r (pW r) = r ∧ pW (min r (pW r)) = pW r) ∨
        (min r (pW r) = pW r ∧ pW (min r (pW r)) = r)) := by
    intro r hr hrX hprX
    have hd : r ∈ (Δ.pole W).dangling := dangling_pole W ▸ hr
    have hpr : pW r ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW hd
    unfold pairLabels
    rw [Finset.mem_filter]
    by_cases hle : r ≤ pW r
    · rw [min_eq_left hle]
      exact ⟨⟨Finset.mem_sdiff.mpr ⟨hr, hrX⟩, hprX, hle⟩, Or.inl ⟨rfl, rfl⟩⟩
    · rw [min_eq_right (not_le.mp hle).le, partner_partner hPW mW hd]
      exact ⟨⟨Finset.mem_sdiff.mpr ⟨hpr, hprX⟩, hrX, (not_le.mp hle).le⟩, Or.inr ⟨rfl, rfl⟩⟩
  -- ends of the canonical graph
  have canThru : ∀ e ∈ Δ.bd X ∩ Δ.bd W,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends e 0 = tok Δ (Δ.bd X) (Δ.bd W) pX e ∧
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends e 1 = innerE Δ MM (pW e) := by
    intro e he
    rw [can_ends_thru _ _ _ _ _ _ _ _ he, can_ends_thru _ _ _ _ _ _ _ _ he]
    simp [thruEnd]
  have canX : ∀ d ∈ Δ.bd X \ Δ.bd W, ∀ i,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends d i =
        if Δ.ends d i ∈ MM then Δ.ends d i else tok Δ (Δ.bd X) (Δ.bd W) pX d := by
    intro d hd i
    have hdΔ := hSXE (Finset.mem_sdiff.mp hd).1
    have hnt : d ∉ Δ.bd X ∩ Δ.bd W := fun h ↦ (Finset.mem_sdiff.mp hd).2 (Finset.mem_inter.mp h).2
    rw [can_ends_X _ _ _ _ _ _ _ _ hnt (Or.inl hd)]
    unfold sideEnds
    rw [if_pos rfl, if_neg (tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE d hdΔ)]
  have canE : ∀ i, (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends eX i =
      if i = 0 then tX else tX + 1 := by
    intro i
    rw [can_ends_X _ _ _ _ _ _ _ _ (fun h ↦ tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _
      (hSXE (Finset.mem_inter.mp h).1) rfl) (Or.inr rfl)]
    unfold sideEnds
    rw [if_pos rfl, if_pos rfl]
  have canW : ∀ d ∈ pairLabels (Δ.bd W) (Δ.bd X) pW,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends d 0 = innerE Δ MM d ∧
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends d 1 = innerE Δ MM (pW d) := by
    intro d hd
    unfold pairLabels at hd
    rw [Finset.mem_filter] at hd
    have hdΔ := hSWE (Finset.mem_sdiff.mp hd.1).1
    have hnt : d ∉ Δ.bd X ∩ Δ.bd W := fun h ↦ (Finset.mem_sdiff.mp hd.1).2 (Finset.mem_inter.mp h).1
    have hnX : ¬ (d ∈ Δ.bd X \ Δ.bd W ∨ d = tokE Δ (Δ.bd X) (Δ.bd W)) := by
      rintro (h | h)
      · exact (Finset.mem_sdiff.mp hd.1).2 (Finset.mem_sdiff.mp h).1
      · exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE d hdΔ h
    rw [can_ends_W _ _ _ _ _ _ _ _ hnt hnX (Or.inl hd.1), can_ends_W _ _ _ _ _ _ _ _ hnt hnX (Or.inl hd.1)]
    simp [sideEnds]
  have canOld : ∀ e ∈ Δ.edgesIn (W \ X), ∀ i,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW true false).ends e i = Δ.ends e i := by
    intro e he i
    have hb := edgesIn_sdiff_ends he
    have heΔ := edgesIn_subset _ he
    rw [can_ends_old _ _ _ _ _ _ _ _ (fun h ↦ hb.1 (Finset.mem_inter.mp h).1) (by
        rintro (h | h)
        · exact hb.1 (Finset.mem_sdiff.mp h).1
        · exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE e heΔ h) (by
        rintro (h | h)
        · exact hb.2 (Finset.mem_sdiff.mp h).1
        · exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE e heΔ h)]
  -- the new edge of a crossing couple is recovered from its through edge
  have ge_fe₀ : cross₀ → ge (fe n₀) = n₀ := by
    intro hc
    obtain ⟨hthru, -, hor⟩ := thru₀_spec hPW mW hnoW hc
    rw [ge_thru hPW mW hthru, if_pos]
    rw [mem_couple₁_iff']
    rcases hor with h | h
    · exact Or.inl h
    · right; rw [h, partner_partner hPW mW (bdEmb_mem hPW 0)]
  have ge_fe₁ : cross₁ → ge (fe (n₀ + 1)) = n₀ + 1 := by
    intro hc
    obtain ⟨hthru, -, hor⟩ := thru₁_spec hPW mW hnoW hc
    rw [ge_thru hPW mW hthru, if_neg]
    have hd : fe (n₀ + 1) ∈ (Δ.pole W).dangling := dangling_pole W ▸ (Finset.mem_inter.mp hthru).2
    rw [← mem_couple₂_iff hPW mW hd, mem_couple₂_iff']
    rcases hor with h | h
    · exact Or.inl h
    · right; rw [h, partner_partner hPW mW (bdEmb_mem hPW _)]
  -- the specification of a first-stage edge
  have specN : ∀ j r, (j = n₀ ∧ r = r₀) ∨ (j = n₀ + 1 ∧ r = r₁) →
      (∃ e ∈ Δ.bd X ∩ Δ.bd W, jcLabel (X := X) hPW mW j r = e ∧ fe j = e ∧ ge e = j ∧ j ∈ (QJ).dangling ∧
        pW e ∈ Δ.bd W \ Δ.bd X ∧
        (((cap hQ m').ends j 0 = (if j ∈ couple₁ hQ m' then uX else uX + 1) ∧
            (cap hQ m').ends j 1 = innerE Δ MM (pW e)) ∨
          ((cap hQ m').ends j 0 = innerE Δ MM (pW e) ∧
            (cap hQ m').ends j 1 = (if j ∈ couple₁ hQ m' then uX else uX + 1)))) ∨
      (jcLabel (X := X) hPW mW j r = min r (pW r) ∧ r ∈ Δ.bd W ∧ r ∉ Δ.bd X ∧ pW r ∉ Δ.bd X ∧
        (cap hQ m').ends j 0 = innerE Δ MM r ∧ (cap hQ m').ends j 1 = innerE Δ MM (pW r)) := by
    intro j r hjr
    have hr : r ∈ Δ.bd W := by rcases hjr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hpr : pW r ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (dangling_pole W ▸ hr)
    have hjQ : j ∈ (QJ).Es := by rcases hjr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have ej : (join hPW mW).ends j 0 = innerEnd hPW r ∧ (join hPW mW).ends j 1 = innerEnd hPW (pW r) := by
      rcases hjr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    by_cases hc : r ∈ Δ.bd X ∨ pW r ∈ Δ.bd X
    · left
      have hjd : j ∈ (QJ).dangling := by
        rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]
        rcases hjr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, hc⟩)
        · exact Or.inr (Or.inr ⟨rfl, hc⟩)
      have hthru : fe j ∈ Δ.bd X ∩ Δ.bd W ∧ pW (fe j) ∈ Δ.bd W \ Δ.bd X ∧ (fe j = r ∨ fe j = pW r) := by
        rcases hjr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact thru₀_spec hPW mW hnoW hc
        · exact thru₁_spec hPW mW hnoW hc
      have hge : ge (fe j) = j := by
        rcases hjr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ge_fe₀ hc
        · exact ge_fe₁ hc
      refine ⟨fe j, hthru.1, by unfold jcLabel; rw [if_pos hc], rfl, hge, hjd, hthru.2.1, ?_⟩
      rw [endsC j hjQ, endsC j hjQ, ej.1, ej.2]
      have hrM : innerEnd hPW r ∈ W \ X ↔ r ∉ Δ.bd X := by
        rw [Finset.mem_sdiff, innerEnd_W_mem_iff hXW hPW hr]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨innerEnd_W_mem_W hPW hr, h⟩⟩
      have hprM : innerEnd hPW (pW r) ∈ W \ X ↔ pW r ∉ Δ.bd X := by
        rw [Finset.mem_sdiff, innerEnd_W_mem_iff hXW hPW hpr]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨innerEnd_W_mem_W hPW hpr, h⟩⟩
      rcases hthru.2.2 with h | h
      · have hrX : r ∈ Δ.bd X := h ▸ (Finset.mem_inter.mp hthru.1).1
        have hprX : pW r ∉ Δ.bd X := hnoW r hr hrX
        left
        rw [if_neg (fun h' ↦ (hrM.mp h') hrX), if_pos (hprM.mpr hprX), h,
          innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hpr, hprX⟩)]
        exact ⟨rfl, rfl⟩
      · have hprX : pW r ∈ Δ.bd X := h ▸ (Finset.mem_inter.mp hthru.1).1
        have hrX : r ∉ Δ.bd X := fun hrX ↦ hnoW r hr hrX hprX
        right
        rw [if_pos (hrM.mpr hrX), if_neg (fun h' ↦ (hprM.mp h') hprX), h,
          partner_partner hPW mW (dangling_pole W ▸ hr),
          innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hr, hrX⟩)]
        exact ⟨rfl, rfl⟩
    · right
      have hc' := hc
      push Not at hc'
      refine ⟨by unfold jcLabel; rw [if_neg hc], hr, hc'.1, hc'.2, ?_, ?_⟩
      · rw [endsC j hjQ, ej.1, if_pos, innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hr, hc'.1⟩)]
        exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hr,
          fun h ↦ hc'.1 ((innerEnd_W_mem_iff hXW hPW hr).mp h)⟩
      · rw [endsC j hjQ, ej.2, if_pos, innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hpr, hc'.2⟩)]
        exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hpr,
          fun h ↦ hc'.2 ((innerEnd_W_mem_iff hXW hPW hpr).mp h)⟩
  -- the labels of the two first-stage edges differ
  have labNe : jcLabel (X := X) hPW mW n₀ r₀ ≠ jcLabel (X := X) hPW mW (n₀ + 1) r₁ := by
    intro hlab
    rcases specN n₀ r₀ (Or.inl ⟨rfl, rfl⟩) with ⟨a, ha, hla, -, hga, -⟩ | ⟨hla, hra, ha1, ha2, -⟩ <;>
      rcases specN (n₀ + 1) r₁ (Or.inr ⟨rfl, rfl⟩) with ⟨b, hb, hlb, -, hgb, -⟩ | ⟨hlb, hrb, hb1, hb2, -⟩
    · rw [hla, hlb] at hlab
      rw [hlab] at hga
      rw [hga] at hgb
      omega
    · rw [hla, hlb] at hlab
      have hp := (pairW r₁ hrb hb1 hb2).1
      unfold pairLabels at hp; rw [Finset.mem_filter] at hp
      rw [← hlab] at hp
      exact (Finset.mem_sdiff.mp hp.1).2 (Finset.mem_inter.mp ha).1
    · rw [hla, hlb] at hlab
      have hp := (pairW r₀ hra ha1 ha2).1
      unfold pairLabels at hp; rw [Finset.mem_filter] at hp
      rw [hlab] at hp
      exact (Finset.mem_sdiff.mp hp.1).2 (Finset.mem_inter.mp hb).1
    · rw [hla, hlb] at hlab
      have m1 : min r₀ (pW r₀) ∈ couple₁ hPW mW := by
        rw [couple₁_eq]
        rcases min_choice r₀ (pW r₀) with h | h <;> rw [h]
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have m2 : min r₁ (pW r₁) ∈ couple₂ hPW mW := by
        rw [couple₂_eq]
        rcases min_choice r₁ (pW r₁) with h | h <;> rw [h]
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [← hlab] at m2
      exact (mem_couple₂_iff hPW mW (couple₁_subset_dangling hPW mW m1)).mp m2 m1
  have hcl₁ : (cap hQ m').IsClosed := cap_isClosed hQ m'
  refine ⟨Iso.mk'' hcl₁ (dblJCfv hPW mW hQ m') (dblJCfe (X := X) hPW mW) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- vertices
    intro v hv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert] at hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union]
    simp only [toks, Bool.false_eq_true, if_false, if_true, Finset.notMem_empty, or_false]
    rcases hv with rfl | rfl | hv
    · rw [fvX0]; right; split_ifs <;> simp
    · rw [fvX1]; right; split_ifs <;> simp
    · rw [fvM v hv]; exact Or.inl hv
  · intro v hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union] at hv
    simp only [toks, Bool.false_eq_true, if_false, if_true, Finset.notMem_empty, or_false,
      Finset.mem_insert, Finset.mem_singleton] at hv
    have memX0 : uX ∈ (cap hQ m').Vs := freshV_mem_cap hQ m'
    have memX1 : uX + 1 ∈ (cap hQ m').Vs := freshV_succ_mem_cap hQ m'
    rcases hv with hv | rfl | rfl
    · exact ⟨v, mem_cap_Vs_of_old hQ m' (by rw [pole_Vs]; exact hv), fvM v hv⟩
    · by_cases h : fX ∈ couple₁ hQ m'
      · exact ⟨uX, memX0, by rw [fvX0, if_pos h]⟩
      · exact ⟨uX + 1, memX1, by rw [fvX1, if_neg h]⟩
    · by_cases h : fX ∈ couple₁ hQ m'
      · exact ⟨uX + 1, memX1, by rw [fvX1, if_pos h]⟩
      · exact ⟨uX, memX0, by rw [fvX0, if_neg h]⟩
  · intro u hu v hv huv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert] at hu hv
    rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv <;>
      first
      | rfl
      | (exfalso
         first
         | (have h := htokM _ hv; rw [fvM _ hv] at huv)
         | (have h := htokM _ hu; rw [fvM _ hu] at huv)
         | skip
         simp only [fvX0, fvX1] at huv
         split_ifs at huv <;> omega)
      | (rw [fvM _ hu, fvM _ hv] at huv; exact huv)
  · -- edges into `can`
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union]
    simp only [surv, Bool.false_eq_true, if_false, if_true]
    rw [cap_Es, Finset.mem_insert, mem_QJ_Es hXW hPW mW hnoW] at he
    rcases he with rfl | he | he | rfl | rfl
    · rw [fe_nX]; exact Or.inl (Or.inr (Finset.mem_insert_self _ _))
    · rw [fe_old e (memM e he) ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he))]
      exact Or.inl (Or.inl (Or.inl he))
    · rw [fe_old e (sdiffX_mem_poleW hXW he) ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inl he)))]
      exact Or.inl (Or.inr (Finset.mem_insert_of_mem he))
    · rw [fe_n₀]
      rcases specN n₀ r₀ (Or.inl ⟨rfl, rfl⟩) with ⟨e, he, hl, -⟩ | ⟨hl, hr, h1, h2, -⟩
      · rw [hl]; exact Or.inl (Or.inl (Or.inr he))
      · rw [hl]; exact Or.inr (pairW r₀ hr h1 h2).1
    · rw [fe_n₁]
      rcases specN (n₀ + 1) r₁ (Or.inr ⟨rfl, rfl⟩) with ⟨e, he, hl, -⟩ | ⟨hl, hr, h1, h2, -⟩
      · rw [hl]; exact Or.inl (Or.inl (Or.inr he))
      · rw [hl]; exact Or.inr (pairW r₁ hr h1 h2).1
  · -- surjective on edges
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union] at he
    simp only [surv, Bool.false_eq_true, if_false, if_true, Finset.mem_insert] at he
    rcases he with ((he | he) | (rfl | he)) | he
    · exact ⟨e, by rw [cap_Es]; exact Finset.mem_insert_of_mem ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he)),
        fe_old e (memM e he) ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he))⟩
    · -- a through edge: the new edge of its couple
      have hfe := fe_ge_thru hPW mW hnoW he
      have hge := ge_thru hPW mW he
      have heX := (Finset.mem_inter.mp he).1
      have hed : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ (Finset.mem_inter.mp he).2
      by_cases h1 : e ∈ couple₁ hPW mW
      · rw [if_pos h1] at hge
        have hc : cross₀ := by
          rw [mem_couple₁_iff'] at h1
          rcases h1 with rfl | h1
          · exact Or.inl heX
          · right; rw [← h1, partner_partner hPW mW hed]; exact heX
        refine ⟨n₀, by rw [cap_Es]; exact Finset.mem_insert_of_mem hn0Q, ?_⟩
        rw [fe_n₀]
        unfold jcLabel
        rw [if_pos hc, ← hge, hfe]
      · rw [if_neg h1] at hge
        have hc : cross₁ := by
          rw [← mem_couple₂_iff hPW mW hed, mem_couple₂_iff'] at h1
          rcases h1 with rfl | h1
          · exact Or.inl heX
          · right; rw [← h1, partner_partner hPW mW hed]; exact heX
        refine ⟨n₀ + 1, by rw [cap_Es]; exact Finset.mem_insert_of_mem hn1Q, ?_⟩
        rw [fe_n₁]
        unfold jcLabel
        rw [if_pos hc, ← hge, hfe]
    · exact ⟨nX, by rw [cap_Es]; exact Finset.mem_insert_self _ _, fe_nX⟩
    · have heQ : e ∈ (QJ).Es := (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inl he))
      exact ⟨e, by rw [cap_Es]; exact Finset.mem_insert_of_mem heQ,
        fe_old e (sdiffX_mem_poleW hXW he) heQ⟩
    · -- a pair label of the `W`-cut
      have he' := he
      unfold pairLabels at he'
      rw [Finset.mem_filter] at he'
      have heW := (Finset.mem_sdiff.mp he'.1).1
      have hed : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ heW
      by_cases h1 : e ∈ couple₁ hPW mW
      · rw [mem_couple₁_iff'] at h1
        have hnc : ¬ cross₀ := by
          rintro (h | h)
          · rcases h1 with h1 | h1
            · exact (Finset.mem_sdiff.mp he'.1).2 (by rw [h1]; exact h)
            · rw [← h1] at h; exact he'.2.1 h
          · rcases h1 with h1 | h1
            · rw [← h1] at h; exact he'.2.1 h
            · rw [← h1, partner_partner hPW mW hed] at h; exact (Finset.mem_sdiff.mp he'.1).2 h
        refine ⟨n₀, by rw [cap_Es]; exact Finset.mem_insert_of_mem hn0Q, ?_⟩
        rw [fe_n₀]
        unfold jcLabel
        rw [if_neg hnc]
        rcases h1 with h1 | h1
        · rw [← h1]; exact min_eq_left he'.2.2
        · rw [← h1, partner_partner hPW mW hed]; exact min_eq_right he'.2.2
      · rw [← mem_couple₂_iff hPW mW hed, mem_couple₂_iff'] at h1
        have hnc : ¬ cross₁ := by
          rintro (h | h)
          · rcases h1 with h1 | h1
            · exact (Finset.mem_sdiff.mp he'.1).2 (by rw [h1]; exact h)
            · rw [← h1] at h; exact he'.2.1 h
          · rcases h1 with h1 | h1
            · rw [← h1] at h; exact he'.2.1 h
            · rw [← h1, partner_partner hPW mW hed] at h; exact (Finset.mem_sdiff.mp he'.1).2 h
        refine ⟨n₀ + 1, by rw [cap_Es]; exact Finset.mem_insert_of_mem hn1Q, ?_⟩
        rw [fe_n₁]
        unfold jcLabel
        rw [if_neg hnc]
        rcases h1 with h1 | h1
        · rw [← h1]; exact min_eq_left he'.2.2
        · rw [← h1, partner_partner hPW mW hed]; exact min_eq_right he'.2.2
  · -- injective on edges
    intro d hd e he hde
    have cls : ∀ e ∈ (cap hQ m').Es,
        (dblJCfe (X := X) hPW mW e = eX ∧ e = nX) ∨
        (dblJCfe (X := X) hPW mW e = e ∧ e ∈ Δ.Es ∧ e ∉ Δ.bd W) ∨
        (dblJCfe (X := X) hPW mW e ∈ Δ.bd W ∧ (e = n₀ ∨ e = n₀ + 1)) := by
      intro e he
      rw [cap_Es, Finset.mem_insert, mem_QJ_Es hXW hPW mW hnoW] at he
      rcases he with rfl | he | he | rfl | rfl
      · left; exact ⟨fe_nX, rfl⟩
      · right; left
        exact ⟨fe_old e (memM e he) ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he)),
          edgesIn_subset _ he, (edgesIn_sdiff_ends he).2⟩
      · right; left
        exact ⟨fe_old e (sdiffX_mem_poleW hXW he) ((mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inl he))),
          hSXE (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
      · right; right
        refine ⟨?_, Or.inl rfl⟩
        rw [fe_n₀]
        rcases specN n₀ r₀ (Or.inl ⟨rfl, rfl⟩) with ⟨e, he, hl, -⟩ | ⟨hl, hr, h1, h2, -⟩
        · rw [hl]; exact (Finset.mem_inter.mp he).2
        · rw [hl]
          have := (pairW r₀ hr h1 h2).1
          unfold pairLabels at this; rw [Finset.mem_filter] at this
          exact (Finset.mem_sdiff.mp this.1).1
      · right; right
        refine ⟨?_, Or.inr rfl⟩
        rw [fe_n₁]
        rcases specN (n₀ + 1) r₁ (Or.inr ⟨rfl, rfl⟩) with ⟨e, he, hl, -⟩ | ⟨hl, hr, h1, h2, -⟩
        · rw [hl]; exact (Finset.mem_inter.mp he).2
        · rw [hl]
          have := (pairW r₁ hr h1 h2).1
          unfold pairLabels at this; rw [Finset.mem_filter] at this
          exact (Finset.mem_sdiff.mp this.1).1
    have cd := cls d hd
    have ce := cls e he
    rcases cd with ⟨hd1, hd2⟩ | ⟨hd1, hd2, hd3⟩ | ⟨hd1, hd2⟩ <;>
      rcases ce with ⟨he1, he2⟩ | ⟨he1, he2, he3⟩ | ⟨he1, he2⟩
    · rw [hd2, he2]
    · exfalso; exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _ he2 (he1.symm.trans (hde.symm.trans hd1))
    · exfalso; exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _ (hSWE he1) (hde.symm.trans hd1)
    · exfalso; exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _ hd2 (hd1.symm.trans (hde.trans he1))
    · rw [hd1, he1] at hde; exact hde
    · exfalso; exact hd3 (by rw [← hd1, hde]; exact he1)
    · exfalso; exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _ (hSWE hd1) (hde.trans he1)
    · exfalso; exact he3 (by rw [← he1, ← hde]; exact hd1)
    · rcases hd2 with rfl | rfl <;> rcases he2 with rfl | rfl
      · rfl
      · exfalso; rw [fe_n₀, fe_n₁] at hde; exact labNe hde
      · exfalso; rw [fe_n₀, fe_n₁] at hde; exact labNe hde.symm
      · rfl
  · -- the ends
    intro e he
    have memBdX : ∀ c ∈ Δ.bd X \ Δ.bd W, c ∈ Δ.bd (W \ X) := fun c hc ↦ by
      rw [bd_middle hcl hXW]; exact Finset.mem_union_left _ hc
    rw [cap_Es, Finset.mem_insert, mem_QJ_Es hXW hPW mW hnoW] at he
    rcases he with rfl | he | he | rfl | rfl
    · -- the new edge of the cap
      have h0 : (cap hQ m').ends nX 0 = uX := by rw [cap_ends_new]; simp
      have h1 : (cap hQ m').ends nX 1 = uX + 1 := by rw [cap_ends_new]; simp
      rw [fe_nX, h0, h1, fvX0, fvX1, canE 0, canE 1]
      simp only [if_true, one_ne_zero, if_false]
      split_ifs
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · -- an old inner edge
      left
      have heW := memM e he
      have heQ : e ∈ (QJ).Es := (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he)
      have hends := (mem_edgesIn.mp he).2
      rw [fe_old e heW heQ, canOld e he, canOld e he, endsC e heQ, endsC e heQ,
        join_ends_eq hPW mW heW, join_ends_eq hPW mW heW, pole_ends, if_pos (hends 0),
        if_pos (hends 1), fvM _ (hends 0), fvM _ (hends 1)]
      exact ⟨rfl, rfl⟩
    · -- an old dangling edge of `X`
      left
      have heW := sdiffX_mem_poleW hXW he
      have heQ : e ∈ (QJ).Es := (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inl he))
      rw [fe_old e heW heQ, canX e he, canX e he, endsC e heQ, endsC e heQ,
        join_ends_eq hPW mW heW, join_ends_eq hPW mW heW, pole_ends]
      have fin : ∀ i, (if Δ.ends e i ∈ MM then Δ.ends e i else tok Δ (Δ.bd X) (Δ.bd W) pX e) =
          dblJCfv hPW mW hQ m' (if Δ.ends e i ∈ MM then Δ.ends e i
            else (if e ∈ couple₁ hQ m' then uX else uX + 1)) := by
        intro i
        by_cases hM : Δ.ends e i ∈ MM
        · rw [if_pos hM, if_pos hM, fvM _ hM]
        · rw [if_neg hM, if_neg hM, tokOld e he]
      exact ⟨fin 0, fin 1⟩
    · -- the first new edge of the join
      rw [fe_n₀]
      rcases specN n₀ r₀ (Or.inl ⟨rfl, rfl⟩) with ⟨e, he, hl, hfe, -, hjd, hpw, hends⟩ |
        ⟨hl, hr, h1, h2, e0, e1⟩
      · rw [hl, (canThru _ he).1, (canThru _ he).2]
        have ht := tokNew n₀ hjd (Or.inl rfl) e he hfe
        have hm := fvM _ (innerE_mem (memBdW _ hpw))
        rcases hends with ⟨a0, a1⟩ | ⟨a0, a1⟩
        · left; rw [a0, a1, ht, hm]; exact ⟨rfl, rfl⟩
        · right; rw [a0, a1, ht, hm]; exact ⟨rfl, rfl⟩
      · rw [hl, e0, e1]
        have hp := pairW r₀ hr h1 h2
        rw [(canW _ hp.1).1, (canW _ hp.1).2, fvM _ (innerE_mem (memBdW _ (Finset.mem_sdiff.mpr ⟨hr, h1⟩))),
          fvM _ (innerE_mem (memBdW _ (Finset.mem_sdiff.mpr ⟨hpr₀, h2⟩)))]
        rcases hp.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
        · right; rw [h4, h3]; exact ⟨rfl, rfl⟩
    · -- the second new edge of the join
      rw [fe_n₁]
      rcases specN (n₀ + 1) r₁ (Or.inr ⟨rfl, rfl⟩) with ⟨e, he, hl, hfe, -, hjd, hpw, hends⟩ |
        ⟨hl, hr, h1, h2, e0, e1⟩
      · rw [hl, (canThru _ he).1, (canThru _ he).2]
        have ht := tokNew (n₀ + 1) hjd (Or.inr rfl) e he hfe
        have hm := fvM _ (innerE_mem (memBdW _ hpw))
        rcases hends with ⟨a0, a1⟩ | ⟨a0, a1⟩
        · left; rw [a0, a1, ht, hm]; exact ⟨rfl, rfl⟩
        · right; rw [a0, a1, ht, hm]; exact ⟨rfl, rfl⟩
      · rw [hl, e0, e1]
        have hp := pairW r₁ hr h1 h2
        rw [(canW _ hp.1).1, (canW _ hp.1).2, fvM _ (innerE_mem (memBdW _ (Finset.mem_sdiff.mpr ⟨hr, h1⟩))),
          fvM _ (innerE_mem (memBdW _ (Finset.mem_sdiff.mpr ⟨hpr₁, h2⟩)))]
        rcases hp.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
        · right; rw [h4, h3]; exact ⟨rfl, rfl⟩

end JC

end FinGraph
end GraphPuzzles
