import GraphPuzzles.Factorization.Diamond.FactorDblCC
import GraphPuzzles.Factorization.Diamond.FactorDblJJ

/-!
# The double completion: cap at `W`, then join at `X`

For nested shores `X ⊆ W`, the cap of the pole of `W` followed by the join of the pole of
`(W \ X) ∪ {new}` is isomorphic to the canonical double completion with a cap gadget at `∂W`
and a join gadget at `∂X`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section CJ

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPW : (Δ.pole W).IsPole4) (mW : Fin 3) (hPX : (Δ.pole X).IsPole4) (mX : Fin 3)
  (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
  (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)
  (hQ : ((cap hPW mW).pole
    (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X)))).IsPole4) (m' : Fin 3)
  (hp' : ∀ c ∈ Δ.bd X, partner hQ m' c = partner hPX mX c)

set_option quotPrecheck false in
local notation "uW" => freshV (Δ.pole W)
set_option quotPrecheck false in
local notation "nW" => freshE (Δ.pole W)
set_option quotPrecheck false in
local notation "ZC" => insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X))
set_option quotPrecheck false in
local notation "QC" => (cap hPW mW).pole (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X)))
set_option quotPrecheck false in
local notation "p₀" => freshE ((cap hPW mW).pole (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X))))
set_option quotPrecheck false in
local notation "c₀" => bdEmb hQ 0
set_option quotPrecheck false in
local notation "c₁" => bdEmb hQ (other m')
set_option quotPrecheck false in
local notation "tW" => tokU Δ (Δ.bd W) (Δ.bd X)
set_option quotPrecheck false in
local notation "eW" => tokE Δ (Δ.bd W) (Δ.bd X)
set_option quotPrecheck false in
local notation "fW" => first (Δ.bd W) (Δ.bd X)
set_option quotPrecheck false in
local notation "pX" => partner hPX mX
set_option quotPrecheck false in
local notation "pW" => partner hPW mW
set_option quotPrecheck false in
local notation "MM" => W \ X

/-- The canonical label of the new edge of the join attached to `c ∈ ∂X`. -/
noncomputable def cjLabel (c : ℕ) : ℕ :=
  if c ∈ Δ.bd W then c else if pX c ∈ Δ.bd W then pX c else min c (pX c)

/-- The vertex map. -/
noncomputable def dblCJfv (v : ℕ) : ℕ :=
  if v = uW then (if fW ∈ couple₁ hPW mW then tW else tW + 1)
  else if v = uW + 1 then (if fW ∈ couple₁ hPW mW then tW + 1 else tW)
  else v

/-- The edge map. -/
noncomputable def dblCJfe (e : ℕ) : ℕ :=
  if e = p₀ then cjLabel (W := W) hPX mX c₀ else if e = p₀ + 1 then cjLabel (W := W) hPX mX c₁
  else if e = nW then eW else e

include hcl hXW hW in
/-- The inner end in the projected pole of a through edge is the fresh vertex of its couple. -/
theorem innerEnd_QC_thru {c : ℕ} (hc : c ∈ Δ.bd X ∩ Δ.bd W) :
    innerEnd hQ c = if c ∈ couple₁ hPW mW then uW else uW + 1 := by
  have hdang := capPole_dangling hcl hXW hW hPW mW
  have hcd : c ∈ (QC).dangling := by rw [hdang]; exact (Finset.mem_inter.mp hc).1
  have hcW : c ∈ (Δ.pole W).Es := by
    rw [pole_Es, Finset.mem_union]; exact Or.inr (Finset.mem_inter.mp hc).2
  have hin := innerEnd_mem hQ hcd
  rw [pole_Vs] at hin
  rw [← ends_innerIdx hQ hcd, pole_ends] at hin ⊢
  rw [cap_ends_eq hPW mW hcW, pole_ends, pole_Vs] at hin ⊢
  by_cases h : Δ.ends c (innerIdx hQ hcd) ∈ W
  · exfalso
    rw [if_pos h] at hin
    have hX : Δ.ends c (innerIdx hQ hcd) ∈ X := (thru_ends hXW hc _).mpr h
    rw [Finset.mem_insert, Finset.mem_insert] at hin
    have huW := uW_notMem (Δ := Δ) (W := W)
    rcases hin with hin | hin | hin
    · exact huW.1 (hin ▸ h)
    · exact huW.2 (hin ▸ h)
    · exact (Finset.mem_sdiff.mp hin).2 hX
  · rw [if_neg h]

include hcl hXW hW in
/-- The inner end in the projected pole of an old dangling edge. -/
theorem innerEnd_QC_old {c : ℕ} (hc : c ∈ Δ.bd X \ Δ.bd W) :
    innerEnd hQ c = innerE Δ MM c := by
  have hdang := capPole_dangling hcl hXW hW hPW mW
  have hcd : c ∈ (QC).dangling := by rw [hdang]; exact (Finset.mem_sdiff.mp hc).1
  have hcW := sdiffX_mem_poleW hXW hc
  have hin := innerEnd_mem hQ hcd
  rw [pole_Vs] at hin
  rw [← ends_innerIdx hQ hcd, pole_ends] at hin ⊢
  rw [cap_ends_eq hPW mW hcW, pole_ends, pole_Vs] at hin ⊢
  have h1 := sdiffX_ends hXW hc (innerIdx hQ hcd)
  rw [if_pos h1.1] at hin ⊢
  rw [Finset.mem_insert, Finset.mem_insert] at hin
  have huW := uW_notMem (Δ := Δ) (W := W)
  have hbd : c ∈ Δ.bd (W \ X) := by
    rw [mem_bd]
    refine ⟨bd_subset X (Finset.mem_sdiff.mp hc).1, ?_⟩
    have h0 := sdiffX_ends hXW hc 0
    have h2 := sdiffX_ends hXW hc 1
    have := (Finset.mem_sdiff.mp hc).1
    rw [mem_bd] at this
    tauto
  rcases hin with hin | hin | hin
  · exact absurd (hin ▸ h1.1) huW.1
  · exact absurd (hin ▸ h1.1) huW.2
  · exact (innerE_eq hbd hin).symm

include hcl hXW hW in
/-- Membership in the edge set of the cap-join. -/
theorem mem_dblCJ_Es {e : ℕ} : e ∈ (join hQ m').Es ↔
    e = p₀ ∨ e = p₀ + 1 ∨ e = nW ∨ e ∈ Δ.edgesIn (W \ X) ∨ e ∈ Δ.bd W \ Δ.bd X := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff,
    mem_capPole_Es hXW hPW mW, capPole_dangling hcl hXW hW hPW mW]
  constructor
  · rintro (rfl | rfl | ⟨h, hX⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · right; right
      rcases h with rfl | h | h | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact absurd h hX
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨h, hX⟩))
  · rintro (rfl | rfl | rfl | h | h)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · right; right
      refine ⟨Or.inl rfl, ?_⟩
      intro h
      exact freshE_notMem (P := Δ.pole W) (by
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, -⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset X h) (hXW hi))
    · exact Or.inr (Or.inr ⟨Or.inr (Or.inl h), (edgesIn_sdiff_ends h).1⟩)
    · exact Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp h).1)),
        (Finset.mem_sdiff.mp h).2⟩)

include hcl hXW hW hnoX hnoW hp' in
/-- **The cap-join is the canonical double completion.** -/
theorem dblCJ_iso : Nonempty (Iso (join hQ m')
    (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) false true)) := by
  have hneX := sdiffX_nonempty hPX mX hnoX
  have hneW := sdiffW_nonempty hPW mW hnoW
  have huW := uW_notMem (Δ := Δ) (W := W)
  have hdang := capPole_dangling hcl hXW hW hPW mW
  have hnW : nW ∉ (Δ.pole W).Es := freshE_notMem
  have hnWΔ : ∀ e ∈ (Δ.pole W).Es, e ≠ nW := fun e he h ↦ hnW (h ▸ he)
  have hnWmem : nW ∈ (QC).Es := (mem_capPole_Es hXW hPW mW).mpr (Or.inl rfl)
  have hp0 : p₀ ∉ (QC).Es := freshE_notMem
  have hp1 : p₀ + 1 ∉ (QC).Es := freshE_succ_notMem
  have hSXE : Δ.bd X ⊆ Δ.Es := bd_subset X
  have hSWE : Δ.bd W ⊆ Δ.Es := bd_subset W
  have hMV : W \ X ⊆ Δ.Vs := fun v hv ↦ hW (Finset.mem_sdiff.mp hv).1
  have htokM : ∀ v ∈ W \ X, v ≠ tW ∧ v ≠ tW + 1 := fun v hv ↦ tokU_notMem Δ (Δ.bd W) (Δ.bd X) v (hMV hv)
  have huWM : ∀ v ∈ W \ X, v ≠ uW ∧ v ≠ uW + 1 := by
    intro v hv
    exact ⟨fun h ↦ huW.1 (by rw [← h]; exact (Finset.mem_sdiff.mp hv).1),
      fun h ↦ huW.2 (by rw [← h]; exact (Finset.mem_sdiff.mp hv).1)⟩
  have memM : ∀ e ∈ Δ.edgesIn (W \ X), e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]; left
    rw [mem_edgesIn] at he ⊢
    exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
  have memSW : ∀ e ∈ Δ.bd W, e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]; exact Or.inr he
  have hpn : p₀ ≠ nW ∧ p₀ + 1 ≠ nW := ⟨fun h ↦ hp0 (h ▸ hnWmem), fun h ↦ hp1 (h ▸ hnWmem)⟩
  -- the vertex map
  have fvW0 : dblCJfv (X := X) hPW mW uW = if fW ∈ couple₁ hPW mW then tW else tW + 1 := by
    unfold dblCJfv; rw [if_pos rfl]
  have fvW1 : dblCJfv (X := X) hPW mW (uW + 1) = if fW ∈ couple₁ hPW mW then tW + 1 else tW := by
    unfold dblCJfv; rw [if_neg (by omega), if_pos rfl]
  have fvM : ∀ v ∈ W \ X, dblCJfv (X := X) hPW mW v = v := by
    intro v hv
    have h := huWM v hv
    unfold dblCJfv
    rw [if_neg h.1, if_neg h.2]
  have tokW : ∀ d ∈ Δ.bd W, dblCJfv (X := X) hPW mW (if d ∈ couple₁ hPW mW then uW else uW + 1) =
      tok Δ (Δ.bd W) (Δ.bd X) pW d := by
    intro d hd
    rw [← tok_eq_of_partner hPW mW (dangling_pole W) pW (fun _ _ ↦ rfl) hneW hd]
    by_cases h : d ∈ couple₁ hPW mW
    · rw [if_pos h, if_pos h]; exact fvW0
    · rw [if_neg h, if_neg h]; exact fvW1
  -- the edge map
  have fe_p₀ : dblCJfe hPW mW hPX mX hQ m' p₀ = cjLabel (W := W) hPX mX c₀ := by
    unfold dblCJfe; rw [if_pos rfl]
  have fe_p₁ : dblCJfe hPW mW hPX mX hQ m' (p₀ + 1) = cjLabel (W := W) hPX mX c₁ := by
    unfold dblCJfe; rw [if_neg (by omega), if_pos rfl]
  have fe_nW : dblCJfe hPW mW hPX mX hQ m' nW = eW := by
    unfold dblCJfe; rw [if_neg hpn.1.symm, if_neg hpn.2.symm, if_pos rfl]
  have fe_old : ∀ e ∈ (Δ.pole W).Es, e ∈ (QC).Es → dblCJfe hPW mW hPX mX hQ m' e = e := by
    intro e he heQ
    have h1 : e ≠ p₀ := fun h ↦ hp0 (h ▸ heQ)
    have h2 : e ≠ p₀ + 1 := fun h ↦ hp1 (h ▸ heQ)
    unfold dblCJfe
    rw [if_neg h1, if_neg h2, if_neg (hnWΔ e he)]
  -- the partner in the projected pole
  have hp'' : ∀ c ∈ (QC).dangling, partner hQ m' c = pX c := by
    intro c hc; rw [hdang] at hc; exact hp' c hc
  -- ends in the first cap for old edges
  have endsP : ∀ e ∈ (Δ.pole W).Es, ∀ i, (cap hPW mW).ends e i =
      if Δ.ends e i ∈ W then Δ.ends e i else (if e ∈ couple₁ hPW mW then uW else uW + 1) := by
    intro e he i
    rw [cap_ends_eq hPW mW he, pole_ends, pole_Vs]
  -- ends of the new edges of the join
  have e₀ : (join hQ m').ends p₀ 0 = innerEnd hQ c₀ ∧
      (join hQ m').ends p₀ 1 = innerEnd hQ (partner hQ m' c₀) := by
    rw [join_ends_new₁, join_ends_new₁, partner_bdEmb]; simp
  have e₁ : (join hQ m').ends (p₀ + 1) 0 = innerEnd hQ c₁ ∧
      (join hQ m').ends (p₀ + 1) 1 = innerEnd hQ (partner hQ m' c₁) := by
    rw [join_ends_new₂, join_ends_new₂, partner_bdEmb]; simp
  -- the specification of the label of a dangling edge `c ∈ ∂X`
  have spec : ∀ c ∈ Δ.bd X,
      (cjLabel (W := W) hPX mX c ∈ Δ.bd X ∩ Δ.bd W ∧ cjLabel (W := W) hPX mX c = c ∧
        innerEnd hQ c = (if c ∈ couple₁ hPW mW then uW else uW + 1) ∧
        innerEnd hQ (pX c) = innerE Δ MM (pX c)) ∨
      (cjLabel (W := W) hPX mX c ∈ Δ.bd X ∩ Δ.bd W ∧ cjLabel (W := W) hPX mX c = pX c ∧
        innerEnd hQ c = innerE Δ MM c ∧
        innerEnd hQ (pX c) = (if pX c ∈ couple₁ hPW mW then uW else uW + 1)) ∨
      (cjLabel (W := W) hPX mX c ∈ pairLabels (Δ.bd X) (Δ.bd W) pX ∧
        innerEnd hQ c = innerE Δ MM c ∧ innerEnd hQ (pX c) = innerE Δ MM (pX c) ∧
        ((cjLabel (W := W) hPX mX c = c ∧ pX (cjLabel (W := W) hPX mX c) = pX c) ∨
          (cjLabel (W := W) hPX mX c = pX c ∧ pX (cjLabel (W := W) hPX mX c) = c))) := by
    intro c hc
    have hcd : c ∈ (Δ.pole X).dangling := dangling_pole X ▸ hc
    have hpXc : pX c ∈ Δ.bd X := pX_mem hPX mX hc
    by_cases h1 : c ∈ Δ.bd W
    · left
      have hthru : c ∈ Δ.bd X ∩ Δ.bd W := Finset.mem_inter.mpr ⟨hc, h1⟩
      have hpX' : pX c ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨hpXc, hnoX c hc h1⟩
      refine ⟨by unfold cjLabel; rw [if_pos h1]; exact hthru, by unfold cjLabel; rw [if_pos h1],
        innerEnd_QC_thru hcl hXW hW hPW mW hQ hthru, innerEnd_QC_old hcl hXW hW hPW mW hQ hpX'⟩
    · by_cases h2 : pX c ∈ Δ.bd W
      · right; left
        have hthru : pX c ∈ Δ.bd X ∩ Δ.bd W := Finset.mem_inter.mpr ⟨hpXc, h2⟩
        have hc' : c ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨hc, h1⟩
        refine ⟨by unfold cjLabel; rw [if_neg h1, if_pos h2]; exact hthru,
          by unfold cjLabel; rw [if_neg h1, if_pos h2],
          innerEnd_QC_old hcl hXW hW hPW mW hQ hc', innerEnd_QC_thru hcl hXW hW hPW mW hQ hthru⟩
      · right; right
        have hc' : c ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨hc, h1⟩
        have hpX' : pX c ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨hpXc, h2⟩
        have hlab : cjLabel (W := W) hPX mX c = min c (pX c) := by unfold cjLabel; rw [if_neg h1, if_neg h2]
        refine ⟨?_, innerEnd_QC_old hcl hXW hW hPW mW hQ hc', innerEnd_QC_old hcl hXW hW hPW mW hQ hpX', ?_⟩
        · rw [hlab]
          unfold pairLabels
          rw [Finset.mem_filter]
          by_cases hle : c ≤ pX c
          · rw [min_eq_left hle]; exact ⟨hc', h2, hle⟩
          · rw [min_eq_right (not_le.mp hle).le, partner_partner hPX mX hcd]
            exact ⟨hpX', h1, (not_le.mp hle).le⟩
        · rw [hlab]
          by_cases hle : c ≤ pX c
          · rw [min_eq_left hle]; exact Or.inl ⟨rfl, rfl⟩
          · rw [min_eq_right (not_le.mp hle).le, partner_partner hPX mX hcd]
            exact Or.inr ⟨rfl, rfl⟩
  have hc₀ : c₀ ∈ Δ.bd X := hdang ▸ bdEmb_mem hQ 0
  have hc₁ : c₁ ∈ Δ.bd X := hdang ▸ bdEmb_mem hQ _
  have hc₀d : c₀ ∈ (QC).dangling := bdEmb_mem hQ 0
  have hc₁d : c₁ ∈ (QC).dangling := bdEmb_mem hQ _
  have lab_mem : ∀ c ∈ Δ.bd X, cjLabel (W := W) hPX mX c = c ∨ cjLabel (W := W) hPX mX c = pX c := by
    intro c hc
    unfold cjLabel
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact min_choice _ _
  -- ends of the canonical graph
  have canThru : ∀ e ∈ Δ.bd X ∩ Δ.bd W,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends e 0 = innerE Δ MM (pX e) ∧
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends e 1 = tok Δ (Δ.bd W) (Δ.bd X) pW e := by
    intro e he
    rw [can_ends_thru _ _ _ _ _ _ _ _ he, can_ends_thru _ _ _ _ _ _ _ _ he]
    simp [thruEnd]
  have canX : ∀ d ∈ pairLabels (Δ.bd X) (Δ.bd W) pX,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends d 0 = innerE Δ MM d ∧
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends d 1 = innerE Δ MM (pX d) := by
    intro d hd
    unfold pairLabels at hd
    rw [Finset.mem_filter] at hd
    have hnt : d ∉ Δ.bd X ∩ Δ.bd W := fun h ↦ (Finset.mem_sdiff.mp hd.1).2 (Finset.mem_inter.mp h).2
    rw [can_ends_X _ _ _ _ _ _ _ _ hnt (Or.inl hd.1), can_ends_X _ _ _ _ _ _ _ _ hnt (Or.inl hd.1)]
    simp [sideEnds]
  have canW : ∀ d ∈ Δ.bd W \ Δ.bd X, ∀ i,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends d i =
        if Δ.ends d i ∈ MM then Δ.ends d i else tok Δ (Δ.bd W) (Δ.bd X) pW d := by
    intro d hd i
    have hdΔ := hSWE (Finset.mem_sdiff.mp hd).1
    have hnt : d ∉ Δ.bd X ∩ Δ.bd W := fun h ↦ (Finset.mem_sdiff.mp hd).2 (Finset.mem_inter.mp h).1
    have hnX : ¬ (d ∈ Δ.bd X \ Δ.bd W ∨ d = tokE Δ (Δ.bd X) (Δ.bd W)) := by
      rintro (h | h)
      · exact (Finset.mem_sdiff.mp hd).2 (Finset.mem_sdiff.mp h).1
      · exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE d hdΔ h
    rw [can_ends_W _ _ _ _ _ _ _ _ hnt hnX (Or.inl hd)]
    unfold sideEnds
    rw [if_pos rfl, if_neg (tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE d hdΔ)]
  have canE : ∀ i, (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends eW i =
      if i = 0 then tW else tW + 1 := by
    intro i
    have hteX := tokE_ne Δ (Δ.bd X) (Δ.bd W) hneX hneW
    rw [can_ends_W _ _ _ _ _ _ _ _ (fun h ↦ tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _
      (hSWE (Finset.mem_inter.mp h).2) rfl) (by
        rintro (h | h)
        · exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ (hSXE (Finset.mem_sdiff.mp h).1) rfl
        · exact hteX h.symm) (Or.inr rfl)]
    unfold sideEnds
    rw [if_pos rfl, if_pos rfl]
  have canOld : ∀ e ∈ Δ.edgesIn (W \ X), ∀ i,
      (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends e i = Δ.ends e i := by
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
  have hcl₁ : (join hQ m').IsClosed := join_isClosed hQ m'
  refine ⟨Iso.mk'' hcl₁ (dblCJfv (X := X) hPW mW) (dblCJfe hPW mW hPX mX hQ m') ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- vertices
    intro v hv
    rw [join_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert] at hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union]
    simp only [toks, Bool.false_eq_true, if_false, if_true, Finset.notMem_empty, or_false]
    rcases hv with rfl | rfl | hv
    · rw [fvW0]; right; split_ifs <;> simp
    · rw [fvW1]; right; split_ifs <;> simp
    · rw [fvM v hv]; exact Or.inl hv
  · intro v hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union] at hv
    simp only [toks, Bool.false_eq_true, if_false, if_true, Finset.notMem_empty, or_false,
      Finset.mem_insert, Finset.mem_singleton] at hv
    have memW0 : uW ∈ (join hQ m').Vs := by rw [join_Vs, pole_Vs]; exact Finset.mem_insert_self _ _
    have memW1 : uW + 1 ∈ (join hQ m').Vs := by
      rw [join_Vs, pole_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rcases hv with hv | rfl | rfl
    · exact ⟨v, by rw [join_Vs, pole_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv),
        fvM v hv⟩
    · by_cases h : fW ∈ couple₁ hPW mW
      · exact ⟨uW, memW0, by rw [fvW0, if_pos h]⟩
      · exact ⟨uW + 1, memW1, by rw [fvW1, if_neg h]⟩
    · by_cases h : fW ∈ couple₁ hPW mW
      · exact ⟨uW + 1, memW1, by rw [fvW1, if_pos h]⟩
      · exact ⟨uW, memW0, by rw [fvW0, if_neg h]⟩
  · intro u hu v hv huv
    rw [join_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert] at hu hv
    rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv <;>
      first
      | rfl
      | (exfalso
         first
         | (have h := htokM _ hv; rw [fvM _ hv] at huv)
         | (have h := htokM _ hu; rw [fvM _ hu] at huv)
         | skip
         simp only [fvW0, fvW1] at huv
         split_ifs at huv <;> omega)
      | (rw [fvM _ hu, fvM _ hv] at huv; exact huv)
  · -- edges into `can`
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union]
    simp only [surv, Bool.false_eq_true, if_false, if_true]
    rw [mem_dblCJ_Es hcl hXW hW hPW mW hQ m'] at he
    rcases he with rfl | rfl | rfl | he | he
    · rw [fe_p₀]
      rcases spec c₀ hc₀ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rw [fe_p₁]
      rcases spec c₁ hc₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rw [fe_nW]; exact Or.inr (Finset.mem_insert_self _ _)
    · rw [fe_old e (memM e he) ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he)))]
      exact Or.inl (Or.inl (Or.inl he))
    · rw [fe_old e (memSW e (Finset.mem_sdiff.mp he).1)
        ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp he).1))))]
      exact Or.inr (Finset.mem_insert_of_mem he)
  · -- surjective on edges
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union] at he
    simp only [surv, Bool.false_eq_true, if_false, if_true, Finset.mem_insert] at he
    rcases he with ((he | he) | he) | (rfl | he)
    · exact ⟨e, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inr (Or.inr (Or.inr (Or.inl he)))),
        fe_old e (memM e he) ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he)))⟩
    · -- a through edge
      have heX := (Finset.mem_inter.mp he).1
      have heW := (Finset.mem_inter.mp he).2
      have hed : e ∈ (QC).dangling := by rw [hdang]; exact heX
      have hpe : partner hQ m' e = pX e := hp' e heX
      have hpXe : pX e ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨pX_mem hPX mX heX, hnoX e heX heW⟩
      have key : ∀ c ∈ Δ.bd X, (c = e ∨ c = pX e) → cjLabel (W := W) hPX mX c = e := by
        intro c _ h
        rcases h with rfl | rfl
        · unfold cjLabel; rw [if_pos heW]
        · unfold cjLabel
          rw [if_neg (Finset.mem_sdiff.mp hpXe).2, partner_partner hPX mX (dangling_pole X ▸ heX),
            if_pos heW]
      by_cases h1 : e ∈ couple₁ hQ m'
      · rw [mem_couple₁_iff'] at h1
        refine ⟨p₀, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inl rfl), ?_⟩
        rw [fe_p₀]
        apply key c₀ hc₀
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
      · rw [← mem_couple₂_iff hQ m' hed, mem_couple₂_iff'] at h1
        refine ⟨p₀ + 1, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inr (Or.inl rfl)), ?_⟩
        rw [fe_p₁]
        apply key c₁ hc₁
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
    · -- a pair label of the `X`-cut
      have he' := he
      unfold pairLabels at he'
      rw [Finset.mem_filter] at he'
      have heX := (Finset.mem_sdiff.mp he'.1).1
      have hed : e ∈ (QC).dangling := by rw [hdang]; exact heX
      have hpe : partner hQ m' e = pX e := hp' e heX
      have hed' : e ∈ (Δ.pole X).dangling := dangling_pole X ▸ heX
      have key : ∀ c ∈ Δ.bd X, (c = e ∨ c = pX e) → cjLabel (W := W) hPX mX c = e := by
        intro c _ h
        rcases h with rfl | rfl
        · unfold cjLabel
          rw [if_neg (Finset.mem_sdiff.mp he'.1).2, if_neg he'.2.1, min_eq_left he'.2.2]
        · unfold cjLabel
          rw [if_neg he'.2.1, partner_partner hPX mX hed', if_neg (Finset.mem_sdiff.mp he'.1).2,
            min_eq_right he'.2.2]
      by_cases h1 : e ∈ couple₁ hQ m'
      · rw [mem_couple₁_iff'] at h1
        refine ⟨p₀, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inl rfl), ?_⟩
        rw [fe_p₀]
        apply key c₀ hc₀
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
      · rw [← mem_couple₂_iff hQ m' hed, mem_couple₂_iff'] at h1
        refine ⟨p₀ + 1, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inr (Or.inl rfl)), ?_⟩
        rw [fe_p₁]
        apply key c₁ hc₁
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
    · exact ⟨nW, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inr (Or.inr (Or.inl rfl))), fe_nW⟩
    · exact ⟨e, (mem_dblCJ_Es hcl hXW hW hPW mW hQ m').mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))),
        fe_old e (memSW e (Finset.mem_sdiff.mp he).1)
          ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp he).1))))⟩
  · -- injective on edges
    intro d hd e he hde
    have cls : ∀ e ∈ (join hQ m').Es,
        (dblCJfe hPW mW hPX mX hQ m' e ∈ Δ.bd X ∧ (e = p₀ ∨ e = p₀ + 1)) ∨
        (dblCJfe hPW mW hPX mX hQ m' e = eW ∧ e = nW) ∨
        (dblCJfe hPW mW hPX mX hQ m' e = e ∧ e ∈ Δ.Es ∧ e ∉ Δ.bd X) := by
      intro e he
      rw [mem_dblCJ_Es hcl hXW hW hPW mW hQ m'] at he
      rcases he with rfl | rfl | rfl | he | he
      · left; refine ⟨?_, Or.inl rfl⟩
        rw [fe_p₀]
        rcases lab_mem c₀ hc₀ with h | h <;> rw [h]
        · exact hc₀
        · exact pX_mem hPX mX hc₀
      · left; refine ⟨?_, Or.inr rfl⟩
        rw [fe_p₁]
        rcases lab_mem c₁ hc₁ with h | h <;> rw [h]
        · exact hc₁
        · exact pX_mem hPX mX hc₁
      · right; left; exact ⟨fe_nW, rfl⟩
      · right; right
        exact ⟨fe_old e (memM e he) ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he))),
          edgesIn_subset _ he, (edgesIn_sdiff_ends he).1⟩
      · right; right
        exact ⟨fe_old e (memSW e (Finset.mem_sdiff.mp he).1)
          ((mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp he).1)))),
          hSWE (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
    have cd := cls d hd
    have ce := cls e he
    rcases cd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ | ⟨hd1, hd2, hd3⟩ <;>
      rcases ce with ⟨he1, he2⟩ | ⟨he1, he2⟩ | ⟨he1, he2, he3⟩
    · rcases hd2 with rfl | rfl <;> rcases he2 with rfl | rfl
      · rfl
      · exfalso
        rw [fe_p₀, fe_p₁] at hde
        have m1 : cjLabel (W := W) hPX mX c₀ ∈ couple₁ hQ m' := by
          rw [couple₁_eq, hp' c₀ hc₀]
          rcases lab_mem c₀ hc₀ with h | h <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have m2 : cjLabel (W := W) hPX mX c₁ ∈ couple₂ hQ m' := by
          rw [couple₂_eq, hp' c₁ hc₁]
          rcases lab_mem c₁ hc₁ with h | h <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [← hde] at m2
        exact (mem_couple₂_iff hQ m' (couple₁_subset_dangling hQ m' m1)).mp m2 m1
      · exfalso
        rw [fe_p₀, fe_p₁] at hde
        have m1 : cjLabel (W := W) hPX mX c₀ ∈ couple₁ hQ m' := by
          rw [couple₁_eq, hp' c₀ hc₀]
          rcases lab_mem c₀ hc₀ with h | h <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have m2 : cjLabel (W := W) hPX mX c₁ ∈ couple₂ hQ m' := by
          rw [couple₂_eq, hp' c₁ hc₁]
          rcases lab_mem c₁ hc₁ with h | h <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [hde] at m2
        exact (mem_couple₂_iff hQ m' (couple₁_subset_dangling hQ m' m1)).mp m2 m1
      · rfl
    · exfalso; exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ (hSXE hd1) (hde.trans he1)
    · exfalso; exact he3 (by rw [← he1, ← hde]; exact hd1)
    · exfalso; exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ (hSXE he1) (hde.symm.trans hd1)
    · rw [hd2, he2]
    · exfalso; exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ he2 (he1.symm.trans (hde.symm.trans hd1))
    · exfalso; exact hd3 (by rw [← hd1, hde]; exact he1)
    · exfalso; exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ hd2 (hd1.symm.trans (hde.trans he1))
    · rw [hd1, he1] at hde; exact hde
  · -- the ends
    intro e he
    have memBd : ∀ c ∈ Δ.bd X \ Δ.bd W, c ∈ Δ.bd (W \ X) := fun c hc ↦ by
      rw [bd_middle hcl hXW]; exact Finset.mem_union_left _ hc
    -- the ends of the new edge attached to a dangling edge `c ∈ ∂X`
    have endsNew : ∀ c ∈ Δ.bd X,
        ((can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends (cjLabel (W := W) hPX mX c) 0 =
            dblCJfv (X := X) hPW mW (innerEnd hQ c) ∧
          (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends (cjLabel (W := W) hPX mX c) 1 =
            dblCJfv (X := X) hPW mW (innerEnd hQ (pX c))) ∨
        ((can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends (cjLabel (W := W) hPX mX c) 0 =
            dblCJfv (X := X) hPW mW (innerEnd hQ (pX c)) ∧
          (can Δ MM (Δ.bd X) (Δ.bd W) pX pW false true).ends (cjLabel (W := W) hPX mX c) 1 =
            dblCJfv (X := X) hPW mW (innerEnd hQ c)) := by
      intro c hc
      have hcd : c ∈ (Δ.pole X).dangling := dangling_pole X ▸ hc
      rcases spec c hc with ⟨h, hl, h1, h2⟩ | ⟨h, hl, h1, h2⟩ | ⟨h, h1, h2, h3⟩
      · right
        rw [hl] at h ⊢
        have hpX' : pX c ∈ Δ.bd X \ Δ.bd W :=
          Finset.mem_sdiff.mpr ⟨pX_mem hPX mX hc, hnoX c hc (Finset.mem_inter.mp h).2⟩
        rw [(canThru _ h).1, (canThru _ h).2, h1, h2, tokW c (Finset.mem_inter.mp h).2,
          fvM _ (innerE_mem (memBd _ hpX'))]
        exact ⟨rfl, rfl⟩
      · left
        rw [hl] at h ⊢
        have hc' : c ∈ Δ.bd X \ Δ.bd W := by
          refine Finset.mem_sdiff.mpr ⟨hc, fun h' ↦ ?_⟩
          have := hnoX (pX c) (pX_mem hPX mX hc) (Finset.mem_inter.mp h).2
          rw [partner_partner hPX mX hcd] at this
          exact this h'
        rw [(canThru _ h).1, (canThru _ h).2, h1, h2, tokW _ (Finset.mem_inter.mp h).2,
          partner_partner hPX mX hcd, fvM _ (innerE_mem (memBd _ hc'))]
        exact ⟨rfl, rfl⟩
      · have hboth : c ∈ Δ.bd X \ Δ.bd W ∧ pX c ∈ Δ.bd X \ Δ.bd W := by
          unfold pairLabels at h; rw [Finset.mem_filter] at h
          rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [h3] at h
            exact ⟨h.1, Finset.mem_sdiff.mpr ⟨pX_mem hPX mX (Finset.mem_sdiff.mp h.1).1, h.2.1⟩⟩
          · rw [h3] at h h4
            rw [h4] at h
            exact ⟨Finset.mem_sdiff.mpr ⟨hc, h.2.1⟩, h.1⟩
        rw [(canX _ h).1, (canX _ h).2, h1, h2, fvM _ (innerE_mem (memBd _ hboth.1)),
          fvM _ (innerE_mem (memBd _ hboth.2))]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
        · right; rw [h4, h3]; exact ⟨rfl, rfl⟩
    rw [mem_dblCJ_Es hcl hXW hW hPW mW hQ m'] at he
    rcases he with rfl | rfl | rfl | he | he
    · rw [fe_p₀, e₀.1, e₀.2, hp' c₀ hc₀]
      exact endsNew c₀ hc₀
    · rw [fe_p₁, e₁.1, e₁.2, hp' c₁ hc₁]
      exact endsNew c₁ hc₁
    · -- the new edge of the cap
      rw [fe_nW, canE 0, canE 1]
      have h0 : (cap hPW mW).ends nW 0 = uW := by rw [cap_ends_new]; simp
      have h1 : (cap hPW mW).ends nW 1 = uW + 1 := by rw [cap_ends_new]; simp
      rw [join_ends_eq hQ m' hnWmem, join_ends_eq hQ m' hnWmem, pole_ends, h0, h1, fvW0, fvW1]
      simp only [if_true, one_ne_zero, if_false]
      split_ifs
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · -- an old inner edge
      left
      have heW := memM e he
      have heQ : e ∈ (QC).Es := (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he))
      rw [fe_old e heW heQ, canOld e he, canOld e he, join_ends_eq hQ m' heQ, join_ends_eq hQ m' heQ,
        pole_ends, endsP e heW, endsP e heW]
      have hends := (mem_edgesIn.mp he).2
      rw [if_pos (Finset.mem_sdiff.mp (hends 0)).1, if_pos (Finset.mem_sdiff.mp (hends 1)).1,
        fvM _ (hends 0), fvM _ (hends 1)]
      exact ⟨rfl, rfl⟩
    · -- an edge of `∂W` not in `∂X`
      left
      have heW := memSW e (Finset.mem_sdiff.mp he).1
      have heQ : e ∈ (QC).Es :=
        (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp he).1)))
      rw [fe_old e heW heQ, canW e he, canW e he, join_ends_eq hQ m' heQ, join_ends_eq hQ m' heQ,
        pole_ends, endsP e heW, endsP e heW]
      have fin : ∀ i, (if Δ.ends e i ∈ MM then Δ.ends e i else tok Δ (Δ.bd W) (Δ.bd X) pW e) =
          dblCJfv (X := X) hPW mW (if Δ.ends e i ∈ W then Δ.ends e i
            else (if e ∈ couple₁ hPW mW then uW else uW + 1)) := by
        intro i
        have h := sdiffW_ends hXW he i
        by_cases hM : Δ.ends e i ∈ MM
        · rw [if_pos hM, if_pos (h.2.mp hM), fvM _ hM]
        · rw [if_neg hM, if_neg (fun h' ↦ hM (h.2.mpr h')), tokW e (Finset.mem_sdiff.mp he).1]
      exact ⟨fin 0, fin 1⟩

end CJ

end FinGraph
end GraphPuzzles
