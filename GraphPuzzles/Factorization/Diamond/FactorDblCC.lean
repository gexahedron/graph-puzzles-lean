import GraphPuzzles.Factorization.Diamond.FactorDblCommon

/-!
# The double completion: cap at `W`, then cap at `X`

For nested shores `X ⊆ W`, the cap of the pole of `W` followed by the cap of the pole of
`(W \ X) ∪ {new}` is isomorphic to the canonical double completion with two cap gadgets.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section CC

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPW : (Δ.pole W).IsPole4) (mW : Fin 3) (hPX : (Δ.pole X).IsPole4) (mX : Fin 3)
  (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
  (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)

set_option quotPrecheck false in
local notation "uW" => freshV (Δ.pole W)
set_option quotPrecheck false in
local notation "nW" => freshE (Δ.pole W)
set_option quotPrecheck false in
local notation "ZC" => insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X))
set_option quotPrecheck false in
local notation "PC" => cap hPW mW

include hcl hXW hW in
/-- The dangling edges of the projected pole are the edges of `∂X`. -/
theorem capPole_dangling : ((cap hPW mW).pole ZC).dangling = Δ.bd X := by
  rw [dangling_pole, cap_bd_insert_both hPW mW hW (Finset.sdiff_subset : W \ X ⊆ W),
    bd_middle hcl hXW]
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

omit hcl in
include hXW hW in
omit hXW hW in
theorem cap_ends_bdW {e : ℕ} (he : e ∈ Δ.bd W) :
    ∃ i, (cap hPW mW).ends e i = uW ∨ (cap hPW mW).ends e i = uW + 1 := by
  have hd : e ∈ (Δ.pole W).dangling := by rw [dangling_pole]; exact he
  refine ⟨outerIdx hPW e, ?_⟩
  rw [cap_ends_outer hPW mW hd]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem uW_notMem : uW ∉ W ∧ uW + 1 ∉ W :=
  ⟨freshV_notMem (P := Δ.pole W), freshV_succ_notMem (P := Δ.pole W)⟩

omit hcl in
include hXW hW in
omit hW in
/-- Membership in the projected pole. -/
theorem mem_capPole_Es {e : ℕ} : e ∈ ((cap hPW mW).pole ZC).Es ↔
    e = nW ∨ e ∈ Δ.edgesIn (W \ X) ∨ e ∈ Δ.bd X ∨ e ∈ Δ.bd W := by
  have huW := uW_notMem (Δ := Δ) (W := W)
  rw [mem_pole_Es_iff', cap_Es, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | he, i, hi⟩
    · exact Or.inl rfl
    · right
      by_cases hbW : e ∈ Δ.bd W
      · exact Or.inr (Or.inr hbW)
      · have heW : e ∈ Δ.edgesIn W := by
          rw [pole_Es, Finset.mem_union] at he
          exact he.resolve_right hbW
        have hends : ∀ j, Δ.ends e j ∈ W := (mem_edgesIn.mp heW).2
        rw [cap_ends_eq hPW mW he, pole_ends, pole_Vs, if_pos (hends i)] at hi
        rw [Finset.mem_insert, Finset.mem_insert] at hi
        rcases hi with hi | hi | hi
        · exact absurd (hi ▸ hends i) huW.1
        · exact absurd (hi ▸ hends i) huW.2
        · by_cases hall : ∀ j, Δ.ends e j ∈ W \ X
          · exact Or.inl (mem_edgesIn.mpr ⟨edgesIn_subset W heW, hall⟩)
          · right; left
            push Not at hall
            obtain ⟨j, hj⟩ := hall
            rw [mem_bd]
            refine ⟨edgesIn_subset W heW, ?_⟩
            have hjX : Δ.ends e j ∈ X := by
              by_contra h
              exact hj (Finset.mem_sdiff.mpr ⟨hends j, h⟩)
            have hiX : Δ.ends e i ∉ X := (Finset.mem_sdiff.mp hi).2
            have hij : i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by
              have : i ≠ j := fun h ↦ hiX (h ▸ hjX)
              omega
            rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (rfl | he | he | he)
    · refine ⟨Or.inl rfl, 0, ?_⟩
      rw [cap_ends_new]
      simp
    · have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]
        left
        rw [mem_edgesIn] at he ⊢
        exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
      refine ⟨Or.inr heW, 0, ?_⟩
      rw [cap_ends_eq hPW mW heW, pole_ends, pole_Vs,
        if_pos (Finset.mem_sdiff.mp ((mem_edgesIn.mp he).2 0)).1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((mem_edgesIn.mp he).2 0))
    · obtain ⟨i, hi, hi'⟩ := bd_side he
      have heΔ := bd_subset X he
      have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]
        exact mem_edgesIn_or_bd heΔ (hXW hi)
      refine ⟨Or.inr heW, ?_⟩
      by_cases hbW : e ∈ Δ.bd W
      · obtain ⟨j, hj⟩ := cap_ends_bdW hPW mW hbW
        refine ⟨j, ?_⟩
        rcases hj with hj | hj <;> rw [hj]
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · have heWW : e ∈ Δ.edgesIn W := by
          rw [pole_Es, Finset.mem_union] at heW
          exact heW.resolve_right hbW
        refine ⟨Fin.rev i, ?_⟩
        rw [cap_ends_eq hPW mW heW, pole_ends, pole_Vs, if_pos ((mem_edgesIn.mp heWW).2 _)]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_sdiff.mpr ⟨(mem_edgesIn.mp heWW).2 _, hi'⟩))
    · have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]; exact Or.inr he
      obtain ⟨j, hj⟩ := cap_ends_bdW hPW mW he
      refine ⟨Or.inr heW, j, ?_⟩
      rcases hj with hj | hj <;> rw [hj]
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

variable (hQ : ((cap hPW mW).pole
    (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X)))).IsPole4) (m' : Fin 3)
  (hp' : ∀ c ∈ Δ.bd X, partner hQ m' c = partner hPX mX c)

set_option quotPrecheck false in
local notation "uX" => freshV ((cap hPW mW).pole ZC)
set_option quotPrecheck false in
local notation "nX" => freshE ((cap hPW mW).pole ZC)
set_option quotPrecheck false in
local notation "tX" => tokU Δ (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "tW" => tokU Δ (Δ.bd W) (Δ.bd X)
set_option quotPrecheck false in
local notation "eX" => tokE Δ (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "eW" => tokE Δ (Δ.bd W) (Δ.bd X)
set_option quotPrecheck false in
local notation "fX" => first (Δ.bd X) (Δ.bd W)
set_option quotPrecheck false in
local notation "fW" => first (Δ.bd W) (Δ.bd X)

/-- The vertex map of the double cap isomorphism. -/
noncomputable def dblCCfv (v : ℕ) : ℕ :=
  if v = uX then (if fX ∈ couple₁ hQ m' then tX else tX + 1)
  else if v = uX + 1 then (if fX ∈ couple₁ hQ m' then tX + 1 else tX)
  else if v = uW then (if fW ∈ couple₁ hPW mW then tW else tW + 1)
  else if v = uW + 1 then (if fW ∈ couple₁ hPW mW then tW + 1 else tW)
  else v

/-- The edge map of the double cap isomorphism. -/
noncomputable def dblCCfe (e : ℕ) : ℕ :=
  if e = nX then eX else if e = nW then eW else e

include hcl hXW hW hnoX hnoW hp' in
/-- **The double cap is the canonical double completion.** -/
theorem dblCC_iso : Nonempty (Iso (cap hQ m')
    (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true)) := by
  -- basic facts
  have hneX := sdiffX_nonempty hPX mX hnoX
  have hneW := sdiffW_nonempty hPW mW hnoW
  have huW := uW_notMem (Δ := Δ) (W := W)
  have hdang := capPole_dangling hcl hXW hW hPW mW
  have hZ : ZC ⊆ (cap hPW mW).Vs := by
    rw [cap_Vs]
    intro v hv
    simp only [Finset.mem_insert, pole_Vs] at hv ⊢
    rcases hv with rfl | rfl | hv
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_sdiff.mp hv).1)
  have huX : uX ∉ ZC ∧ uX + 1 ∉ ZC :=
    ⟨freshV_notMem (P := (cap hPW mW).pole ZC), freshV_succ_notMem (P := (cap hPW mW).pole ZC)⟩
  have hnX : nX ∉ ((cap hPW mW).pole ZC).Es := freshE_notMem
  have hnW : nW ∉ (Δ.pole W).Es := freshE_notMem
  have hnWΔ : ∀ e ∈ (Δ.pole W).Es, e ≠ nW := fun e he h ↦ hnW (h ▸ he)
  have hnXP : ∀ e ∈ ((cap hPW mW).pole ZC).Es, e ≠ nX := fun e he h ↦ hnX (h ▸ he)
  have hnWmem : nW ∈ ((cap hPW mW).pole ZC).Es := (mem_capPole_Es hXW hPW mW).mpr (Or.inl rfl)
  have htok := tokU_ne Δ (Δ.bd X) (Δ.bd W) hneX hneW
  have hteX := tokE_ne Δ (Δ.bd X) (Δ.bd W) hneX hneW
  have hSXE : Δ.bd X ⊆ Δ.Es := bd_subset X
  have hSWE : Δ.bd W ⊆ Δ.Es := bd_subset W
  have hMV : W \ X ⊆ Δ.Vs := fun v hv ↦ hW (Finset.mem_sdiff.mp hv).1
  have memM : ∀ e ∈ Δ.edgesIn (W \ X), e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]
    left
    rw [mem_edgesIn] at he ⊢
    exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
  have memSX : ∀ e ∈ Δ.bd X, e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]
    obtain ⟨i, hi, -⟩ := bd_side he
    exact mem_edgesIn_or_bd (bd_subset X he) (hXW hi)
  have memSW : ∀ e ∈ Δ.bd W, e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]; exact Or.inr he
  have htokM : ∀ v ∈ W \ X, v ≠ tX ∧ v ≠ tX + 1 ∧ v ≠ tW ∧ v ≠ tW + 1 := by
    intro v hv
    have h1 := tokU_notMem Δ (Δ.bd X) (Δ.bd W) v (hMV hv)
    have h2 := tokU_notMem Δ (Δ.bd W) (Δ.bd X) v (hMV hv)
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hnXW : nX ≠ nW := fun h ↦ hnX (h ▸ hnWmem)
  have huXW : uX ≠ uW ∧ uX ≠ uW + 1 ∧ uX + 1 ≠ uW ∧ uX + 1 ≠ uW + 1 := by
    refine ⟨fun h ↦ huX.1 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h ↦ huX.1 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
      fun h ↦ huX.2 (by rw [h]; exact Finset.mem_insert_self _ _),
      fun h ↦ huX.2 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  have huXM : ∀ v ∈ W \ X, v ≠ uX ∧ v ≠ uX + 1 ∧ v ≠ uW ∧ v ≠ uW + 1 := by
    intro v hv
    refine ⟨fun h ↦ huX.1 (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)),
      fun h ↦ huX.2 (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)),
      fun h ↦ huW.1 (by rw [← h]; exact (Finset.mem_sdiff.mp hv).1),
      fun h ↦ huW.2 (by rw [← h]; exact (Finset.mem_sdiff.mp hv).1)⟩
  -- the vertex map on the fresh vertices
  have fvX0 : dblCCfv hPW mW hQ m' uX = if fX ∈ couple₁ hQ m' then tX else tX + 1 := by
    unfold dblCCfv; rw [if_pos rfl]
  have fvX1 : dblCCfv hPW mW hQ m' (uX + 1) = if fX ∈ couple₁ hQ m' then tX + 1 else tX := by
    unfold dblCCfv; rw [if_neg (by omega), if_pos rfl]
  have fvW0 : dblCCfv hPW mW hQ m' uW = if fW ∈ couple₁ hPW mW then tW else tW + 1 := by
    unfold dblCCfv; rw [if_neg huXW.1.symm, if_neg huXW.2.2.1.symm, if_pos rfl]
  have fvW1 : dblCCfv hPW mW hQ m' (uW + 1) = if fW ∈ couple₁ hPW mW then tW + 1 else tW := by
    unfold dblCCfv
    rw [if_neg huXW.2.1.symm, if_neg huXW.2.2.2.symm, if_neg (by omega), if_pos rfl]
  have fvM : ∀ v ∈ W \ X, dblCCfv hPW mW hQ m' v = v := by
    intro v hv
    have h := huXM v hv
    unfold dblCCfv
    rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2]
  -- the token of a dangling edge of `X` in the second cap
  have tokX : ∀ d ∈ Δ.bd X, dblCCfv hPW mW hQ m' (if d ∈ couple₁ hQ m' then uX else uX + 1) =
      tok Δ (Δ.bd X) (Δ.bd W) (partner hPX mX) d := by
    intro d hd
    rw [← tok_eq_of_partner hQ m' hdang (partner hPX mX) hp' hneX hd]
    by_cases h : d ∈ couple₁ hQ m'
    · rw [if_pos h, if_pos h]; exact fvX0
    · rw [if_neg h, if_neg h]; exact fvX1
  have tokW : ∀ d ∈ Δ.bd W, dblCCfv hPW mW hQ m' (if d ∈ couple₁ hPW mW then uW else uW + 1) =
      tok Δ (Δ.bd W) (Δ.bd X) (partner hPW mW) d := by
    intro d hd
    rw [← tok_eq_of_partner hPW mW (dangling_pole W) (partner hPW mW) (fun _ _ ↦ rfl) hneW hd]
    by_cases h : d ∈ couple₁ hPW mW
    · rw [if_pos h, if_pos h]; exact fvW0
    · rw [if_neg h, if_neg h]; exact fvW1
  -- ends in the first cap for old edges
  have endsP : ∀ e ∈ (Δ.pole W).Es, ∀ i, (cap hPW mW).ends e i =
      if Δ.ends e i ∈ W then Δ.ends e i else (if e ∈ couple₁ hPW mW then uW else uW + 1) := by
    intro e he i
    rw [cap_ends_eq hPW mW he, pole_ends, pole_Vs]
  -- ends in the second cap
  have endsQ : ∀ e ∈ ((cap hPW mW).pole ZC).Es, ∀ i, (cap hQ m').ends e i =
      if (cap hPW mW).ends e i ∈ ZC then (cap hPW mW).ends e i
      else (if e ∈ couple₁ hQ m' then uX else uX + 1) := by
    intro e he i
    rw [cap_ends_eq hQ m' he, pole_ends, pole_Vs]
  have hcl₁ : (cap hQ m').IsClosed := cap_isClosed hQ m'
  refine ⟨Iso.mk'' hcl₁ (dblCCfv hPW mW hQ m') (dblCCfe (X := X) hPW mW) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · -- vertices map into `can`
    intro v hv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert] at hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union]
    simp only [toks, if_true]
    rcases hv with rfl | rfl | rfl | rfl | hv
    · rw [fvX0]; left; right; split_ifs <;> simp
    · rw [fvX1]; left; right; split_ifs <;> simp
    · rw [fvW0]; right; split_ifs <;> simp
    · rw [fvW1]; right; split_ifs <;> simp
    · rw [fvM v hv]; exact Or.inl (Or.inl hv)
  · -- surjective on vertices
    intro v hv
    rw [can_Vs, Finset.mem_union, Finset.mem_union] at hv
    simp only [toks, if_true, Finset.mem_insert, Finset.mem_singleton] at hv
    have memX0 : uX ∈ (cap hQ m').Vs := freshV_mem_cap hQ m'
    have memX1 : uX + 1 ∈ (cap hQ m').Vs := freshV_succ_mem_cap hQ m'
    have memW0 : uW ∈ (cap hQ m').Vs := mem_cap_Vs_of_old hQ m' (Finset.mem_insert_self _ _)
    have memW1 : uW + 1 ∈ (cap hQ m').Vs :=
      mem_cap_Vs_of_old hQ m' (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rcases hv with (hv | rfl | rfl) | rfl | rfl
    · exact ⟨v, mem_cap_Vs_of_old hQ m' (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)),
        fvM v hv⟩
    · by_cases h : fX ∈ couple₁ hQ m'
      · exact ⟨uX, memX0, by rw [fvX0, if_pos h]⟩
      · exact ⟨uX + 1, memX1, by rw [fvX1, if_neg h]⟩
    · by_cases h : fX ∈ couple₁ hQ m'
      · exact ⟨uX + 1, memX1, by rw [fvX1, if_pos h]⟩
      · exact ⟨uX, memX0, by rw [fvX0, if_neg h]⟩
    · by_cases h : fW ∈ couple₁ hPW mW
      · exact ⟨uW, memW0, by rw [fvW0, if_pos h]⟩
      · exact ⟨uW + 1, memW1, by rw [fvW1, if_neg h]⟩
    · by_cases h : fW ∈ couple₁ hPW mW
      · exact ⟨uW + 1, memW1, by rw [fvW1, if_pos h]⟩
      · exact ⟨uW, memW0, by rw [fvW0, if_neg h]⟩
  · -- injective on vertices
    intro u hu v hv huv
    rw [cap_Vs, pole_Vs, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert] at hu hv
    rcases hu with rfl | rfl | rfl | rfl | hu <;> rcases hv with rfl | rfl | rfl | rfl | hv <;>
      first
      | rfl
      | (exfalso
         first
         | (have h := htokM _ hv; rw [fvM _ hv] at huv)
         | (have h := htokM _ hu; rw [fvM _ hu] at huv)
         | skip
         simp only [fvX0, fvX1, fvW0, fvW1] at huv
         split_ifs at huv <;> omega)
      | (rw [fvM _ hu, fvM _ hv] at huv; exact huv)
  · -- edges map into `can`
    intro e he
    rw [cap_Es, Finset.mem_insert] at he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union]
    simp only [surv, if_true]
    rcases he with rfl | he
    · unfold dblCCfe; rw [if_pos rfl]
      left; right; exact Finset.mem_insert_self _ _
    · have hne := hnXP e he
      rw [mem_capPole_Es hXW hPW mW] at he
      unfold dblCCfe
      rw [if_neg hne]
      rcases he with rfl | he | he | he
      · rw [if_pos rfl]; right; exact Finset.mem_insert_self _ _
      · rw [if_neg (hnWΔ e (memM e he))]
        left; left; left; exact he
      · rw [if_neg (hnWΔ e (memSX e he))]
        by_cases hbW : e ∈ Δ.bd W
        · left; left; right; exact Finset.mem_inter.mpr ⟨he, hbW⟩
        · left; right; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨he, hbW⟩)
      · rw [if_neg (hnWΔ e (memSW e he))]
        by_cases hbX : e ∈ Δ.bd X
        · left; left; right; exact Finset.mem_inter.mpr ⟨hbX, he⟩
        · right; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨he, hbX⟩)
  · -- surjective on edges
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union] at he
    simp only [surv, if_true, Finset.mem_insert] at he
    have old : ∀ d ∈ (Δ.pole W).Es, d ∈ ((cap hPW mW).pole ZC).Es →
        dblCCfe (X := X) hPW mW d = d := by
      intro d hd hd'
      unfold dblCCfe
      rw [if_neg (hnXP d hd'), if_neg (hnWΔ d hd)]
    rcases he with ((he | he) | (rfl | he)) | (rfl | he)
    · have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
        (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he))
      exact ⟨e, Finset.mem_insert_of_mem hm, old e (memM e he) hm⟩
    · have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
        (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inl (Finset.mem_inter.mp he).1)))
      exact ⟨e, Finset.mem_insert_of_mem hm, old e (memSX e (Finset.mem_inter.mp he).1) hm⟩
    · refine ⟨nX, Finset.mem_insert_self _ _, ?_⟩
      unfold dblCCfe; rw [if_pos rfl]
    · have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
        (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mp he).1)))
      exact ⟨e, Finset.mem_insert_of_mem hm, old e (memSX e (Finset.mem_sdiff.mp he).1) hm⟩
    · refine ⟨nW, Finset.mem_insert_of_mem hnWmem, ?_⟩
      unfold dblCCfe; rw [if_neg hnXW.symm, if_pos rfl]
    · have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
        (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp he).1)))
      exact ⟨e, Finset.mem_insert_of_mem hm, old e (memSW e (Finset.mem_sdiff.mp he).1) hm⟩
  · -- injective on edges
    intro d hd e he hde
    -- the value of the edge map on an old edge
    have oldE : ∀ d ∈ (cap hQ m').Es, d ≠ nX → d ≠ nW → dblCCfe (X := X) hPW mW d = d ∧ d ∈ Δ.Es := by
      intro d hd h1 h2
      refine ⟨by unfold dblCCfe; rw [if_neg h1, if_neg h2], ?_⟩
      rw [cap_Es, Finset.mem_insert] at hd
      rcases hd with h | hd
      · exact absurd h h1
      · rw [mem_capPole_Es hXW hPW mW] at hd
        rcases hd with h | hd | hd | hd
        · exact absurd h h2
        · exact edgesIn_subset _ hd
        · exact hSXE hd
        · exact hSWE hd
    have valX : dblCCfe (X := X) hPW mW nX = eX := by unfold dblCCfe; rw [if_pos rfl]
    have valW : dblCCfe (X := X) hPW mW nW = eW := by
      unfold dblCCfe; rw [if_neg hnXW.symm, if_pos rfl]
    by_cases hd1 : d = nX <;> by_cases hd2 : d = nW <;> by_cases he1 : e = nX <;>
      by_cases he2 : e = nW
    all_goals first
      | (subst hd1; subst he1; rfl)
      | (subst hd2; subst he2; rfl)
      | (exfalso; subst hd1; subst he2; rw [valX, valW] at hde; exact hteX hde)
      | (exfalso; subst hd2; subst he1; rw [valX, valW] at hde; exact hteX hde.symm)
      | (exfalso; exact hnXW (hd1.symm.trans hd2))
      | (exfalso; exact hnXW (he1.symm.trans he2))
      | (exfalso; subst hd1
         obtain ⟨hf, hΔ⟩ := oldE e he he1 he2
         rw [valX, hf] at hde
         exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE e hΔ hde.symm)
      | (exfalso; subst hd2
         obtain ⟨hf, hΔ⟩ := oldE e he he1 he2
         rw [valW, hf] at hde
         exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE e hΔ hde.symm)
      | (exfalso; subst he1
         obtain ⟨hf, hΔ⟩ := oldE d hd hd1 hd2
         rw [valX, hf] at hde
         exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE d hΔ hde)
      | (exfalso; subst he2
         obtain ⟨hf, hΔ⟩ := oldE d hd hd1 hd2
         rw [valW, hf] at hde
         exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE d hΔ hde)
      | (rw [(oldE d hd hd1 hd2).1, (oldE e he he1 he2).1] at hde; exact hde)
  · -- the ends
    intro e he
    rw [cap_Es, Finset.mem_insert] at he
    rcases he with rfl | he
    · -- the new edge of the second cap
      have h0 : (cap hQ m').ends nX 0 = uX := by rw [cap_ends_new]; simp
      have h1 : (cap hQ m').ends nX 1 = uX + 1 := by rw [cap_ends_new]; simp
      have hf : dblCCfe (X := X) hPW mW nX = eX := by unfold dblCCfe; rw [if_pos rfl]
      rw [hf, h0, h1, fvX0, fvX1]
      have hc : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true).ends
          eX i = if i = 0 then tX else tX + 1 := by
        intro i
        rw [can_ends_X _ _ _ _ _ _ _ _ (fun h ↦ tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE _
          (hSXE (Finset.mem_inter.mp h).1) rfl) (Or.inr rfl)]
        unfold sideEnds
        rw [if_pos rfl, if_pos rfl]
      rw [hc 0, hc 1]
      simp only [if_true, one_ne_zero, if_false]
      split_ifs
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · have hne := hnXP e he
      have hfe : dblCCfe (X := X) hPW mW e = if e = nW then eW else e := by
        unfold dblCCfe; rw [if_neg hne]
      rw [mem_capPole_Es hXW hPW mW] at he
      rcases he with rfl | he | he | he
      · -- the new edge of the first cap
        have hm : nW ∈ ((cap hPW mW).pole ZC).Es := hnWmem
        rw [hfe, if_pos rfl]
        have hP0 : (cap hPW mW).ends nW 0 = uW := by rw [cap_ends_new]; simp
        have hP1 : (cap hPW mW).ends nW 1 = uW + 1 := by rw [cap_ends_new]; simp
        rw [endsQ _ hm 0, endsQ _ hm 1, hP0, hP1, if_pos (Finset.mem_insert_self _ _),
          if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), fvW0, fvW1]
        have hc : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true).ends
            eW i = if i = 0 then tW else tW + 1 := by
          intro i
          rw [can_ends_W _ _ _ _ _ _ _ _ (fun h ↦ tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _
            (hSWE (Finset.mem_inter.mp h).2) rfl) (by
              rintro (h | h)
              · exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE _ (hSXE (Finset.mem_sdiff.mp h).1) rfl
              · exact hteX h.symm) (Or.inr rfl)]
          unfold sideEnds
          rw [if_pos rfl, if_pos rfl]
        rw [hc 0, hc 1]
        simp only [if_true, one_ne_zero, if_false]
        split_ifs
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · -- an edge inside the middle part
        have heW : e ∈ (Δ.pole W).Es := by
          rw [pole_Es, Finset.mem_union]
          left
          rw [mem_edgesIn] at he ⊢
          exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
        have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
          (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inl he))
        rw [hfe, if_neg (hnWΔ e heW)]
        have hends := (mem_edgesIn.mp he).2
        have hb := edgesIn_sdiff_ends he
        have hin : ∀ i, (cap hQ m').ends e i = Δ.ends e i := by
          intro i
          rw [endsQ _ hm, endsP _ heW, if_pos (Finset.mem_sdiff.mp (hends i)).1,
            if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hends i)))]
        have hc : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true).ends
            e i = Δ.ends e i := by
          intro i
          rw [can_ends_old _ _ _ _ _ _ _ _ (fun h ↦ hb.1 (Finset.mem_inter.mp h).1) (by
              rintro (h | h)
              · exact hb.1 (Finset.mem_sdiff.mp h).1
              · exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE e (edgesIn_subset _ he) h) (by
              rintro (h | h)
              · exact hb.2 (Finset.mem_sdiff.mp h).1
              · exact tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE e (edgesIn_subset _ he) h)]
        left
        rw [hin, hin, hc, hc, fvM _ (hends 0), fvM _ (hends 1)]
        exact ⟨rfl, rfl⟩
      · -- an edge of `∂X`
        have heΔ := hSXE he
        have heW : e ∈ (Δ.pole W).Es := by
          rw [pole_Es, Finset.mem_union]
          obtain ⟨i, hi, -⟩ := bd_side he
          exact mem_edgesIn_or_bd heΔ (hXW hi)
        have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
          (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inl he)))
        rw [hfe, if_neg (hnWΔ e heW)]
        by_cases hbW : e ∈ Δ.bd W
        · -- a through edge
          have hthru : e ∈ Δ.bd X ∩ Δ.bd W := Finset.mem_inter.mpr ⟨he, hbW⟩
          obtain ⟨i, hi, hi'⟩ := bd_side he
          have hiW : Δ.ends e i ∈ W := (thru_ends hXW hthru i).mp hi
          have hi'W : Δ.ends e (Fin.rev i) ∉ W := fun h ↦ hi' ((thru_ends hXW hthru _).mpr h)
          -- the end in `X` goes to the second gadget, the other end to the first
          have hA : (cap hQ m').ends e i = if e ∈ couple₁ hQ m' then uX else uX + 1 := by
            rw [endsQ _ hm, endsP _ heW, if_pos hiW, if_neg]
            intro h
            rw [Finset.mem_insert, Finset.mem_insert] at h
            rcases h with h | h | h
            · exact huW.1 (h ▸ hiW)
            · exact huW.2 (h ▸ hiW)
            · exact (Finset.mem_sdiff.mp h).2 hi
          have hB : (cap hQ m').ends e (Fin.rev i) =
              if e ∈ couple₁ hPW mW then uW else uW + 1 := by
            rw [endsQ _ hm, endsP _ heW, if_neg hi'W, if_pos]
            split_ifs
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have hc0 := can_ends_thru Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
            true true hthru 0
          have hc1 := can_ends_thru Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
            true true hthru 1
          simp only [if_true, one_ne_zero, if_false, thruEnd] at hc0 hc1
          have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · rw [Iso.rev_zero'] at hB
            left
            rw [hc0, hc1, hA, hB, tokX e he, tokW e hbW]
            exact ⟨rfl, rfl⟩
          · rw [Iso.rev_one'] at hB
            right
            rw [hc0, hc1, hA, hB, tokX e he, tokW e hbW]
            exact ⟨rfl, rfl⟩
        · -- an edge of `∂X` inside `W`
          have hsd : e ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨he, hbW⟩
          have hin : ∀ i, (cap hQ m').ends e i = if Δ.ends e i ∈ W \ X then Δ.ends e i
              else (if e ∈ couple₁ hQ m' then uX else uX + 1) := by
            intro i
            have h := sdiffX_ends hXW hsd i
            rw [endsQ _ hm, endsP _ heW, if_pos h.1]
            by_cases hM : Δ.ends e i ∈ W \ X
            · rw [if_pos hM, if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hM))]
            · rw [if_neg hM, if_neg]
              intro h'
              rw [Finset.mem_insert, Finset.mem_insert] at h'
              rcases h' with h' | h' | h'
              · exact huW.1 (h' ▸ h.1)
              · exact huW.2 (h' ▸ h.1)
              · exact hM h'
          have hc : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true).ends
              e i = if Δ.ends e i ∈ W \ X then Δ.ends e i
                else tok Δ (Δ.bd X) (Δ.bd W) (partner hPX mX) e := by
            intro i
            rw [can_ends_X _ _ _ _ _ _ _ _ (fun h ↦ hbW (Finset.mem_inter.mp h).2) (Or.inl hsd)]
            unfold sideEnds
            rw [if_pos rfl, if_neg (tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE e heΔ)]
          have fin : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
              true true).ends e i = dblCCfv hPW mW hQ m' ((cap hQ m').ends e i) := by
            intro i
            rw [hin, hc]
            by_cases hM : Δ.ends e i ∈ W \ X
            · rw [if_pos hM, if_pos hM, fvM _ hM]
            · rw [if_neg hM, if_neg hM, tokX e he]
          exact Or.inl ⟨fin 0, fin 1⟩
      · -- an edge of `∂W` not in `∂X`
        have heΔ := hSWE he
        have heW : e ∈ (Δ.pole W).Es := by
          rw [pole_Es, Finset.mem_union]; exact Or.inr he
        have hm : e ∈ ((cap hPW mW).pole ZC).Es :=
          (mem_capPole_Es hXW hPW mW).mpr (Or.inr (Or.inr (Or.inr he)))
        rw [hfe, if_neg (hnWΔ e heW)]
        by_cases hbX : e ∈ Δ.bd X
        · -- a through edge (already handled above, but the case split repeats it)
          have hthru : e ∈ Δ.bd X ∩ Δ.bd W := Finset.mem_inter.mpr ⟨hbX, he⟩
          obtain ⟨i, hi, hi'⟩ := bd_side hbX
          have hiW : Δ.ends e i ∈ W := (thru_ends hXW hthru i).mp hi
          have hi'W : Δ.ends e (Fin.rev i) ∉ W := fun h ↦ hi' ((thru_ends hXW hthru _).mpr h)
          have hA : (cap hQ m').ends e i = if e ∈ couple₁ hQ m' then uX else uX + 1 := by
            rw [endsQ _ hm, endsP _ heW, if_pos hiW, if_neg]
            intro h
            rw [Finset.mem_insert, Finset.mem_insert] at h
            rcases h with h | h | h
            · exact huW.1 (h ▸ hiW)
            · exact huW.2 (h ▸ hiW)
            · exact (Finset.mem_sdiff.mp h).2 hi
          have hB : (cap hQ m').ends e (Fin.rev i) =
              if e ∈ couple₁ hPW mW then uW else uW + 1 := by
            rw [endsQ _ hm, endsP _ heW, if_neg hi'W, if_pos]
            split_ifs
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have hc0 := can_ends_thru Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
            true true hthru 0
          have hc1 := can_ends_thru Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
            true true hthru 1
          simp only [if_true, one_ne_zero, if_false, thruEnd] at hc0 hc1
          have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · rw [Iso.rev_zero'] at hB
            left
            rw [hc0, hc1, hA, hB, tokX e hbX, tokW e he]
            exact ⟨rfl, rfl⟩
          · rw [Iso.rev_one'] at hB
            right
            rw [hc0, hc1, hA, hB, tokX e hbX, tokW e he]
            exact ⟨rfl, rfl⟩
        · have hsd : e ∈ Δ.bd W \ Δ.bd X := Finset.mem_sdiff.mpr ⟨he, hbX⟩
          have hin : ∀ i, (cap hQ m').ends e i = if Δ.ends e i ∈ W \ X then Δ.ends e i
              else (if e ∈ couple₁ hPW mW then uW else uW + 1) := by
            intro i
            have h := sdiffW_ends hXW hsd i
            rw [endsQ _ hm, endsP _ heW]
            by_cases hM : Δ.ends e i ∈ W \ X
            · rw [if_pos (h.2.mp hM), if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hM)),
                if_pos hM]
            · rw [if_neg (fun h' ↦ hM (h.2.mpr h')), if_neg hM, if_pos]
              split_ifs
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have hc : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) true true).ends
              e i = if Δ.ends e i ∈ W \ X then Δ.ends e i
                else tok Δ (Δ.bd W) (Δ.bd X) (partner hPW mW) e := by
            intro i
            rw [can_ends_W _ _ _ _ _ _ _ _ (fun h ↦ hbX (Finset.mem_inter.mp h).1) (by
                rintro (h | h)
                · exact hbX (Finset.mem_sdiff.mp h).1
                · exact tokE_notMem Δ (Δ.bd X) (Δ.bd W) hSXE e heΔ h) (Or.inl hsd)]
            unfold sideEnds
            rw [if_pos rfl, if_neg (tokE_notMem Δ (Δ.bd W) (Δ.bd X) hSWE e heΔ)]
          have fin : ∀ i, (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW)
              true true).ends e i = dblCCfv hPW mW hQ m' ((cap hQ m').ends e i) := by
            intro i
            rw [hin, hc]
            by_cases hM : Δ.ends e i ∈ W \ X
            · rw [if_pos hM, if_pos hM, fvM _ hM]
            · rw [if_neg hM, if_neg hM, tokW e he]
          exact Or.inl ⟨fin 0, fin 1⟩

end CC

end FinGraph
end GraphPuzzles
