import GraphPuzzles.Factorization.Diamond.FactorDblCommon

/-!
# The double completion: join at `W`, then join at `X`

For nested shores `X ⊆ W`, the join of the pole of `W` followed by the join of the pole of
`W \ X` is isomorphic to the canonical double completion with two join gadgets.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section JJ

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPW : (Δ.pole W).IsPole4) (mW : Fin 3) (hPX : (Δ.pole X).IsPole4) (mX : Fin 3)
  (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
  (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)

set_option quotPrecheck false in
local notation "n₀" => freshE (Δ.pole W)
set_option quotPrecheck false in
local notation "PJ" => join hPW mW
set_option quotPrecheck false in
local notation "r₀" => bdEmb hPW 0
set_option quotPrecheck false in
local notation "r₁" => bdEmb hPW (other mW)
set_option quotPrecheck false in
local notation "pW" => partner hPW mW
set_option quotPrecheck false in
local notation "pX" => partner hPX mX

omit hcl hW in
include hXW in
/-- The inner end of a boundary edge of `W` lies in `X` iff the edge is on `∂X`. -/
theorem innerEnd_W_mem_iff {d : ℕ} (hd : d ∈ Δ.bd W) : innerEnd hPW d ∈ X ↔ d ∈ Δ.bd X := by
  have hd' : d ∈ (Δ.pole W).dangling := by rw [dangling_pole]; exact hd
  rw [← ends_innerIdx hPW hd', pole_ends]
  have hin : Δ.ends d (innerIdx hPW hd') ∈ W := (innerIdx_spec hPW hd').1
  constructor
  · intro h
    rw [mem_bd]
    refine ⟨bd_subset W hd, ?_⟩
    have hout : Δ.ends d (Fin.rev (innerIdx hPW hd')) ∉ W := (innerIdx_spec hPW hd').2
    have hout' : Δ.ends d (Fin.rev (innerIdx hPW hd')) ∉ X := fun h' ↦ hout (hXW h')
    rcases dangling_idx_cases hPW hd' with ⟨hi, -⟩ | ⟨hi, -⟩ <;> rw [hi] at h hout'
    · rw [Iso.rev_zero'] at hout'; tauto
    · rw [Iso.rev_one'] at hout'; tauto
  · intro h
    exact (thru_ends hXW (Finset.mem_inter.mpr ⟨h, hd⟩) _).mpr hin

omit hcl hW in
theorem innerEnd_W_mem_W {d : ℕ} (hd : d ∈ Δ.bd W) : innerEnd hPW d ∈ W := by
  have hd' : d ∈ (Δ.pole W).dangling := by rw [dangling_pole]; exact hd
  have := innerEnd_mem hPW hd'
  rw [pole_Vs] at this
  exact this

omit hcl hW in
include hXW in
/-- The inner end of an edge of `∂W \ ∂X` is its end in the middle part. -/
theorem innerEnd_W_eq_innerE {d : ℕ} (hd : d ∈ Δ.bd W \ Δ.bd X) :
    innerEnd hPW d = innerE Δ (W \ X) d := by
  have hdW := (Finset.mem_sdiff.mp hd).1
  have hd' : d ∈ (Δ.pole W).dangling := by rw [dangling_pole]; exact hdW
  have hin : innerEnd hPW d ∈ W \ X := Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hdW,
    fun h ↦ (Finset.mem_sdiff.mp hd).2 ((innerEnd_W_mem_iff hXW hPW hdW).mp h)⟩
  have hbd : d ∈ Δ.bd (W \ X) := by
    rw [mem_bd]
    refine ⟨bd_subset W hdW, ?_⟩
    have h1 := (sdiffW_ends hXW hd 0).2
    have h2 := (sdiffW_ends hXW hd 1).2
    rw [mem_bd] at hdW
    tauto
  rw [← ends_innerIdx hPW hd', pole_ends] at hin ⊢
  exact (innerE_eq hbd hin).symm

omit hcl hXW hW in
theorem PJ_ends_n₀ : (join hPW mW).ends n₀ 0 = innerEnd hPW r₀ ∧
    (join hPW mW).ends n₀ 1 = innerEnd hPW (pW r₀) := by
  rw [join_ends_new₁, join_ends_new₁, partner_bdEmb]
  simp

omit hcl hXW hW in
theorem PJ_ends_n₁ : (join hPW mW).ends (n₀ + 1) 0 = innerEnd hPW r₁ ∧
    (join hPW mW).ends (n₀ + 1) 1 = innerEnd hPW (pW r₁) := by
  rw [join_ends_new₂, join_ends_new₂, partner_bdEmb]
  simp

omit hcl hW in
include hXW hnoW in
/-- The new edge of a couple crosses `W \ X` iff a member of the couple lies on `∂X`. -/
theorem cross_iff' {r : ℕ} (hr : r ∈ Δ.bd W) :
    (¬ (innerEnd hPW r ∈ W \ X ↔ innerEnd hPW (pW r) ∈ W \ X)) ↔
      (r ∈ Δ.bd X ∨ pW r ∈ Δ.bd X) := by
  have hpr : pW r ∈ Δ.bd W := by
    have := partner_mem hPW mW (dangling_pole W ▸ hr)
    rw [dangling_pole] at this
    exact this
  have h1 : innerEnd hPW r ∈ W \ X ↔ r ∉ Δ.bd X := by
    rw [Finset.mem_sdiff, innerEnd_W_mem_iff hXW hPW hr]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨innerEnd_W_mem_W hPW hr, h⟩⟩
  have h2 : innerEnd hPW (pW r) ∈ W \ X ↔ pW r ∉ Δ.bd X := by
    rw [Finset.mem_sdiff, innerEnd_W_mem_iff hXW hPW hpr]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨innerEnd_W_mem_W hPW hpr, h⟩⟩
  rw [h1, h2]
  have hno := hnoW r hr
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h ⟨fun _ ↦ h'.2, fun _ ↦ h'.1⟩
  · rintro (h | h) hiff
    · exact (hiff.mpr (hno h)) h
    · have hr' : r ∉ Δ.bd X := by
        intro hr'
        have := hnoW (pW r) hpr h
        rw [partner_partner hPW mW (dangling_pole W ▸ hr)] at this
        exact this hr'
      exact (hiff.mp hr') h

set_option quotPrecheck false in
local notation "cross₀" => (r₀ ∈ Δ.bd X ∨ pW r₀ ∈ Δ.bd X)
set_option quotPrecheck false in
local notation "cross₁" => (r₁ ∈ Δ.bd X ∨ pW r₁ ∈ Δ.bd X)
set_option quotPrecheck false in
local notation "QJ" => (join hPW mW).pole (W \ X)

include hcl hXW hW hnoW in
/-- The dangling edges of the projected pole. -/
theorem mem_QJ_dangling {c : ℕ} : c ∈ (QJ).dangling ↔
    c ∈ Δ.bd X \ Δ.bd W ∨ (c = n₀ ∧ cross₀) ∨ (c = n₀ + 1 ∧ cross₁) := by
  rw [dangling_pole, join_bd_old hPW mW (Z := W \ X) Finset.sdiff_subset hW, Finset.mem_union,
    Finset.mem_filter, Finset.mem_filter, bd_sdiff_eq hcl hXW, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  have e0 := PJ_ends_n₀ hPW mW
  have e1 := PJ_ends_n₁ hPW mW
  have c0 := cross_iff' hXW hPW mW hnoW (bdEmb_mem hPW 0 |> (dangling_pole W ▸ ·))
  have c1 := cross_iff' hXW hPW mW hnoW (bdEmb_mem hPW (other mW) |> (dangling_pole W ▸ ·))
  constructor
  · rintro (⟨h, hW'⟩ | ⟨h, hc⟩)
    · rcases h with h | h
      · exact Or.inl h
      · exact absurd (Finset.mem_sdiff.mp h).1 hW'
    · rcases h with rfl | rfl
      · rw [e0.1, e0.2] at hc
        exact Or.inr (Or.inl ⟨rfl, c0.mp hc⟩)
      · rw [e1.1, e1.2] at hc
        exact Or.inr (Or.inr ⟨rfl, c1.mp hc⟩)
  · rintro (h | ⟨rfl, hc⟩ | ⟨rfl, hc⟩)
    · exact Or.inl ⟨Or.inl h, (Finset.mem_sdiff.mp h).2⟩
    · right
      refine ⟨Or.inl rfl, ?_⟩
      rw [e0.1, e0.2]
      exact c0.mpr hc
    · right
      refine ⟨Or.inr rfl, ?_⟩
      rw [e1.1, e1.2]
      exact c1.mpr hc

omit hcl hW in
include hXW hnoW in
theorem innerEnd_n₀_mem : innerEnd hPW r₀ ∈ W \ X ∨ innerEnd hPW (pW r₀) ∈ W \ X := by
  have hr : r₀ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW 0
  have hpr : pW r₀ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW 0)
  by_cases h : r₀ ∈ Δ.bd X
  · right
    exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hpr,
      fun h' ↦ hnoW r₀ hr h ((innerEnd_W_mem_iff hXW hPW hpr).mp h')⟩
  · left
    exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hr,
      fun h' ↦ h ((innerEnd_W_mem_iff hXW hPW hr).mp h')⟩

omit hcl hW in
include hXW hnoW in
theorem innerEnd_n₁_mem : innerEnd hPW r₁ ∈ W \ X ∨ innerEnd hPW (pW r₁) ∈ W \ X := by
  have hr : r₁ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW _
  have hpr : pW r₁ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW _)
  by_cases h : r₁ ∈ Δ.bd X
  · right
    exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hpr,
      fun h' ↦ hnoW r₁ hr h ((innerEnd_W_mem_iff hXW hPW hpr).mp h')⟩
  · left
    exact Finset.mem_sdiff.mpr ⟨innerEnd_W_mem_W hPW hr,
      fun h' ↦ h ((innerEnd_W_mem_iff hXW hPW hr).mp h')⟩

omit hcl hW in
theorem PJ_Es : (join hPW mW).Es = insert n₀ (insert (n₀ + 1) ((Δ.pole W).Es \ Δ.bd W)) := by
  rw [join_Es, dangling_pole]

omit hcl hW in
include hXW hnoW in
/-- Membership in the projected pole. -/
theorem mem_QJ_Es {e : ℕ} : e ∈ (QJ).Es ↔
    e ∈ Δ.edgesIn (W \ X) ∨ e ∈ Δ.bd X \ Δ.bd W ∨ e = n₀ ∨ e = n₀ + 1 := by
  rw [mem_pole_Es_iff', PJ_Es hPW mW, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
  have e0 := PJ_ends_n₀ hPW mW
  have e1 := PJ_ends_n₁ hPW mW
  constructor
  · rintro ⟨rfl | rfl | ⟨he, hbW⟩, i, hi⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · rw [join_ends_eq hPW mW he, pole_ends] at hi
      have heW : e ∈ Δ.edgesIn W := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.resolve_right hbW
      have hends := (mem_edgesIn.mp heW).2
      by_cases hall : ∀ j, Δ.ends e j ∈ W \ X
      · exact Or.inl (mem_edgesIn.mpr ⟨edgesIn_subset W heW, hall⟩)
      · right; left
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        refine Finset.mem_sdiff.mpr ⟨?_, hbW⟩
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
  · rintro (he | he | rfl | rfl)
    · have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]
        left
        rw [mem_edgesIn] at he ⊢
        exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
      refine ⟨Or.inr (Or.inr ⟨heW, (edgesIn_sdiff_ends he).2⟩), 0, ?_⟩
      rw [join_ends_eq hPW mW heW, pole_ends]
      exact (mem_edgesIn.mp he).2 0
    · have hsd := he
      rw [Finset.mem_sdiff] at he
      obtain ⟨i, hi, hi'⟩ := bd_side he.1
      have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]
        exact mem_edgesIn_or_bd (bd_subset X he.1) (hXW hi)
      refine ⟨Or.inr (Or.inr ⟨heW, he.2⟩), Fin.rev i, ?_⟩
      rw [join_ends_eq hPW mW heW, pole_ends]
      exact (sdiffX_ends hXW hsd _).2.mpr hi'
    · refine ⟨Or.inl rfl, ?_⟩
      rcases innerEnd_n₀_mem hXW hPW mW hnoW with h | h
      · exact ⟨0, by rw [e0.1]; exact h⟩
      · exact ⟨1, by rw [e0.2]; exact h⟩
    · refine ⟨Or.inr (Or.inl rfl), ?_⟩
      rcases innerEnd_n₁_mem hXW hPW mW hnoW with h | h
      · exact ⟨0, by rw [e1.1]; exact h⟩
      · exact ⟨1, by rw [e1.2]; exact h⟩

omit hcl hW in
include hXW in
/-- The inner end in the projected pole of an old dangling edge. -/
theorem innerEnd_QJ_old (hQ : (QJ).IsPole4) {c : ℕ} (hc : c ∈ (QJ).dangling)
    (hcX : c ∈ Δ.bd X \ Δ.bd W) : innerEnd hQ c = innerE Δ (W \ X) c := by
  have hcW : c ∈ (Δ.pole W).Es := by
    rw [pole_Es, Finset.mem_union]
    obtain ⟨i, hi, -⟩ := bd_side (Finset.mem_sdiff.mp hcX).1
    exact mem_edgesIn_or_bd (bd_subset X (Finset.mem_sdiff.mp hcX).1) (hXW hi)
  have hin := innerEnd_mem hQ hc
  rw [pole_Vs] at hin
  rw [← ends_innerIdx hQ hc, pole_ends, join_ends_eq hPW mW hcW, pole_ends] at hin ⊢
  have hbd : c ∈ Δ.bd (W \ X) := by
    rw [mem_bd]
    refine ⟨bd_subset X (Finset.mem_sdiff.mp hcX).1, ?_⟩
    have h1 := sdiffX_ends hXW hcX 0
    have h2 := sdiffX_ends hXW hcX 1
    have := (Finset.mem_sdiff.mp hcX).1
    rw [mem_bd] at this
    tauto
  exact (innerE_eq hbd hin).symm

omit hcl hXW hW in
include hnoW in
/-- The through edge of a crossing new edge. -/
theorem thru₀_spec (hc : cross₀) :
    joinPoleFe hPW mW X n₀ ∈ Δ.bd X ∩ Δ.bd W ∧
      pW (joinPoleFe hPW mW X n₀) ∈ Δ.bd W \ Δ.bd X ∧
      (joinPoleFe hPW mW X n₀ = r₀ ∨ joinPoleFe hPW mW X n₀ = pW r₀) := by
  have hr : r₀ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW 0
  have hpr : pW r₀ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW 0)
  have hfe : joinPoleFe hPW mW X n₀ = if r₀ ∈ Δ.bd X then r₀ else pW r₀ := by
    unfold joinPoleFe
    rw [if_pos rfl, partner_bdEmb]
  rw [hfe]
  by_cases h : r₀ ∈ Δ.bd X
  · rw [if_pos h]
    refine ⟨Finset.mem_inter.mpr ⟨h, hr⟩, Finset.mem_sdiff.mpr ⟨hpr, hnoW r₀ hr h⟩, Or.inl rfl⟩
  · rw [if_neg h]
    have h' : pW r₀ ∈ Δ.bd X := hc.resolve_left h
    refine ⟨Finset.mem_inter.mpr ⟨h', hpr⟩, ?_, Or.inr rfl⟩
    rw [partner_partner hPW mW (bdEmb_mem hPW 0)]
    exact Finset.mem_sdiff.mpr ⟨hr, h⟩

omit hcl hXW hW in
include hnoW in
theorem thru₁_spec (hc : cross₁) :
    joinPoleFe hPW mW X (n₀ + 1) ∈ Δ.bd X ∩ Δ.bd W ∧
      pW (joinPoleFe hPW mW X (n₀ + 1)) ∈ Δ.bd W \ Δ.bd X ∧
      (joinPoleFe hPW mW X (n₀ + 1) = r₁ ∨ joinPoleFe hPW mW X (n₀ + 1) = pW r₁) := by
  have hr : r₁ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW _
  have hpr : pW r₁ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW _)
  have hfe : joinPoleFe hPW mW X (n₀ + 1) = if r₁ ∈ Δ.bd X then r₁ else pW r₁ := by
    unfold joinPoleFe
    rw [if_neg (by omega), if_pos rfl, partner_bdEmb]
  rw [hfe]
  by_cases h : r₁ ∈ Δ.bd X
  · rw [if_pos h]
    refine ⟨Finset.mem_inter.mpr ⟨h, hr⟩, Finset.mem_sdiff.mpr ⟨hpr, hnoW r₁ hr h⟩, Or.inl rfl⟩
  · rw [if_neg h]
    have h' : pW r₁ ∈ Δ.bd X := hc.resolve_left h
    refine ⟨Finset.mem_inter.mpr ⟨h', hpr⟩, ?_, Or.inr rfl⟩
    rw [partner_partner hPW mW (bdEmb_mem hPW _)]
    exact Finset.mem_sdiff.mpr ⟨hr, h⟩

omit hcl hW in
include hXW hnoW in
/-- The inner end of a crossing new edge in the projected pole. -/
theorem innerEnd_QJ_n₀ (hQ : (QJ).IsPole4) (hc : cross₀) (hd : n₀ ∈ (QJ).dangling) :
    innerEnd hQ n₀ = innerE Δ (W \ X) (pW (joinPoleFe hPW mW X n₀)) := by
  obtain ⟨-, hpw, hor⟩ := thru₀_spec hPW mW hnoW hc
  have hin := innerEnd_mem hQ hd
  rw [pole_Vs] at hin
  rw [← ends_innerIdx hQ hd, pole_ends] at hin ⊢
  have e0 := PJ_ends_n₀ hPW mW
  have hr : r₀ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW 0
  have hpr : pW r₀ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW 0)
  rw [← innerEnd_W_eq_innerE hXW hPW hpw]
  rcases hor with h | h
  · rw [h] at hpw ⊢
    -- the inner end of `r₀` is in `X`, so the inner index is `1`
    have hi : innerIdx hQ hd = 1 := by
      by_contra h'
      have h0 : innerIdx hQ hd = 0 := by omega
      rw [h0, e0.1] at hin
      have := (Finset.mem_sdiff.mp hin).2
      exact this ((innerEnd_W_mem_iff hXW hPW hr).mpr (hc.resolve_right (Finset.mem_sdiff.mp hpw).2))
    rw [hi, e0.2]
  · rw [h, partner_partner hPW mW (bdEmb_mem hPW 0)] at hpw ⊢
    have hi : innerIdx hQ hd = 0 := by
      by_contra h'
      have h1 : innerIdx hQ hd = 1 := by omega
      rw [h1, e0.2] at hin
      have := (Finset.mem_sdiff.mp hin).2
      exact this ((innerEnd_W_mem_iff hXW hPW hpr).mpr (hc.resolve_left (Finset.mem_sdiff.mp hpw).2))
    rw [hi, e0.1]

omit hcl hW in
include hXW hnoW in
theorem innerEnd_QJ_n₁ (hQ : (QJ).IsPole4) (hc : cross₁) (hd : n₀ + 1 ∈ (QJ).dangling) :
    innerEnd hQ (n₀ + 1) = innerE Δ (W \ X) (pW (joinPoleFe hPW mW X (n₀ + 1))) := by
  obtain ⟨-, hpw, hor⟩ := thru₁_spec hPW mW hnoW hc
  have hin := innerEnd_mem hQ hd
  rw [pole_Vs] at hin
  rw [← ends_innerIdx hQ hd, pole_ends] at hin ⊢
  have e1 := PJ_ends_n₁ hPW mW
  have hr : r₁ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW _
  have hpr : pW r₁ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW _)
  rw [← innerEnd_W_eq_innerE hXW hPW hpw]
  rcases hor with h | h
  · rw [h] at hpw ⊢
    have hi : innerIdx hQ hd = 1 := by
      by_contra h'
      have h0 : innerIdx hQ hd = 0 := by omega
      rw [h0, e1.1] at hin
      have := (Finset.mem_sdiff.mp hin).2
      exact this ((innerEnd_W_mem_iff hXW hPW hr).mpr (hc.resolve_right (Finset.mem_sdiff.mp hpw).2))
    rw [hi, e1.2]
  · rw [h, partner_partner hPW mW (bdEmb_mem hPW _)] at hpw ⊢
    have hi : innerIdx hQ hd = 0 := by
      by_contra h'
      have h1 : innerIdx hQ hd = 1 := by omega
      rw [h1, e1.2] at hin
      have := (Finset.mem_sdiff.mp hin).2
      exact this ((innerEnd_W_mem_iff hXW hPW hpr).mpr (hc.resolve_left (Finset.mem_sdiff.mp hpw).2))
    rw [hi, e1.1]

omit hcl hXW hW in
/-- The inverse map on a through edge. -/
theorem ge_thru {e : ℕ} (he : e ∈ Δ.bd X ∩ Δ.bd W) :
    joinPoleGe hPW mW X e = if e ∈ couple₁ hPW mW then n₀ else n₀ + 1 := by
  have heX := (Finset.mem_inter.mp he).1
  have hd : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ (Finset.mem_inter.mp he).2
  unfold joinPoleGe
  by_cases h : e ∈ couple₁ hPW mW
  · rw [if_pos ⟨h, heX⟩, if_pos h]
  · rw [if_neg (fun h' ↦ h h'.1), if_pos ⟨(mem_couple₂_iff hPW mW hd).mpr h, heX⟩, if_neg h]

omit hcl hXW hW in
include hnoW in
theorem fe_ge_thru {e : ℕ} (he : e ∈ Δ.bd X ∩ Δ.bd W) :
    joinPoleFe hPW mW X (joinPoleGe hPW mW X e) = e := by
  have heX := (Finset.mem_inter.mp he).1
  have heW := (Finset.mem_inter.mp he).2
  have hd : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ heW
  rw [ge_thru hPW mW he]
  by_cases h : e ∈ couple₁ hPW mW
  · rw [if_pos h]
    have hfe : joinPoleFe hPW mW X n₀ = if r₀ ∈ Δ.bd X then r₀ else pW r₀ := by
      unfold joinPoleFe
      rw [if_pos rfl, partner_bdEmb]
    rw [hfe]
    rw [mem_couple₁_iff'] at h
    rcases h with rfl | h
    · rw [if_pos heX]
    · rw [← h, if_neg (hnoW e heW heX), partner_partner hPW mW hd]
  · rw [if_neg h]
    have hfe : joinPoleFe hPW mW X (n₀ + 1) = if r₁ ∈ Δ.bd X then r₁ else pW r₁ := by
      unfold joinPoleFe
      rw [if_neg (by omega), if_pos rfl, partner_bdEmb]
    rw [hfe]
    rw [← mem_couple₂_iff hPW mW hd, mem_couple₂_iff'] at h
    rcases h with rfl | h
    · rw [if_pos heX]
    · rw [← h, if_neg (hnoW e heW heX), partner_partner hPW mW hd]

include hcl hXW hW hnoW in
theorem ge_thru_mem_dangling {e : ℕ} (he : e ∈ Δ.bd X ∩ Δ.bd W) :
    joinPoleGe hPW mW X e ∈ (QJ).dangling := by
  have heX := (Finset.mem_inter.mp he).1
  have heW := (Finset.mem_inter.mp he).2
  have hd : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ heW
  rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW, ge_thru hPW mW he]
  by_cases h : e ∈ couple₁ hPW mW
  · rw [if_pos h]
    right; left
    refine ⟨rfl, ?_⟩
    rw [mem_couple₁_iff'] at h
    rcases h with rfl | h
    · exact Or.inl heX
    · right; rw [← h, partner_partner hPW mW hd]; exact heX
  · rw [if_neg h]
    right; right
    refine ⟨rfl, ?_⟩
    rw [← mem_couple₂_iff hPW mW hd, mem_couple₂_iff'] at h
    rcases h with rfl | h
    · exact Or.inl heX
    · right; rw [← h, partner_partner hPW mW hd]; exact heX

omit hcl hXW hW in
theorem ge_old {c : ℕ} (hc : c ∉ Δ.bd W) : joinPoleGe hPW mW X c = c :=
  joinPoleGe_old hPW mW X (fun h ↦ hc (dangling_pole W ▸ h.1))

omit hcl hXW hW in
theorem fe_old' {c : ℕ} (hc : c ∈ (Δ.pole W).Es) : joinPoleFe hPW mW X c = c :=
  joinPoleFe_old hPW mW X hc

omit hcl hXW hW in
theorem n_notMem_poleW : n₀ ∉ (Δ.pole W).Es ∧ n₀ + 1 ∉ (Δ.pole W).Es :=
  ⟨freshE_notMem, freshE_succ_notMem⟩

omit hcl hW in
include hXW in
theorem sdiffX_mem_poleW {c : ℕ} (hc : c ∈ Δ.bd X \ Δ.bd W) : c ∈ (Δ.pole W).Es := by
  rw [pole_Es, Finset.mem_union]
  obtain ⟨i, hi, -⟩ := bd_side (Finset.mem_sdiff.mp hc).1
  exact mem_edgesIn_or_bd (bd_subset X (Finset.mem_sdiff.mp hc).1) (hXW hi)

omit hcl hXW hW in
theorem pX_mem {c : ℕ} (hc : c ∈ Δ.bd X) : pX c ∈ Δ.bd X :=
  dangling_pole X ▸ partner_mem hPX mX (dangling_pole X ▸ hc)

section Main

variable (hQ : ((join hPW mW).pole (W \ X)).IsPole4) (m' : Fin 3)
  (hp' : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling,
    partner hQ m' c = joinPoleGe hPW mW X (partner hPX mX (joinPoleFe hPW mW X c)))

set_option quotPrecheck false in
local notation "p₀" => freshE ((join hPW mW).pole (W \ X))
set_option quotPrecheck false in
local notation "c₀" => bdEmb hQ 0
set_option quotPrecheck false in
local notation "c₁" => bdEmb hQ (other m')
set_option quotPrecheck false in
local notation "p'" => partner hQ m'
set_option quotPrecheck false in
local notation "fe" => joinPoleFe hPW mW X
set_option quotPrecheck false in
local notation "ge" => joinPoleGe hPW mW X
set_option quotPrecheck false in
local notation "MM" => W \ X

/-- The canonical label of the new edge of the second join attached to `c`. -/
noncomputable def jjLabel (c : ℕ) : ℕ :=
  if c = n₀ ∨ c = n₀ + 1 then fe c
  else if p' c = n₀ ∨ p' c = n₀ + 1 then fe (p' c)
  else min c (p' c)

/-- The edge map of the double join isomorphism. -/
noncomputable def dblJJfe (e : ℕ) : ℕ :=
  if e = p₀ then jjLabel hPW mW hQ m' c₀
  else if e = p₀ + 1 then jjLabel hPW mW hQ m' c₁
  else if e = n₀ then min r₀ (pW r₀)
  else if e = n₀ + 1 then min r₁ (pW r₁)
  else e

include hcl hXW hW hnoX hnoW hp' in
/-- **Specification of the canonical label.** -/
theorem jjLabel_spec {c : ℕ} (hc : c ∈ ((join hPW mW).pole (W \ X)).dangling) :
    (jjLabel hPW mW hQ m' c ∈ Δ.bd X ∩ Δ.bd W ∧ ge (jjLabel hPW mW hQ m' c) = c ∧
      innerEnd hQ c = innerE Δ MM (pW (jjLabel hPW mW hQ m' c)) ∧
      innerEnd hQ (p' c) = innerE Δ MM (pX (jjLabel hPW mW hQ m' c))) ∨
    (jjLabel hPW mW hQ m' c ∈ Δ.bd X ∩ Δ.bd W ∧ ge (jjLabel hPW mW hQ m' c) = p' c ∧
      innerEnd hQ c = innerE Δ MM (pX (jjLabel hPW mW hQ m' c)) ∧
      innerEnd hQ (p' c) = innerE Δ MM (pW (jjLabel hPW mW hQ m' c))) ∨
    (jjLabel hPW mW hQ m' c ∈ pairLabels (Δ.bd X) (Δ.bd W) pX ∧
      innerEnd hQ c = innerE Δ MM c ∧ innerEnd hQ (p' c) = innerE Δ MM (p' c) ∧
      ((jjLabel hPW mW hQ m' c = c ∧ pX (jjLabel hPW mW hQ m' c) = p' c) ∨
        (jjLabel hPW mW hQ m' c = p' c ∧ pX (jjLabel hPW mW hQ m' c) = c))) := by
  have hn := n_notMem_poleW (Δ := Δ) (W := W)
  have hpc := hp' c hc
  have hc' := hc
  rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW] at hc'
  rcases hc' with hcX | ⟨rfl, hcr⟩ | ⟨rfl, hcr⟩
  · -- an old dangling edge
    have hcW := sdiffX_mem_poleW hXW hcX
    have hcn : ¬ (c = n₀ ∨ c = n₀ + 1) := by
      rintro (h | h)
      · exact hn.1 (h ▸ hcW)
      · exact hn.2 (h ▸ hcW)
    have hfe : fe c = c := fe_old' hPW mW hcW
    rw [hfe] at hpc
    have hpXc : pX c ∈ Δ.bd X := pX_mem hPX mX (Finset.mem_sdiff.mp hcX).1
    have hinner : innerEnd hQ c = innerE Δ MM c := innerEnd_QJ_old hXW hPW mW hQ hc hcX
    by_cases hW' : pX c ∈ Δ.bd W
    · -- the partner is a through edge; its new edge is the partner in the projected pole
      have hthru : pX c ∈ Δ.bd X ∩ Δ.bd W := Finset.mem_inter.mpr ⟨hpXc, hW'⟩
      have hge := ge_thru hPW mW hthru
      have hpn : p' c = n₀ ∨ p' c = n₀ + 1 := by
        rw [hpc, hge]; split_ifs <;> simp
      right; left
      have hlab : jjLabel hPW mW hQ m' c = pX c := by
        unfold jjLabel
        rw [if_neg hcn, if_pos hpn, hpc, fe_ge_thru hPW mW hnoW hthru]
      rw [hlab]
      refine ⟨hthru, hpc.symm, ?_, ?_⟩
      · rw [hinner, partner_partner hPX mX (dangling_pole X ▸ (Finset.mem_sdiff.mp hcX).1)]
      · rw [hpc, hge]
        have hd : pX c ∈ (Δ.pole W).dangling := dangling_pole W ▸ hW'
        by_cases h1 : pX c ∈ couple₁ hPW mW
        · rw [if_pos h1]
          have hcr : cross₀ := by
            rw [mem_couple₁_iff'] at h1
            rcases h1 with h1 | h1
            · exact Or.inl (h1 ▸ hpXc)
            · right; rw [← h1, partner_partner hPW mW hd]; exact hpXc
          have hd0 : n₀ ∈ ((join hPW mW).pole (W \ X)).dangling := by
            rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inr (Or.inl ⟨rfl, hcr⟩)
          rw [innerEnd_QJ_n₀ hXW hPW mW hnoW hQ hcr hd0]
          congr 2
          have := fe_ge_thru hPW mW hnoW hthru
          rw [hge, if_pos h1] at this
          exact this
        · rw [if_neg h1]
          have h2 : pX c ∈ couple₂ hPW mW := (mem_couple₂_iff hPW mW hd).mpr h1
          have hcr : cross₁ := by
            rw [mem_couple₂_iff'] at h2
            rcases h2 with h2 | h2
            · exact Or.inl (h2 ▸ hpXc)
            · right; rw [← h2, partner_partner hPW mW hd]; exact hpXc
          have hd1 : n₀ + 1 ∈ ((join hPW mW).pole (W \ X)).dangling := by
            rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inr (Or.inr ⟨rfl, hcr⟩)
          rw [innerEnd_QJ_n₁ hXW hPW mW hnoW hQ hcr hd1]
          congr 2
          have := fe_ge_thru hPW mW hnoW hthru
          rw [hge, if_neg h1] at this
          exact this
    · -- both members of the couple are old
      have hge : ge (pX c) = pX c := ge_old hPW mW hW'
      rw [hge] at hpc
      have hpX' : pX c ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr ⟨hpXc, hW'⟩
      have hpXW := sdiffX_mem_poleW hXW hpX'
      have hpn : ¬ (p' c = n₀ ∨ p' c = n₀ + 1) := by
        rw [hpc]
        rintro (h | h)
        · exact hn.1 (h ▸ hpXW)
        · exact hn.2 (h ▸ hpXW)
      have hlab : jjLabel hPW mW hQ m' c = min c (pX c) := by
        unfold jjLabel
        rw [if_neg hcn, if_neg hpn, hpc]
      right; right
      have hpXd : pX c ∈ ((join hPW mW).pole (W \ X)).dangling := by
        rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hpX'
      have hinner' : innerEnd hQ (p' c) = innerE Δ MM (p' c) := by
        rw [hpc]; exact innerEnd_QJ_old hXW hPW mW hQ hpXd hpX'
      refine ⟨?_, hinner, hinner', ?_⟩
      · rw [hlab]
        unfold pairLabels
        rw [Finset.mem_filter]
        have hcd : c ∈ (Δ.pole X).dangling := dangling_pole X ▸ (Finset.mem_sdiff.mp hcX).1
        by_cases hle : c ≤ pX c
        · rw [min_eq_left hle]
          exact ⟨hcX, hW', hle⟩
        · rw [min_eq_right ((not_le.mp hle).le), partner_partner hPX mX hcd]
          exact ⟨hpX', (Finset.mem_sdiff.mp hcX).2, (not_le.mp hle).le⟩
      · rw [hlab, hpc]
        have hcd : c ∈ (Δ.pole X).dangling := dangling_pole X ▸ (Finset.mem_sdiff.mp hcX).1
        by_cases hle : c ≤ pX c
        · rw [min_eq_left hle]; exact Or.inl ⟨rfl, rfl⟩
        · rw [min_eq_right ((not_le.mp hle).le), partner_partner hPX mX hcd]
          exact Or.inr ⟨rfl, rfl⟩
  · -- the first new edge
    left
    obtain ⟨hthru, hpw, hor⟩ := thru₀_spec hPW mW hnoW hcr
    have hlab : jjLabel hPW mW hQ m' n₀ = fe n₀ := by
      unfold jjLabel; rw [if_pos (Or.inl rfl)]
    rw [hlab]
    have hge : ge (fe n₀) = n₀ := by
      rw [ge_thru hPW mW hthru, if_pos]
      rw [mem_couple₁_iff']
      rcases hor with h | h
      · exact Or.inl h
      · right; rw [h, partner_partner hPW mW (bdEmb_mem hPW 0)]
    have hpXe : pX (fe n₀) ∈ Δ.bd X \ Δ.bd W :=
      Finset.mem_sdiff.mpr ⟨pX_mem hPX mX (Finset.mem_inter.mp hthru).1,
        hnoX _ (Finset.mem_inter.mp hthru).1 (Finset.mem_inter.mp hthru).2⟩
    have hpn : p' n₀ = pX (fe n₀) := by
      rw [hpc, ge_old hPW mW (Finset.mem_sdiff.mp hpXe).2]
    refine ⟨hthru, hge, innerEnd_QJ_n₀ hXW hPW mW hnoW hQ hcr hc, ?_⟩
    rw [hpn]
    have hd : pX (fe n₀) ∈ ((join hPW mW).pole (W \ X)).dangling := by
      rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hpXe
    exact innerEnd_QJ_old hXW hPW mW hQ hd hpXe
  · -- the second new edge
    left
    obtain ⟨hthru, hpw, hor⟩ := thru₁_spec hPW mW hnoW hcr
    have hlab : jjLabel hPW mW hQ m' (n₀ + 1) = fe (n₀ + 1) := by
      unfold jjLabel; rw [if_pos (Or.inr rfl)]
    rw [hlab]
    have hge : ge (fe (n₀ + 1)) = n₀ + 1 := by
      rw [ge_thru hPW mW hthru, if_neg]
      have hd : fe (n₀ + 1) ∈ (Δ.pole W).dangling := dangling_pole W ▸ (Finset.mem_inter.mp hthru).2
      rw [← mem_couple₂_iff hPW mW hd, mem_couple₂_iff']
      rcases hor with h | h
      · exact Or.inl h
      · right; rw [h, partner_partner hPW mW (bdEmb_mem hPW _)]
    have hpXe : pX (fe (n₀ + 1)) ∈ Δ.bd X \ Δ.bd W :=
      Finset.mem_sdiff.mpr ⟨pX_mem hPX mX (Finset.mem_inter.mp hthru).1,
        hnoX _ (Finset.mem_inter.mp hthru).1 (Finset.mem_inter.mp hthru).2⟩
    have hpn : p' (n₀ + 1) = pX (fe (n₀ + 1)) := by
      rw [hpc, ge_old hPW mW (Finset.mem_sdiff.mp hpXe).2]
    refine ⟨hthru, hge, innerEnd_QJ_n₁ hXW hPW mW hnoW hQ hcr hc, ?_⟩
    rw [hpn]
    have hd : pX (fe (n₀ + 1)) ∈ ((join hPW mW).pole (W \ X)).dangling := by
      rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hpXe
    exact innerEnd_QJ_old hXW hPW mW hQ hd hpXe

include hcl hXW hW hnoW in
/-- Membership in the edge set of the double join. -/
theorem mem_dblJJ_Es {e : ℕ} : e ∈ (join hQ m').Es ↔
    e = p₀ ∨ e = p₀ + 1 ∨ e ∈ Δ.edgesIn (W \ X) ∨ (e = n₀ ∧ ¬ cross₀) ∨ (e = n₀ + 1 ∧ ¬ cross₁) := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff,
    mem_QJ_Es hXW hPW mW hnoW, mem_QJ_dangling hcl hXW hW hPW mW hnoW]
  have hn := n_notMem_poleW (Δ := Δ) (W := W)
  constructor
  · rintro (rfl | rfl | ⟨h, hd⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · right; right
      rcases h with h | h | rfl | rfl
      · exact Or.inl h
      · exact absurd (Or.inl h) hd
      · right; left; exact ⟨rfl, fun hc ↦ hd (Or.inr (Or.inl ⟨rfl, hc⟩))⟩
      · right; right; exact ⟨rfl, fun hc ↦ hd (Or.inr (Or.inr ⟨rfl, hc⟩))⟩
  · rintro (rfl | rfl | h | ⟨rfl, hc⟩ | ⟨rfl, hc⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · right; right
      refine ⟨Or.inl h, ?_⟩
      have hb := edgesIn_sdiff_ends h
      have heW : e ∈ (Δ.pole W).Es := by
        rw [pole_Es, Finset.mem_union]; left
        rw [mem_edgesIn] at h ⊢
        exact ⟨h.1, fun j ↦ (Finset.mem_sdiff.mp (h.2 j)).1⟩
      rintro (h' | ⟨h', -⟩ | ⟨h', -⟩)
      · exact hb.1 (Finset.mem_sdiff.mp h').1
      · exact hn.1 (h' ▸ heW)
      · exact hn.2 (h' ▸ heW)
    · right; right
      refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rintro (h' | ⟨-, h'⟩ | ⟨h', -⟩)
      · exact hn.1 (sdiffX_mem_poleW hXW h')
      · exact hc h'
      · omega
    · right; right
      refine ⟨Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      rintro (h' | ⟨h', -⟩ | ⟨-, h'⟩)
      · exact hn.2 (sdiffX_mem_poleW hXW h')
      · omega
      · exact hc h'

include hcl hXW hW hnoX hnoW hp' in
/-- **The double join is the canonical double completion.** -/
theorem dblJJ_iso : Nonempty (Iso (join hQ m')
    (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) false false)) := by
  have hn := n_notMem_poleW (Δ := Δ) (W := W)
  have hp0 : p₀ ∉ ((join hPW mW).pole (W \ X)).Es := freshE_notMem
  have hp1 : p₀ + 1 ∉ ((join hPW mW).pole (W \ X)).Es := freshE_succ_notMem
  have hSXE : Δ.bd X ⊆ Δ.Es := bd_subset X
  have hSWE : Δ.bd W ⊆ Δ.Es := bd_subset W
  have hn0Q : n₀ ∈ ((join hPW mW).pole (W \ X)).Es :=
    (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hn1Q : n₀ + 1 ∈ ((join hPW mW).pole (W \ X)).Es :=
    (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hpn : p₀ ≠ n₀ ∧ p₀ ≠ n₀ + 1 ∧ p₀ + 1 ≠ n₀ ∧ p₀ + 1 ≠ n₀ + 1 :=
    ⟨fun h ↦ hp0 (h ▸ hn0Q), fun h ↦ hp0 (h ▸ hn1Q), fun h ↦ hp1 (h ▸ hn0Q), fun h ↦ hp1 (h ▸ hn1Q)⟩
  have hc₀ : c₀ ∈ ((join hPW mW).pole (W \ X)).dangling := bdEmb_mem hQ 0
  have hc₁ : c₁ ∈ ((join hPW mW).pole (W \ X)).dangling := bdEmb_mem hQ _
  have spec₀ := jjLabel_spec hcl hXW hW hPW mW hPX mX hnoX hnoW hQ m' hp' hc₀
  have spec₁ := jjLabel_spec hcl hXW hW hPW mW hPX mX hnoX hnoW hQ m' hp' hc₁
  have memM : ∀ e ∈ Δ.edgesIn (W \ X), e ∈ (Δ.pole W).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union]; left
    rw [mem_edgesIn] at he ⊢
    exact ⟨he.1, fun j ↦ (Finset.mem_sdiff.mp (he.2 j)).1⟩
  have hr₀ : r₀ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW 0
  have hr₁ : r₁ ∈ Δ.bd W := dangling_pole W ▸ bdEmb_mem hPW _
  have hpr₀ : pW r₀ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW 0)
  have hpr₁ : pW r₁ ∈ Δ.bd W := dangling_pole W ▸ partner_mem hPW mW (bdEmb_mem hPW _)
  -- the value of the edge map
  have fe_p₀ : dblJJfe hPW mW hQ m' p₀ = jjLabel hPW mW hQ m' c₀ := by
    unfold dblJJfe; rw [if_pos rfl]
  have fe_p₁ : dblJJfe hPW mW hQ m' (p₀ + 1) = jjLabel hPW mW hQ m' c₁ := by
    unfold dblJJfe; rw [if_neg (by omega), if_pos rfl]
  have fe_n₀ : dblJJfe hPW mW hQ m' n₀ = min r₀ (pW r₀) := by
    unfold dblJJfe; rw [if_neg hpn.1.symm, if_neg hpn.2.2.1.symm, if_pos rfl]
  have fe_n₁ : dblJJfe hPW mW hQ m' (n₀ + 1) = min r₁ (pW r₁) := by
    unfold dblJJfe
    rw [if_neg hpn.2.1.symm, if_neg hpn.2.2.2.symm, if_neg (by omega), if_pos rfl]
  have fe_old : ∀ e ∈ Δ.edgesIn (W \ X), dblJJfe hPW mW hQ m' e = e := by
    intro e he
    have heW := memM e he
    have heQ : e ∈ ((join hPW mW).pole (W \ X)).Es :=
      (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he)
    have h1 : e ≠ p₀ := fun h ↦ hp0 (h ▸ heQ)
    have h2 : e ≠ p₀ + 1 := fun h ↦ hp1 (h ▸ heQ)
    have h3 : e ≠ n₀ := fun h ↦ hn.1 (h ▸ heW)
    have h4 : e ≠ n₀ + 1 := fun h ↦ hn.2 (h ▸ heW)
    unfold dblJJfe
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
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
    · rw [min_eq_right ((not_le.mp hle).le), partner_partner hPW mW hd]
      exact ⟨⟨Finset.mem_sdiff.mpr ⟨hpr, hprX⟩, hrX, (not_le.mp hle).le⟩, Or.inr ⟨rfl, rfl⟩⟩
  -- ends of the canonical graph on the various labels
  have canThru : ∀ e ∈ Δ.bd X ∩ Δ.bd W,
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends e 0 = innerE Δ MM (pX e) ∧
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends e 1 = innerE Δ MM (pW e) := by
    intro e he
    rw [can_ends_thru _ _ _ _ _ _ _ _ he, can_ends_thru _ _ _ _ _ _ _ _ he]
    simp [thruEnd]
  have canX : ∀ d ∈ pairLabels (Δ.bd X) (Δ.bd W) pX,
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends d 0 = innerE Δ MM d ∧
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends d 1 = innerE Δ MM (pX d) := by
    intro d hd
    unfold pairLabels at hd
    rw [Finset.mem_filter] at hd
    have hnt : d ∉ Δ.bd X ∩ Δ.bd W := fun h ↦ (Finset.mem_sdiff.mp hd.1).2 (Finset.mem_inter.mp h).2
    rw [can_ends_X _ _ _ _ _ _ _ _ hnt (Or.inl hd.1), can_ends_X _ _ _ _ _ _ _ _ hnt (Or.inl hd.1)]
    simp [sideEnds]
  have canW : ∀ d ∈ pairLabels (Δ.bd W) (Δ.bd X) pW,
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends d 0 = innerE Δ MM d ∧
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends d 1 = innerE Δ MM (pW d) := by
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
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) pX pW false false).ends e i = Δ.ends e i := by
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
  -- the ends of the new edges of the second join
  have e₀ : (join hQ m').ends p₀ 0 = innerEnd hQ c₀ ∧ (join hQ m').ends p₀ 1 = innerEnd hQ (p' c₀) := by
    rw [join_ends_new₁, join_ends_new₁, partner_bdEmb]; simp
  have e₁ : (join hQ m').ends (p₀ + 1) 0 = innerEnd hQ c₁ ∧
      (join hQ m').ends (p₀ + 1) 1 = innerEnd hQ (p' c₁) := by
    rw [join_ends_new₂, join_ends_new₂, partner_bdEmb]; simp
  -- the ends of a surviving first-stage edge
  have en₀ : (join hQ m').ends n₀ 0 = innerEnd hPW r₀ ∧ (join hQ m').ends n₀ 1 = innerEnd hPW (pW r₀) := by
    rw [join_ends_eq hQ m' hn0Q, join_ends_eq hQ m' hn0Q, pole_ends]
    exact PJ_ends_n₀ hPW mW
  have en₁ : (join hQ m').ends (n₀ + 1) 0 = innerEnd hPW r₁ ∧
      (join hQ m').ends (n₀ + 1) 1 = innerEnd hPW (pW r₁) := by
    rw [join_ends_eq hQ m' hn1Q, join_ends_eq hQ m' hn1Q, pole_ends]
    exact PJ_ends_n₁ hPW mW
  -- the classification of the values of the edge map
  have cls : ∀ e ∈ (join hQ m').Es,
      (dblJJfe hPW mW hQ m' e ∈ Δ.bd X ∧ (e = p₀ ∨ e = p₀ + 1)) ∨
      (dblJJfe hPW mW hQ m' e = e ∧ e ∈ Δ.edgesIn (W \ X)) ∨
      (dblJJfe hPW mW hQ m' e ∈ Δ.bd W \ Δ.bd X ∧
        ((e = n₀ ∧ ¬ cross₀) ∨ (e = n₀ + 1 ∧ ¬ cross₁))) := by
    intro e he
    rw [mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m'] at he
    rcases he with rfl | rfl | he | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · left; refine ⟨?_, Or.inl rfl⟩
      rw [fe_p₀]
      rcases spec₀ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_inter.mp h).1
      · unfold pairLabels at h; rw [Finset.mem_filter] at h; exact (Finset.mem_sdiff.mp h.1).1
    · left; refine ⟨?_, Or.inr rfl⟩
      rw [fe_p₁]
      rcases spec₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_inter.mp h).1
      · unfold pairLabels at h; rw [Finset.mem_filter] at h; exact (Finset.mem_sdiff.mp h.1).1
    · right; left; exact ⟨fe_old e he, he⟩
    · right; right
      push Not at hc
      refine ⟨?_, Or.inl ⟨rfl, fun h ↦ h.elim hc.1 hc.2⟩⟩
      rw [fe_n₀]
      have := (pairW r₀ hr₀ hc.1 hc.2).1
      unfold pairLabels at this; rw [Finset.mem_filter] at this; exact this.1
    · right; right
      push Not at hc
      refine ⟨?_, Or.inr ⟨rfl, fun h ↦ h.elim hc.1 hc.2⟩⟩
      rw [fe_n₁]
      have := (pairW r₁ hr₁ hc.1 hc.2).1
      unfold pairLabels at this; rw [Finset.mem_filter] at this; exact this.1
  -- the label of a new edge determines the couple
  have lab_couple : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling, ∀ d,
      d ∈ ({c, p' c} : Finset ℕ) →
      (jjLabel hPW mW hQ m' c ∈ Δ.bd X ∩ Δ.bd W → ge (jjLabel hPW mW hQ m' c) ∈ ({c, p' c} : Finset ℕ)) := by
    intro c hc d _ hthru
    rcases jjLabel_spec hcl hXW hW hPW mW hPX mX hnoX hnoW hQ m' hp' hc with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exfalso
      unfold pairLabels at h; rw [Finset.mem_filter] at h
      exact (Finset.mem_sdiff.mp h.1).2 (Finset.mem_inter.mp hthru).2
  have lab_pair : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling,
      jjLabel hPW mW hQ m' c ∉ Δ.bd X ∩ Δ.bd W → jjLabel hPW mW hQ m' c ∈ ({c, p' c} : Finset ℕ) := by
    intro c hc hnt
    rcases jjLabel_spec hcl hXW hW hPW mW hPX mX hnoX hnoW hQ m' hp' hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h⟩
    · exact absurd h hnt
    · exact absurd h hnt
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have couple₁Q : ({c₀, p' c₀} : Finset ℕ) = couple₁ hQ m' := (couple₁_eq hQ m').symm
  have couple₂Q : ({c₁, p' c₁} : Finset ℕ) = couple₂ hQ m' := (couple₂_eq hQ m').symm
  have hcl₁ : (join hQ m').IsClosed := join_isClosed hQ m'
  refine ⟨Iso.mk'' hcl₁ id (dblJJfe hPW mW hQ m') ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro v hv
    rw [join_Vs, pole_Vs] at hv
    rw [can_Vs]
    simp only [toks, Bool.false_eq_true, if_false, Finset.union_empty, id]
    exact hv
  · intro v hv
    rw [can_Vs] at hv
    simp only [toks, Bool.false_eq_true, if_false, Finset.union_empty] at hv
    exact ⟨v, by rw [join_Vs, pole_Vs]; exact hv, rfl⟩
  · intro u _ v _ h; exact h
  · -- edges map into `can`
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union]
    simp only [surv, Bool.false_eq_true, if_false]
    rw [mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m'] at he
    rcases he with rfl | rfl | he | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · rw [fe_p₀]
      rcases spec₀ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rw [fe_p₁]
      rcases spec₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rw [fe_old e he]; exact Or.inl (Or.inl (Or.inl he))
    · push Not at hc
      rw [fe_n₀]; exact Or.inr (pairW r₀ hr₀ hc.1 hc.2).1
    · push Not at hc
      rw [fe_n₁]; exact Or.inr (pairW r₁ hr₁ hc.1 hc.2).1
  · -- surjective on edges
    intro e he
    rw [can_Es, Finset.mem_union, Finset.mem_union, Finset.mem_union] at he
    simp only [surv, Bool.false_eq_true, if_false] at he
    rcases he with ((he | he) | he) | he
    · exact ⟨e, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr (Or.inr (Or.inr (Or.inl he))),
        fe_old e he⟩
    · -- a through edge
      have hge := ge_thru_mem_dangling hcl hXW hW hPW mW hnoW he
      have hfe := fe_ge_thru hPW mW hnoW he
      have hgen : ge e = n₀ ∨ ge e = n₀ + 1 := by
        rw [ge_thru hPW mW he]; split_ifs <;> simp
      -- the partner of the new edge is old
      have hpge : p' (ge e) = pX e := by
        rw [hp' _ hge, hfe, ge_old hPW mW (hnoX e (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2)]
      have hpXe : pX e ∈ Δ.bd X \ Δ.bd W := Finset.mem_sdiff.mpr
        ⟨pX_mem hPX mX (Finset.mem_inter.mp he).1,
          hnoX e (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2⟩
      have hpXn : ¬ (pX e = n₀ ∨ pX e = n₀ + 1) := by
        have := sdiffX_mem_poleW hXW hpXe
        rintro (h | h)
        · exact hn.1 (h ▸ this)
        · exact hn.2 (h ▸ this)
      -- the label of the couple of `ge e` is `e`
      have key : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling, (c = ge e ∨ p' c = ge e) →
          jjLabel hPW mW hQ m' c = e := by
        intro c hc h
        rcases h with rfl | h
        · unfold jjLabel; rw [if_pos hgen, hfe]
        · have hc' : c = pX e := by
            rw [← partner_partner hQ m' hc, h, hpge]
          unfold jjLabel
          rw [if_neg (hc' ▸ hpXn), if_pos (h ▸ hgen), h, hfe]
      by_cases h1 : ge e ∈ couple₁ hQ m'
      · rw [mem_couple₁_iff'] at h1
        refine ⟨p₀, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr (Or.inl rfl), ?_⟩
        rw [fe_p₀]
        apply key c₀ hc₀
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, partner_partner hQ m' hge]
      · rw [← mem_couple₂_iff hQ m' hge, mem_couple₂_iff'] at h1
        refine ⟨p₀ + 1, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr (Or.inr (Or.inl rfl)), ?_⟩
        rw [fe_p₁]
        apply key c₁ hc₁
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, partner_partner hQ m' hge]
    · -- a pair label of the `X`-cut
      have he' := he
      unfold pairLabels at he'
      rw [Finset.mem_filter] at he'
      have hed : e ∈ ((join hPW mW).pole (W \ X)).dangling := by
        rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl he'.1
      have hpe : p' e = pX e := by
        rw [hp' _ hed, fe_old' hPW mW (sdiffX_mem_poleW hXW he'.1), ge_old hPW mW he'.2.1]
      have hpXe : pX e ∈ Δ.bd X \ Δ.bd W :=
        Finset.mem_sdiff.mpr ⟨pX_mem hPX mX (Finset.mem_sdiff.mp he'.1).1, he'.2.1⟩
      have hen : ¬ (e = n₀ ∨ e = n₀ + 1) := by
        have := sdiffX_mem_poleW hXW he'.1
        rintro (h | h)
        · exact hn.1 (h ▸ this)
        · exact hn.2 (h ▸ this)
      have hpXn : ¬ (pX e = n₀ ∨ pX e = n₀ + 1) := by
        have := sdiffX_mem_poleW hXW hpXe
        rintro (h | h)
        · exact hn.1 (h ▸ this)
        · exact hn.2 (h ▸ this)
      have hed' : e ∈ (Δ.pole X).dangling := dangling_pole X ▸ (Finset.mem_sdiff.mp he'.1).1
      have hpXd : pX e ∈ ((join hPW mW).pole (W \ X)).dangling := by
        rw [mem_QJ_dangling hcl hXW hW hPW mW hnoW]; exact Or.inl hpXe
      have hppe : p' (pX e) = e := by
        rw [← hpe, partner_partner hQ m' hed]
      have key : ∀ c ∈ ((join hPW mW).pole (W \ X)).dangling, (c = e ∨ c = pX e) →
          jjLabel hPW mW hQ m' c = e := by
        intro c _ h
        rcases h with rfl | rfl
        · unfold jjLabel
          rw [if_neg hen, hpe, if_neg hpXn, min_eq_left he'.2.2]
        · unfold jjLabel
          rw [if_neg hpXn, hppe, if_neg hen, min_eq_right he'.2.2]
      by_cases h1 : e ∈ couple₁ hQ m'
      · rw [mem_couple₁_iff'] at h1
        refine ⟨p₀, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr (Or.inl rfl), ?_⟩
        rw [fe_p₀]
        apply key c₀ hc₀
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
      · rw [← mem_couple₂_iff hQ m' hed, mem_couple₂_iff'] at h1
        refine ⟨p₀ + 1, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr (Or.inr (Or.inl rfl)), ?_⟩
        rw [fe_p₁]
        apply key c₁ hc₁
        rcases h1 with h1 | h1
        · exact Or.inl h1.symm
        · right; rw [← h1, hpe]
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
        refine ⟨n₀, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hnc⟩)))), ?_⟩
        rw [fe_n₀]
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
        refine ⟨n₀ + 1, (mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m').mpr
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hnc⟩)))), ?_⟩
        rw [fe_n₁]
        rcases h1 with h1 | h1
        · rw [← h1]; exact min_eq_left he'.2.2
        · rw [← h1, partner_partner hPW mW hed]; exact min_eq_right he'.2.2
  · -- injective on edges
    intro d hd e he hde
    have cd := cls d hd
    have ce := cls e he
    have hdisj₁ : ∀ x, x ∈ Δ.bd X → x ∈ Δ.edgesIn (W \ X) → False :=
      fun x h1 h2 ↦ (edgesIn_sdiff_ends h2).1 h1
    have hdisj₂ : ∀ x, x ∈ Δ.bd X → x ∈ Δ.bd W \ Δ.bd X → False :=
      fun x h1 h2 ↦ (Finset.mem_sdiff.mp h2).2 h1
    have hdisj₃ : ∀ x, x ∈ Δ.edgesIn (W \ X) → x ∈ Δ.bd W \ Δ.bd X → False :=
      fun x h1 h2 ↦ (edgesIn_sdiff_ends h1).2 (Finset.mem_sdiff.mp h2).1
    rcases cd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ <;>
      rcases ce with ⟨he1, he2⟩ | ⟨he1, he2⟩ | ⟨he1, he2⟩
    · -- both are new edges of the second join
      rcases hd2 with rfl | rfl <;> rcases he2 with rfl | rfl
      · rfl
      · exfalso
        rw [fe_p₀, fe_p₁] at hde
        by_cases hthru : jjLabel hPW mW hQ m' c₀ ∈ Δ.bd X ∩ Δ.bd W
        · have h1 := lab_couple c₀ hc₀ c₀ (Finset.mem_insert_self _ _) hthru
          have h2 := lab_couple c₁ hc₁ c₁ (Finset.mem_insert_self _ _) (hde ▸ hthru)
          rw [← hde] at h2
          rw [couple₁Q] at h1
          rw [couple₂Q] at h2
          have hgd : ge (jjLabel hPW mW hQ m' c₀) ∈ ((join hPW mW).pole (W \ X)).dangling :=
            couple₁_subset_dangling hQ m' h1
          exact (mem_couple₂_iff hQ m' hgd).mp h2 h1
        · have h1 := lab_pair c₀ hc₀ hthru
          have h2 := lab_pair c₁ hc₁ (hde ▸ hthru)
          rw [← hde] at h2
          rw [couple₁Q] at h1
          rw [couple₂Q] at h2
          have hgd : jjLabel hPW mW hQ m' c₀ ∈ ((join hPW mW).pole (W \ X)).dangling :=
            couple₁_subset_dangling hQ m' h1
          exact (mem_couple₂_iff hQ m' hgd).mp h2 h1
      · exfalso
        rw [fe_p₀, fe_p₁] at hde
        by_cases hthru : jjLabel hPW mW hQ m' c₀ ∈ Δ.bd X ∩ Δ.bd W
        · have h1 := lab_couple c₀ hc₀ c₀ (Finset.mem_insert_self _ _) hthru
          have h2 := lab_couple c₁ hc₁ c₁ (Finset.mem_insert_self _ _) (hde ▸ hthru)
          rw [← hde] at h1
          rw [couple₁Q] at h1
          rw [couple₂Q] at h2
          have hgd : ge (jjLabel hPW mW hQ m' c₁) ∈ ((join hPW mW).pole (W \ X)).dangling :=
            couple₁_subset_dangling hQ m' h1
          exact (mem_couple₂_iff hQ m' hgd).mp h2 h1
        · have h1 := lab_pair c₀ hc₀ hthru
          have h2 := lab_pair c₁ hc₁ (hde ▸ hthru)
          rw [← hde] at h1
          rw [couple₁Q] at h1
          rw [couple₂Q] at h2
          have hgd : jjLabel hPW mW hQ m' c₁ ∈ ((join hPW mW).pole (W \ X)).dangling :=
            couple₁_subset_dangling hQ m' h1
          exact (mem_couple₂_iff hQ m' hgd).mp h2 h1
      · rfl
    · exfalso; exact hdisj₁ _ hd1 (by rw [hde, he1]; exact he2)
    · exfalso; exact hdisj₂ _ hd1 (by rw [hde]; exact he1)
    · exfalso; exact hdisj₁ _ he1 (by rw [← hde, hd1]; exact hd2)
    · rw [hd1, he1] at hde; exact hde
    · exfalso; exact hdisj₃ _ (by rw [← hde, hd1]; exact hd2) he1
    · exfalso; exact hdisj₂ _ he1 (by rw [← hde]; exact hd1)
    · exfalso; exact hdisj₃ _ (by rw [hde, he1]; exact he2) hd1
    · -- both are surviving first-stage edges
      rcases hd2 with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> rcases he2 with ⟨rfl, hc'⟩ | ⟨rfl, hc'⟩
      · rfl
      · exfalso
        rw [fe_n₀, fe_n₁] at hde
        push Not at hc hc'
        have h1 := (pairW r₀ hr₀ hc.1 hc.2).2
        have h2 := (pairW r₁ hr₁ hc'.1 hc'.2).2
        have m1 : min r₀ (pW r₀) ∈ couple₁ hPW mW := by
          rw [couple₁_eq]
          rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have m2 : min r₁ (pW r₁) ∈ couple₂ hPW mW := by
          rw [couple₂_eq]
          rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [← hde] at m2
        exact (mem_couple₂_iff hPW mW (couple₁_subset_dangling hPW mW m1)).mp m2 m1
      · exfalso
        rw [fe_n₀, fe_n₁] at hde
        push Not at hc hc'
        have h1 := (pairW r₀ hr₀ hc'.1 hc'.2).2
        have h2 := (pairW r₁ hr₁ hc.1 hc.2).2
        have m1 : min r₀ (pW r₀) ∈ couple₁ hPW mW := by
          rw [couple₁_eq]
          rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have m2 : min r₁ (pW r₁) ∈ couple₂ hPW mW := by
          rw [couple₂_eq]
          rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [hde] at m2
        exact (mem_couple₂_iff hPW mW (couple₁_subset_dangling hPW mW m1)).mp m2 m1
      · rfl
  · -- the ends
    intro e he
    simp only [id]
    rw [mem_dblJJ_Es hcl hXW hW hPW mW hnoW hQ m'] at he
    rcases he with rfl | rfl | he | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · rw [fe_p₀, e₀.1, e₀.2]
      rcases spec₀ with ⟨h, -, h1, h2⟩ | ⟨h, -, h1, h2⟩ | ⟨h, h1, h2, h3⟩
      · right; rw [(canThru _ h).1, (canThru _ h).2, h1, h2]; exact ⟨rfl, rfl⟩
      · left; rw [(canThru _ h).1, (canThru _ h).2, h1, h2]; exact ⟨rfl, rfl⟩
      · rw [(canX _ h).1, (canX _ h).2, h1, h2]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
        · right; rw [h4, h3]; exact ⟨rfl, rfl⟩
    · rw [fe_p₁, e₁.1, e₁.2]
      rcases spec₁ with ⟨h, -, h1, h2⟩ | ⟨h, -, h1, h2⟩ | ⟨h, h1, h2, h3⟩
      · right; rw [(canThru _ h).1, (canThru _ h).2, h1, h2]; exact ⟨rfl, rfl⟩
      · left; rw [(canThru _ h).1, (canThru _ h).2, h1, h2]; exact ⟨rfl, rfl⟩
      · rw [(canX _ h).1, (canX _ h).2, h1, h2]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
        · right; rw [h4, h3]; exact ⟨rfl, rfl⟩
    · left
      rw [fe_old e he, canOld e he, canOld e he]
      have heQ : e ∈ ((join hPW mW).pole (W \ X)).Es :=
        (mem_QJ_Es hXW hPW mW hnoW).mpr (Or.inl he)
      rw [join_ends_eq hQ m' heQ, join_ends_eq hQ m' heQ, pole_ends,
        join_ends_eq hPW mW (memM e he), join_ends_eq hPW mW (memM e he), pole_ends]
      exact ⟨rfl, rfl⟩
    · push Not at hc
      rw [fe_n₀, en₀.1, en₀.2]
      have hp := pairW r₀ hr₀ hc.1 hc.2
      rw [(canW _ hp.1).1, (canW _ hp.1).2]
      rw [innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hr₀, hc.1⟩),
        innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hpr₀, hc.2⟩)]
      rcases hp.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
      · right; rw [h4, h3]; exact ⟨rfl, rfl⟩
    · push Not at hc
      rw [fe_n₁, en₁.1, en₁.2]
      have hp := pairW r₁ hr₁ hc.1 hc.2
      rw [(canW _ hp.1).1, (canW _ hp.1).2]
      rw [innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hr₁, hc.1⟩),
        innerEnd_W_eq_innerE hXW hPW (Finset.mem_sdiff.mpr ⟨hpr₁, hc.2⟩)]
      rcases hp.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · left; rw [h4, h3]; exact ⟨rfl, rfl⟩
      · right; rw [h4, h3]; exact ⟨rfl, rfl⟩

end Main

end JJ

end FinGraph
end GraphPuzzles
