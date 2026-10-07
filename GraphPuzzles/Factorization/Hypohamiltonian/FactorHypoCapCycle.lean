import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoDescentCore
import GraphPuzzles.Factorization.Bicritical.FactorCapBicriticalB

/-!
# Hamilton cycles of a cap from the side part of a cycle

Given a Hamilton cycle `C` of a shore `S` of `Δ`, the edges of `C` touching `Y`, viewed in the
cap of the pole at `Y` (with the new edge `uw` optionally added), form a Hamilton cycle of the
corresponding vertex set of the cap, provided the degrees at the new vertices work out and the
cut edges of the two couples are linked on the `Y` side (or `uw` is present).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hY : Y ⊆ Δ.Vs)
  (hind : Δ.IsIndependentCut Y) (hPY : (Δ.pole Y).IsPole4) (m : Fin 3)

section HalfEdges

/-- Half-edges of an edge set of the cap at an old vertex. -/
theorem cap_halfEdgesIn_old {F : Finset ℕ} (hF : F ⊆ (cap hPY m).Es) {y : ℕ} (hy : y ∈ Y) :
    (cap hPY m).halfEdgesIn F y = Δ.halfEdgesIn (F.erase (freshE (Δ.pole Y))) y := by
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, mem_halfEdgesIn]
  dsimp only
  constructor
  · rintro ⟨he, hend⟩
    have heE := hF he
    rw [cap_Es, Finset.mem_insert] at heE
    rcases heE with rfl | heP
    · exfalso
      rw [cap_ends_new] at hend
      split_ifs at hend
      · exact huY (hend ▸ hy)
      · exact hwY (hend ▸ hy)
    · refine ⟨Finset.mem_erase.mpr ⟨fun h ↦ freshE_notMem (h ▸ heP), he⟩, ?_⟩
      rw [cap_ends_eq hPY m heP] at hend
      split_ifs at hend with hin hc
      · exact hend
      · exfalso; rw [← hend] at hy; exact huY hy
      · exfalso; rw [← hend] at hy; exact hwY hy
  · rintro ⟨he, hend⟩
    rw [Finset.mem_erase] at he
    have heP : e ∈ (Δ.pole Y).Es := by
      have := hF he.2
      rw [cap_Es, Finset.mem_insert] at this
      exact this.resolve_left he.1
    refine ⟨he.2, ?_⟩
    rw [cap_ends_eq hPY m heP]
    have hin : (Δ.pole Y).ends e i ∈ (Δ.pole Y).Vs := by rw [pole_ends, pole_Vs, hend]; exact hy
    rw [if_pos hin]
    exact hend

/-- Half-edges of an edge set of the cap at the first new vertex. -/
theorem cap_halfEdgesIn_u {F : Finset ℕ} (hF : F ⊆ (cap hPY m).Es) :
    (cap hPY m).halfEdgesIn F (freshV (Δ.pole Y)) =
      (if freshE (Δ.pole Y) ∈ F then {(freshE (Δ.pole Y), 0)} else ∅) ∪
        ((F ∩ couple₁ hPY m).image fun d ↦ (d, outerIdx hPY d)) := by
  classical
  ext ⟨e, i⟩
  have h1 : (e, i) ∈ (cap hPY m).halfEdgesIn F (freshV (Δ.pole Y)) ↔
      e ∈ F ∧ (e, i) ∈ (cap hPY m).halfEdgesIn (cap hPY m).Es (freshV (Δ.pole Y)) := by
    rw [mem_halfEdgesIn, mem_halfEdgesIn]
    constructor
    · rintro ⟨he, hend⟩; exact ⟨he, hF he, hend⟩
    · rintro ⟨he, -, hend⟩; exact ⟨he, hend⟩
  rw [h1, cap_halfEdges_u, Finset.mem_insert, Finset.mem_image, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨he, h | ⟨d, hd, hde⟩⟩
    · left
      rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos he]; exact Finset.mem_singleton_self _
    · right
      rw [Prod.mk.injEq] at hde
      obtain ⟨rfl, rfl⟩ := hde
      exact ⟨d, Finset.mem_inter.mpr ⟨he, hd⟩, rfl⟩
  · rintro (h | ⟨d, hd, hde⟩)
    · split_ifs at h with hf
      · rw [Finset.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hf, Or.inl rfl⟩
      · exact absurd h (Finset.notMem_empty _)
    · rw [Prod.mk.injEq] at hde
      obtain ⟨rfl, rfl⟩ := hde
      rw [Finset.mem_inter] at hd
      exact ⟨hd.1, Or.inr ⟨d, hd.2, rfl⟩⟩

/-- Half-edges of an edge set of the cap at the second new vertex. -/
theorem cap_halfEdgesIn_w {F : Finset ℕ} (hF : F ⊆ (cap hPY m).Es) :
    (cap hPY m).halfEdgesIn F (freshV (Δ.pole Y) + 1) =
      (if freshE (Δ.pole Y) ∈ F then {(freshE (Δ.pole Y), 1)} else ∅) ∪
        ((F ∩ couple₂ hPY m).image fun d ↦ (d, outerIdx hPY d)) := by
  classical
  ext ⟨e, i⟩
  have h1 : (e, i) ∈ (cap hPY m).halfEdgesIn F (freshV (Δ.pole Y) + 1) ↔
      e ∈ F ∧ (e, i) ∈ (cap hPY m).halfEdgesIn (cap hPY m).Es (freshV (Δ.pole Y) + 1) := by
    rw [mem_halfEdgesIn, mem_halfEdgesIn]
    constructor
    · rintro ⟨he, hend⟩; exact ⟨he, hF he, hend⟩
    · rintro ⟨he, -, hend⟩; exact ⟨he, hend⟩
  rw [h1, cap_halfEdges_w, Finset.mem_insert, Finset.mem_image, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨he, h | ⟨d, hd, hde⟩⟩
    · left
      rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos he]; exact Finset.mem_singleton_self _
    · right
      rw [Prod.mk.injEq] at hde
      obtain ⟨rfl, rfl⟩ := hde
      exact ⟨d, Finset.mem_inter.mpr ⟨he, hd⟩, rfl⟩
  · rintro (h | ⟨d, hd, hde⟩)
    · split_ifs at h with hf
      · rw [Finset.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hf, Or.inl rfl⟩
      · exact absurd h (Finset.notMem_empty _)
    · rw [Prod.mk.injEq] at hde
      obtain ⟨rfl, rfl⟩ := hde
      rw [Finset.mem_inter] at hd
      exact ⟨hd.1, Or.inr ⟨d, hd.2, rfl⟩⟩

theorem cap_degIn_u {F : Finset ℕ} (hF : F ⊆ (cap hPY m).Es) :
    (cap hPY m).degIn F (freshV (Δ.pole Y)) =
      (if freshE (Δ.pole Y) ∈ F then 1 else 0) + (F ∩ couple₁ hPY m).card := by
  classical
  rw [degIn_eq_card, cap_halfEdgesIn_u hPY m hF, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h ↦ (Prod.mk.inj h).1)]
  · split_ifs <;> simp
  · rw [Finset.disjoint_left]
    intro x hx hx'
    split_ifs at hx with hf
    · rw [Finset.mem_singleton] at hx
      rw [hx, Finset.mem_image] at hx'
      obtain ⟨d, hd, hde⟩ := hx'
      rw [Prod.mk.injEq] at hde
      have := (Finset.mem_inter.mp hd).2
      rw [hde.1] at this
      exact freshE_notMem ((mem_dangling.mp (couple₁_subset_dangling hPY m this)).1)
    · exact absurd hx (Finset.notMem_empty _)

theorem cap_degIn_w {F : Finset ℕ} (hF : F ⊆ (cap hPY m).Es) :
    (cap hPY m).degIn F (freshV (Δ.pole Y) + 1) =
      (if freshE (Δ.pole Y) ∈ F then 1 else 0) + (F ∩ couple₂ hPY m).card := by
  classical
  rw [degIn_eq_card, cap_halfEdgesIn_w hPY m hF, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h ↦ (Prod.mk.inj h).1)]
  · split_ifs <;> simp
  · rw [Finset.disjoint_left]
    intro x hx hx'
    split_ifs at hx with hf
    · rw [Finset.mem_singleton] at hx
      rw [hx, Finset.mem_image] at hx'
      obtain ⟨d, hd, hde⟩ := hx'
      rw [Prod.mk.injEq] at hde
      have := (Finset.mem_inter.mp hd).2
      rw [hde.1] at this
      exact freshE_notMem ((mem_dangling.mp (couple₂_subset_dangling hPY m this)).1)
    · exact absurd hx (Finset.notMem_empty _)

end HalfEdges

section Adjacency

/-- Old edges of the cap sharing a vertex of `Y` in `Δ` are adjacent in the cap. -/
theorem cap_adjIn_old {F : Finset ℕ} {e f : ℕ} (he : e ∈ F) (hf : f ∈ F)
    (heP : e ∈ (Δ.pole Y).Es) (hfP : f ∈ (Δ.pole Y).Es) {i j : Fin 2} (hij : Δ.ends e i = Δ.ends f j)
    (hy : Δ.ends e i ∈ Y) : (cap hPY m).AdjIn F e f := by
  refine ⟨he, hf, i, j, ?_⟩
  rw [cap_ends_eq hPY m heP, cap_ends_eq hPY m hfP]
  have h1 : (Δ.pole Y).ends e i ∈ (Δ.pole Y).Vs := hy
  have h2 : (Δ.pole Y).ends f j ∈ (Δ.pole Y).Vs := by rw [pole_ends, ← hij]; exact hy
  rw [if_pos h1, if_pos h2]
  exact hij

theorem cap_ends_outer_of_couple₁ {d : ℕ} (hd : d ∈ couple₁ hPY m) :
    (cap hPY m).ends d (outerIdx hPY d) = freshV (Δ.pole Y) := by
  rw [cap_ends_outer hPY m (couple₁_subset_dangling hPY m hd), if_pos hd]

theorem cap_ends_outer_of_couple₂ {d : ℕ} (hd : d ∈ couple₂ hPY m) :
    (cap hPY m).ends d (outerIdx hPY d) = freshV (Δ.pole Y) + 1 := by
  rw [cap_ends_outer hPY m (couple₂_subset_dangling hPY m hd),
    if_neg ((mem_couple₂_iff hPY m (couple₂_subset_dangling hPY m hd)).mp hd)]

end Adjacency

section Main

variable {S C : Finset ℕ} (hC : Δ.IsHamCycle S C) (hSV : S ⊆ Δ.Vs)
include hcl hY hind hC hSV

omit hcl hY hSV in
/-- **A Hamilton cycle of the cap from the side part.** -/
theorem cap_hamCycle (uw : Bool) {T : Finset ℕ}
    (hT_old : ∀ y ∈ Y, y ∈ T ↔ y ∈ S)
    (hT_sub : T ⊆ insert (freshV (Δ.pole Y)) (insert (freshV (Δ.pole Y) + 1) Y))
    (hT_u : freshV (Δ.pole Y) ∈ T ↔ (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty)
    (hT_w : freshV (Δ.pole Y) + 1 ∈ T ↔ (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty)
    (hdeg_u : (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty →
      (C ∩ Δ.bd Y ∩ couple₁ hPY m).card + (if uw then 1 else 0) = 2)
    (hdeg_w : (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty →
      (C ∩ Δ.bd Y ∩ couple₂ hPY m).card + (if uw then 1 else 0) = 2)
    (huw : uw = true → (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty ∧
      (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty)
    (hK : (C ∩ Δ.bd Y).Nonempty)
    (hcross : uw = false → (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty →
      (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty →
      ∃ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∃ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
        Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) a b) :
    (cap hPY m).IsHamCycle T
      (Δ.sidePart C Y ∪ (if uw then {freshE (Δ.pole Y)} else ∅)) := by
  classical
  set P := Δ.pole Y with hPdef
  set u := freshV P with hudef
  set w := freshV P + 1 with hwdef
  set Ĉ := Δ.sidePart C Y ∪ (if uw then {freshE P} else ∅) with hĈdef
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset S)
  have hside_P : ∀ e ∈ Δ.sidePart C Y, e ∈ P.Es := by
    intro e he
    rw [mem_sidePart_iff] at he
    rw [hPdef, pole_Es, Finset.mem_union]; exact he.2
  have hsideC : Δ.sidePart C Y ⊆ C := sidePart_subset
  have hĈE : Ĉ ⊆ (cap hPY m).Es := by
    intro e he
    rw [hĈdef, Finset.mem_union] at he
    rw [cap_Es, Finset.mem_insert]
    rcases he with he | he
    · exact Or.inr (hside_P e he)
    · split_ifs at he
      · exact Or.inl (Finset.mem_singleton.mp he)
      · exact absurd he (Finset.notMem_empty _)
  have hfresh_side : freshE P ∉ Δ.sidePart C Y := fun h ↦ freshE_notMem (hside_P _ h)
  have hĈerase : Ĉ.erase (freshE P) = Δ.sidePart C Y := by
    ext e
    rw [Finset.mem_erase, hĈdef, Finset.mem_union]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact h
      · exfalso
        split_ifs at h
        · exact hne (Finset.mem_singleton.mp h)
        · exact Finset.notMem_empty _ h
    · intro h
      exact ⟨fun h' ↦ hfresh_side (h' ▸ h), Or.inl h⟩
  have hĈ_couple₁ : Ĉ ∩ couple₁ hPY m = C ∩ Δ.bd Y ∩ couple₁ hPY m := by
    ext e
    simp only [Finset.mem_inter, hĈdef, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hc⟩
      · rw [mem_sidePart_iff] at h
        refine ⟨⟨h.1, ?_⟩, hc⟩
        rw [← dangling_pole]; exact couple₁_subset_dangling hPY m hc
      · exfalso
        split_ifs at h
        · exact freshE_notMem ((mem_dangling.mp (couple₁_subset_dangling hPY m
            ((Finset.mem_singleton.mp h) ▸ hc))).1)
        · exact Finset.notMem_empty _ h
    · rintro ⟨⟨hc, hb⟩, hc'⟩
      exact ⟨Or.inl (mem_sidePart_of_bd hCE hc hb), hc'⟩
  have hĈ_couple₂ : Ĉ ∩ couple₂ hPY m = C ∩ Δ.bd Y ∩ couple₂ hPY m := by
    ext e
    simp only [Finset.mem_inter, hĈdef, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hc⟩
      · rw [mem_sidePart_iff] at h
        refine ⟨⟨h.1, ?_⟩, hc⟩
        rw [← dangling_pole]; exact couple₂_subset_dangling hPY m hc
      · exfalso
        split_ifs at h
        · exact freshE_notMem ((mem_dangling.mp (couple₂_subset_dangling hPY m
            ((Finset.mem_singleton.mp h) ▸ hc))).1)
        · exact Finset.notMem_empty _ h
    · rintro ⟨⟨hc, hb⟩, hc'⟩
      exact ⟨Or.inl (mem_sidePart_of_bd hCE hc hb), hc'⟩
  have huwĈ : freshE P ∈ Ĉ ↔ uw = true := by
    rw [hĈdef, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact absurd h hfresh_side
      · split_ifs at h with h'
        · exact h'
        · exact absurd h (Finset.notMem_empty _)
    · intro h; right; rw [if_pos h]; exact Finset.mem_singleton_self _
  -- a cut edge of `C` is in one of the two couples
  have hcouple : ∀ k ∈ C ∩ Δ.bd Y, k ∈ couple₁ hPY m ∨ k ∈ couple₂ hPY m := by
    intro k hk
    have hd : k ∈ P.dangling := by rw [dangling_pole]; exact (Finset.mem_inter.mp hk).2
    by_cases h : k ∈ couple₁ hPY m
    · exact Or.inl h
    · exact Or.inr ((mem_couple₂_iff hPY m hd).mpr h)
  refine ⟨?_, ?_, ?_⟩
  · -- the edges lie inside `T`
    intro e he
    rw [mem_edgesIn]
    refine ⟨hĈE he, fun i ↦ ?_⟩
    rw [hĈdef, Finset.mem_union] at he
    rcases he with he | he
    · have heC := hsideC he
      have heP := hside_P e he
      rw [cap_ends_eq hPY m heP]
      split_ifs with hin hc₁
      · have hS' : Δ.ends e i ∈ S := (mem_edgesIn.mp (hC.subset heC)).2 i
        exact (hT_old _ hin).mpr hS'
      · apply hT_u.mpr
        refine ⟨e, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨heC, ?_⟩, hc₁⟩⟩
        rw [← dangling_pole]; exact couple₁_subset_dangling hPY m hc₁
      · apply hT_w.mpr
        have hd : e ∈ P.dangling := mem_dangling.mpr ⟨heP, i, hin⟩
        have hc₂ := (mem_couple₂_iff hPY m hd).mpr hc₁
        refine ⟨e, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨heC, ?_⟩, hc₂⟩⟩
        rw [← dangling_pole]; exact hd
    · split_ifs at he with h
      · rw [Finset.mem_singleton] at he
        subst he
        rw [cap_ends_new]
        obtain ⟨h1, h2⟩ := huw h
        split_ifs
        · exact hT_u.mpr h1
        · exact hT_w.mpr h2
      · exact absurd he (Finset.notMem_empty _)
  · -- degrees
    intro t ht
    have ht' := hT_sub ht
    rw [Finset.mem_insert, Finset.mem_insert] at ht'
    rcases ht' with rfl | rfl | htY
    · rw [cap_degIn_u hPY m hĈE, hĈ_couple₁]
      have hne := hT_u.mp ht
      have := hdeg_u hne
      by_cases h : uw = true
      · rw [if_pos (huwĈ.mpr h)]; rw [if_pos h] at this; omega
      · have h' : uw = false := by simpa using h
        rw [if_neg (fun h'' ↦ h (huwĈ.mp h''))]; rw [if_neg h] at this; omega
    · rw [cap_degIn_w hPY m hĈE, hĈ_couple₂]
      have hne := hT_w.mp ht
      have := hdeg_w hne
      by_cases h : uw = true
      · rw [if_pos (huwĈ.mpr h)]; rw [if_pos h] at this; omega
      · rw [if_neg (fun h'' ↦ h (huwĈ.mp h''))]; rw [if_neg h] at this; omega
    · rw [degIn_eq_card, cap_halfEdgesIn_old hPY m hĈE htY, hĈerase, ← degIn_eq_card]
      have htS : t ∈ S := (hT_old t htY).mp ht
      rw [← hC.deg t htS, degIn_eq_card, degIn_eq_card]
      congr 1
      ext ⟨e, i⟩
      rw [mem_halfEdgesIn, mem_halfEdgesIn]
      constructor
      · rintro ⟨he, hend⟩; exact ⟨hsideC he, hend⟩
      · rintro ⟨he, hend⟩; exact ⟨mem_sidePart_of_ends hCE he (hend ▸ htY), hend⟩
  · -- connectivity
    -- translating links on the `Y` side into the cap
    have htrans : ∀ x y, Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) x y →
        Relation.ReflTransGen ((cap hPY m).AdjIn Ĉ) x y := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hlast ih =>
        obtain ⟨hb, hc, i, j, hij⟩ := hlast
        by_cases hin : Δ.ends b i ∈ Y
        · exact ih.tail (cap_adjIn_old hPY m (Finset.mem_union_left _ hb)
            (Finset.mem_union_left _ hc) (hside_P b hb) (hside_P c hc) hij hin)
        · -- both are cut edges sharing their outer end: they coincide
          have hbbd : b ∈ Δ.bd Y := by
            rw [mem_sidePart_iff] at hb
            rcases hb.2 with h | h
            · exact absurd ((mem_edgesIn.mp h).2 i) hin
            · exact h
          have hcbd : c ∈ Δ.bd Y := by
            rw [mem_sidePart_iff] at hc
            rcases hc.2 with h | h
            · exact absurd ((mem_edgesIn.mp h).2 j) (hij ▸ hin)
            · exact h
          rw [hind.eq_of_ends hbbd hcbd hij] at ih
          exact ih
    -- every edge of `Ĉ` reaches a cut edge of `C`
    obtain ⟨k₀, hk₀⟩ := hK
    have hreach : ∀ e ∈ Ĉ, ∃ k ∈ C ∩ Δ.bd Y, Relation.ReflTransGen ((cap hPY m).AdjIn Ĉ) e k := by
      intro e he
      rw [hĈdef, Finset.mem_union] at he
      rcases he with he | he
      · obtain ⟨b, hb, hbS, hpath⟩ := linked_to_cut hCE he (Finset.mem_inter.mp hk₀).2
          (hC.connected e (hsideC he) k₀ (Finset.mem_inter.mp hk₀).1)
        exact ⟨b, Finset.mem_inter.mpr ⟨hsideC hbS, hb⟩, htrans _ _ hpath⟩
      · split_ifs at he with h
        · rw [Finset.mem_singleton] at he
          subst he
          obtain ⟨⟨a, ha⟩, -⟩ := huw h
          have haK := Finset.mem_inter.mp ha
          refine ⟨a, haK.1, Relation.ReflTransGen.single ⟨huwĈ.mpr h,
            Finset.mem_union_left _ (mem_sidePart_of_bd hCE (Finset.mem_inter.mp haK.1).1
              (Finset.mem_inter.mp haK.1).2), 0, outerIdx hPY a, ?_⟩⟩
          rw [cap_ends_new, if_pos rfl, cap_ends_outer_of_couple₁ hPY m haK.2]
        · exact absurd he (Finset.notMem_empty _)
    -- cut edges of the same couple are adjacent in the cap
    have hsame₁ : ∀ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∀ b ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m,
        (cap hPY m).AdjIn Ĉ a b := by
      intro a ha b hb
      have haK := Finset.mem_inter.mp ha
      have hbK := Finset.mem_inter.mp hb
      refine ⟨Finset.mem_union_left _ (mem_sidePart_of_bd hCE (Finset.mem_inter.mp haK.1).1
        (Finset.mem_inter.mp haK.1).2), Finset.mem_union_left _ (mem_sidePart_of_bd hCE
        (Finset.mem_inter.mp hbK.1).1 (Finset.mem_inter.mp hbK.1).2), outerIdx hPY a,
        outerIdx hPY b, ?_⟩
      rw [cap_ends_outer_of_couple₁ hPY m haK.2, cap_ends_outer_of_couple₁ hPY m hbK.2]
    have hsame₂ : ∀ a ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m, ∀ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
        (cap hPY m).AdjIn Ĉ a b := by
      intro a ha b hb
      have haK := Finset.mem_inter.mp ha
      have hbK := Finset.mem_inter.mp hb
      refine ⟨Finset.mem_union_left _ (mem_sidePart_of_bd hCE (Finset.mem_inter.mp haK.1).1
        (Finset.mem_inter.mp haK.1).2), Finset.mem_union_left _ (mem_sidePart_of_bd hCE
        (Finset.mem_inter.mp hbK.1).1 (Finset.mem_inter.mp hbK.1).2), outerIdx hPY a,
        outerIdx hPY b, ?_⟩
      rw [cap_ends_outer_of_couple₂ hPY m haK.2, cap_ends_outer_of_couple₂ hPY m hbK.2]
    -- cut edges of different couples are linked
    have hdiff : ∀ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∀ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
        Relation.ReflTransGen ((cap hPY m).AdjIn Ĉ) a b := by
      intro a ha b hb
      by_cases h : uw = true
      · have haK := Finset.mem_inter.mp ha
        have hbK := Finset.mem_inter.mp hb
        have haĈ : a ∈ Ĉ := Finset.mem_union_left _ (mem_sidePart_of_bd hCE
          (Finset.mem_inter.mp haK.1).1 (Finset.mem_inter.mp haK.1).2)
        have hbĈ : b ∈ Ĉ := Finset.mem_union_left _ (mem_sidePart_of_bd hCE
          (Finset.mem_inter.mp hbK.1).1 (Finset.mem_inter.mp hbK.1).2)
        refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single
          ⟨haĈ, huwĈ.mpr h, outerIdx hPY a, 0, ?_⟩) (Relation.ReflTransGen.single
          ⟨huwĈ.mpr h, hbĈ, 1, outerIdx hPY b, ?_⟩)
        · rw [cap_ends_outer_of_couple₁ hPY m haK.2, cap_ends_new, if_pos rfl]
        · rw [cap_ends_outer_of_couple₂ hPY m hbK.2, cap_ends_new, if_neg (by decide)]
      · have h' : uw = false := by simpa using h
        obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hcross h' ⟨a, ha⟩ ⟨b, hb⟩
        exact (Relation.ReflTransGen.single (hsame₁ a ha a₀ ha₀)).trans
          ((htrans _ _ hab).trans (Relation.ReflTransGen.single (hsame₂ b₀ hb₀ b hb)))
    -- any two cut edges are linked
    have hKK : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y,
        Relation.ReflTransGen ((cap hPY m).AdjIn Ĉ) a b := by
      intro a ha b hb
      rcases hcouple a ha with ha₁ | ha₂ <;> rcases hcouple b hb with hb₁ | hb₂
      · exact Relation.ReflTransGen.single (hsame₁ a (Finset.mem_inter.mpr ⟨ha, ha₁⟩) b
          (Finset.mem_inter.mpr ⟨hb, hb₁⟩))
      · exact hdiff a (Finset.mem_inter.mpr ⟨ha, ha₁⟩) b (Finset.mem_inter.mpr ⟨hb, hb₂⟩)
      · exact reflTransGen_adjIn_symm (hdiff b (Finset.mem_inter.mpr ⟨hb, hb₁⟩) a
          (Finset.mem_inter.mpr ⟨ha, ha₂⟩))
      · exact Relation.ReflTransGen.single (hsame₂ a (Finset.mem_inter.mpr ⟨ha, ha₂⟩) b
          (Finset.mem_inter.mpr ⟨hb, hb₂⟩))
    intro e he f hf
    obtain ⟨k, hk, hek⟩ := hreach e he
    obtain ⟨k', hk', hfk'⟩ := hreach f hf
    exact hek.trans ((hKK k hk k' hk').trans (reflTransGen_adjIn_symm hfk'))

end Main

end FinGraph
end GraphPuzzles
