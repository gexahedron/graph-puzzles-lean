import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoDescentCore
import GraphPuzzles.Factorization.Bicritical.FactorCapBicriticalB

/-!
# Hamilton cycles of a join from the complementary side of a cycle

Given a Hamilton cycle `C` of a shore `S` of `Δ` whose cut edges form whole couples, the edges
of `C` inside the complement of `Y` together with the new edges of the couples met by `C` form
a Hamilton cycle of the corresponding vertex set of the join, provided the two couples (when
both are met) are linked on the complementary side.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hY : Y ⊆ Δ.Vs)
  (hind : Δ.IsIndependentCut Y) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)

section HalfEdges

variable {Γ : FinGraph}

theorem halfEdgesIn_union (A B : Finset ℕ) (v : ℕ) :
    Γ.halfEdgesIn (A ∪ B) v = Γ.halfEdgesIn A v ∪ Γ.halfEdgesIn B v := by
  ext ⟨e, i⟩
  simp only [mem_halfEdgesIn, Finset.mem_union]
  tauto

theorem halfEdgesIn_filter {A B : Finset ℕ} (h : A ⊆ B) (v : ℕ) :
    Γ.halfEdgesIn A v = (Γ.halfEdgesIn B v).filter (fun x ↦ x.1 ∈ A) := by
  ext ⟨e, i⟩
  simp only [mem_halfEdgesIn, Finset.mem_filter]
  constructor
  · rintro ⟨he, hi⟩; exact ⟨⟨h he, hi⟩, he⟩
  · rintro ⟨⟨-, hi⟩, he⟩; exact ⟨he, hi⟩

theorem halfEdgesIn_disjoint_of_disjoint {A B : Finset ℕ} (h : Disjoint A B) (v : ℕ) :
    Disjoint (Γ.halfEdgesIn A v) (Γ.halfEdgesIn B v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_halfEdgesIn] at hx hx'
  exact Finset.disjoint_left.mp h hx.1 hx'.1

end HalfEdges

section Join

/-- The new edge of the couple of a cut edge. -/
noncomputable def newE (k : ℕ) : ℕ :=
  if k ∈ couple₁ hPYc m then freshE (Δ.pole (Δ.Vs \ Y)) else freshE (Δ.pole (Δ.Vs \ Y)) + 1

theorem newE_eq_newHalf_fst {k : Fin 4} :
    newE hPYc m (bdEmb hPYc k) = (newHalf (P := Δ.pole (Δ.Vs \ Y)) m k).1 := by
  unfold newE
  split_ifs with h
  · rw [newHalf_fst_of_couple₁ hPYc m h]
  · rw [newHalf_fst_of_couple₂ hPYc m ((mem_couple₂_iff hPYc m (bdEmb_mem hPYc k)).mpr h)]

theorem newE_mem_join {k : ℕ} : newE hPYc m k ∈ (join hPYc m).Es := by
  unfold newE
  rw [join_Es]
  split_ifs <;> simp

/-- The outer end of a cut edge is an end of its new edge. -/
theorem newE_ends (hcl : Δ.IsClosed) {k : ℕ} (hk : k ∈ Δ.bd Y) :
    ∃ i, (join hPYc m).ends (newE hPYc m k) i = innerEnd hPYc k := by
  obtain ⟨p, hp⟩ := exists_bdEmb_eq hPYc (mem_dangling_compl hcl hk)
  rw [← hp, newE_eq_newHalf_fst]
  exact ⟨_, join_ends_newHalf hPYc m p⟩

/-- An end of a cut edge outside `Y` is its outer end. -/
theorem ends_eq_innerEnd_compl (hcl : Δ.IsClosed) {e : ℕ} (hb : e ∈ Δ.bd Y) {i : Fin 2}
    (hi : Δ.ends e i ∈ Δ.Vs \ Y) : Δ.ends e i = innerEnd hPYc e := by
  obtain ⟨j', hj'⟩ := ends_innerEnd_compl hcl hPYc hb
  have hmem := innerEnd_compl_mem hcl hPYc hb
  by_cases hij : i = j'
  · rw [hij]; exact hj'
  · exfalso
    rw [mem_bd] at hb
    apply hb.2
    have h0 : Δ.ends e j' ∉ Y := by rw [hj']; exact (Finset.mem_sdiff.mp hmem).2
    have h1 : Δ.ends e i ∉ Y := (Finset.mem_sdiff.mp hi).2
    have hi0 : i = 0 ∨ i = 1 := by omega
    have hj0 : j' = 0 ∨ j' = 1 := by omega
    rcases hi0 with rfl | rfl <;> rcases hj0 with rfl | rfl
    · exact absurd rfl hij
    · exact ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h0⟩
    · exact ⟨fun h ↦ absurd h h0, fun h ↦ absurd h h1⟩
    · exact absurd rfl hij

/-- The ends of a new edge are outer ends of cut edges of its couple. -/
theorem ends_of_new (hcl : Δ.IsClosed) {e : ℕ} (he : e = freshE (Δ.pole (Δ.Vs \ Y)) ∨
    e = freshE (Δ.pole (Δ.Vs \ Y)) + 1) (i : Fin 2) :
    ∃ k, k ∈ Δ.bd Y ∧ newE hPYc m k = e ∧ (join hPYc m).ends e i = innerEnd hPYc k := by
  have hnew := newHalf_newPos (P := Δ.pole (Δ.Vs \ Y)) m (e, i) he
  refine ⟨bdEmb hPYc (newPos (Δ.pole (Δ.Vs \ Y)) m (e, i)), ?_, ?_, ?_⟩
  · rw [← bd_compl hcl, ← dangling_pole]; exact bdEmb_mem hPYc _
  · rw [newE_eq_newHalf_fst, hnew]
  · have := join_ends_newHalf hPYc m (newPos (Δ.pole (Δ.Vs \ Y)) m (e, i))
    rw [hnew] at this
    exact this

end Join

section Main

variable {S C : Finset ℕ} (hC : Δ.IsHamCycle S C) (hSV : S ⊆ Δ.Vs) (h2 : 2 ≤ S.card)
include hcl hY hind hC hSV h2

omit hY hSV in
/-- **A Hamilton cycle of the join from the complementary side.** -/
theorem join_hamCycle {T : Finset ℕ}
    (hT : ∀ x ∈ Δ.Vs \ Y, x ∈ T ↔ x ∈ S) (hTY : T ⊆ Δ.Vs \ Y)
    (hK₁ : (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty → couple₁ hPYc m ⊆ C)
    (hK₂ : (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty → couple₂ hPYc m ⊆ C)
    (hK : (C ∩ Δ.bd Y).Nonempty)
    (hlink : (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty → (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty →
      ∃ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPYc m, ∃ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPYc m,
        Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) a b) :
    (join hPYc m).IsHamCycle T ((C ∩ Δ.edgesIn (Δ.Vs \ Y)) ∪
      ((if (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty then {freshE (Δ.pole (Δ.Vs \ Y))} else ∅) ∪
       (if (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty then {freshE (Δ.pole (Δ.Vs \ Y)) + 1} else ∅))) := by
  classical
  set F₁ := C ∩ Δ.edgesIn (Δ.Vs \ Y) with hF₁def
  set N := (if (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty then ({freshE (Δ.pole (Δ.Vs \ Y))} : Finset ℕ) else ∅) ∪
    (if (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty then ({freshE (Δ.pole (Δ.Vs \ Y)) + 1} : Finset ℕ) else ∅)
    with hNdef
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset S)
  have hloop := hC.no_loop h2
  have hF₁P : ∀ e ∈ F₁, e ∈ (Δ.pole (Δ.Vs \ Y)).Es \ (Δ.pole (Δ.Vs \ Y)).dangling := by
    intro e he
    rw [hF₁def, Finset.mem_inter] at he
    rw [Finset.mem_sdiff, pole_Es, Finset.mem_union, dangling_pole]
    exact ⟨Or.inl he.2, fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd _) he.2 h⟩
  have hF₁J : F₁ ⊆ (join hPYc m).Es := by
    intro e he
    rw [join_Es]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hF₁P e he))
  have hNnew : ∀ e ∈ N, e = freshE (Δ.pole (Δ.Vs \ Y)) ∨ e = freshE (Δ.pole (Δ.Vs \ Y)) + 1 := by
    intro e he
    rw [hNdef, Finset.mem_union] at he
    rcases he with he | he <;> split_ifs at he
    · exact Or.inl (Finset.mem_singleton.mp he)
    · exact absurd he (Finset.notMem_empty _)
    · exact Or.inr (Finset.mem_singleton.mp he)
    · exact absurd he (Finset.notMem_empty _)
  have hNJ : N ⊆ (join hPYc m).Es := by
    intro e he
    rw [join_Es]
    rcases hNnew e he with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hF₁N : Disjoint F₁ N := by
    rw [Finset.disjoint_left]
    intro e he he'
    have := (Finset.mem_sdiff.mp (hF₁P e he)).1
    rcases hNnew e he' with rfl | rfl
    · exact freshE_notMem this
    · exact freshE_succ_notMem this
  -- membership of new edges in `N`
  have hnewE_mem : ∀ k ∈ C ∩ Δ.bd Y, newE hPYc m k ∈ N := by
    intro k hk
    have hd : k ∈ (Δ.pole (Δ.Vs \ Y)).dangling := mem_dangling_compl hcl (Finset.mem_inter.mp hk).2
    rw [hNdef, Finset.mem_union]
    unfold newE
    by_cases h : k ∈ couple₁ hPYc m
    · left; rw [if_pos h, if_pos ⟨k, Finset.mem_inter.mpr ⟨hk, h⟩⟩]; exact Finset.mem_singleton_self _
    · right
      rw [if_neg h, if_pos ⟨k, Finset.mem_inter.mpr ⟨hk, (mem_couple₂_iff hPYc m hd).mpr h⟩⟩]
      exact Finset.mem_singleton_self _
  -- a cut edge whose new edge is in `N` lies in `C`
  have hmem_of_newE : ∀ k ∈ Δ.bd Y, newE hPYc m k ∈ N → k ∈ C := by
    intro k hk hN
    have hd : k ∈ (Δ.pole (Δ.Vs \ Y)).dangling := mem_dangling_compl hcl hk
    rw [hNdef, Finset.mem_union] at hN
    unfold newE at hN
    by_cases h : k ∈ couple₁ hPYc m
    · rw [if_pos h] at hN
      rcases hN with hN | hN <;> split_ifs at hN with hne
      · exact hK₁ hne h
      · exact absurd hN (Finset.notMem_empty _)
      · exfalso; have := Finset.mem_singleton.mp hN; omega
      · exact absurd hN (Finset.notMem_empty _)
    · rw [if_neg h] at hN
      have h₂ : k ∈ couple₂ hPYc m := (mem_couple₂_iff hPYc m hd).mpr h
      rcases hN with hN | hN <;> split_ifs at hN with hne
      · exfalso; have := Finset.mem_singleton.mp hN; omega
      · exact absurd hN (Finset.notMem_empty _)
      · exact hK₂ hne h₂
      · exact absurd hN (Finset.notMem_empty _)
  -- new edges of `N` are new edges of cut edges of `C`
  have hN_newE : ∀ e ∈ N, ∀ i, ∃ k ∈ C ∩ Δ.bd Y, newE hPYc m k = e ∧
      (join hPYc m).ends e i = innerEnd hPYc k := by
    intro e he i
    obtain ⟨k, hk, hke, hend⟩ := ends_of_new hPYc m hcl (hNnew e he) i
    exact ⟨k, Finset.mem_inter.mpr ⟨hmem_of_newE k hk (hke ▸ he), hk⟩, hke, hend⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the edges lie inside `T`
    intro e he
    rw [Finset.mem_union] at he
    rw [mem_edgesIn]
    rcases he with he | he
    · refine ⟨hF₁J he, fun i ↦ ?_⟩
      rw [join_ends_old hPYc m (Finset.mem_sdiff.mp (hF₁P e he)).1]
      have heC := (Finset.mem_inter.mp he).1
      have hin := (mem_edgesIn.mp (Finset.mem_inter.mp he).2).2 i
      exact (hT _ hin).mpr ((mem_edgesIn.mp (hC.subset heC)).2 i)
    · refine ⟨hNJ he, fun i ↦ ?_⟩
      obtain ⟨k, hk, -, hend⟩ := hN_newE e he i
      rw [hend]
      have hkY := (Finset.mem_inter.mp hk).2
      have hkC := (Finset.mem_inter.mp hk).1
      obtain ⟨j, hj⟩ := ends_innerEnd_compl hcl hPYc hkY
      rw [← hj]
      exact (hT _ (hj ▸ innerEnd_compl_mem hcl hPYc hkY)).mpr ((mem_edgesIn.mp (hC.subset hkC)).2 j)
  · -- degrees
    intro t ht
    have htV := hTY ht
    have htS := (hT t htV).mp ht
    rw [degIn_eq_card, halfEdgesIn_union, Finset.card_union_of_disjoint
      (halfEdgesIn_disjoint_of_disjoint hF₁N t)]
    -- old half-edges: those of `C` at `t` that are not cut edges
    have hold : (join hPYc m).halfEdgesIn F₁ t = (Δ.halfEdgesIn C t).filter fun x ↦ x.1 ∉ Δ.bd Y := by
      ext ⟨e, i⟩
      rw [mem_halfEdgesIn, Finset.mem_filter, mem_halfEdgesIn]
      constructor
      · rintro ⟨he, hend⟩
        rw [join_ends_old hPYc m (Finset.mem_sdiff.mp (hF₁P e he)).1] at hend
        refine ⟨⟨(Finset.mem_inter.mp he).1, hend⟩, ?_⟩
        exact fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd _) (Finset.mem_inter.mp he).2
          (by rw [bd_compl hcl]; exact h)
      · rintro ⟨⟨he, hend⟩, hb⟩
        have heF : e ∈ F₁ := by
          rw [hF₁def, Finset.mem_inter]
          refine ⟨he, ?_⟩
          rcases mem_edgesIn_or_bd (hCE he) (i := i) (hend ▸ htV) with h | h
          · exact h
          · exact absurd (by rw [bd_compl hcl] at h; exact h) hb
        refine ⟨heF, ?_⟩
        rw [join_ends_old hPYc m (Finset.mem_sdiff.mp (hF₁P e heF)).1]
        exact hend
    -- new half-edges: the positions attached at `t` whose new edge is in `N`
    have hnew : (join hPYc m).halfEdgesIn N t =
        ((Finset.univ.filter fun k : Fin 4 ↦ innerEnd hPYc (bdEmb hPYc k) = t).filter
          fun k ↦ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m k).1 ∈ N).image (newHalf (P := Δ.pole (Δ.Vs \ Y)) m) := by
      have hsub : N ⊆ {freshE (Δ.pole (Δ.Vs \ Y)), freshE (Δ.pole (Δ.Vs \ Y)) + 1} := by
        intro e he
        rcases hNnew e he with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [halfEdgesIn_filter hsub, join_halfEdges_new, Finset.filter_image]
    have hcut_split := Finset.card_filter_add_card_filter_not (s := Δ.halfEdgesIn C t)
      (fun x ↦ x.1 ∈ Δ.bd Y)
    rw [← degIn_eq_card, hC.deg t htS] at hcut_split
    rw [hold, hnew, Finset.card_image_of_injective _ (newHalf_injective m)]
    -- the cut half-edges at `t` number at most one, and so do the attached positions
    have hcut_le : ((Δ.halfEdgesIn C t).filter fun x ↦ x.1 ∈ Δ.bd Y).card ≤ 1 := by
      rw [Finset.card_le_one]
      rintro ⟨e, i⟩ he ⟨f, j⟩ hf
      rw [Finset.mem_filter, mem_halfEdgesIn] at he hf
      dsimp only at he hf
      have hef : e = f := hind.eq_of_ends he.2 hf.2 (he.1.2.trans hf.1.2.symm)
      subst hef
      rw [idx_eq_of_ends_eq_single (hloop e he.1.1) (he.1.2.trans hf.1.2.symm)]
    have hpos_le : ((Finset.univ.filter fun k : Fin 4 ↦ innerEnd hPYc (bdEmb hPYc k) = t).filter
        fun k ↦ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m k).1 ∈ N).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro k hk k' hk'
      rw [Finset.mem_filter, Finset.mem_filter] at hk hk'
      have hb : ∀ k : Fin 4, bdEmb hPYc k ∈ Δ.bd Y := fun k ↦ by
        rw [← bd_compl hcl, ← dangling_pole]; exact bdEmb_mem hPYc k
      exact bdEmb_injective hPYc (innerEnd_compl_inj hcl hPYc hind (hb k) (hb k')
        (hk.1.2.trans hk'.1.2.symm))
    -- the two are nonempty together
    have hiff : ((Δ.halfEdgesIn C t).filter fun x ↦ x.1 ∈ Δ.bd Y).Nonempty ↔
        ((Finset.univ.filter fun k : Fin 4 ↦ innerEnd hPYc (bdEmb hPYc k) = t).filter
          fun k ↦ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m k).1 ∈ N).Nonempty := by
      constructor
      · rintro ⟨⟨e, i⟩, he⟩
        rw [Finset.mem_filter, mem_halfEdgesIn] at he
        dsimp only at he
        obtain ⟨p, hp⟩ := exists_bdEmb_eq hPYc (mem_dangling_compl hcl he.2)
        refine ⟨p, ?_⟩
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [hp]
          have := ends_eq_innerEnd_compl hPYc hcl he.2 (i := i) (he.1.2 ▸ htV)
          exact this.symm.trans he.1.2
        · rw [← newE_eq_newHalf_fst, hp]
          exact hnewE_mem e (Finset.mem_inter.mpr ⟨he.1.1, he.2⟩)
      · rintro ⟨p, hp⟩
        rw [Finset.mem_filter, Finset.mem_filter] at hp
        have hpY : bdEmb hPYc p ∈ Δ.bd Y := by
          rw [← bd_compl hcl, ← dangling_pole]; exact bdEmb_mem hPYc p
        have hpC : bdEmb hPYc p ∈ C := by
          apply hmem_of_newE _ hpY
          rw [newE_eq_newHalf_fst]; exact hp.2
        obtain ⟨j, hj⟩ := ends_innerEnd_compl hcl hPYc hpY
        refine ⟨(bdEmb hPYc p, j), ?_⟩
        rw [Finset.mem_filter, mem_halfEdgesIn]
        exact ⟨⟨hpC, hj.trans hp.1.2⟩, hpY⟩
    by_cases hne : ((Δ.halfEdgesIn C t).filter fun x ↦ x.1 ∈ Δ.bd Y).Nonempty
    · have h1 := hiff.mp hne
      have := Finset.card_pos.mpr hne
      have := Finset.card_pos.mpr h1
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h1 : ((Finset.univ.filter fun k : Fin 4 ↦ innerEnd hPYc (bdEmb hPYc k) = t).filter
          fun k ↦ (newHalf (P := Δ.pole (Δ.Vs \ Y)) m k).1 ∈ N) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        intro h; exact (Finset.not_nonempty_iff_eq_empty.mpr hne) (hiff.mpr h)
      rw [hne, Finset.card_empty] at hcut_split
      rw [h1, Finset.card_empty]
      omega
  · -- connectivity: translate links on the complementary side
    have hnewE_C : ∀ k ∈ C ∩ Δ.bd Y, newE hPYc m k ∈ F₁ ∪ N :=
      fun k hk ↦ Finset.mem_union_right _ (hnewE_mem k hk)
    -- the translation of an edge of the complementary side part
    let τ : ℕ → ℕ := fun e ↦ if e ∈ Δ.bd Y then newE hPYc m e else e
    have hτ_mem : ∀ e ∈ Δ.sidePart C (Δ.Vs \ Y), τ e ∈ F₁ ∪ N := by
      intro e he
      rw [mem_sidePart_iff] at he
      by_cases hb : e ∈ Δ.bd Y
      · simp only [τ, hb, if_true]
        exact hnewE_C e (Finset.mem_inter.mpr ⟨he.1, hb⟩)
      · simp only [τ, hb, if_false]
        apply Finset.mem_union_left
        rw [hF₁def, Finset.mem_inter]
        refine ⟨he.1, ?_⟩
        rcases he.2 with h | h
        · exact h
        · exfalso; rw [bd_compl hcl] at h; exact hb h
    -- an end in `Vs \ Y` of an edge of the side part is an end of its translation
    have hτ_ends : ∀ e ∈ Δ.sidePart C (Δ.Vs \ Y), ∀ i, Δ.ends e i ∈ Δ.Vs \ Y →
        ∃ j, (join hPYc m).ends (τ e) j = Δ.ends e i := by
      intro e he i hi
      by_cases hb : e ∈ Δ.bd Y
      · simp only [τ, hb, if_true]
        obtain ⟨j, hj⟩ := newE_ends hPYc m hcl hb
        exact ⟨j, hj.trans (ends_eq_innerEnd_compl hPYc hcl hb hi).symm⟩
      · simp only [τ, hb, if_false]
        rw [mem_sidePart_iff] at he
        have heP : e ∈ (Δ.pole (Δ.Vs \ Y)).Es := by
          rw [pole_Es, Finset.mem_union]
          rcases he.2 with h | h
          · exact Or.inl h
          · rw [bd_compl hcl] at h; exact absurd h hb
        exact ⟨i, join_ends_old hPYc m heP i⟩
    have htrans : ∀ x y, Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) x y →
        Relation.ReflTransGen ((join hPYc m).AdjIn (F₁ ∪ N)) (τ x) (τ y) := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hlast ih =>
        obtain ⟨hb, hc, i, j, hij⟩ := hlast
        by_cases hout : Δ.ends b i ∈ Δ.Vs \ Y
        · obtain ⟨i', hi'⟩ := hτ_ends b hb i hout
          obtain ⟨j', hj'⟩ := hτ_ends c hc j (by rw [← hij]; exact hout)
          exact ih.tail ⟨hτ_mem b hb, hτ_mem c hc, i', j', by rw [hi', hj', hij]⟩
        · have hbV : Δ.ends b i ∈ Δ.Vs := hcl b (hCE (sidePart_subset hb)) i
          have hinY : Δ.ends b i ∈ Y := by
            by_contra h; exact hout (Finset.mem_sdiff.mpr ⟨hbV, h⟩)
          have hbbd : b ∈ Δ.bd Y := by
            rw [mem_sidePart_iff] at hb
            rcases hb.2 with h | h
            · exact absurd hinY (Finset.mem_sdiff.mp ((mem_edgesIn.mp h).2 i)).2
            · rwa [bd_compl hcl] at h
          have hcbd : c ∈ Δ.bd Y := by
            rw [mem_sidePart_iff] at hc
            rcases hc.2 with h | h
            · exact absurd (by rw [← hij]; exact hinY) (Finset.mem_sdiff.mp ((mem_edgesIn.mp h).2 j)).2
            · rwa [bd_compl hcl] at h
          have := hind.eq_of_ends hbbd hcbd hij
          subst this
          exact ih
    -- every edge reaches a new edge
    obtain ⟨k₀, hk₀⟩ := hK
    have hreach : ∀ e ∈ F₁ ∪ N, ∃ n ∈ N, Relation.ReflTransGen ((join hPYc m).AdjIn (F₁ ∪ N)) e n := by
      intro e he
      rw [Finset.mem_union] at he
      rcases he with he | he
      · have heS : e ∈ Δ.sidePart C (Δ.Vs \ Y) := by
          rw [mem_sidePart_iff]
          exact ⟨(Finset.mem_inter.mp he).1, Or.inl (Finset.mem_inter.mp he).2⟩
        obtain ⟨b, hb, hbS, hpath⟩ := linked_to_cut hCE heS (a₀ := k₀)
          (by rw [bd_compl hcl]; exact (Finset.mem_inter.mp hk₀).2)
          (hC.connected e (Finset.mem_inter.mp he).1 k₀ (Finset.mem_inter.mp hk₀).1)
        rw [bd_compl hcl] at hb
        have hτe : τ e = e := by
          show (if e ∈ Δ.bd Y then newE hPYc m e else e) = e
          rw [if_neg (fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd _)
            (Finset.mem_inter.mp he).2 (by rw [bd_compl hcl]; exact h))]
        have hτb : τ b = newE hPYc m b := by
          show (if b ∈ Δ.bd Y then newE hPYc m b else b) = newE hPYc m b
          rw [if_pos hb]
        refine ⟨newE hPYc m b, hnewE_mem b (Finset.mem_inter.mpr ⟨sidePart_subset hbS, hb⟩), ?_⟩
        have := htrans e b hpath
        rwa [hτe, hτb] at this
      · exact ⟨e, he, Relation.ReflTransGen.refl⟩
    -- the two new edges are linked when both present
    have hfresh₁ : freshE (Δ.pole (Δ.Vs \ Y)) ∈ N → (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty := by
      intro h
      rw [hNdef, Finset.mem_union] at h
      rcases h with h | h <;> split_ifs at h with hc
      · exact hc
      · exact absurd h (Finset.notMem_empty _)
      · exfalso; have := Finset.mem_singleton.mp h; omega
      · exact absurd h (Finset.notMem_empty _)
    have hfresh₂ : freshE (Δ.pole (Δ.Vs \ Y)) + 1 ∈ N → (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty := by
      intro h
      rw [hNdef, Finset.mem_union] at h
      rcases h with h | h <;> split_ifs at h with hc
      · exfalso; have := Finset.mem_singleton.mp h; omega
      · exact absurd h (Finset.notMem_empty _)
      · exact hc
      · exact absurd h (Finset.notMem_empty _)
    have hlinkN : freshE (Δ.pole (Δ.Vs \ Y)) ∈ N → freshE (Δ.pole (Δ.Vs \ Y)) + 1 ∈ N →
        Relation.ReflTransGen ((join hPYc m).AdjIn (F₁ ∪ N)) (freshE (Δ.pole (Δ.Vs \ Y)))
          (freshE (Δ.pole (Δ.Vs \ Y)) + 1) := by
      intro hn hn'
      obtain ⟨a, ha, b, hb, hab⟩ := hlink (hfresh₁ hn) (hfresh₂ hn')
      have haK := Finset.mem_inter.mp ha
      have hbK := Finset.mem_inter.mp hb
      have hτa : τ a = freshE (Δ.pole (Δ.Vs \ Y)) := by
        show (if a ∈ Δ.bd Y then newE hPYc m a else a) = _
        rw [if_pos (Finset.mem_inter.mp haK.1).2]
        unfold newE
        rw [if_pos haK.2]
      have hτb : τ b = freshE (Δ.pole (Δ.Vs \ Y)) + 1 := by
        show (if b ∈ Δ.bd Y then newE hPYc m b else b) = _
        rw [if_pos (Finset.mem_inter.mp hbK.1).2]
        unfold newE
        rw [if_neg ((mem_couple₂_iff hPYc m
          (mem_dangling_compl hcl (Finset.mem_inter.mp hbK.1).2)).mp hbK.2)]
      have := htrans a b hab
      rwa [hτa, hτb] at this
    have hNN : ∀ n ∈ N, ∀ n' ∈ N, Relation.ReflTransGen ((join hPYc m).AdjIn (F₁ ∪ N)) n n' := by
      intro n hn n' hn'
      rcases hNnew n hn with rfl | rfl <;> rcases hNnew n' hn' with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact hlinkN hn hn'
      · exact reflTransGen_adjIn_symm (hlinkN hn' hn)
      · exact Relation.ReflTransGen.refl
    intro e he f hf
    obtain ⟨n, hn, hen⟩ := hreach e he
    obtain ⟨n', hn', hfn'⟩ := hreach f hf
    exact hen.trans ((hNN n hn n' hn').trans (reflTransGen_adjIn_symm hfn'))

end Main

end FinGraph
end GraphPuzzles
