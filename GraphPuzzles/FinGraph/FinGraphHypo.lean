import GraphPuzzles.FinGraph.FinGraphPaths
import GraphPuzzles.Factorization.Bicritical.FactorParity

/-!
# Hamilton cycles and colourings

* `IsHamCycle.card_eq`, `IsHamCycle.no_loop`: basic facts.
* `colourable_of_isHamCycle`: a Hamiltonian closed cubic graph is three-edge-colourable, hence
  a snark is not Hamiltonian.
* `IsHypohamiltonian.isBicritical`: hypohamiltonian cubic graphs are bicritical (the Hamilton
  cycle through the deleted vertex minus the second vertex is a path, coloured alternately).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section Basic

/-- The colours of the two classes of a two-edge-colouring. -/
def twoColor (x : Fin 2) : Color := if x = 0 then (1, 0) else (0, 1)

theorem twoColor_ne_zero (x : Fin 2) : twoColor x ≠ 0 := by
  revert x; decide

theorem twoColor_inj {x y : Fin 2} (h : twoColor x = twoColor y) : x = y := by
  revert x y; decide

theorem twoColor_ne_third (x : Fin 2) : twoColor x ≠ (1, 1) := by
  revert x; decide

theorem twoColor_sub_ne (x : Fin 2) : twoColor (1 - x) ≠ twoColor x := by
  revert x; decide

theorem IsHamCycle.card_eq {S C : Finset ℕ} (h : Γ.IsHamCycle S C) : C.card = S.card := by
  have h1 := sum_degIn_eq (Γ := Γ) C S
  rw [Finset.sum_congr rfl (fun v hv ↦ h.deg v hv), Finset.sum_const, smul_eq_mul,
    Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_edgesIn (h.subset he)), Finset.sum_const,
    smul_eq_mul] at h1
  omega

/-- The two half-edges of a set of degree two at a vertex. -/
theorem halfEdges_two {C : Finset ℕ} {v : ℕ} (h : Γ.degIn C v = 2) :
    ∃ e₁ i₁ e₂ i₂, (e₁, i₁) ≠ (e₂, i₂) ∧ Γ.halfEdgesIn C v = {(e₁, i₁), (e₂, i₂)} := by
  rw [degIn_eq_card, Finset.card_eq_two] at h
  obtain ⟨⟨e₁, i₁⟩, ⟨e₂, i₂⟩, hne, hset⟩ := h
  exact ⟨e₁, i₁, e₂, i₂, hne, hset⟩

/-- A Hamilton cycle of a set with at least two vertices has no loops. -/
theorem IsHamCycle.no_loop {S C : Finset ℕ} (h : Γ.IsHamCycle S C) (h2 : 2 ≤ S.card) :
    ∀ e ∈ C, Γ.ends e 0 ≠ Γ.ends e 1 := by
  intro e he hl
  have hv : Γ.ends e 0 ∈ S := (mem_edgesIn.mp (h.subset he)).2 0
  have hset : Γ.halfEdgesIn C (Γ.ends e 0) = {(e, 0), (e, 1)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_halfEdgesIn.mpr ⟨he, rfl⟩
      · exact mem_halfEdgesIn.mpr ⟨he, hl.symm⟩
    · rw [Finset.card_pair (by simp), ← degIn_eq_card, h.deg _ hv]
  -- every edge of `C` is `e`
  have hall : ∀ f ∈ C, f = e := by
    intro f hf
    have hwalk := h.connected e he f hf
    induction hwalk with
    | refl => rfl
    | @tail b c _ hlast ih =>
      have hb : b = e := ih hlast.mem_left
      subst hb
      obtain ⟨-, hcC, k, l, hkl⟩ := hlast
      have hk : Γ.ends b k = Γ.ends b 0 := by
        have hk0 : k = 0 ∨ k = 1 := by omega
        rcases hk0 with rfl | rfl
        · rfl
        · exact hl.symm
      have : (c, l) ∈ Γ.halfEdgesIn C (Γ.ends b 0) := mem_halfEdgesIn.mpr ⟨hcC, hkl.symm.trans hk⟩
      rw [hset, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.mk.injEq] at this
      rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact h1
  -- another vertex of `S` has degree two, but carries no end of `e`
  obtain ⟨w, hwS, hw⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) (Γ.ends e 0)
  have hpos : 0 < Γ.degIn C w := by rw [h.deg w hwS]; omega
  rw [degIn_eq_card, Finset.card_pos] at hpos
  obtain ⟨⟨f, j⟩, hfj⟩ := hpos
  rw [mem_halfEdgesIn] at hfj
  rw [hall f hfj.1] at hfj
  have hj0 : j = 0 ∨ j = 1 := by omega
  rcases hj0 with rfl | rfl
  · exact hw hfj.2.symm
  · exact hw (hl.trans hfj.2).symm

/-- The half-edge of a cubic graph at `v` outside an edge set of degree two there. -/
theorem third_halfEdge (hcub : Γ.IsCubic) {v : ℕ} (hv : v ∈ Γ.Vs) {C : Finset ℕ} (hC : C ⊆ Γ.Es)
    (hdeg : Γ.degIn C v = 2) :
    ∃ f j, f ∈ Γ.Es ∧ f ∉ C ∧ Γ.ends f j = v ∧
      ∀ g l, g ∈ Γ.Es → g ∉ C → Γ.ends g l = v → (g, l) = (f, j) := by
  have hsub : Γ.halfEdgesIn C v ⊆ Γ.halfEdgesIn Γ.Es v := halfEdgesIn_mono hC v
  have hcard : (Γ.halfEdgesIn Γ.Es v \ Γ.halfEdgesIn C v).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, ← degIn_eq_card, ← degIn_eq_card, hdeg]
    have := hcub v hv
    unfold deg at this
    omega
  obtain ⟨⟨f, j⟩, hfj⟩ := Finset.card_eq_one.mp hcard
  have hmem : (f, j) ∈ Γ.halfEdgesIn Γ.Es v \ Γ.halfEdgesIn C v := by
    rw [hfj]; exact Finset.mem_singleton_self _
  rw [Finset.mem_sdiff, mem_halfEdgesIn, mem_halfEdgesIn] at hmem
  refine ⟨f, j, hmem.1.1, fun h ↦ hmem.2 ⟨h, hmem.1.2⟩, hmem.1.2, ?_⟩
  intro g l hg hgC hl
  have : (g, l) ∈ Γ.halfEdgesIn Γ.Es v \ Γ.halfEdgesIn C v := by
    rw [Finset.mem_sdiff, mem_halfEdgesIn, mem_halfEdgesIn]
    exact ⟨⟨hg, hl⟩, fun h ↦ hgC h.1⟩
  rw [hfj, Finset.mem_singleton] at this
  exact this

theorem bd_Vs_eq_empty (hcl : Γ.IsClosed) : Γ.bd Γ.Vs = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_bd] at he
  exact he.2 ⟨fun _ ↦ hcl e he.1 1, fun _ ↦ hcl e he.1 0⟩

theorem even_card_Vs (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) : Even Γ.Vs.card := by
  have := three_mul_card_eq hcub (subset_refl Γ.Vs)
  rw [bd_Vs_eq_empty hcl, Finset.card_empty] at this
  exact Nat.even_iff.mpr (by omega)

end Basic

section Hamiltonian

/-- **An even cycle has a proper two-edge-colouring.** -/
theorem IsHamCycle.exists_two_colouring_even {S C : Finset ℕ} (hC : Γ.IsHamCycle S C)
    (h2 : 2 ≤ S.card) (heven : Even S.card) :
    ∃ c : ℕ → Fin 2, ∀ f ∈ C, ∀ g ∈ C, f ≠ g → ∀ v ∈ S, ∀ i j,
      Γ.ends f i = v → Γ.ends g j = v → c f ≠ c g := by
  classical
  have hloop := hC.no_loop h2
  have hcard := hC.card_eq
  obtain ⟨e, he⟩ : C.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  have hab : Γ.ends e 0 ≠ Γ.ends e 1 := hloop e he
  have haV : Γ.ends e 0 ∈ S := (mem_edgesIn.mp (hC.subset he)).2 0
  have hbV : Γ.ends e 1 ∈ S := (mem_edgesIn.mp (hC.subset he)).2 1
  have hconnP := isConnected_erase_of_cycle hC.subset hC.deg hC.connected hloop he
  have hPE : C.erase e ⊆ Γ.edgesIn S := (Finset.erase_subset e C).trans hC.subset
  have hdegP : ∀ v ∈ S, Γ.degIn (C.erase e) v ≤ 2 :=
    fun v hv ↦ (degIn_mono (Finset.erase_subset e C) v).trans (hC.deg v hv).le
  have hdega : Γ.degIn (C.erase e) (Γ.ends e 0) = 1 := by
    have := degIn_erase_of_ends he hab 0
    rw [hC.deg _ haV] at this; omega
  have hdegb : Γ.degIn (C.erase e) (Γ.ends e 1) = 1 := by
    have := degIn_erase_of_ends he hab 1
    rw [hC.deg _ hbV] at this; omega
  obtain ⟨c₂, hprop, hend⟩ := exists_two_colouring (C.erase e).card (C.erase e) rfl hPE hdegP
    hconnP (fun f hf ↦ hloop f (Finset.erase_subset e C hf)) _ _ haV hbV hab hdega hdegb
  have hodd : Odd (C.erase e).card := by
    rw [Finset.card_erase_of_mem he, hcard]
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp heven; omega)
  obtain ⟨⟨g, k⟩, hgk⟩ : (Γ.halfEdgesIn (C.erase e) (Γ.ends e 0)).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdega]; omega
  rw [mem_halfEdgesIn] at hgk
  have hendcol : ∀ (f : ℕ) (j : Fin 2), f ∈ C.erase e →
      (Γ.ends f j = Γ.ends e 0 ∨ Γ.ends f j = Γ.ends e 1) → c₂ f = c₂ g := by
    intro f j hf hj
    rcases hj with hj | hj
    · exact ((eq_of_degIn_eq_one hdega hf hgk.1 hj hgk.2).1 ▸ rfl)
    · exact ((hend g hgk.1 f hf ⟨k, hgk.2⟩ ⟨j, hj⟩).mpr hodd).symm
  have hflip : ∀ x : Fin 2, 1 - x ≠ x := by decide
  have hends : ∀ (f : ℕ) (i : Fin 2) (v : ℕ), f = e → Γ.ends f i = v →
      Γ.ends e 0 = v ∨ Γ.ends e 1 = v := by
    intro f i v hfe hi
    subst hfe
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  refine ⟨fun f ↦ if f ∈ C.erase e then c₂ f else 1 - c₂ g, ?_⟩
  intro f hf f' hf' hff v hv i j hi hj
  show (if f ∈ C.erase e then c₂ f else 1 - c₂ g) ≠ (if f' ∈ C.erase e then c₂ f' else 1 - c₂ g)
  by_cases hfe : f = e <;> by_cases hfe' : f' = e
  · exact absurd (hfe.trans hfe'.symm) hff
  · have hf'P : f' ∈ C.erase e := Finset.mem_erase.mpr ⟨hfe', hf'⟩
    rw [if_neg (by rw [hfe]; exact Finset.notMem_erase e C), if_pos hf'P]
    rw [hendcol f' j hf'P (by
      rcases hends f i v hfe hi with h | h
      · exact Or.inl (hj.trans h.symm)
      · exact Or.inr (hj.trans h.symm))]
    exact hflip _
  · have hfP : f ∈ C.erase e := Finset.mem_erase.mpr ⟨hfe, hf⟩
    rw [if_pos hfP, if_neg (by rw [hfe']; exact Finset.notMem_erase e C)]
    rw [hendcol f i hfP (by
      rcases hends f' j v hfe' hj with h | h
      · exact Or.inl (hi.trans h.symm)
      · exact Or.inr (hi.trans h.symm))]
    exact (hflip _).symm
  · have hfP : f ∈ C.erase e := Finset.mem_erase.mpr ⟨hfe, hf⟩
    have hf'P : f' ∈ C.erase e := Finset.mem_erase.mpr ⟨hfe', hf'⟩
    rw [if_pos hfP, if_pos hf'P]
    exact hprop f hfP f' hf'P hff ⟨hfP, hf'P, i, j, hi.trans hj.symm⟩

/-- **A Hamiltonian closed cubic graph is three-edge-colourable.** -/
theorem colourable_of_isHamCycle (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (h2 : 2 ≤ Γ.Vs.card)
    {C : Finset ℕ} (hC : Γ.IsHamCycle Γ.Vs C) : Γ.Colourable := by
  classical
  have hloop := hC.no_loop h2
  have hcard := hC.card_eq
  have heven := even_card_Vs hcl hcub
  have hCE : C ⊆ Γ.Es := hC.subset.trans (edgesIn_subset _)
  obtain ⟨e, he⟩ : C.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  have hab : Γ.ends e 0 ≠ Γ.ends e 1 := hloop e he
  have haV : Γ.ends e 0 ∈ Γ.Vs := hcl e (hCE he) 0
  have hbV : Γ.ends e 1 ∈ Γ.Vs := hcl e (hCE he) 1
  have hconnP := isConnected_erase_of_cycle hC.subset hC.deg hC.connected hloop he
  have hPE : C.erase e ⊆ Γ.edgesIn Γ.Vs := (Finset.erase_subset e C).trans hC.subset
  have hdegP : ∀ v ∈ Γ.Vs, Γ.degIn (C.erase e) v ≤ 2 :=
    fun v hv ↦ (degIn_mono (Finset.erase_subset e C) v).trans (hC.deg v hv).le
  have hdega : Γ.degIn (C.erase e) (Γ.ends e 0) = 1 := by
    have := degIn_erase_of_ends he hab 0
    rw [hC.deg _ haV] at this; omega
  have hdegb : Γ.degIn (C.erase e) (Γ.ends e 1) = 1 := by
    have := degIn_erase_of_ends he hab 1
    rw [hC.deg _ hbV] at this; omega
  obtain ⟨c₂, hprop, hend⟩ := exists_two_colouring (C.erase e).card (C.erase e) rfl hPE hdegP
    hconnP (fun f hf ↦ hloop f (Finset.erase_subset e C hf)) _ _ haV hbV hab hdega hdegb
  have hodd : Odd (C.erase e).card := by
    rw [Finset.card_erase_of_mem he, hcard]
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp heven; omega)
  -- the edge of the path at the first end of `e`
  obtain ⟨⟨g, k⟩, hgk⟩ : (Γ.halfEdgesIn (C.erase e) (Γ.ends e 0)).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdega]; omega
  rw [mem_halfEdgesIn] at hgk
  refine ⟨fun f ↦ if f ∈ C.erase e then twoColor (c₂ f) else
    if f = e then twoColor (1 - c₂ g) else (1, 1), ?_, ?_⟩
  · intro f _
    dsimp only
    split_ifs
    · exact twoColor_ne_zero _
    · exact twoColor_ne_zero _
    · decide
  · intro v hv h₁ h₁m h₂ h₂m heq
    dsimp only at heq
    rw [mem_halfEdgesIn] at h₁m h₂m
    obtain ⟨f, j⟩ := h₁
    obtain ⟨f', j'⟩ := h₂
    simp only at h₁m h₂m heq
    obtain ⟨t, jt, htE, htC, hjt, huniq⟩ := third_halfEdge hcub hv hCE (hC.deg v hv)
    -- the classification of a half-edge at `v`
    have classify : ∀ (f : ℕ) (j : Fin 2), f ∈ Γ.Es → Γ.ends f j = v →
        f ∈ C.erase e ∨ f = e ∨ (f, j) = (t, jt) := by
      intro f j hf hj
      by_cases hfC : f ∈ C
      · by_cases hfe : f = e
        · exact Or.inr (Or.inl hfe)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hfe, hfC⟩)
      · exact Or.inr (Or.inr (huniq f j hf hfC hj))
    -- two path edges at `v` are distinct as half-edges only if distinct as edges
    have hpath : ∀ (f : ℕ) (j : Fin 2) (f' : ℕ) (j' : Fin 2), f ∈ C.erase e → f' ∈ C.erase e →
        Γ.ends f j = v → Γ.ends f' j' = v → twoColor (c₂ f) = twoColor (c₂ f') → (f, j) = (f', j') := by
      intro f j f' j' hf hf' hj hj' hcol
      by_cases hff : f = f'
      · subst hff
        rw [idx_eq_of_ends_eq_single (hloop f (Finset.erase_subset e C hf)) (hj.trans hj'.symm)]
      · exfalso
        exact hprop f hf f' hf' hff ⟨hf, hf', j, j', hj.trans hj'.symm⟩ (twoColor_inj hcol)
    -- the path edge at an end of `e` has the colour of `g`
    have hendcol : ∀ (f : ℕ) (j : Fin 2), f ∈ C.erase e → (Γ.ends f j = Γ.ends e 0 ∨ Γ.ends f j = Γ.ends e 1) →
        c₂ f = c₂ g := by
      intro f j hf hj
      rcases hj with hj | hj
      · exact ((eq_of_degIn_eq_one hdega hf hgk.1 hj hgk.2).1 ▸ rfl)
      · exact ((hend g hgk.1 f hf ⟨k, hgk.2⟩ ⟨j, hj⟩).mpr hodd).symm
    rcases classify f j h₁m.1 h₁m.2 with hf | hf | hf <;>
      rcases classify f' j' h₂m.1 h₂m.2 with hf' | hf' | hf'
    · rw [if_pos hf, if_pos hf'] at heq
      exact hpath f j f' j' hf hf' h₁m.2 h₂m.2 heq
    · exfalso
      subst hf'
      rw [if_pos hf, if_neg (Finset.notMem_erase _ _), if_pos rfl] at heq
      have hj' : Γ.ends f j = Γ.ends f' 0 ∨ Γ.ends f j = Γ.ends f' 1 := by
        have : j' = 0 ∨ j' = 1 := by omega
        rcases this with rfl | rfl
        · exact Or.inl (h₁m.2.trans h₂m.2.symm)
        · exact Or.inr (h₁m.2.trans h₂m.2.symm)
      rw [hendcol f j hf hj'] at heq
      exact twoColor_sub_ne _ heq.symm
    · exfalso
      rw [Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_pos hf, if_neg (fun h ↦ htC (Finset.mem_of_mem_erase h)),
        if_neg (fun h ↦ htC (by rw [h]; exact he))] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      subst hf
      rw [if_pos hf', if_neg (Finset.notMem_erase _ _), if_pos rfl] at heq
      have hj : Γ.ends f' j' = Γ.ends f 0 ∨ Γ.ends f' j' = Γ.ends f 1 := by
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl
        · exact Or.inl (h₂m.2.trans h₁m.2.symm)
        · exact Or.inr (h₂m.2.trans h₁m.2.symm)
      rw [hendcol f' j' hf' hj] at heq
      exact twoColor_sub_ne _ heq
    · subst hf; subst hf'
      rw [idx_eq_of_ends_eq_single hab (h₁m.2.trans h₂m.2.symm)]
    · exfalso
      subst hf
      rw [Prod.mk.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_neg (Finset.notMem_erase _ _), if_pos rfl,
        if_neg (fun h ↦ htC (Finset.mem_of_mem_erase h)), if_neg (fun h ↦ htC (by rw [h]; exact he))] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      rw [Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [if_neg (fun h ↦ htC (Finset.mem_of_mem_erase h)), if_neg (fun h ↦ htC (by rw [h]; exact he)),
        if_pos hf'] at heq
      exact twoColor_ne_third _ heq.symm
    · exfalso
      rw [Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      subst hf'
      rw [if_neg (fun h ↦ htC (Finset.mem_of_mem_erase h)), if_neg (fun h ↦ htC (by rw [h]; exact he)),
        if_neg (Finset.notMem_erase _ _), if_pos rfl] at heq
      exact twoColor_ne_third _ heq.symm
    · rw [hf, hf']

/-- A snark is not Hamiltonian. -/
theorem not_isHamiltonian_of_not_colourable (hcl : Γ.IsClosed) (hcub : Γ.IsCubic)
    (h2 : 2 ≤ Γ.Vs.card) (hnc : ¬ Γ.Colourable) : ¬ Γ.IsHamiltonian :=
  fun ⟨_, hC⟩ ↦ hnc (colourable_of_isHamCycle hcl hcub h2 hC)

end Hamiltonian

end FinGraph
end GraphPuzzles
