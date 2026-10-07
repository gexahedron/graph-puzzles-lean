import GraphPuzzles.Factorization.FactorAtom

/-!
# Structure of cycle-separating `4`-cuts

In a cyclically `4`-edge-connected cubic graph of girth at least five, every cycle-separating
`4`-cut is independent (no two of its edges share a vertex), and conversely an independent
`4`-cut is cycle-separating.  A couple of the boundary of a cycle-separating shore `A` that lies
inside another cut `S` is a couple of `S` (the colouring types force it), and an atom's
boundary never meets another cut in exactly three edges (Chladný–Škoviera, Lemma 9.1).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section Independent

/-- The edges incident with a vertex. -/
def edgesAt (Γ : FinGraph) (v : ℕ) : Finset ℕ := Γ.Es.filter fun e ↦ ∃ i, Γ.ends e i = v

theorem mem_edgesAt {v e : ℕ} : e ∈ Γ.edgesAt v ↔ e ∈ Γ.Es ∧ ∃ i, Γ.ends e i = v := by
  simp [edgesAt]

/-- Without loops at `v`, the edges at `v` are counted by the degree. -/
theorem card_edgesAt (hg : Γ.Girth5) (hcl : Γ.IsClosed) {v : ℕ} (_hv : v ∈ Γ.Vs) :
    (Γ.edgesAt v).card = Γ.deg v := by
  unfold deg degIn
  symm
  apply Finset.card_bij (fun h _ ↦ h.1)
  · intro h hh
    rw [mem_halfEdgesIn] at hh
    exact mem_edgesAt.mpr ⟨hh.1, h.2, hh.2⟩
  · intro h hh h' hh' heq
    rw [mem_halfEdgesIn] at hh hh'
    by_cases hij : h.2 = h'.2
    · exact Prod.ext heq hij
    · exfalso
      have hloop := hg.no_loop hh.1 (hcl _ hh.1 0)
      have h0 : Γ.ends h.1 h.2 = v := hh.2
      have h1 : Γ.ends h.1 h'.2 = v := heq ▸ hh'.2
      have h2 : h.2 = 0 ∨ h.2 = 1 := by omega
      have h2' : h'.2 = 0 ∨ h'.2 = 1 := by omega
      rcases h2 with h2 | h2 <;> rcases h2' with h2' | h2' <;> rw [h2] at h0 <;> rw [h2'] at h1
      · exact hij (h2.trans h2'.symm)
      · exact hloop (h0.trans h1.symm)
      · exact hloop (h1.trans h0.symm)
      · exact hij (h2.trans h2'.symm)
  · intro e he
    obtain ⟨heE, i, hi⟩ := mem_edgesAt.mp he
    exact ⟨(e, i), mem_halfEdgesIn.mpr ⟨heE, hi⟩, rfl⟩

/-- The boundary of a single vertex consists of its edges (no loops). -/
theorem bd_singleton (hg : Γ.Girth5) (hcl : Γ.IsClosed) {v : ℕ} (_hv : v ∈ Γ.Vs) :
    Γ.bd {v} = Γ.edgesAt v := by
  ext e
  rw [mem_bd, mem_edgesAt]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    by_cases h0 : Γ.ends e 0 = v
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      by_contra h1
      exact h ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
  · rintro ⟨he, i, hi⟩
    refine ⟨he, fun h ↦ ?_⟩
    have hloop := hg.no_loop he (hcl _ he 0)
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · exact hloop (hi.trans (h.mp hi).symm)
    · exact hloop ((h.mpr hi).trans hi.symm)

/-- An independent cut: every vertex meets at most one cut edge. -/
def IsIndependentCut (Γ : FinGraph) (Y : Finset ℕ) : Prop := ∀ v, Γ.degIn (Γ.bd Y) v ≤ 1

theorem degIn_bd_le_of_two_edges {Y : Finset ℕ} {v e f : ℕ} (he : e ∈ Γ.bd Y) (hf : f ∈ Γ.bd Y)
    (hef : e ≠ f) {i j : Fin 2} (hi : Γ.ends e i = v) (hj : Γ.ends f j = v) :
    2 ≤ Γ.degIn (Γ.bd Y) v := by
  unfold degIn
  have : ({(e, i), (f, j)} : Finset (ℕ × Fin 2)) ⊆ Γ.halfEdgesIn (Γ.bd Y) v := by
    intro h hh
    rw [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact mem_halfEdgesIn.mpr ⟨he, hi⟩
    · exact mem_halfEdgesIn.mpr ⟨hf, hj⟩
  have hcard : ({(e, i), (f, j)} : Finset (ℕ × Fin 2)).card = 2 :=
    Finset.card_pair (fun h ↦ hef (congrArg Prod.fst h))
  have := Finset.card_le_card this
  rw [hcard] at this
  exact this

/-- **Cycle-separating `4`-cuts are independent** in a cyclically `4`-edge-connected cubic
graph of girth at least five. -/
theorem CycSep.independent (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hg : Γ.Girth5)
    (hc4 : Γ.Cyc4Conn) {Y : Finset ℕ} (hY : Γ.CycSep Y) : Γ.IsIndependentCut Y := by
  -- it suffices to treat vertices of `Y`, by symmetry
  suffices key : ∀ Z, Γ.CycSep Z → ∀ v ∈ Z, Γ.degIn (Γ.bd Z) v ≤ 1 by
    intro v
    by_cases hv : v ∈ Γ.Vs
    · by_cases hvY : v ∈ Y
      · exact key Y hY v hvY
      · have := key (Γ.Vs \ Y) (cycSep_compl hcl hY) v (Finset.mem_sdiff.mpr ⟨hv, hvY⟩)
        rw [bd_compl hcl] at this
        exact this
    · rw [degIn_eq_zero_iff.mpr]
      · omega
      intro e he i hi
      exact hv (hi ▸ hcl e (bd_subset Y he) i)
  intro Z hZ v hv
  by_contra hlt
  push Not at hlt
  have hvV : v ∈ Γ.Vs := hZ.1 hv
  -- the internal degree of `v` is at most one
  have hint : Γ.degIn (Γ.edgesIn Z) v ≤ 1 := by
    have := degIn_edgesIn_add_bd (Γ := Γ) hv
    rw [hcub v hvV] at this
    omega
  have hZ' : Γ.HasCycle (Z.erase v) := HasCycle.erase hvV hZ.2.2.1 hint
  have hZ'V : Z.erase v ⊆ Γ.Vs := (Finset.erase_subset _ _).trans hZ.1
  have hcompl : Γ.HasCycle (Γ.Vs \ Z.erase v) :=
    hZ.2.2.2.mono (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.erase_subset _ _))
  have h4 := hc4 _ hZ'V hZ' hcompl
  -- the boundary of `Z.erase v` has at most three edges
  have hunion : Z = Z.erase v ∪ {v} := by
    rw [Finset.union_singleton, Finset.insert_erase hv]
  have hdisj : Disjoint (Z.erase v) {v} := by
    rw [Finset.disjoint_singleton_right]
    exact Finset.notMem_erase v Z
  have hcb := card_bd_union (Γ := Γ) hdisj
  rw [← hunion, hZ.2.1, bd_singleton hg hcl hvV, card_edgesAt hg hcl hvV, hcub v hvV] at hcb
  -- the edges between `Z.erase v` and `v` avoid the two boundary edges at `v`
  have hb : (Γ.between (Z.erase v) {v}).card ≤ 1 := by
    -- edges at `v` not in the boundary of `Z`
    have hsub : Γ.between (Z.erase v) {v} ⊆ (Γ.edgesAt v).filter fun e ↦ e ∉ Γ.bd Z := by
      intro e he
      rw [mem_between] at he
      rw [Finset.mem_filter, mem_edgesAt, mem_bd]
      rcases he.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [Finset.mem_singleton] at h1
        refine ⟨⟨he.1, 1, h1⟩, fun h ↦ h.2 ⟨fun _ ↦ h1 ▸ hv, fun _ ↦ (Finset.mem_erase.mp h0).2⟩⟩
      · rw [Finset.mem_singleton] at h0
        refine ⟨⟨he.1, 0, h0⟩, fun h ↦ h.2 ⟨fun _ ↦ (Finset.mem_erase.mp h1).2, fun _ ↦ h0 ▸ hv⟩⟩
    have hcard := Finset.card_filter_add_card_filter_not (s := Γ.edgesAt v)
      (p := fun e ↦ e ∈ Γ.bd Z)
    rw [card_edgesAt hg hcl hvV, hcub v hvV] at hcard
    -- at least two edges at `v` lie in the boundary
    have h2 : 2 ≤ ((Γ.edgesAt v).filter fun e ↦ e ∈ Γ.bd Z).card := by
      have : Γ.halfEdgesIn (Γ.bd Z) v ⊆
          ((Γ.edgesAt v).filter fun e ↦ e ∈ Γ.bd Z) ×ˢ (Finset.univ : Finset (Fin 2)) := by
        intro h hh
        rw [mem_halfEdgesIn] at hh
        rw [Finset.mem_product, Finset.mem_filter, mem_edgesAt]
        exact ⟨⟨⟨bd_subset Z hh.1, h.2, hh.2⟩, hh.1⟩, Finset.mem_univ _⟩
      have hc := Finset.card_le_card this
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
      unfold degIn at hlt
      -- distinct half-edges at `v` have distinct edges (no loops)
      have hinj : ∀ h ∈ Γ.halfEdgesIn (Γ.bd Z) v, ∀ h' ∈ Γ.halfEdgesIn (Γ.bd Z) v,
          h.1 = h'.1 → h = h' := by
        intro h hh h' hh' heq
        rw [mem_halfEdgesIn] at hh hh'
        by_cases hij : h.2 = h'.2
        · exact Prod.ext heq hij
        · exfalso
          have he := bd_subset Z hh.1
          have hloop := hg.no_loop he (hcl _ he 0)
          have h0 : Γ.ends h.1 h.2 = v := hh.2
          have h1 : Γ.ends h.1 h'.2 = v := heq ▸ hh'.2
          have h2 : h.2 = 0 ∨ h.2 = 1 := by omega
          have h2' : h'.2 = 0 ∨ h'.2 = 1 := by omega
          rcases h2 with h2 | h2 <;> rcases h2' with h2' | h2' <;> rw [h2] at h0 <;>
            rw [h2'] at h1
          · exact hij (h2.trans h2'.symm)
          · exact hloop (h0.trans h1.symm)
          · exact hloop (h1.trans h0.symm)
          · exact hij (h2.trans h2'.symm)
      have himg : (Γ.halfEdgesIn (Γ.bd Z) v).card ≤
          ((Γ.edgesAt v).filter fun e ↦ e ∈ Γ.bd Z).card := by
        rw [← Finset.card_image_of_injOn (f := Prod.fst) (fun h hh h' hh' heq ↦ hinj h hh h' hh' heq)]
        apply Finset.card_le_card
        intro e he
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
        rw [mem_halfEdgesIn] at hh
        rw [Finset.mem_filter, mem_edgesAt]
        exact ⟨⟨bd_subset Z hh.1, h.2, hh.2⟩, hh.1⟩
      omega
    have := Finset.card_le_card hsub
    omega
  omega

/-- The boundary size is the sum of boundary degrees over the shore. -/
theorem card_bd_eq_sum_degIn (_hcl : Γ.IsClosed) {Z : Finset ℕ} (_hZ : Z ⊆ Γ.Vs) :
    (Γ.bd Z).card = ∑ v ∈ Z, Γ.degIn (Γ.bd Z) v := by
  rw [sum_degIn_eq, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun e he ↦ (endsIn_of_mem_bd he).symm

/-- **An independent `4`-cut is cycle-separating** (both sides have minimum internal degree two,
hence contain cycles). -/
theorem cycSep_of_independent (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) {Z : Finset ℕ}
    (hZ : Z ⊆ Γ.Vs) (h4 : (Γ.bd Z).card = 4) (hind : Γ.IsIndependentCut Z) : Γ.CycSep Z := by
  have key : ∀ W, W ⊆ Γ.Vs → (Γ.bd W).card = 4 → Γ.IsIndependentCut W → Γ.HasCycle W := by
    intro W hW hW4 hWind
    have hne : W.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      have : Γ.bd ∅ = ∅ := by
        ext e
        rw [mem_bd]
        simp
      rw [this] at hW4
      simp at hW4
    by_contra hno
    have hlt := card_edgesIn_lt hne hno
    have hhs := three_mul_card_eq hcub hW
    have hsum := card_bd_eq_sum_degIn hcl hW
    have hle : ∑ v ∈ W, Γ.degIn (Γ.bd W) v ≤ ∑ _v ∈ W, 1 := Finset.sum_le_sum fun v _ ↦ hWind v
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
    omega
  refine ⟨hZ, h4, key Z hZ h4 hind, key (Γ.Vs \ Z) Finset.sdiff_subset ?_ ?_⟩
  · rw [bd_compl hcl]; exact h4
  · intro v
    rw [bd_compl hcl]
    exact hind v

end Independent

section Couples

/-- The pairing containing a given pair of positions. -/
def pairOf (i j : Fin 4) : Fin 3 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 else 2

theorem pairing_pairOf (i j : Fin 4) (h : i ≠ j) : pairing (pairOf i j) i = j := by
  revert i j
  decide

set_option maxRecDepth 100000 in
theorem valid_eq_iff_iso (t : Fin 4 → Color) (hv : Valid t) (i j : Fin 4) (h : i ≠ j) :
    t i = t j ↔ ∀ k, t k = t (pairing (pairOf i j) k) := by
  revert t i j
  decide

set_option maxRecDepth 100000 in
theorem valid_ne_iff_het (t : Fin 4 → Color) (hv : Valid t) (i j : Fin 4) (h : i ≠ j) :
    t i ≠ t j ↔ ∀ k, t k ≠ t (pairing (pairOf i j) k) := by
  revert t i j
  decide

/-- Two positions always equal in every colouring: the pole is isochromatic with that couple. -/
theorem isoWith_of_always_eq (hP : Γ.IsPole4) {i j : Fin 4} (h : i ≠ j)
    (heq : ∀ t ∈ Col hP, t i = t j) : IsoWith hP (pairOf i j) := by
  intro t ht k
  exact (valid_eq_iff_iso t (Col.valid hP ht) i j h).mp (heq t ht) k

theorem hetWith_of_always_ne (hP : Γ.IsPole4) {i j : Fin 4} (h : i ≠ j)
    (hne : ∀ t ∈ Col hP, t i ≠ t j) : HetWith hP (pairOf i j) := by
  intro t ht k
  exact (valid_ne_iff_het t (Col.valid hP ht) i j h).mp (hne t ht) k

/-- Colourings of a pole restrict to colourings of a sub-pole. -/
theorem IsColouring.restrict {A Y : Finset ℕ} (hAY : A ⊆ Y) {c : ℕ → Color}
    (hc : (Γ.pole Y).IsColouring c) : (Γ.pole A).IsColouring c := by
  have hsub : (Γ.pole A).Es ⊆ (Γ.pole Y).Es := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he ⊢
    rcases he with he | he
    · exact Or.inl (edgesIn_mono hAY he)
    · have h := mem_bd.mp he
      obtain ⟨i, hi, hi'⟩ := bd_side he
      by_cases hY : Γ.ends e (Fin.rev i) ∈ Y
      · left
        rw [mem_edgesIn]
        refine ⟨h.1, fun j ↦ ?_⟩
        have hj : j = i ∨ j = Fin.rev i := by
          by_cases hji : j = i
          · exact Or.inl hji
          · exact Or.inr (fin2_eq_rev_of_ne hji)
        rcases hj with rfl | rfl
        · exact hAY hi
        · exact hY
      · right
        rw [mem_bd]
        refine ⟨h.1, fun hiff ↦ ?_⟩
        have hi0 : i = 0 ∨ i = 1 := by omega
        rcases hi0 with rfl | rfl
        · exact hY (hiff.mp (hAY hi))
        · exact hY (hiff.mpr (hAY hi))
  refine ⟨fun e he ↦ hc.1 e (hsub he), fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  have m₁ : h₁ ∈ (Γ.pole Y).halfEdgesIn (Γ.pole Y).Es v := by
    rw [mem_halfEdgesIn] at h₁m ⊢
    exact ⟨hsub h₁m.1, h₁m.2⟩
  have m₂ : h₂ ∈ (Γ.pole Y).halfEdgesIn (Γ.pole Y).Es v := by
    rw [mem_halfEdgesIn] at h₂m ⊢
    exact ⟨hsub h₂m.1, h₂m.2⟩
  exact hc.unique_halfEdge (hAY hv) m₁ m₂ heq

/-- **A couple of the boundary of a sub-shore lying in a cut is a couple of that cut.**  If the
positions `i₁, i₂` of `∂A` form a couple (for the `A`-datum) and both edges are boundary edges of
`Y ⊇ A` at positions `k₁, k₂`, then `{k₁, k₂}` is a couple of the `Y`-pole: the `Y`-pole is
isochromatic with pairing `pairOf k₁ k₂` if `A` is, and heterochromatic if `A` is. -/
theorem couple_transfer {A Y : Finset ℕ} (hAY : A ⊆ Y) (hPA : (Γ.pole A).IsPole4)
    (hPY : (Γ.pole Y).IsPole4) {i₁ i₂ k₁ k₂ : Fin 4} (_hi : i₁ ≠ i₂) (hk : k₁ ≠ k₂)
    (e₁ : bdEmb hPA i₁ = bdEmb hPY k₁) (e₂ : bdEmb hPA i₂ = bdEmb hPY k₂) {m : Fin 3}
    (hpair : pairing m i₁ = i₂) :
    (IsoWith hPA m → IsoWith hPY (pairOf k₁ k₂)) ∧ (HetWith hPA m → HetWith hPY (pairOf k₁ k₂)) := by
  constructor
  · intro hiso
    apply isoWith_of_always_eq hPY hk
    rintro t ⟨c, hc, rfl⟩
    have hcA := hc.restrict hAY
    have := hiso (tvec hPA c) ⟨c, hcA, rfl⟩ i₁
    unfold tvec at this ⊢
    rw [hpair, e₁, e₂] at this
    exact this
  · intro het
    apply hetWith_of_always_ne hPY hk
    rintro t ⟨c, hc, rfl⟩
    have hcA := hc.restrict hAY
    have := het (tvec hPA c) ⟨c, hcA, rfl⟩ i₁
    unfold tvec at this ⊢
    rw [hpair, e₁, e₂] at this
    exact this

end Couples

section NineOne

/-- For `A ⊆ Y`, the edges between `A` and `Y \ A` are the boundary edges of `A` not in `∂Y`. -/
theorem between_sdiff_eq (_hcl : Γ.IsClosed) {A Y : Finset ℕ} (hAY : A ⊆ Y) (_hY : Y ⊆ Γ.Vs) :
    Γ.between A (Y \ A) = Γ.bd A \ Γ.bd Y := by
  ext e
  rw [Finset.mem_sdiff, mem_bd, mem_bd, mem_between]
  constructor
  · rintro ⟨he, h⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [Finset.mem_sdiff] at h1
      exact ⟨⟨he, fun hiff ↦ h1.2 (hiff.mp h0)⟩, fun h ↦ h.2 ⟨fun _ ↦ h1.1, fun _ ↦ hAY h0⟩⟩
    · rw [Finset.mem_sdiff] at h0
      exact ⟨⟨he, fun hiff ↦ h0.2 (hiff.mpr h1)⟩, fun h ↦ h.2 ⟨fun _ ↦ hAY h1, fun _ ↦ h0.1⟩⟩
  · rintro ⟨⟨he, hA⟩, hY'⟩
    refine ⟨he, ?_⟩
    have hY'' : Γ.ends e 0 ∈ Y ↔ Γ.ends e 1 ∈ Y := by
      by_contra h
      exact hY' ⟨he, h⟩
    by_cases h0 : Γ.ends e 0 ∈ A
    · have h1 : Γ.ends e 1 ∉ A := fun h1 ↦ hA ⟨fun _ ↦ h1, fun _ ↦ h0⟩
      exact Or.inl ⟨h0, Finset.mem_sdiff.mpr ⟨hY''.mp (hAY h0), h1⟩⟩
    · have h1 : Γ.ends e 1 ∈ A := by
        by_contra h1
        exact hA ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
      exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hY''.mpr (hAY h1), h0⟩, h1⟩

/-- The boundary of `Y \ A` for cycle-separating `A ⊆ Y`. -/
theorem card_bd_sdiff (hcl : Γ.IsClosed) {A Y : Finset ℕ} (hAY : A ⊆ Y) (hY : Y ⊆ Γ.Vs)
    (hA4 : (Γ.bd A).card = 4) (hY4 : (Γ.bd Y).card = 4) :
    (Γ.bd (Y \ A)).card + 2 * (Γ.bd A ∩ Γ.bd Y).card = 8 := by
  have hdisj : Disjoint A (Y \ A) := Finset.disjoint_sdiff
  have h := card_bd_union (Γ := Γ) hdisj
  rw [Finset.union_sdiff_of_subset hAY, between_sdiff_eq hcl hAY hY, hA4, hY4] at h
  have h2 := Finset.card_sdiff_add_card_inter (Γ.bd A) (Γ.bd Y)
  omega

/-- **Chladný–Škoviera, Lemma 9.1.**  An atom's boundary does not meet another
cycle-separating `4`-cut in exactly three edges. -/
theorem IsAtom.card_inter_ne_three (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hg : Γ.Girth5)
    (hc4 : Γ.Cyc4Conn) {A Y : Finset ℕ} (hA : Γ.IsAtom A) (hY : Γ.CycSep Y) :
    (Γ.bd A ∩ Γ.bd Y).card ≠ 3 := by
  intro h3
  -- the atom lies on one side; replace `Y` by its complement if needed
  have key : ∀ Z, Γ.CycSep Z → A ⊆ Z → (Γ.bd A ∩ Γ.bd Z).card = 3 → False := by
    intro Z hZ hAZ h3
    have hZV := hZ.1
    have hcard := card_bd_sdiff hcl hAZ hZV hA.1.2.1 hZ.2.1
    rw [h3] at hcard
    have hK2 : (Γ.bd (Z \ A)).card = 2 := by omega
    have hKV : Z \ A ⊆ Γ.Vs := Finset.sdiff_subset.trans hZV
    have hKne : (Z \ A).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hK2
      have : Γ.bd ∅ = ∅ := by
        ext e
        rw [mem_bd]
        simp
      rw [this] at hK2
      simp at hK2
    by_cases hKc : Γ.HasCycle (Z \ A)
    · have hcompl : Γ.HasCycle (Γ.Vs \ (Z \ A)) := by
        apply hA.1.2.2.1.mono
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨hA.1.1 hv, fun h ↦ (Finset.mem_sdiff.mp h).2 hv⟩
      have := hc4 _ hKV hKc hcompl
      omega
    · have h1 := card_add_two_le_card_bd hcub hKV hKne hKc
      have h2 := Finset.card_pos.mpr hKne
      omega
  rcases IsAtom.subset_or_subset_compl hcl hcub hg hc4 hA hY with h | h
  · exact key Y hY h h3
  · apply key (Γ.Vs \ Y) (cycSep_compl hcl hY) h
    rw [bd_compl hcl]
    exact h3

end NineOne

end FinGraph
end GraphPuzzles
