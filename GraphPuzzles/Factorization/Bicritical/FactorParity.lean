import GraphPuzzles.Factorization.FactorRecap

/-!
# Parity, gluing and small cuts

* the parity lemma for cubic multipoles whose dangling edges have one inner end;
* gluing colourings of the two poles of a cut which agree on the cut (up to a colour
  permutation);
* a cut of at most three edges with both poles colourable makes the graph colourable;
* bicritical snarks are cyclically `4`-edge-connected.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

set_option maxRecDepth 100000

variable {Γ : FinGraph} {c : ℕ → Color}

section Parity

/-- **Parity lemma** for cubic multipoles whose dangling edges have exactly one inner end. -/
theorem IsColouring.card_dangling_color' (hcub : Γ.IsCubic)
    (hinner : ∀ e ∈ Γ.dangling, ∃ i, Γ.ends e i ∈ Γ.Vs ∧ Γ.ends e (Fin.rev i) ∉ Γ.Vs)
    (hc : Γ.IsColouring c) {κ : Color} (hκ : κ ≠ 0) :
    (Γ.dangling.filter fun e ↦ c e = κ).card % 2 = Γ.Vs.card % 2 := by
  set F := Γ.Es.filter fun e ↦ c e = κ with hF
  have h1 : ∑ v ∈ Γ.Vs, Γ.degIn F v = Γ.Vs.card := by
    rw [Finset.sum_congr rfl (fun v hv ↦ hc.degIn_color hcub hv hκ)]
    simp
  rw [sum_degIn_eq] at h1
  have hsplit : F = (F.filter fun e ↦ e ∈ Γ.dangling) ∪ (F.filter fun e ↦ e ∉ Γ.dangling) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  rw [hsplit, Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _)] at h1
  have hA : ∑ e ∈ F.filter (fun e ↦ e ∈ Γ.dangling), Γ.endsIn Γ.Vs e =
      (Γ.dangling.filter fun e ↦ c e = κ).card := by
    have : F.filter (fun e ↦ e ∈ Γ.dangling) = Γ.dangling.filter fun e ↦ c e = κ := by
      ext e
      simp only [hF, Finset.mem_filter, mem_dangling]
      tauto
    rw [this, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨i, hi, hi'⟩ := hinner e he.1
    rw [endsIn_eq]
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · have hi'' : Γ.ends e 1 ∉ Γ.Vs := hi'
      rw [if_pos hi, if_neg hi'']
    · have hi'' : Γ.ends e 0 ∉ Γ.Vs := hi'
      rw [if_neg hi'', if_pos hi]
  have hB : ∑ e ∈ F.filter (fun e ↦ e ∉ Γ.dangling), Γ.endsIn Γ.Vs e =
      2 * (F.filter fun e ↦ e ∉ Γ.dangling).card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter, mem_dangling, hF, Finset.mem_filter] at he
    rw [endsIn_eq]
    have h0 : Γ.ends e 0 ∈ Γ.Vs := by
      by_contra h
      exact he.2 ⟨he.1.1, 0, h⟩
    have h1 : Γ.ends e 1 ∈ Γ.Vs := by
      by_contra h
      exact he.2 ⟨he.1.1, 1, h⟩
    rw [if_pos h0, if_pos h1]
    rfl
  rw [hA, hB] at h1
  omega

/-- Every dangling edge of a pole has exactly one inner end. -/
theorem pole_inner (X : Finset ℕ) : ∀ e ∈ (Γ.pole X).dangling,
    ∃ i, (Γ.pole X).ends e i ∈ (Γ.pole X).Vs ∧ (Γ.pole X).ends e (Fin.rev i) ∉ (Γ.pole X).Vs := by
  intro e he
  rw [dangling_pole] at he
  obtain ⟨i, hi, hi'⟩ := bd_side he
  exact ⟨i, hi, hi'⟩

/-- The boundary of a shore of a cubic graph has the parity of the shore. -/
theorem card_bd_mod_two (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs) :
    (Γ.bd X).card % 2 = X.card % 2 := by
  have := three_mul_card_eq hcub hX
  omega

/-- The parity lemma for the pole of a shore: each colour occurs on the boundary with the parity
of the boundary. -/
theorem IsColouring.card_bd_color (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hc : (Γ.pole X).IsColouring c) {κ : Color} (hκ : κ ≠ 0) :
    ((Γ.bd X).filter fun e ↦ c e = κ).card % 2 = (Γ.bd X).card % 2 := by
  have := hc.card_dangling_color' (pole_isCubic hcub hX) (pole_inner X) hκ
  rw [dangling_pole, pole_Vs] at this
  rw [this, card_bd_mod_two hcub hX]

/-- A pole with a single boundary edge is uncolourable. -/
theorem not_colourable_of_card_bd_one (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (h1 : (Γ.bd X).card = 1) : ¬ (Γ.pole X).Colourable := by
  rintro ⟨c, hc⟩
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h1
  have hdE : d ∈ (Γ.pole X).Es := by
    rw [pole_Es, Finset.mem_union, hd]; exact Or.inr (Finset.mem_singleton_self _)
  have hne := hc.1 d hdE
  -- a colour different from `c d`
  obtain ⟨κ, hκ0, hκd⟩ := exists_ne_color (c d)
  have := hc.card_bd_color hcub hX hκ0
  rw [h1, hd] at this
  have hzero : (({d} : Finset ℕ).filter fun e ↦ c e = κ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    rw [Finset.mem_singleton] at he
    rw [he]; exact hκd.symm
  rw [hzero] at this
  simp at this

/-- On a pole with two boundary edges, both receive the same colour. -/
theorem IsColouring.bd_two_eq (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hc : (Γ.pole X).IsColouring c) {d₁ d₂ : ℕ} (hbd : Γ.bd X = {d₁, d₂}) (hne : d₁ ≠ d₂) :
    c d₁ = c d₂ := by
  by_contra h
  have hd₁E : d₁ ∈ (Γ.pole X).Es := by
    rw [pole_Es, Finset.mem_union, hbd]; exact Or.inr (Finset.mem_insert_self _ _)
  have := hc.card_bd_color hcub hX (hc.1 d₁ hd₁E)
  rw [hbd, Finset.card_pair hne] at this
  have hone : (({d₁, d₂} : Finset ℕ).filter fun e ↦ c e = c d₁) = {d₁} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, he⟩
      · rfl
      · exact absurd he.symm h
    · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
  rw [hone] at this
  simp at this

/-- On a pole with three boundary edges, the colours are pairwise distinct. -/
theorem IsColouring.bd_three_ne (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (hc : (Γ.pole X).IsColouring c) {d₁ d₂ d₃ : ℕ} (hbd : Γ.bd X = {d₁, d₂, d₃})
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) : c d₁ ≠ c d₂ := by
  intro h
  have hd₁E : d₁ ∈ (Γ.pole X).Es := by
    rw [pole_Es, Finset.mem_union, hbd]; exact Or.inr (Finset.mem_insert_self _ _)
  have hne := hc.1 d₁ hd₁E
  have hcard : (Γ.bd X).card = 3 := by
    rw [hbd, Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  -- the colour of `d₁` occurs at least twice, hence three times, hence `d₃` has it too
  have hthree : c d₃ = c d₁ := by
    by_contra h3
    have := hc.card_bd_color hcub hX hne
    rw [hcard, hbd] at this
    have htwo : (({d₁, d₂, d₃} : Finset ℕ).filter fun e ↦ c e = c d₁) = {d₁, d₂} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, he⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd he h3
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr (Or.inl rfl), h.symm⟩
    rw [htwo, Finset.card_pair h12] at this
    omega
  -- then another colour occurs zero times
  obtain ⟨κ, hκ0, hκd⟩ := exists_ne_color (c d₁)
  have := hc.card_bd_color hcub hX hκ0
  rw [hcard, hbd] at this
  have hzero : (({d₁, d₂, d₃} : Finset ℕ).filter fun e ↦ c e = κ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hκd.symm
    · rw [← h]; exact hκd.symm
    · rw [hthree]; exact hκd.symm
  rw [hzero] at this
  simp at this

end Parity

section Glue

/-- **Gluing colourings of the two poles of a cut** after a colour permutation on one side. -/
theorem colourable_of_perm (hcl : Γ.IsClosed) {X : Finset ℕ} {c c' : ℕ → Color}
    (hc : (Γ.pole X).IsColouring c) (hc' : (Γ.pole (Γ.Vs \ X)).IsColouring c')
    (σ : Color → Color) (hσinj : Function.Injective σ) (hσ0 : σ 0 = 0)
    (hagree : ∀ e ∈ Γ.bd X, σ (c e) = c' e) : Γ.Colourable := by
  refine ⟨fun e ↦ if e ∈ Γ.edgesIn X ∪ Γ.bd X then σ (c e) else c' e, fun e he ↦ ?_,
    fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  · dsimp only
    split_ifs with hmem
    · intro h0
      have := hc.1 e hmem
      rw [← hσ0] at h0
      exact this (hσinj h0)
    · have hmem' : e ∈ Γ.edgesIn (Γ.Vs \ X) ∪ Γ.bd (Γ.Vs \ X) := by
        rw [Finset.mem_union, mem_edgesIn]
        refine Or.inl ⟨he, fun i ↦ Finset.mem_sdiff.mpr ⟨hcl e he i, fun hi ↦ hmem ?_⟩⟩
        exact Finset.mem_union.mpr (mem_edgesIn_or_bd he hi)
      exact hc'.1 e hmem'
  · have h₁' := mem_halfEdgesIn.mp h₁m
    have h₂' := mem_halfEdgesIn.mp h₂m
    by_cases hvX : v ∈ X
    · have m₁ : h₁ ∈ (Γ.pole X).halfEdgesIn (Γ.pole X).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₁'.1 (h₁'.2 ▸ hvX), h₁'.2⟩
      have m₂ : h₂ ∈ (Γ.pole X).halfEdgesIn (Γ.pole X).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₂'.1 (h₂'.2 ▸ hvX), h₂'.2⟩
      have e₁ : h₁.1 ∈ Γ.edgesIn X ∪ Γ.bd X := (mem_halfEdgesIn.mp m₁).1
      have e₂ : h₂.1 ∈ Γ.edgesIn X ∪ Γ.bd X := (mem_halfEdgesIn.mp m₂).1
      dsimp only at heq
      rw [if_pos e₁, if_pos e₂] at heq
      exact hc.unique_halfEdge hvX m₁ m₂ (hσinj heq)
    · have hvX' : v ∈ Γ.Vs \ X := Finset.mem_sdiff.mpr ⟨hv, hvX⟩
      have m₁ : h₁ ∈ (Γ.pole (Γ.Vs \ X)).halfEdgesIn (Γ.pole (Γ.Vs \ X)).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₁'.1 (h₁'.2 ▸ hvX'), h₁'.2⟩
      have m₂ : h₂ ∈ (Γ.pole (Γ.Vs \ X)).halfEdgesIn (Γ.pole (Γ.Vs \ X)).Es v := by
        rw [mem_halfEdgesIn, pole_Es, Finset.mem_union]
        exact ⟨mem_edgesIn_or_bd h₂'.1 (h₂'.2 ▸ hvX'), h₂'.2⟩
      have key : ∀ h ∈ Γ.halfEdgesIn Γ.Es v,
          (if h.1 ∈ Γ.edgesIn X ∪ Γ.bd X then σ (c h.1) else c' h.1) = c' h.1 := by
        intro h hm
        have hm' := mem_halfEdgesIn.mp hm
        split_ifs with hmem
        · rw [Finset.mem_union] at hmem
          rcases hmem with hmem | hmem
          · exact absurd ((mem_edgesIn.mp hmem).2 h.2) (hm'.2 ▸ hvX)
          · exact hagree _ hmem
        · rfl
      dsimp only at heq
      rw [key h₁ h₁m, key h₂ h₂m] at heq
      exact hc'.unique_halfEdge hvX' m₁ m₂ heq

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- A colour outside three distinct nonzero colours is zero. -/
theorem eq_zero_of_ne_three (a₁ a₂ a₃ z : Color) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) (hz1 : z ≠ a₁) (hz2 : z ≠ a₂) (hz3 : z ≠ a₃) :
    z = 0 := by
  revert a₁ a₂ a₃ z
  decide

/-- The colour permutation matching two triples of distinct nonzero colours. -/
def permTriple (a₁ a₂ a₃ b₁ b₂ b₃ : Color) (x : Color) : Color :=
  if x = a₁ then b₁ else if x = a₂ then b₂ else if x = a₃ then b₃ else 0

theorem permTriple_zero (a₁ a₂ a₃ b₁ b₂ b₃ : Color) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0) :
    permTriple a₁ a₂ a₃ b₁ b₂ b₃ 0 = 0 := by
  unfold permTriple
  rw [if_neg ha₁.symm, if_neg ha₂.symm, if_neg ha₃.symm]

theorem permTriple_left_inverse (a₁ a₂ a₃ b₁ b₂ b₃ : Color) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (ha₃ : a₃ ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃)
    (h23 : a₂ ≠ a₃) (g12 : b₁ ≠ b₂) (g13 : b₁ ≠ b₃) (g23 : b₂ ≠ b₃) (x : Color) :
    permTriple b₁ b₂ b₃ a₁ a₂ a₃ (permTriple a₁ a₂ a₃ b₁ b₂ b₃ x) = x := by
  by_cases hx1 : x = a₁
  · rw [hx1]; unfold permTriple; rw [if_pos rfl, if_pos rfl]
  by_cases hx2 : x = a₂
  · rw [hx2]; unfold permTriple; rw [if_neg h12.symm, if_pos rfl, if_neg g12.symm, if_pos rfl]
  by_cases hx3 : x = a₃
  · rw [hx3]; unfold permTriple
    rw [if_neg h13.symm, if_neg h23.symm, if_pos rfl, if_neg g13.symm, if_neg g23.symm, if_pos rfl]
  have hx0 := eq_zero_of_ne_three a₁ a₂ a₃ x ha₁ ha₂ ha₃ h12 h13 h23 hx1 hx2 hx3
  rw [hx0, permTriple_zero _ _ _ _ _ _ ha₁ ha₂ ha₃, permTriple_zero _ _ _ _ _ _ hb₁ hb₂ hb₃]

theorem permTriple_injective (a₁ a₂ a₃ b₁ b₂ b₃ : Color) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (ha₃ : a₃ ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃)
    (h23 : a₂ ≠ a₃) (g12 : b₁ ≠ b₂) (g13 : b₁ ≠ b₃) (g23 : b₂ ≠ b₃) :
    Function.Injective (permTriple a₁ a₂ a₃ b₁ b₂ b₃) :=
  Function.LeftInverse.injective
    (permTriple_left_inverse a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ h12 h13 h23 g12 g13 g23)

/-- **A cut of at most three edges with both poles colourable makes the graph colourable.** -/
theorem colourable_of_small_cut (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) {X : Finset ℕ}
    (hX : X ⊆ Γ.Vs) (hk : (Γ.bd X).card ≤ 3) (hc : (Γ.pole X).Colourable)
    (hc' : (Γ.pole (Γ.Vs \ X)).Colourable) : Γ.Colourable := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨c', hc'⟩ := hc'
  have hXc : Γ.Vs \ X ⊆ Γ.Vs := Finset.sdiff_subset
  have hbdc : Γ.bd (Γ.Vs \ X) = Γ.bd X := bd_compl hcl X
  have hmem : ∀ e ∈ Γ.bd X, e ∈ (Γ.pole X).Es ∧ e ∈ (Γ.pole (Γ.Vs \ X)).Es := by
    intro e he
    constructor
    · rw [pole_Es, Finset.mem_union]; exact Or.inr he
    · rw [pole_Es, Finset.mem_union, hbdc]; exact Or.inr he
  have hk' : (Γ.bd X).card = 0 ∨ (Γ.bd X).card = 1 ∨ (Γ.bd X).card = 2 ∨ (Γ.bd X).card = 3 := by
    omega
  rcases hk' with h0 | h1 | h2 | h3
  · -- no cut edges: glue directly
    rw [Finset.card_eq_zero] at h0
    exact colourable_of_perm hcl hc hc' id Function.injective_id rfl (by rw [h0]; simp)
  · exact absurd ⟨c, hc⟩ (not_colourable_of_card_bd_one hcub hX h1)
  · obtain ⟨d₁, d₂, hne, hbd⟩ := Finset.card_eq_two.mp h2
    have e₁ := hc.bd_two_eq hcub hX hbd hne
    have e₂ := hc'.bd_two_eq hcub hXc (hbdc.trans hbd) hne
    have hd₁ : d₁ ∈ Γ.bd X := by rw [hbd]; exact Finset.mem_insert_self _ _
    have ha : c d₁ ≠ 0 := hc.1 d₁ (hmem d₁ hd₁).1
    have hb : c' d₁ ≠ 0 := hc'.1 d₁ (hmem d₁ hd₁).2
    refine colourable_of_perm hcl hc hc' (swapC (c d₁) (c' d₁)) (swapC_injective _ _)
      (swapC_zero ha hb) ?_
    intro e he
    rw [hbd, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact swapC_left _ _
    · rw [← e₁, ← e₂]; exact swapC_left _ _
  · obtain ⟨d₁, d₂, d₃, h12, h13, h23, hbd⟩ := Finset.card_eq_three.mp h3
    have hd₁ : d₁ ∈ Γ.bd X := by rw [hbd]; exact Finset.mem_insert_self _ _
    have hd₂ : d₂ ∈ Γ.bd X := by rw [hbd]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hd₃ : d₃ ∈ Γ.bd X := by
      rw [hbd]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have n₁ := hc.1 d₁ (hmem d₁ hd₁).1
    have n₂ := hc.1 d₂ (hmem d₂ hd₂).1
    have n₃ := hc.1 d₃ (hmem d₃ hd₃).1
    have m₁ := hc'.1 d₁ (hmem d₁ hd₁).2
    have m₂ := hc'.1 d₂ (hmem d₂ hd₂).2
    have m₃ := hc'.1 d₃ (hmem d₃ hd₃).2
    have hbd' : Γ.bd (Γ.Vs \ X) = {d₁, d₂, d₃} := hbdc.trans hbd
    have a12 := hc.bd_three_ne hcub hX hbd h12 h13 h23
    have a13 : c d₁ ≠ c d₃ := hc.bd_three_ne hcub hX (by rw [hbd]; ext; simp; tauto) h13 h12 h23.symm
    have a23 : c d₂ ≠ c d₃ := hc.bd_three_ne hcub hX (by rw [hbd]; ext; simp; tauto) h23 h12.symm h13.symm
    have b12 := hc'.bd_three_ne hcub hXc hbd' h12 h13 h23
    have b13 : c' d₁ ≠ c' d₃ := hc'.bd_three_ne hcub hXc (by rw [hbd']; ext; simp; tauto) h13 h12 h23.symm
    have b23 : c' d₂ ≠ c' d₃ := hc'.bd_three_ne hcub hXc (by rw [hbd']; ext; simp; tauto) h23 h12.symm h13.symm
    refine colourable_of_perm hcl hc hc' (permTriple (c d₁) (c d₂) (c d₃) (c' d₁) (c' d₂) (c' d₃))
      (permTriple_injective _ _ _ _ _ _ n₁ n₂ n₃ m₁ m₂ m₃ a12 a13 a23 b12 b13 b23)
      (permTriple_zero _ _ _ _ _ _ n₁ n₂ n₃) ?_
    intro e he
    rw [hbd, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he
    unfold permTriple
    rcases he with rfl | rfl | rfl
    · rw [if_pos rfl]
    · rw [if_neg a12.symm, if_pos rfl]
    · rw [if_neg a13.symm, if_neg a23.symm, if_pos rfl]

end Glue

section Bicritical

/-- **Bicritical**: removing any two distinct vertices leaves a colourable multipole. -/
def IsBicritical (Γ : FinGraph) : Prop :=
  ∀ x ∈ Γ.Vs, ∀ y ∈ Γ.Vs, x ≠ y → (Γ.pole (Γ.Vs \ {x, y})).Colourable

/-- A pole avoiding two vertices of a bicritical graph is colourable. -/
theorem IsBicritical.pole_colourable (hb : Γ.IsBicritical) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    (h2 : 2 ≤ (Γ.Vs \ X).card) : (Γ.pole X).Colourable := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
  obtain ⟨c, hc⟩ := hb x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hxy
  refine ⟨c, hc.restrict ?_⟩
  intro v hv
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨hX hv, ?_⟩
  rintro (rfl | rfl)
  · exact (Finset.mem_sdiff.mp hx).2 hv
  · exact (Finset.mem_sdiff.mp hy).2 hv

/-- A loop makes a pole containing its vertex uncolourable. -/
theorem not_colourable_of_loop {X : Finset ℕ} {e : ℕ} (he : e ∈ Γ.Es) (h0 : Γ.ends e 0 ∈ X)
    (hloop : Γ.ends e 0 = Γ.ends e 1) : ¬ (Γ.pole X).Colourable := by
  rintro ⟨c, hc⟩
  have heP : e ∈ (Γ.pole X).Es := by
    rw [pole_Es, Finset.mem_union]; left
    refine mem_edgesIn.mpr ⟨he, fun i ↦ ?_⟩
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact h0
    · rw [← hloop]; exact h0
  have := hc.unique_halfEdge (v := Γ.ends e 0) h0 (h₁ := (e, 0)) (mem_halfEdgesIn.mpr ⟨heP, rfl⟩)
    (h₂ := (e, 1)) (mem_halfEdgesIn.mpr ⟨heP, hloop.symm⟩) rfl
  simp at this

/-- A shore carrying a cycle has a vertex; if it has only one vertex, that vertex has a loop. -/
theorem HasCycle.exists_loop_or_two {X : Finset ℕ} (h : Γ.HasCycle X) :
    (∃ e ∈ Γ.Es, Γ.ends e 0 ∈ X ∧ Γ.ends e 0 = Γ.ends e 1) ∨ 2 ≤ X.card := by
  obtain ⟨F, hF, ⟨e, he⟩, -⟩ := h
  have heX := hF he
  rw [mem_edgesIn] at heX
  by_cases hl : Γ.ends e 0 = Γ.ends e 1
  · exact Or.inl ⟨e, heX.1, heX.2 0, hl⟩
  · right
    exact Finset.one_lt_card.mpr ⟨_, heX.2 0, _, heX.2 1, hl⟩

/-- **Bicritical snarks are cyclically `4`-edge-connected.** -/
theorem IsBicritical.cyc4Conn (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable)
    (hb : Γ.IsBicritical) (h3 : 3 ≤ Γ.Vs.card) : Γ.Cyc4Conn := by
  intro X hX hcX hcXc
  by_contra hlt
  push Not at hlt
  have hk : (Γ.bd X).card ≤ 3 := by omega
  have hXc : Γ.Vs \ X ⊆ Γ.Vs := Finset.sdiff_subset
  have hcardX : X.card + (Γ.Vs \ X).card = Γ.Vs.card := by
    rw [Finset.card_sdiff_of_subset hX]
    have := Finset.card_le_card hX
    omega
  -- a loop on either side contradicts bicriticality; otherwise both poles are colourable
  have loop_case : ∀ Y ⊆ Γ.Vs, (∃ e ∈ Γ.Es, Γ.ends e 0 ∈ Y ∧ Γ.ends e 0 = Γ.ends e 1) →
      2 ≤ (Γ.Vs \ Y).card → False := by
    rintro Y hY ⟨e, he, h0, hl⟩ h2
    exact not_colourable_of_loop he h0 hl (hb.pole_colourable hY h2)
  rcases hcX.exists_loop_or_two with hl | h2 <;> rcases hcXc.exists_loop_or_two with hl' | h2'
  · -- both sides have a loop: each side has at least one vertex, and a loop side of one vertex
    -- with the other side of one vertex gives only two vertices
    obtain ⟨e, he, h0, hloop⟩ := hl
    obtain ⟨e', he', h0', hloop'⟩ := hl'
    have hx : X.Nonempty := ⟨_, h0⟩
    have hx' : (Γ.Vs \ X).Nonempty := ⟨_, h0'⟩
    by_cases h2 : 2 ≤ (Γ.Vs \ X).card
    · exact loop_case X hX ⟨e, he, h0, hloop⟩ h2
    · have h2' : 2 ≤ (Γ.Vs \ (Γ.Vs \ X)).card := by
        rw [Finset.sdiff_sdiff_eq_self hX]
        have := Finset.card_pos.mpr hx'
        omega
      exact loop_case (Γ.Vs \ X) hXc ⟨e', he', h0', hloop'⟩ h2'
  · exact loop_case X hX hl h2'
  · exact loop_case (Γ.Vs \ X) hXc hl' (by rw [Finset.sdiff_sdiff_eq_self hX]; exact h2)
  · exact hnc (colourable_of_small_cut hcl hcub hX hk (hb.pole_colourable hX h2')
      (hb.pole_colourable hXc (by rw [Finset.sdiff_sdiff_eq_self hX]; exact h2)))

end Bicritical

end FinGraph
end GraphPuzzles
