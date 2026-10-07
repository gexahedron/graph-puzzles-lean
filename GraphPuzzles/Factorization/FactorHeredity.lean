import GraphPuzzles.Factorization.FactorAssoc

/-!
# Heredity of the atom in the factor containing it (Chladný–Škoviera, Proposition 9.3)

Let `A` be an atom and `Y ⊇ A` a cycle-separating shore of a graph of a good class, with
`Y ≠ A` and `Y` not quasiatomic for `A`.  Then `A` is a cycle-separating shore of the factor of
`Y`.  The boundary of `A` in the factor still has four edges (each edge of `∂A ∩ ∂Y` is replaced
by the join edge of its couple, which crosses `A`), and the complement of `A` in the factor has
a cycle: otherwise it has at most two vertices, and a count of the edges at these vertices in
the original graph shows that `Y` is quasiatomic.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph}

section Counting

variable (hcl : Δ.IsClosed) (hcub : Δ.IsCubic) (hg : Δ.Girth5) (hc4 : Δ.Cyc4Conn)
include hcl hcub hg hc4

omit hcub hg hc4 in
/-- Common boundary edges of `A ⊆ Y` are the edges from `A` to the outside of `Y`. -/
theorem bd_inter_bd_eq_between {A Y : Finset ℕ} (hAY : A ⊆ Y) :
    Δ.bd A ∩ Δ.bd Y = Δ.between A (Δ.Vs \ Y) := by
  ext e
  rw [Finset.mem_inter, mem_bd, mem_bd, mem_between]
  constructor
  · rintro ⟨⟨he, hA⟩, ⟨-, hY⟩⟩
    refine ⟨he, ?_⟩
    by_cases h0 : Δ.ends e 0 ∈ A
    · have h1 : Δ.ends e 1 ∉ Y := fun h1 ↦ hY ⟨fun _ ↦ h1, fun _ ↦ hAY h0⟩
      exact Or.inl ⟨h0, Finset.mem_sdiff.mpr ⟨hcl e he 1, h1⟩⟩
    · have h1 : Δ.ends e 1 ∈ A := by
        by_contra h1
        exact hA ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
      have h0' : Δ.ends e 0 ∉ Y := fun h0' ↦ hY ⟨fun _ ↦ hAY h1, fun _ ↦ h0'⟩
      exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hcl e he 0, h0'⟩, h1⟩
  · rintro ⟨he, h⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [Finset.mem_sdiff] at h1
      exact ⟨⟨he, fun h ↦ h1.2 (hAY (h.mp h0))⟩, ⟨he, fun h ↦ h1.2 (h.mp (hAY h0))⟩⟩
    · rw [Finset.mem_sdiff] at h0
      exact ⟨⟨he, fun h ↦ h0.2 (hAY (h.mpr h1))⟩, ⟨he, fun h ↦ h0.2 (h.mpr (hAY h1))⟩⟩

/-- If `Y \ A` consists of two vertices, `Y` is quasiatomic. -/
theorem quasiatomic_of_pair {A Y : Finset ℕ} (hA : Δ.CycSep A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    {v₁ v₂ : ℕ} (hv : v₁ ≠ v₂) (hK : Y \ A = {v₁, v₂}) (_hc3 : (Δ.bd A ∩ Δ.bd Y).card ≠ 3)
    (_hne : Y ≠ A) : Δ.IsQuasiatomic A Y := by
  have hYV := hY.1
  have hAV := hA.1
  have hv₁ : v₁ ∈ Y \ A := by rw [hK]; exact Finset.mem_insert_self _ _
  have hv₂ : v₂ ∈ Y \ A := by rw [hK]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hv₁Y := (Finset.mem_sdiff.mp hv₁).1
  have hv₂Y := (Finset.mem_sdiff.mp hv₂).1
  have hv₁A := (Finset.mem_sdiff.mp hv₁).2
  have hv₂A := (Finset.mem_sdiff.mp hv₂).2
  have hind := CycSep.independent hcl hcub hg hc4 hY
  -- partitions
  have eY : Y = (A ∪ {v₁}) ∪ {v₂} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · have : x ∈ Y \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
        rw [hK, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr rfl
    · rintro ((hx | rfl) | rfl)
      · exact hAY hx
      · exact hv₁Y
      · exact hv₂Y
  have e₁ : Δ.Vs \ {v₁} = A ∪ {v₂} ∪ (Δ.Vs \ Y) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hx1⟩
      by_cases hxY : x ∈ Y
      · rw [eY] at hxY
        simp only [Finset.mem_union, Finset.mem_singleton] at hxY
        rcases hxY with (h | h) | h
        · exact Or.inl (Or.inl h)
        · exact absurd h hx1
        · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨hx, hxY⟩
    · rintro ((hx | rfl) | ⟨hx, hxY⟩)
      · exact ⟨hAV hx, fun h ↦ hv₁A (h ▸ hx)⟩
      · exact ⟨hYV hv₂Y, Ne.symm hv⟩
      · exact ⟨hx, fun h ↦ hxY (h ▸ hv₁Y)⟩
  have e₂ : Δ.Vs \ {v₂} = A ∪ {v₁} ∪ (Δ.Vs \ Y) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hx2⟩
      by_cases hxY : x ∈ Y
      · rw [eY] at hxY
        simp only [Finset.mem_union, Finset.mem_singleton] at hxY
        rcases hxY with (h | h) | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact absurd h hx2
      · exact Or.inr ⟨hx, hxY⟩
    · rintro ((hx | rfl) | ⟨hx, hxY⟩)
      · exact ⟨hAV hx, fun h ↦ hv₂A (h ▸ hx)⟩
      · exact ⟨hYV hv₁Y, hv⟩
      · exact ⟨hx, fun h ↦ hxY (h ▸ hv₂Y)⟩
  have eA : Δ.Vs \ A = {v₁} ∪ {v₂} ∪ (Δ.Vs \ Y) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxA⟩
      by_cases hxY : x ∈ Y
      · have : x ∈ Y \ A := Finset.mem_sdiff.mpr ⟨hxY, hxA⟩
        rw [hK, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨hx, hxY⟩
    · rintro ((rfl | rfl) | ⟨hx, hxY⟩)
      · exact ⟨hYV hv₁Y, hv₁A⟩
      · exact ⟨hYV hv₂Y, hv₂A⟩
      · exact ⟨hx, fun h ↦ hxY (hAY h)⟩
  -- disjointness
  have dA1 : Disjoint A {v₁} := Finset.disjoint_singleton_right.mpr hv₁A
  have dA2 : Disjoint A {v₂} := Finset.disjoint_singleton_right.mpr hv₂A
  have d12 : Disjoint ({v₁} : Finset ℕ) {v₂} := Finset.disjoint_singleton.mpr hv
  have dAc : Disjoint A (Δ.Vs \ Y) := by
    rw [Finset.disjoint_left]; intro x hx hx'; exact (Finset.mem_sdiff.mp hx').2 (hAY hx)
  have d1c : Disjoint ({v₁} : Finset ℕ) (Δ.Vs \ Y) := by
    rw [Finset.disjoint_singleton_left]; intro h; exact (Finset.mem_sdiff.mp h).2 hv₁Y
  have d2c : Disjoint ({v₂} : Finset ℕ) (Δ.Vs \ Y) := by
    rw [Finset.disjoint_singleton_left]; intro h; exact (Finset.mem_sdiff.mp h).2 hv₂Y
  -- the counts
  have deg₁ : (Δ.bd {v₁}).card = (Δ.between {v₁} A).card + (Δ.between {v₁} {v₂}).card +
      (Δ.between {v₁} (Δ.Vs \ Y)).card :=
    card_bd_eq_three hcl e₁ dA1.symm d12 d1c dA2 dAc d2c
  have deg₂ : (Δ.bd {v₂}).card = (Δ.between {v₂} A).card + (Δ.between {v₂} {v₁}).card +
      (Δ.between {v₂} (Δ.Vs \ Y)).card :=
    card_bd_eq_three hcl e₂ dA2.symm d12.symm d2c dA1 dAc d1c
  have bdA : (Δ.bd A).card = (Δ.between A {v₁}).card + (Δ.between A {v₂}).card +
      (Δ.between A (Δ.Vs \ Y)).card :=
    card_bd_eq_three hcl eA dA1 dA2 dAc d12 d1c d2c
  have bdY : (Δ.bd Y).card = (Δ.between A (Δ.Vs \ Y)).card +
      (Δ.between {v₁} (Δ.Vs \ Y)).card + (Δ.between {v₂} (Δ.Vs \ Y)).card := by
    have h1 := card_between_union_right (Γ := Δ) (X := Δ.Vs \ Y) (Z := A ∪ {v₁}) (Z' := {v₂})
      (Finset.disjoint_union_right.mpr ⟨dAc.symm, d1c.symm⟩) d2c.symm
      (Finset.disjoint_union_left.mpr ⟨dA2, d12⟩)
    have h2 := card_between_union_right (Γ := Δ) (X := Δ.Vs \ Y) (Z := A) (Z' := {v₁})
      dAc.symm d1c.symm dA1
    rw [← eY] at h1
    rw [bd_eq_between hcl, between_comm, h1, h2, between_comm (Δ.Vs \ Y) A,
      between_comm (Δ.Vs \ Y) {v₁}, between_comm (Δ.Vs \ Y) {v₂}]
  have hc : (Δ.bd A ∩ Δ.bd Y).card = (Δ.between A (Δ.Vs \ Y)).card := by
    rw [bd_inter_bd_eq_between hcl hAY]
  have hd₁ : (Δ.bd {v₁}).card = 3 := by
    rw [bd_singleton hg hcl (hYV hv₁Y), card_edgesAt hg hcl (hYV hv₁Y), hcub _ (hYV hv₁Y)]
  have hd₂ : (Δ.bd {v₂}).card = 3 := by
    rw [bd_singleton hg hcl (hYV hv₂Y), card_edgesAt hg hcl (hYV hv₂Y), hcub _ (hYV hv₂Y)]
  have hs₁ : (Δ.between {v₁} (Δ.Vs \ Y)).card ≤ 1 :=
    (card_between_singleton_le hv₁Y).trans (hind v₁)
  have hs₂ : (Δ.between {v₂} (Δ.Vs \ Y)).card ≤ 1 :=
    (card_between_singleton_le hv₂Y).trans (hind v₂)
  have ht : (Δ.between {v₁} {v₂}).card ≤ 1 := card_between_singletons_le hg (hYV hv₁Y) hv
  have hcle : (Δ.bd A ∩ Δ.bd Y).card ≤ 4 := by
    rw [← hA.2.1]; exact Finset.card_le_card Finset.inter_subset_left
  have hc4' : (Δ.bd A ∩ Δ.bd Y).card ≠ 4 := by
    intro h4
    have hsub : Δ.bd A ⊆ Δ.bd Y := by
      have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := Δ.bd A)
        (s₂ := Δ.bd Y)) (by rw [h4, hA.2.1])
      intro e he
      rw [← this] at he
      exact (Finset.mem_inter.mp he).2
    have hcard0 := card_bd_sdiff hcl hAY hYV hA.2.1 hY.2.1
    rw [Finset.inter_eq_left.mpr hsub, hA.2.1] at hcard0
    have hK0 : (Δ.bd (Y \ A)).card = 0 := by omega
    have hKV : Y \ A ⊆ Δ.Vs := Finset.sdiff_subset.trans hYV
    have hKne : (Y \ A).Nonempty := ⟨v₁, hv₁⟩
    by_cases hKc : Δ.HasCycle (Y \ A)
    · have hcompl : Δ.HasCycle (Δ.Vs \ (Y \ A)) := by
        apply hA.2.2.1.mono
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨hAV hv, fun h ↦ (Finset.mem_sdiff.mp h).2 hv⟩
      have := hc4 _ hKV hKc hcompl
      omega
    · have h1 := card_add_two_le_card_bd hcub hKV hKne hKc
      have h2 := Finset.card_pos.mpr hKne
      omega
  have hA4 := hA.2.1
  have hY4 := hY.2.1
  rw [between_comm {v₁} A] at deg₁
  rw [between_comm {v₂} A, between_comm {v₂} {v₁}] at deg₂
  refine ⟨hAY, v₁, v₂, hv, hK, ?_, ?_, ?_⟩ <;> omega

/-- `Y \ A` cannot be a single vertex. -/
theorem not_singleton_sdiff {A Y : Finset ℕ} (hA : Δ.CycSep A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    {v : ℕ} (hK : Y \ A = {v}) (_hc3 : (Δ.bd A ∩ Δ.bd Y).card ≠ 3) : False := by
  have hYV := hY.1
  have hAV := hA.1
  have hv₁ : v ∈ Y \ A := by rw [hK]; exact Finset.mem_singleton_self _
  have hvY := (Finset.mem_sdiff.mp hv₁).1
  have hvA := (Finset.mem_sdiff.mp hv₁).2
  have hind := CycSep.independent hcl hcub hg hc4 hY
  have eY : Y = A ∪ {v} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · have : x ∈ Y \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
        rw [hK, Finset.mem_singleton] at this
        exact Or.inr this
    · rintro (hx | rfl)
      · exact hAY hx
      · exact hvY
  have eA : Δ.Vs \ A = {v} ∪ (Δ.Vs \ Y) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxA⟩
      by_cases hxY : x ∈ Y
      · have : x ∈ Y \ A := Finset.mem_sdiff.mpr ⟨hxY, hxA⟩
        rw [hK, Finset.mem_singleton] at this
        exact Or.inl this
      · exact Or.inr ⟨hx, hxY⟩
    · rintro (rfl | ⟨hx, hxY⟩)
      · exact ⟨hYV hvY, hvA⟩
      · exact ⟨hx, fun h ↦ hxY (hAY h)⟩
  have ev : Δ.Vs \ {v} = A ∪ (Δ.Vs \ Y) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxv⟩
      by_cases hxY : x ∈ Y
      · rw [eY, Finset.mem_union, Finset.mem_singleton] at hxY
        exact Or.inl (hxY.resolve_right hxv)
      · exact Or.inr ⟨hx, hxY⟩
    · rintro (hx | ⟨hx, hxY⟩)
      · exact ⟨hAV hx, fun h ↦ hvA (h ▸ hx)⟩
      · exact ⟨hx, fun h ↦ hxY (h ▸ hvY)⟩
  have dAv : Disjoint A {v} := Finset.disjoint_singleton_right.mpr hvA
  have dAc : Disjoint A (Δ.Vs \ Y) := by
    rw [Finset.disjoint_left]; intro x hx hx'; exact (Finset.mem_sdiff.mp hx').2 (hAY hx)
  have dvc : Disjoint ({v} : Finset ℕ) (Δ.Vs \ Y) := by
    rw [Finset.disjoint_singleton_left]; intro h; exact (Finset.mem_sdiff.mp h).2 hvY
  have degv : (Δ.bd {v}).card = (Δ.between {v} A).card + (Δ.between {v} (Δ.Vs \ Y)).card := by
    rw [bd_eq_between hcl, ev, card_between_union_right dAv.symm dvc dAc]
  have bdA : (Δ.bd A).card = (Δ.between A {v}).card + (Δ.between A (Δ.Vs \ Y)).card := by
    rw [bd_eq_between hcl, eA, card_between_union_right dAv dAc dvc]
  have bdY : (Δ.bd Y).card = (Δ.between A (Δ.Vs \ Y)).card + (Δ.between {v} (Δ.Vs \ Y)).card := by
    have h1 := card_between_union_right (Γ := Δ) (X := Δ.Vs \ Y) (Z := A) (Z' := {v})
      dAc.symm dvc.symm dAv
    rw [← eY] at h1
    rw [bd_eq_between hcl, between_comm, h1, between_comm (Δ.Vs \ Y) A,
      between_comm (Δ.Vs \ Y) {v}]
  have hc : (Δ.bd A ∩ Δ.bd Y).card = (Δ.between A (Δ.Vs \ Y)).card := by
    rw [bd_inter_bd_eq_between hcl hAY]
  have hd : (Δ.bd {v}).card = 3 := by
    rw [bd_singleton hg hcl (hYV hvY), card_edgesAt hg hcl (hYV hvY), hcub _ (hYV hvY)]
  have hs : (Δ.between {v} (Δ.Vs \ Y)).card ≤ 1 :=
    (card_between_singleton_le hvY).trans (hind v)
  have hA4 := hA.2.1
  have hY4 := hY.2.1
  rw [between_comm {v} A] at degv
  omega

end Counting

section Heredity

variable {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ)
include hG hΔ

/-- The number of common boundary edges of an atom and a non-atomic shore containing it is at
most two. -/
theorem card_inter_le_two {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) : (Δ.bd A ∩ Δ.bd Y).card ≤ 2 := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  have hc4 := hG.cyc4 Δ hΔ
  have h3 := IsAtom.card_inter_ne_three hcl hcub hg hc4 hA hY
  have hle : (Δ.bd A ∩ Δ.bd Y).card ≤ 4 := by
    rw [← hA.1.2.1]; exact Finset.card_le_card Finset.inter_subset_left
  have h4 : (Δ.bd A ∩ Δ.bd Y).card ≠ 4 := by
    intro h4
    have hsub : Δ.bd A ⊆ Δ.bd Y := by
      have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := Δ.bd A)
        (s₂ := Δ.bd Y)) (by rw [h4, hA.1.2.1])
      intro e he
      rw [← this] at he
      exact (Finset.mem_inter.mp he).2
    have hcard0 := card_bd_sdiff hcl hAY hY.1 hA.1.2.1 hY.2.1
    rw [Finset.inter_eq_left.mpr hsub, hA.1.2.1] at hcard0
    have hK0 : (Δ.bd (Y \ A)).card = 0 := by omega
    have hKne : (Y \ A).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h) hAY)
    have hKV : Y \ A ⊆ Δ.Vs := Finset.sdiff_subset.trans hY.1
    by_cases hKc : Δ.HasCycle (Y \ A)
    · have hcompl : Δ.HasCycle (Δ.Vs \ (Y \ A)) := by
        apply hA.1.2.2.1.mono
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨hA.1.1 hv, fun h ↦ (Finset.mem_sdiff.mp h).2 hv⟩
      have := hc4 _ hKV hKc hcompl
      omega
    · have h1 := card_add_two_le_card_bd hcub hKV hKne hKc
      have h2 := Finset.card_pos.mpr hKne
      omega
  omega

omit hG hΔ in
/-- Summing over the four boundary positions grouped by couples. -/
theorem sum_couples (m : Fin 3) (g : Fin 4 → ℕ) :
    ∑ k, g k = g 0 + g (pairing m 0) + g (other m) + g (pairing m (other m)) := by
  rw [Fin.sum_univ_four]
  fin_cases m <;> simp [pairing, other] <;> ring

omit hG hΔ in
/-- The common boundary edges counted by positions of the `Y`-pole. -/
theorem card_inter_eq_card_filter {A Y : Finset ℕ} (hPY : (Δ.pole Y).IsPole4) :
    (Δ.bd A ∩ Δ.bd Y).card = (Finset.univ.filter fun k : Fin 4 ↦ bdEmb hPY k ∈ Δ.bd A).card := by
  have : Δ.bd A ∩ Δ.bd Y = (Finset.univ.filter fun k : Fin 4 ↦ bdEmb hPY k ∈ Δ.bd A).image
      (bdEmb hPY) := by
    ext e
    rw [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨hA, hY⟩
      obtain ⟨k, rfl⟩ := exists_bdEmb_eq hPY (dangling_pole Y ▸ hY)
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Finset.mem_filter.mp hk).2, dangling_pole Y ▸ bdEmb_mem hPY k⟩
  rw [this, Finset.card_image_of_injective _ (bdEmb_injective hPY)]

/-- **Chladný–Škoviera, Proposition 9.3.**  The atom is a cycle-separating shore of the factor
of a non-associated cut containing it. -/
theorem cycSep_in_factor {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hnq : ¬ Δ.IsQuasiatomic A Y) : (factorOf Δ Y).CycSep A := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  have hc4 := hG.cyc4 Δ hΔ
  have hYV := hY.1
  have hc3 := IsAtom.card_inter_ne_three hcl hcub hg hc4 hA hY
  have hcle2 := card_inter_le_two hG hΔ hA hY hAY hne
  have hKne : (Y \ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h) hAY)
  have hcycA := hA.1.2.2.1
  have hA4 := hA.1.2.1
  -- the small cases of `Y \ A` are excluded
  have hsmall : ¬ (Y \ A).card ≤ 2 := by
    intro hle
    have hpos := Finset.card_pos.mpr hKne
    have h12 : (Y \ A).card = 1 ∨ (Y \ A).card = 2 := by omega
    rcases h12 with h1 | h2
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
      exact not_singleton_sdiff hcl hcub hg hc4 hA.1 hY hAY hv hc3
    · obtain ⟨v₁, v₂, hv, hK⟩ := Finset.card_eq_two.mp h2
      exact hnq (quasiatomic_of_pair hcl hcub hg hc4 hA.1 hY hAY hv hK hc3 hne)
  obtain ⟨hPY, hPYc, m, hcase⟩ := factor_cases hG hΔ hY
  rcases hcase with ⟨hiso, hhet, hfac, hPmem, -, -⟩ | ⟨hhet, hiso, hfac, hPmem, -, -⟩
  · -- cap case
    rw [hfac]
    set Q := cap hPY m with hQ
    have hQcl := hG.closed Q hPmem
    have hQcub := hG.cubic Q hPmem
    have hAQ : A ⊆ Q.Vs := fun v hv ↦ mem_cap_Vs_of_old hPY m (hAY hv)
    have hbd : (Q.bd A).card = 4 := by rw [hQ, cap_bd_old hPY m hcl hYV hAY, hA4]
    have hcyc : Q.HasCycle A := cap_hasCycle_of hPY m hAY hYV hcycA
    refine ⟨hAQ, hbd, hcyc, ?_⟩
    by_contra hno
    have hne' : (Q.Vs \ A).Nonempty := by
      obtain ⟨v, hv⟩ := hKne
      exact ⟨v, Finset.mem_sdiff.mpr ⟨mem_cap_Vs_of_old hPY m (Finset.mem_sdiff.mp hv).1,
        (Finset.mem_sdiff.mp hv).2⟩⟩
    have h1 := card_add_two_le_card_bd hQcub Finset.sdiff_subset hne' hno
    rw [bd_compl hQcl, hbd] at h1
    -- `Q.Vs \ A` contains `Y \ A` and the two fresh vertices
    have hsub : insert (freshV (Δ.pole Y)) (insert (freshV (Δ.pole Y) + 1) (Y \ A)) ⊆ Q.Vs \ A := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rw [Finset.mem_sdiff]
      rcases hv with rfl | rfl | hv
      · exact ⟨freshV_mem_cap hPY m, fun h ↦ freshV_notMem (P := Δ.pole Y) (hAY h)⟩
      · exact ⟨freshV_succ_mem_cap hPY m, fun h ↦ freshV_succ_notMem (P := Δ.pole Y) (hAY h)⟩
      · exact ⟨mem_cap_Vs_of_old hPY m (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] at hcard
    · omega
    · intro h
      exact freshV_succ_notMem (P := Δ.pole Y) (Finset.mem_sdiff.mp h).1
    · rw [Finset.mem_insert, not_or]
      exact ⟨by omega, fun h ↦ freshV_notMem (P := Δ.pole Y) (Finset.mem_sdiff.mp h).1⟩
  · -- join case
    rw [hfac]
    set Q := join hPY m with hQ
    have hQcl := hG.closed Q hPmem
    have hQcub := hG.cubic Q hPmem
    have hAQ : A ⊆ Q.Vs := by rw [hQ, join_Vs, pole_Vs]; exact hAY
    have hcyc : Q.HasCycle A := join_hasCycle_of hPY m hAY hYV hcycA
    -- no couple of the `Y`-cut lies inside `∂A`
    have hnocouple : ∀ k, bdEmb hPY k ∈ Δ.bd A → bdEmb hPY (pairing m k) ∈ Δ.bd A → False := by
      intro k h₁ h₂
      have h2 : 2 ≤ (Δ.bd A ∩ Δ.bd Y).card := by
        have : ({bdEmb hPY k, bdEmb hPY (pairing m k)} : Finset ℕ) ⊆ Δ.bd A ∩ Δ.bd Y := by
          intro e he
          rw [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨h₁, dangling_pole Y ▸ bdEmb_mem hPY _⟩
          · exact Finset.mem_inter.mpr ⟨h₂, dangling_pole Y ▸ bdEmb_mem hPY _⟩
        have := Finset.card_le_card this
        rw [Finset.card_pair (fun h ↦ pairing_ne m k (bdEmb_injective hPY h).symm)] at this
        exact this
      exact no_couple_in_cut hG hΔ hA.1 hY hAY hne hPY h₁ h₂ (by omega) (Or.inr hhet) rfl
    -- the boundary of `A` in the join
    have hbd : (Q.bd A).card = 4 := by
      rw [hQ, join_bd_old hPY m hAY hYV]
      have hf₁ : freshE (Δ.pole Y) ∉ Δ.bd A := by
        intro h
        refine freshE_notMem (P := Δ.pole Y) ?_
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset A h) (hAY hi)
      have hf₂ : freshE (Δ.pole Y) + 1 ∉ Δ.bd A := by
        intro h
        refine freshE_succ_notMem (P := Δ.pole Y) ?_
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side h
        exact mem_edgesIn_or_bd (bd_subset A h) (hAY hi)
      rw [Finset.card_union_of_disjoint]
      · have e1 : ((Δ.bd A).filter fun e ↦ e ∉ Δ.bd Y).card = 4 - (Δ.bd A ∩ Δ.bd Y).card := by
          have := Finset.card_sdiff_add_card_inter (Δ.bd A) (Δ.bd Y)
          have e : (Δ.bd A).filter (fun e ↦ e ∉ Δ.bd Y) = Δ.bd A \ Δ.bd Y := by
            ext e; simp [Finset.mem_filter, Finset.mem_sdiff]
          rw [e]
          omega
        -- the crossing new edges are counted by the common boundary edges
        have hcross : ∀ k, (k = 0 ∨ k = other m) →
            ((¬ ((join hPY m).ends (newHalf (P := Δ.pole Y) m k).1 0 ∈ A ↔
              (join hPY m).ends (newHalf (P := Δ.pole Y) m k).1 1 ∈ A)) ↔
            (bdEmb hPY k ∈ Δ.bd A ∨ bdEmb hPY (pairing m k) ∈ Δ.bd A)) := by
          intro k hk
          have h0 : (join hPY m).ends (newHalf (P := Δ.pole Y) m k).1 0 =
              innerEnd hPY (bdEmb hPY k) := by
            have := join_ends_newHalf hPY m k
            have hk0 : (newHalf (P := Δ.pole Y) m k).2 = 0 := by
              rcases hk with rfl | rfl
              · rw [newHalf_zero]
              · rw [newHalf_other]
            rw [hk0] at this
            exact this
          have h1 : (join hPY m).ends (newHalf (P := Δ.pole Y) m k).1 1 =
              innerEnd hPY (bdEmb hPY (pairing m k)) := by
            have := join_ends_newHalf hPY m (pairing m k)
            have hk1 : (newHalf (P := Δ.pole Y) m (pairing m k)).1 =
                (newHalf (P := Δ.pole Y) m k).1 := (newHalf_pairing (Q := Δ.pole Y) m k).1
            have hk2 : (newHalf (P := Δ.pole Y) m (pairing m k)).2 = 1 := by
              rw [(newHalf_pairing (Q := Δ.pole Y) m k).2]
              rcases hk with rfl | rfl
              · rw [newHalf_zero]; exact Iso.rev_zero'
              · rw [newHalf_other]; exact Iso.rev_zero'
            rw [hk1, hk2] at this
            exact this
          rw [h0, h1]
          have hd := bdEmb_mem hPY k
          have hd' := bdEmb_mem hPY (pairing m k)
          constructor
          · intro h
            by_contra hc
            rw [not_or] at hc
            exact h ⟨fun h' ↦ absurd h' (innerEnd_notMem_of_notMem hAY hPY hc.1 hd),
              fun h' ↦ absurd h' (innerEnd_notMem_of_notMem hAY hPY hc.2 hd')⟩
          · rintro (h | h) hiff
            · have := innerEnd_mem_of_mem_inter hAY hPY h hd
              have h2 := hiff.mp this
              by_cases hc : bdEmb hPY (pairing m k) ∈ Δ.bd A
              · exact hnocouple k h hc
              · exact innerEnd_notMem_of_notMem hAY hPY hc hd' h2
            · have := innerEnd_mem_of_mem_inter hAY hPY h hd'
              have h2 := hiff.mpr this
              by_cases hc : bdEmb hPY k ∈ Δ.bd A
              · exact hnocouple k hc h
              · exact innerEnd_notMem_of_notMem hAY hPY hc hd h2
        have e2 : (({freshE (Δ.pole Y), freshE (Δ.pole Y) + 1} : Finset ℕ).filter fun f ↦
            ¬ ((join hPY m).ends f 0 ∈ A ↔ (join hPY m).ends f 1 ∈ A)).card =
              (Δ.bd A ∩ Δ.bd Y).card := by
          rw [card_inter_eq_card_filter hPY, Finset.card_filter, Finset.card_filter,
            sum_couples m, Finset.sum_pair (by omega)]
          have c₁ := hcross 0 (Or.inl rfl)
          have c₂ := hcross (other m) (Or.inr rfl)
          rw [newHalf_zero_fst] at c₁
          rw [newHalf_other_fst] at c₂
          have n₁ := hnocouple 0
          have n₂ := hnocouple (other m)
          by_cases a0 : bdEmb hPY 0 ∈ Δ.bd A <;> by_cases a1 : bdEmb hPY (pairing m 0) ∈ Δ.bd A <;>
            by_cases a2 : bdEmb hPY (other m) ∈ Δ.bd A <;>
            by_cases a3 : bdEmb hPY (pairing m (other m)) ∈ Δ.bd A <;>
            simp only [a0, a1, a2, a3, or_true, or_false, c₁, c₂, if_true, if_false] <;>
            first | rfl | exact absurd a1 (n₁ a0) | exact absurd a3 (n₂ a2)
        omega
      · rw [Finset.disjoint_left]
        intro e h1 h2
        rw [Finset.mem_filter] at h1 h2
        rw [Finset.mem_insert, Finset.mem_singleton] at h2
        rcases h2.1 with rfl | rfl
        · exact hf₁ h1.1
        · exact hf₂ h1.1
    refine ⟨hAQ, hbd, hcyc, ?_⟩
    by_contra hno
    have hcompl : Q.Vs \ A = Y \ A := by rw [hQ, join_Vs, pole_Vs]
    have h1 := card_add_two_le_card_bd hQcub Finset.sdiff_subset (by rw [hcompl]; exact hKne) hno
    rw [bd_compl hQcl, hbd, hcompl] at h1
    exact hsmall (by omega)

end Heredity

end FinGraph
end GraphPuzzles
