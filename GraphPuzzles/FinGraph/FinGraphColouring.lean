import GraphPuzzles.FinGraph.FinGraphCycles

/-!
# Poles, colourings, and the parity lemma

The pole of a graph on a vertex set `X` keeps the edges inside `X` and the boundary edges, which
become dangling.  A colouring assigns nonzero colours to all edges so that the half-edges at each
vertex receive distinct colours.  In a cubic pole every vertex then sees each of the three
colours exactly once, and counting half-edges of one colour gives the parity lemma: the number
of dangling edges of each colour is congruent to the number of vertices modulo two.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable (Γ : FinGraph)

/-- The dangling edges: edges with an end outside the vertex set. -/
def dangling : Finset ℕ := Γ.Es.filter fun e ↦ ∃ i, Γ.ends e i ∉ Γ.Vs

/-- The pole on `X`: vertices `X`, edges inside `X` together with the boundary edges. -/
def pole (X : Finset ℕ) : FinGraph := ⟨X, Γ.edgesIn X ∪ Γ.bd X, Γ.ends⟩

/-- A proper three-edge-colouring: nonzero colours, distinct at every vertex. -/
def IsColouring (c : ℕ → Color) : Prop :=
  (∀ e ∈ Γ.Es, c e ≠ 0) ∧
    ∀ v ∈ Γ.Vs, ∀ h₁ ∈ Γ.halfEdgesIn Γ.Es v, ∀ h₂ ∈ Γ.halfEdgesIn Γ.Es v,
      c h₁.1 = c h₂.1 → h₁ = h₂

/-- Admits a proper three-edge-colouring. -/
def Colourable : Prop := ∃ c, Γ.IsColouring c

/-- Girth at least five: every nonempty even edge set has at least five edges.  This excludes
loops and parallel edges as well. -/
def Girth5 : Prop := ∀ F ⊆ Γ.Es, F.Nonempty → Γ.IsEven F → 5 ≤ F.card

/-- Cyclically four-edge-connected: a cut separating two cyclic sides has at least four edges. -/
def Cyc4Conn : Prop :=
  ∀ X ⊆ Γ.Vs, Γ.HasCycle X → Γ.HasCycle (Γ.Vs \ X) → 4 ≤ (Γ.bd X).card

/-- A cycle-separating four-edge-cut, given by its shore. -/
def CycSep (X : Finset ℕ) : Prop :=
  X ⊆ Γ.Vs ∧ (Γ.bd X).card = 4 ∧ Γ.HasCycle X ∧ Γ.HasCycle (Γ.Vs \ X)

/-- A cubic multipole with four dangling edges, every edge having an end at a vertex. -/
structure IsPole4 : Prop where
  cubic : Γ.IsCubic
  card_dangling : Γ.dangling.card = 4
  has_inner : ∀ e ∈ Γ.Es, ∃ i, Γ.ends e i ∈ Γ.Vs

variable {Γ}

theorem mem_dangling {e : ℕ} : e ∈ Γ.dangling ↔ e ∈ Γ.Es ∧ ∃ i, Γ.ends e i ∉ Γ.Vs := by
  simp [dangling]

@[simp] theorem pole_Vs (X : Finset ℕ) : (Γ.pole X).Vs = X := rfl
@[simp] theorem pole_Es (X : Finset ℕ) : (Γ.pole X).Es = Γ.edgesIn X ∪ Γ.bd X := rfl
@[simp] theorem pole_ends (X : Finset ℕ) : (Γ.pole X).ends = Γ.ends := rfl

theorem pole_degIn (X F : Finset ℕ) (v : ℕ) : (Γ.pole X).degIn F v = Γ.degIn F v := rfl

theorem pole_edgesIn (X Y : Finset ℕ) (hYX : Y ⊆ X) : (Γ.pole X).edgesIn Y = Γ.edgesIn Y := by
  ext e
  simp only [mem_edgesIn, pole_Es, Finset.mem_union, mem_bd, pole_ends]
  constructor
  · rintro ⟨h, hY⟩
    exact ⟨h.elim (fun h ↦ h.1) (fun h ↦ h.1), hY⟩
  · rintro ⟨he, hY⟩
    exact ⟨Or.inl ⟨he, fun i ↦ hYX (hY i)⟩, hY⟩

theorem pole_hasCycle {X Y : Finset ℕ} (hX : X ⊆ Γ.Vs) (hYX : Y ⊆ X) :
    (Γ.pole X).HasCycle Y ↔ Γ.HasCycle Y := by
  unfold HasCycle
  rw [pole_edgesIn X Y hYX]
  have hYV : Y ⊆ Γ.Vs := hYX.trans hX
  constructor
  · rintro ⟨F, hF, hne, hev⟩
    refine ⟨F, hF, hne, ?_⟩
    rw [isEven_iff_of_subset hYV hF]
    rw [isEven_iff_of_subset (Γ := Γ.pole X) (Y := Y) hYX
      (by rw [pole_edgesIn X Y hYX]; exact hF)] at hev
    exact hev
  · rintro ⟨F, hF, hne, hev⟩
    refine ⟨F, hF, hne, ?_⟩
    rw [isEven_iff_of_subset (Γ := Γ.pole X) (Y := Y) hYX
      (by rw [pole_edgesIn X Y hYX]; exact hF)]
    rw [isEven_iff_of_subset hYV hF] at hev
    exact hev

theorem dangling_pole (X : Finset ℕ) : (Γ.pole X).dangling = Γ.bd X := by
  ext e
  simp only [mem_dangling, pole_Es, Finset.mem_union, pole_Vs, pole_ends, mem_edgesIn, mem_bd]
  constructor
  · rintro ⟨h, i, hi⟩
    rcases h with h | h
    · exact absurd (h.2 i) hi
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    obtain ⟨i, _, hi⟩ := bd_side (mem_bd.mpr h)
    exact ⟨Fin.rev i, hi⟩

theorem pole_deg (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs) {v : ℕ} (hv : v ∈ X) :
    (Γ.pole X).deg v = 3 := by
  unfold deg
  rw [pole_Es, pole_degIn, degIn_union_of_disjoint (disjoint_edgesIn_bd X),
    degIn_edgesIn_add_bd hv]
  exact hcub v (hX hv)

theorem pole_isCubic (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs) : (Γ.pole X).IsCubic :=
  fun _ hv ↦ pole_deg hcub hX hv

theorem pole_isPole4 (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs) (h4 : (Γ.bd X).card = 4) :
    (Γ.pole X).IsPole4 where
  cubic := pole_isCubic hcub hX
  card_dangling := by rw [dangling_pole]; exact h4
  has_inner := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he
    rcases he with he | he
    · exact ⟨0, (mem_edgesIn.mp he).2 0⟩
    · obtain ⟨i, hi, _⟩ := bd_side he
      exact ⟨i, hi⟩

/-- In a pole every dangling edge has exactly one end at a vertex: the inner end. -/
theorem IsPole4.exists_unique_inner (hP : Γ.IsPole4) {e : ℕ} (he : e ∈ Γ.dangling) :
    ∃ i, Γ.ends e i ∈ Γ.Vs ∧ Γ.ends e (Fin.rev i) ∉ Γ.Vs := by
  rw [mem_dangling] at he
  obtain ⟨heE, j, hj⟩ := he
  obtain ⟨i, hi⟩ := hP.has_inner e heE
  refine ⟨i, hi, ?_⟩
  have : j = Fin.rev i := by
    by_contra h
    have : j = i := by
      have hi0 : i = 0 ∨ i = 1 := by omega
      have hj0 : j = 0 ∨ j = 1 := by omega
      rcases hi0 with rfl | rfl <;> rcases hj0 with rfl | rfl <;> first | rfl | exact absurd rfl h
    exact hj (this ▸ hi)
  exact this ▸ hj

section Colouring

variable {c : ℕ → Color}

/-- The three nonzero colours. -/
theorem card_nonzero_colors : Fintype.card {κ : Color // κ ≠ 0} = 3 := by decide

/-- In a cubic colouring the half-edges at a vertex are in bijection with the nonzero colours. -/
theorem IsColouring.exists_halfEdge (hcub : Γ.IsCubic) (hc : Γ.IsColouring c) {v : ℕ}
    (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0) : ∃ h ∈ Γ.halfEdgesIn Γ.Es v, c h.1 = κ := by
  classical
  let f : Γ.halfEdgesIn Γ.Es v → {κ : Color // κ ≠ 0} :=
    fun h ↦ ⟨c h.1.1, hc.1 h.1.1 (mem_halfEdgesIn.mp h.2).1⟩
  have hinj : Function.Injective f := by
    intro h₁ h₂ heq
    apply Subtype.ext
    exact hc.2 v hv h₁.1 h₁.2 h₂.1 h₂.2 (congrArg Subtype.val heq)
  have hcard : Fintype.card (Γ.halfEdgesIn Γ.Es v) = Fintype.card {κ : Color // κ ≠ 0} := by
    rw [card_nonzero_colors, Fintype.card_coe]
    exact hcub v hv
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  obtain ⟨h, hh⟩ := hsurj.2 ⟨κ, hκ⟩
  exact ⟨h.1, h.2, congrArg Subtype.val hh⟩

theorem IsColouring.unique_halfEdge (hc : Γ.IsColouring c) {v : ℕ} (hv : v ∈ Γ.Vs)
    {h₁ h₂ : ℕ × Fin 2} (h₁m : h₁ ∈ Γ.halfEdgesIn Γ.Es v) (h₂m : h₂ ∈ Γ.halfEdgesIn Γ.Es v)
    (heq : c h₁.1 = c h₂.1) : h₁ = h₂ :=
  hc.2 v hv h₁ h₁m h₂ h₂m heq

/-- No loops: an edge with both ends at a vertex would repeat a colour there. -/
theorem IsColouring.ends_ne (hc : Γ.IsColouring c) {e : ℕ} (he : e ∈ Γ.Es)
    (h0 : Γ.ends e 0 ∈ Γ.Vs) : Γ.ends e 0 ≠ Γ.ends e 1 := by
  intro heq
  have h := hc.2 (Γ.ends e 0) h0 (e, 0) (mem_halfEdgesIn.mpr ⟨he, rfl⟩) (e, 1)
    (mem_halfEdgesIn.mpr ⟨he, heq.symm⟩) rfl
  simp at h

/-- The degree of a vertex inside the edges of one colour is one. -/
theorem IsColouring.degIn_color (hcub : Γ.IsCubic) (hc : Γ.IsColouring c) {v : ℕ}
    (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0) :
    Γ.degIn (Γ.Es.filter fun e ↦ c e = κ) v = 1 := by
  obtain ⟨h, hh, hκh⟩ := hc.exists_halfEdge hcub hv hκ
  unfold degIn
  rw [Finset.card_eq_one]
  refine ⟨h, ?_⟩
  ext h'
  simp only [mem_halfEdgesIn, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨he, hκ'⟩, hv'⟩
    exact hc.unique_halfEdge hv (mem_halfEdgesIn.mpr ⟨he, hv'⟩) hh (hκ'.trans hκh.symm)
  · rintro rfl
    have := mem_halfEdgesIn.mp hh
    exact ⟨⟨this.1, hκh⟩, this.2⟩

/-- **Parity lemma.**  The number of dangling edges of a colour has the parity of the number of
vertices. -/
theorem IsColouring.card_dangling_color (hP : Γ.IsPole4) (hc : Γ.IsColouring c) {κ : Color}
    (hκ : κ ≠ 0) :
    (Γ.dangling.filter fun e ↦ c e = κ).card % 2 = Γ.Vs.card % 2 := by
  set F := Γ.Es.filter fun e ↦ c e = κ with hF
  have h1 : ∑ v ∈ Γ.Vs, Γ.degIn F v = Γ.Vs.card := by
    rw [Finset.sum_congr rfl (fun v hv ↦ hc.degIn_color hP.cubic hv hκ)]
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
    obtain ⟨i, hi, hi'⟩ := hP.exists_unique_inner he.1
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

/-- In a colouring of a `4`-pole every colour occurs an even number of times on the dangling
edges. -/
theorem IsColouring.even_card_dangling_color (hP : Γ.IsPole4) (hc : Γ.IsColouring c) {κ : Color}
    (hκ : κ ≠ 0) : Even (Γ.dangling.filter fun e ↦ c e = κ).card := by
  have h1 := hc.card_dangling_color hP (κ := (1, 0)) (by decide)
  have h2 := hc.card_dangling_color hP (κ := (0, 1)) (by decide)
  have h3 := hc.card_dangling_color hP (κ := (1, 1)) (by decide)
  have hκ' := hc.card_dangling_color hP hκ
  have hsum : (Γ.dangling.filter fun e ↦ c e = (1, 0)).card +
      (Γ.dangling.filter fun e ↦ c e = (0, 1)).card +
      (Γ.dangling.filter fun e ↦ c e = (1, 1)).card = 4 := by
    rw [← hP.card_dangling]
    have hd : ∀ e ∈ Γ.dangling, c e = (1, 0) ∨ c e = (0, 1) ∨ c e = (1, 1) := by
      intro e he
      have hne := hc.1 e (mem_dangling.mp he).1
      revert hne
      generalize c e = x
      revert x
      decide
    rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1
      ext e
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro he
        rcases hd e he with h | h | h
        · exact Or.inl (Or.inl ⟨he, h⟩)
        · exact Or.inl (Or.inr ⟨he, h⟩)
        · exact Or.inr ⟨he, h⟩
    · rw [Finset.disjoint_left]
      intro e h1 h2
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at h1
      rw [Finset.mem_filter] at h2
      rcases h1 with h1 | h1 <;> rw [h1.2] at h2 <;> exact absurd h2.2 (by decide)
    · rw [Finset.disjoint_left]
      intro e h1 h2
      rw [Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact absurd h2.2 (by decide)
  rw [Nat.even_iff]
  omega

end Colouring

end FinGraph
end GraphPuzzles
