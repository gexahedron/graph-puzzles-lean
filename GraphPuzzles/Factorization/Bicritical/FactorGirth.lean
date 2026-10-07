import GraphPuzzles.Factorization.Bicritical.FactorGirthCombinatorics
import GraphPuzzles.Factorization.Bicritical.FactorFourCycle

/-!
# Bicritical snarks have girth at least `5`

Loops, parallel edges and triangles produce small cycle-separating cuts; a quadrilateral
would be a cycle-separating `4`-cut whose pole is neither isochromatic nor heterochromatic.
(Nedela–Škoviera, cf. Chladný–Škoviera Proposition 2.4, for graphs with at least six
vertices.)
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- The third edge at a vertex of a cubic graph without loops. -/
theorem third_edge (hcub : Γ.IsCubic) (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1) {a : ℕ}
    (ha : a ∈ Γ.Vs) {e₁ e₂ : ℕ} (he₁ : e₁ ∈ Γ.Es) (he₂ : e₂ ∈ Γ.Es) (hne : e₁ ≠ e₂)
    {i₁ i₂ : Fin 2} (hi₁ : Γ.ends e₁ i₁ = a) (hi₂ : Γ.ends e₂ i₂ = a) :
    ∃ x ∈ Γ.Es, (∃ j, Γ.ends x j = a) ∧ x ≠ e₁ ∧ x ≠ e₂ ∧
      ∀ y ∈ Γ.Es, ∀ j', Γ.ends y j' = a → y = e₁ ∨ y = e₂ ∨ y = x := by
  have hcard : (Γ.halfEdgesIn Γ.Es a).card = 3 := hcub a ha
  have hm₁ : (e₁, i₁) ∈ Γ.halfEdgesIn Γ.Es a := mem_halfEdgesIn.mpr ⟨he₁, hi₁⟩
  have hm₂ : (e₂, i₂) ∈ Γ.halfEdgesIn Γ.Es a := mem_halfEdgesIn.mpr ⟨he₂, hi₂⟩
  have hT : ({(e₁, i₁), (e₂, i₂)} : Finset (ℕ × Fin 2)) ⊆ Γ.halfEdgesIn Γ.Es a := by
    intro h hh
    rw [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> assumption
  have hne' : (e₁, i₁) ≠ (e₂, i₂) := fun h ↦ hne (congrArg Prod.fst h)
  have hlt : ({(e₁, i₁), (e₂, i₂)} : Finset (ℕ × Fin 2)).card < (Γ.halfEdgesIn Γ.Es a).card := by
    rw [Finset.card_pair hne', hcard]; omega
  obtain ⟨h, hh, hhT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_singleton] at hhT
  rw [mem_halfEdgesIn] at hh
  -- a second half-edge of `e₁` or `e₂` at `a` would be a loop
  have key : ∀ (e : ℕ) (i : Fin 2), e ∈ Γ.Es → Γ.ends e i = a → h.1 = e → h ≠ (e, i) → False := by
    intro e i he hi h1 h2
    have hj : h.2 ≠ i := fun h' ↦ h2 (Prod.ext h1 h')
    have hji : h.2 = Fin.rev i := fin2_eq_rev_of_ne hj
    have hend := hh.2
    rw [h1, hji] at hend
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rw [Iso.rev_zero'] at hend; exact hloop e he (hi.trans hend.symm)
    · rw [Iso.rev_one'] at hend; exact hloop e he (hend.trans hi.symm)
  have hx₁ : h.1 ≠ e₁ := fun h' ↦ key e₁ i₁ he₁ hi₁ h' (fun h'' ↦ hhT (Or.inl h''))
  have hx₂ : h.1 ≠ e₂ := fun h' ↦ key e₂ i₂ he₂ hi₂ h' (fun h'' ↦ hhT (Or.inr h''))
  refine ⟨h.1, hh.1, ⟨h.2, hh.2⟩, hx₁, hx₂, ?_⟩
  intro y hy j' hj'
  have hS : Γ.halfEdgesIn Γ.Es a = {h, (e₁, i₁), (e₂, i₂)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact mem_halfEdgesIn.mpr hh
      · exact hm₁
      · exact hm₂
    · rw [hcard, Finset.card_insert_of_notMem (by
        rw [Finset.mem_insert, Finset.mem_singleton]; exact hhT), Finset.card_pair hne']
  have : (y, j') ∈ Γ.halfEdgesIn Γ.Es a := mem_halfEdgesIn.mpr ⟨hy, hj'⟩
  rw [hS] at this
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
  rcases this with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
  · right; right; rw [← h1]
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)

section Girth

variable (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable) (hb : Γ.IsBicritical)
  (h6 : 6 ≤ Γ.Vs.card)
include hcl hcub hnc hb h6

/-- A bicritical snark with at least six vertices has no quadrilateral. -/
theorem IsBicritical.no_quad (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1) (hc4 : Γ.Cyc4Conn)
    (_hcycle_compl : ∀ X ⊆ Γ.Vs, (Γ.bd X).card ≤ 3 → X.card ≤ 3 → Γ.HasCycle (Γ.Vs \ X))
    (ends_mem : ∀ e ∈ Γ.Es, ∀ a b, Γ.Joins e a b → a ∈ Γ.Vs ∧ b ∈ Γ.Vs)
    (joins_in : ∀ e ∈ Γ.Es, ∀ a b, Γ.Joins e a b → ∀ X : Finset ℕ, a ∈ X → b ∈ X →
      e ∈ Γ.edgesIn X) :
    ∀ e₁ ∈ Γ.Es, ∀ e₂ ∈ Γ.Es, ∀ e₃ ∈ Γ.Es, ∀ e₄ ∈ Γ.Es,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₁ ≠ e₄ → e₂ ≠ e₃ → e₂ ≠ e₄ → e₃ ≠ e₄ →
      ∀ a b c d, a ≠ b → b ≠ c → c ≠ d → a ≠ d → a ≠ c → b ≠ d →
      Γ.Joins e₁ a b → Γ.Joins e₂ b c → Γ.Joins e₃ c d → Γ.Joins e₄ d a → False := by
  intro e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ n12 n13 n14 n23 n24 n34 a b c d hab hbc hcd had hac hbd
    j₁ j₂ j₃ j₄
  obtain ⟨haV, hbV⟩ := ends_mem e₁ he₁ a b j₁
  obtain ⟨-, hcV⟩ := ends_mem e₂ he₂ b c j₂
  obtain ⟨-, hdV⟩ := ends_mem e₃ he₃ c d j₃
  set X : Finset ℕ := {a, b, c, d} with hXdef
  have hX : X ⊆ Γ.Vs := by
    intro v hv
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hXcard : X.card = 4 := by
    rw [hXdef, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have haX : a ∈ X := by simp [hXdef]
  have hbX : b ∈ X := by simp [hXdef]
  have hcX : c ∈ X := by simp [hXdef]
  have hdX : d ∈ X := by simp [hXdef]
  set F : Finset ℕ := {e₁, e₂, e₃, e₄} with hFdef
  have hF : F ⊆ Γ.edgesIn X := by
    intro x hx
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact joins_in _ he₁ _ _ j₁ _ haX hbX
    · exact joins_in _ he₂ _ _ j₂ _ hbX hcX
    · exact joins_in _ he₃ _ _ j₃ _ hcX hdX
    · exact joins_in _ he₄ _ _ j₄ _ hdX haX
  have hev : Γ.IsEven F := by
    intro v _
    rw [hFdef, degIn_eq_sum, Finset.sum_insert (by simp [n12, n13, n14]),
      Finset.sum_insert (by simp [n23, n24]), Finset.sum_pair n34,
      endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hcd,
      endCount_of_joins j₄ had.symm]
    split_ifs <;> first | decide | omega
  have hcyc : Γ.HasCycle X := ⟨F, hF, ⟨e₁, by simp [hFdef]⟩, hev⟩
  have hFcard : F.card = 4 := by
    rw [hFdef, Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
      Finset.card_insert_of_notMem (by simp [n23, n24]), Finset.card_pair n34]
  have h3' := three_mul_card_eq hcub hX
  have hle : 4 ≤ (Γ.edgesIn X).card := by
    have := Finset.card_le_card hF; rw [hFcard] at this; exact this
  have hbd4' : (Γ.bd X).card ≤ 4 := by omega
  have hXc2 : 2 ≤ (Γ.Vs \ X).card := by
    rw [Finset.card_sdiff_of_subset hX]; omega
  have hbd4 : (Γ.bd X).card = 4 := by
    by_cases hcycc : Γ.HasCycle (Γ.Vs \ X)
    · have := hc4 X hX hcyc hcycc; omega
    · have := card_add_two_le_card_bd hcub Finset.sdiff_subset
        (Finset.card_pos.mp (by omega)) hcycc
      rw [bd_compl hcl] at this
      omega
  have hEin : Γ.edgesIn X = F := by
    symm
    apply Finset.eq_of_subset_of_card_le hF
    rw [hFcard]; omega
  -- the pendant edge at a vertex of the quadrilateral
  have pendant : ∀ (v f g : ℕ) (i j : Fin 2), v ∈ X → f ∈ F → g ∈ F → f ≠ g →
      Γ.ends f i = v → Γ.ends g j = v →
      (∀ y ∈ F, y ≠ f → y ≠ g → ∀ j', Γ.ends y j' ≠ v) →
      ∃ x ∈ Γ.bd X, ∃ k, Γ.ends x k = v ∧ Γ.ends x (Fin.rev k) ∉ X := by
    intro v f g i j hv hf hg hfg hi hj hother
    have hfE : f ∈ Γ.Es := edgesIn_subset X (hF hf)
    have hgE : g ∈ Γ.Es := edgesIn_subset X (hF hg)
    obtain ⟨x, hxE, ⟨k, hk⟩, hxf, hxg, -⟩ := third_edge hcub hloop (hX hv) hfE hgE hfg hi hj
    have hxF : x ∉ F := fun h ↦ hother x h hxf hxg k hk
    have hxbd : x ∈ Γ.bd X := by
      rcases mem_edgesIn_or_bd hxE (hk ▸ hv) with h | h
      · exact absurd (hEin ▸ h) hxF
      · exact h
    refine ⟨x, hxbd, k, hk, ?_⟩
    obtain ⟨i', hi', ho'⟩ := bd_side hxbd
    by_cases hki : k = i'
    · rw [hki]; exact ho'
    · exfalso
      have hk' : Γ.ends x k ∈ X := hk ▸ hv
      rw [fin2_eq_rev_of_ne hki] at hk'
      exact ho' hk'
  -- the other cycle edges avoid a given vertex
  have avoid : ∀ (y a' b' v : ℕ), Γ.Joins y a' b' → v ≠ a' → v ≠ b' →
      ∀ j', Γ.ends y j' ≠ v := by
    intro y a' b' v hj h1 h2 j' hj'
    rcases Joins.end_eq hj j' with h | h
    · exact h1 (hj'.symm.trans h)
    · exact h2 (hj'.symm.trans h)
  have jmem : ∀ y ∈ F, y = e₁ ∨ y = e₂ ∨ y = e₃ ∨ y = e₄ := by
    intro y hy; simpa [hFdef] using hy
  -- pendant edges at `a`, `b`, `c`, `d`
  have hF₁ : e₁ ∈ F := by simp [hFdef]
  have hF₂ : e₂ ∈ F := by simp [hFdef]
  have hF₃ : e₃ ∈ F := by simp [hFdef]
  have hF₄ : e₄ ∈ F := by simp [hFdef]
  obtain ⟨i₁, hi₁⟩ := Joins.exists_end j₁
  obtain ⟨i₂, hi₂⟩ := Joins.exists_end j₂
  obtain ⟨i₃, hi₃⟩ := Joins.exists_end j₃
  obtain ⟨i₄, hi₄⟩ := Joins.exists_end j₄
  obtain ⟨i₁', hi₁'⟩ := Joins.exists_end j₁.symm
  obtain ⟨i₂', hi₂'⟩ := Joins.exists_end j₂.symm
  obtain ⟨i₃', hi₃'⟩ := Joins.exists_end j₃.symm
  obtain ⟨i₄', hi₄'⟩ := Joins.exists_end j₄.symm
  obtain ⟨p₁, hp₁, k₁, hk₁, ho₁⟩ := pendant a e₄ e₁ i₄' i₁ haX hF₄ hF₁ n14.symm hi₄' hi₁ (by
    intro y hy hy4 hy1
    rcases jmem y hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy1
    · exact avoid _ _ _ _ j₂ hab hac
    · exact avoid _ _ _ _ j₃ hac had
    · exact absurd rfl hy4)
  obtain ⟨p₂, hp₂, k₂, hk₂, ho₂⟩ := pendant b e₁ e₂ i₁' i₂ hbX hF₁ hF₂ n12 hi₁' hi₂ (by
    intro y hy hy1 hy2
    rcases jmem y hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy1
    · exact absurd rfl hy2
    · exact avoid _ _ _ _ j₃ hbc hbd
    · exact avoid _ _ _ _ j₄ hbd hab.symm)
  obtain ⟨p₃, hp₃, k₃, hk₃, ho₃⟩ := pendant c e₂ e₃ i₂' i₃ hcX hF₂ hF₃ n23 hi₂' hi₃ (by
    intro y hy hy2 hy3
    rcases jmem y hy with rfl | rfl | rfl | rfl
    · exact avoid _ _ _ _ j₁ hac.symm hbc.symm
    · exact absurd rfl hy2
    · exact absurd rfl hy3
    · exact avoid _ _ _ _ j₄ hcd hac.symm)
  obtain ⟨p₄, hp₄, k₄, hk₄, ho₄⟩ := pendant d e₃ e₄ i₃' i₄ hdX hF₃ hF₄ n34 hi₃' hi₄ (by
    intro y hy hy3 hy4
    rcases jmem y hy with rfl | rfl | rfl | rfl
    · exact avoid _ _ _ _ j₁ had.symm hbd.symm
    · exact avoid _ _ _ _ j₂ hbd.symm hcd.symm
    · exact absurd rfl hy3
    · exact absurd rfl hy4)
  -- the pendant edges are distinct: each has its attachment vertex determined
  have attach : ∀ (x v : ℕ) (k : Fin 2), x ∈ Γ.bd X → Γ.ends x k = v → Γ.ends x (Fin.rev k) ∉ X →
      ∀ (v' : ℕ) (k' : Fin 2), Γ.ends x k' = v' → v' ∈ X → v' = v := by
    intro x v k _ hk ho v' k' hk' hv'
    by_cases hkk : k' = k
    · rw [hkk, hk] at hk'; exact hk'.symm
    · rw [← fin2_eq_rev_of_ne hkk, hk'] at ho; exact absurd hv' ho
  have hp12 : p₁ ≠ p₂ := fun h ↦ hab (attach p₁ a k₁ hp₁ hk₁ ho₁ b k₂ (h ▸ hk₂) hbX).symm
  have hp13 : p₁ ≠ p₃ := fun h ↦ hac (attach p₁ a k₁ hp₁ hk₁ ho₁ c k₃ (h ▸ hk₃) hcX).symm
  have hp14 : p₁ ≠ p₄ := fun h ↦ had (attach p₁ a k₁ hp₁ hk₁ ho₁ d k₄ (h ▸ hk₄) hdX).symm
  have hp23 : p₂ ≠ p₃ := fun h ↦ hbc (attach p₂ b k₂ hp₂ hk₂ ho₂ c k₃ (h ▸ hk₃) hcX).symm
  have hp24 : p₂ ≠ p₄ := fun h ↦ hbd (attach p₂ b k₂ hp₂ hk₂ ho₂ d k₄ (h ▸ hk₄) hdX).symm
  have hp34 : p₃ ≠ p₄ := fun h ↦ hcd (attach p₃ c k₃ hp₃ hk₃ ho₃ d k₄ (h ▸ hk₄) hdX).symm
  have hbdeq : Γ.bd X = {p₁, p₂, p₃, p₄} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [hbd4, Finset.card_insert_of_notMem (by simp [hp12, hp13, hp14]),
        Finset.card_insert_of_notMem (by simp [hp23, hp24]), Finset.card_pair hp34]
  have hEs : (Γ.pole X).Es = {e₁, e₂, e₃, e₄, p₁, p₂, p₃, p₄} := by
    rw [pole_Es, hEin, hbdeq, hFdef]
    simp only [Finset.insert_union, Finset.singleton_union]
  -- both poles are colourable and the cut is cycle-separating: a pairing exists
  have hP : (Γ.pole X).IsPole4 := pole_isPole4 hcub hX hbd4
  have hPc : (Γ.pole (Γ.Vs \ X)).IsPole4 :=
    pole_isPole4 hcub Finset.sdiff_subset (by rw [bd_compl hcl]; exact hbd4)
  have hcolX : (Γ.pole X).Colourable := hb.pole_colourable hX (by
    rw [Finset.card_sdiff_of_subset hX]; omega)
  have hcolXc : (Γ.pole (Γ.Vs \ X)).Colourable := by
    apply hb.pole_colourable Finset.sdiff_subset
    rw [Finset.sdiff_sdiff_eq_self hX]
    omega
  obtain ⟨m, hm⟩ := exists_pairing hcl hnc hP hPc hcolX hcolXc
  have := fourCycle_types rfl hab hac had hbc hbd hcd j₁ j₂ j₃ j₄ ⟨k₁, hk₁, ho₁⟩ ⟨k₂, hk₂, ho₂⟩
    ⟨k₃, hk₃, ho₃⟩ ⟨k₄, hk₄, ho₄⟩ hEs hP m
  rcases hm with ⟨h, -⟩ | ⟨h, -⟩
  · exact this.1 h
  · exact this.2 h

/-- **Bicritical snarks with at least six vertices have girth at least `5`.** -/
theorem IsBicritical.girth5 : Γ.Girth5 := by
  have h3 : 3 ≤ Γ.Vs.card := by omega
  have hc4 := hb.cyc4Conn hcl hcub hnc h3
  -- no loops
  have hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1 := by
    intro e he hl
    have hv : Γ.ends e 0 ∈ Γ.Vs := hcl e he 0
    have hsub : ({Γ.ends e 0} : Finset ℕ) ⊆ Γ.Vs := Finset.singleton_subset_iff.mpr hv
    have hcol := hb.pole_colourable hsub (by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]; omega)
    exact not_colourable_of_loop he (Finset.mem_singleton_self _) hl hcol
  -- the complement of a small shore with a small boundary carries a cycle
  have hcycle_compl : ∀ X ⊆ Γ.Vs, (Γ.bd X).card ≤ 3 → X.card ≤ 3 → Γ.HasCycle (Γ.Vs \ X) := by
    intro X hX hbd hXc
    by_contra hno
    have hne : (Γ.Vs \ X).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hX]; omega
    have := card_add_two_le_card_bd hcub Finset.sdiff_subset hne hno
    rw [bd_compl hcl, Finset.card_sdiff_of_subset hX] at this
    omega
  -- the vertices of a joined edge
  have ends_mem : ∀ e ∈ Γ.Es, ∀ a b, Γ.Joins e a b → a ∈ Γ.Vs ∧ b ∈ Γ.Vs := by
    intro e he a b h
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨h0 ▸ hcl e he 0, h1 ▸ hcl e he 1⟩
    · exact ⟨h1 ▸ hcl e he 1, h0 ▸ hcl e he 0⟩
  have joins_in : ∀ e ∈ Γ.Es, ∀ a b, Γ.Joins e a b → ∀ X : Finset ℕ, a ∈ X → b ∈ X →
      e ∈ Γ.edgesIn X := by
    intro e he a b h X ha hb'
    exact mem_edgesIn.mpr ⟨he, Joins.ends_mem h ha hb'⟩
  apply girth5_of_no_short_cycles hcl hloop
  · -- parallel edges
    intro e he e' he' hne a b hab j j'
    obtain ⟨haV, hbV⟩ := ends_mem e he a b j
    have hX : ({a, b} : Finset ℕ) ⊆ Γ.Vs := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    have hF : ({e, e'} : Finset ℕ) ⊆ Γ.edgesIn {a, b} := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact joins_in _ he _ _ j _ (by simp) (by simp)
      · exact joins_in _ he' _ _ j' _ (by simp) (by simp)
    have hev : Γ.IsEven {e, e'} := by
      intro v _
      rw [degIn_eq_sum, Finset.sum_pair hne, endCount_of_joins j hab, endCount_of_joins j' hab]
      split_ifs <;> decide
    have hcyc : Γ.HasCycle {a, b} := ⟨{e, e'}, hF, ⟨e, Finset.mem_insert_self _ _⟩, hev⟩
    have hbd : (Γ.bd {a, b}).card ≤ 2 := by
      have h3' := three_mul_card_eq hcub hX
      have hle : 2 ≤ (Γ.edgesIn {a, b}).card := by
        have := Finset.card_le_card hF; rw [Finset.card_pair hne] at this; exact this
      have hXc : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      omega
    have := hc4 _ hX hcyc (hcycle_compl _ hX (by omega) (by
      have : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two; omega))
    omega
  · -- triangles
    intro e₁ he₁ e₂ he₂ e₃ he₃ n12 n13 n23 a b c hab hbc hac j₁ j₂ j₃
    obtain ⟨haV, hbV⟩ := ends_mem e₁ he₁ a b j₁
    obtain ⟨-, hcV⟩ := ends_mem e₂ he₂ b c j₂
    have hX : ({a, b, c} : Finset ℕ) ⊆ Γ.Vs := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hF : ({e₁, e₂, e₃} : Finset ℕ) ⊆ Γ.edgesIn {a, b, c} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact joins_in _ he₁ _ _ j₁ _ (by simp) (by simp)
      · exact joins_in _ he₂ _ _ j₂ _ (by simp) (by simp)
      · exact joins_in _ he₃ _ _ j₃ _ (by simp) (by simp)
    have hev : Γ.IsEven {e₁, e₂, e₃} := by
      intro v _
      rw [degIn_eq_sum, Finset.sum_insert (by simp [n12, n13]), Finset.sum_pair n23,
        endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hac.symm]
      split_ifs <;> first | decide | omega
    have hcyc : Γ.HasCycle {a, b, c} := ⟨_, hF, ⟨e₁, Finset.mem_insert_self _ _⟩, hev⟩
    have hcard3 : ({e₁, e₂, e₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [n12, n13]), Finset.card_pair n23]
    have hbd : (Γ.bd {a, b, c}).card ≤ 3 := by
      have h3' := three_mul_card_eq hcub hX
      have hle : 3 ≤ (Γ.edgesIn {a, b, c}).card := by
        have := Finset.card_le_card hF; rw [hcard3] at this; exact this
      have hXc : ({a, b, c} : Finset ℕ).card ≤ 3 := Finset.card_le_three
      omega
    have := hc4 _ hX hcyc (hcycle_compl _ hX (by omega) (by
      have : ({a, b, c} : Finset ℕ).card ≤ 3 := Finset.card_le_three; omega))
    omega
  · exact IsBicritical.no_quad hcl hcub hnc hb h6 hloop hc4 hcycle_compl ends_mem joins_in

end Girth

end FinGraph
end GraphPuzzles
