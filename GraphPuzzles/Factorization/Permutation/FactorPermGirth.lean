import GraphPuzzles.Factorization.Permutation.FactorPermColouring
import GraphPuzzles.Factorization.Bicritical.FactorFourCycle
import GraphPuzzles.Factorization.Bicritical.FactorGirthCombinatorics
import GraphPuzzles.Factorization.Bicritical.FactorGirth

/-!
# Permutation snarks have girth at least five

Short cycles in a permutation graph: parallel edges and triangles force a rim of length two
or three; a quadrilateral is a pair of consecutive spokes with their rim edges.  A triangle rim
produces such a quadrilateral, and a quadrilateral is excluded by `fourCycle_types`, since both
of its poles are colourable.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂)
  (hcl : Γ.IsClosed)
include hP hcl

namespace IsPermGraph

/-- The side of the ends of an edge: a spoke joins the two sides, a rim edge stays on one. -/
theorem sides {e a b : ℕ} (he : e ∈ Γ.Es) (hj : Γ.Joins e a b) :
    (e ∈ Γ.bd V₁ ∧ (a ∈ V₁ ↔ b ∉ V₁)) ∨ (e ∈ R₁ ∧ a ∈ V₁ ∧ b ∈ V₁) ∨
      (e ∈ R₂ ∧ a ∉ V₁ ∧ b ∉ V₁) := by
  have haV : a ∈ Γ.Vs := by
    rcases hj with ⟨h0, -⟩ | ⟨-, h1⟩
    · rw [← h0]; exact hcl e he 0
    · rw [← h1]; exact hcl e he 1
  have hbV : b ∈ Γ.Vs := by
    rcases hj with ⟨-, h1⟩ | ⟨h0, -⟩
    · rw [← h1]; exact hcl e he 1
    · rw [← h0]; exact hcl e he 0
  obtain ⟨i, hi⟩ := Joins.exists_end hj
  obtain ⟨j, hj'⟩ := Joins.exists_end hj.symm
  by_cases ha : a ∈ V₁
  · rcases hP.edge_at_V₁ he (hi ▸ ha) with h | h
    · right; left
      refine ⟨h, ha, ?_⟩
      have := (mem_edgesIn.mp (hP.ham₁.subset h)).2 j
      rwa [hj'] at this
    · left
      refine ⟨h, ?_⟩
      rw [mem_bd] at h
      constructor
      · intro _ hb
        apply h.2
        rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
        · exact ⟨fun _ ↦ hb, fun _ ↦ ha⟩
        · exact ⟨fun _ ↦ ha, fun _ ↦ hb⟩
      · intro _; exact ha
  · have ha₂ : a ∈ V₂ := (hP.mem_V₂_iff haV).mpr ha
    rcases hP.edge_at_V₂ hcl he (hi ▸ ha₂) with h | h
    · right; right
      refine ⟨h, ha, ?_⟩
      have := (mem_edgesIn.mp (hP.ham₂.subset h)).2 j
      rw [hj'] at this
      exact fun hb ↦ Finset.disjoint_left.mp hP.disj hb this
    · left
      have hb₁ : b ∈ V₁ := by
        by_contra hb₁
        rw [mem_bd] at h
        apply h.2
        rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
        · exact ⟨fun h' ↦ absurd h' ha, fun h' ↦ absurd h' hb₁⟩
        · exact ⟨fun h' ↦ absurd h' hb₁, fun h' ↦ absurd h' ha⟩
      exact ⟨h, ⟨fun h' ↦ absurd h' ha, fun hb ↦ absurd hb₁ hb⟩⟩

omit hcl in
/-- No two parallel rim edges of `R₁`. -/
theorem no_parallel₁ {e e' a b : ℕ} (he : e ∈ R₁) (he' : e' ∈ R₁) (hne : e ≠ e') (hab : a ≠ b)
    (hj : Γ.Joins e a b) (hj' : Γ.Joins e' a b) : False := by
  have hF : ({e, e'} : Finset ℕ) = R₁ := by
    apply hP.ham₁.eq_of_subset
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · exact ⟨e, Finset.mem_insert_self _ _⟩
    · intro v _
      rw [degIn_eq_sum, Finset.sum_pair hne, endCount_of_joins hj hab, endCount_of_joins hj' hab]
      split_ifs <;> simp
  have := hP.ham₁.card_eq
  rw [← hF, Finset.card_pair hne] at this
  have := hP.three
  omega

/-- No two parallel rim edges of `R₂`. -/
theorem no_parallel₂ {e e' a b : ℕ} (he : e ∈ R₂) (he' : e' ∈ R₂) (hne : e ≠ e') (hab : a ≠ b)
    (hj : Γ.Joins e a b) (hj' : Γ.Joins e' a b) : False := by
  have hF : ({e, e'} : Finset ℕ) = R₂ := by
    apply hP.ham₂.eq_of_subset
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · exact ⟨e, Finset.mem_insert_self _ _⟩
    · intro v _
      rw [degIn_eq_sum, Finset.sum_pair hne, endCount_of_joins hj hab, endCount_of_joins hj' hab]
      split_ifs <;> simp
  have := hP.ham₂.card_eq
  rw [← hF, Finset.card_pair hne, hP.card_V₂ hcl] at this
  have := hP.three
  omega

/-- **No parallel edges.** -/
theorem no_parallel {e e' a b : ℕ} (he : e ∈ Γ.Es) (he' : e' ∈ Γ.Es) (hne : e ≠ e') (hab : a ≠ b)
    (hj : Γ.Joins e a b) (hj' : Γ.Joins e' a b) : False := by
  obtain ⟨i, hi⟩ := Joins.exists_end hj
  obtain ⟨i', hi'⟩ := Joins.exists_end hj'
  have haV : a ∈ Γ.Vs := by rw [← hi]; exact hcl e he i
  rcases hP.sides hcl he hj with ⟨hs, hab'⟩ | ⟨hr, ha, hb⟩ | ⟨hr, ha, hb⟩ <;>
    rcases hP.sides hcl he' hj' with ⟨hs', hab''⟩ | ⟨hr', ha', hb'⟩ | ⟨hr', ha', hb'⟩
  · exact hne (hP.spoke_unique haV hs hs' hi hi')
  · exact (hab'.mp ha') hb'
  · exact ha' (hab'.mpr hb')
  · exact (hab''.mp ha) hb
  · exact hP.no_parallel₁ hr hr' hne hab hj hj'
  · exact ha' ha
  · exact ha (hab''.mpr hb)
  · exact ha ha'
  · exact hP.no_parallel₂ hcl hr hr' hne hab hj hj'


omit hP hcl in
/-- The swapped permutation structure. -/
theorem swap (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂) (hcl : Γ.IsClosed) : Γ.IsPermGraph V₂ V₁ R₂ R₁ where
  disj := hP.disj.symm
  union := by rw [Finset.union_comm]; exact hP.union
  ham₁ := hP.ham₂
  ham₂ := hP.ham₁
  induced₁ := hP.induced₂
  induced₂ := hP.induced₁
  spoke := by rw [hP.bd_V₂ hcl]; exact hP.spoke
  three := by rw [hP.card_V₂ hcl]; exact hP.three

omit hP hcl in
/-- The other rim edge at a rim vertex `v` whose rim neighbour `v'` is given. -/
theorem other_rim_edge {R V : Finset ℕ} (hR : Γ.IsHamCycle V R) (hRE : R ⊆ Γ.Es)
    (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1)
    (hnp : ∀ e e' a b, e ∈ R → e' ∈ R → e ≠ e' → a ≠ b → Γ.Joins e a b → Γ.Joins e' a b → False)
    {v v' e : ℕ} (hv : v ∈ V) (hvv' : v ≠ v') (he : e ∈ R) (hj : Γ.Joins e v' v) :
    ∃ g ∈ R, g ≠ e ∧ ∃ k, Γ.ends g k = v ∧ Γ.ends g (Fin.rev k) ∈ V ∧
      Γ.ends g (Fin.rev k) ≠ v ∧ Γ.ends g (Fin.rev k) ≠ v' := by
  obtain ⟨g₁, i₁, g₂, i₂, hne, hset⟩ := halfEdges_two (hR.deg v hv)
  obtain ⟨ie, hie⟩ := Joins.exists_end hj.symm
  have hmem : (e, ie) ∈ Γ.halfEdgesIn R v := mem_halfEdgesIn.mpr ⟨he, hie⟩
  have hm₁ : (g₁, i₁) ∈ Γ.halfEdgesIn R v := by rw [hset]; exact Finset.mem_insert_self _ _
  have hm₂ : (g₂, i₂) ∈ Γ.halfEdgesIn R v := by
    rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [mem_halfEdgesIn] at hm₁ hm₂
  dsimp only at hm₁ hm₂
  rw [hset, Finset.mem_insert, Finset.mem_singleton] at hmem
  have pick : ∃ g ∈ R, ∃ k, Γ.ends g k = v ∧ (g, k) ≠ (e, ie) := by
    rcases hmem with h | h
    · exact ⟨g₂, hm₂.1, i₂, hm₂.2, by rw [h]; exact hne.symm⟩
    · exact ⟨g₁, hm₁.1, i₁, hm₁.2, by rw [h]; exact hne⟩
  obtain ⟨g, hg, k, hk, hgk⟩ := pick
  have hge : g ≠ e := by
    rintro rfl
    exact hgk (Prod.ext rfl (idx_eq_of_ends_eq_single (hloop g (hRE hg)) (hk.trans hie.symm)))
  refine ⟨g, hg, hge, k, hk, (mem_edgesIn.mp (hR.subset hg)).2 _, ?_, ?_⟩
  · intro h
    exact fin2_rev_ne k (idx_eq_of_ends_eq_single (hloop g (hRE hg)) (h.trans hk.symm))
  · intro h
    have hjg : Γ.Joins g v' v := by
      have hk0 : k = 0 ∨ k = 1 := by omega
      rcases hk0 with rfl | rfl
      · rw [Iso.rev_zero'] at h; exact Or.inr ⟨hk, h⟩
      · rw [Iso.rev_one'] at h; exact Or.inl ⟨h, hk⟩
    exact hnp g e v' v hg he hge hvv'.symm hjg hj

variable (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂) (hcl : Γ.IsClosed) (hcub : Γ.IsCubic)
  (hnc : ¬ Γ.Colourable)
include hP hcl hcub hnc

/-- **No rung quadrilateral**: two spokes `ab`, `cd` with `a, d ∈ V₁`, `b, c ∈ V₂`, and rim
edges `da ∈ R₁`, `bc ∈ R₂`. -/
theorem no_rung {a b c d e₁ e₂ e₃ e₄ : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d)
    (hac : a ≠ c) (hbd : b ≠ d) (ha : a ∈ V₁) (hd : d ∈ V₁) (hb : b ∈ V₂) (hc : c ∈ V₂)
    (he₁ : e₁ ∈ Γ.bd V₁) (he₂ : e₂ ∈ R₂) (he₃ : e₃ ∈ Γ.bd V₁) (he₄ : e₄ ∈ R₁)
    (j₁ : Γ.Joins e₁ a b) (j₂ : Γ.Joins e₂ b c) (j₃ : Γ.Joins e₃ c d) (j₄ : Γ.Joins e₄ d a) :
    False := by
  classical
  have hloop := hP.no_loop hcl
  have haV : a ∈ Γ.Vs := hP.V₁_subset ha
  have hbV : b ∈ Γ.Vs := hP.V₂_subset hb
  have hcV : c ∈ Γ.Vs := hP.V₂_subset hc
  have hdV : d ∈ Γ.Vs := hP.V₁_subset hd
  have he₁E : e₁ ∈ Γ.Es := bd_subset _ he₁
  have he₂E : e₂ ∈ Γ.Es := hP.R₂_subset he₂
  have he₃E : e₃ ∈ Γ.Es := bd_subset _ he₃
  have he₄E : e₄ ∈ Γ.Es := hP.R₁_subset he₄
  have hb₁ : b ∉ V₁ := fun h ↦ Finset.disjoint_left.mp hP.disj h hb
  have hc₁ : c ∉ V₁ := fun h ↦ Finset.disjoint_left.mp hP.disj h hc
  have ha₂ : a ∉ V₂ := fun h ↦ Finset.disjoint_left.mp hP.disj ha h
  have hd₂ : d ∉ V₂ := fun h ↦ Finset.disjoint_left.mp hP.disj hd h
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
  -- the other rim edges at the four vertices
  obtain ⟨ga, hga, hgae, ka, hka, hgaV, hga₁, hga₂⟩ :=
    other_rim_edge hP.ham₁ hP.R₁_subset hloop (fun e e' x y he he' hne hxy hj hj' ↦
      hP.no_parallel₁ he he' hne hxy hj hj') ha had he₄ j₄
  obtain ⟨gd, hgd, hgde, kd, hkd, hgdV, hgd₁, hgd₂⟩ :=
    other_rim_edge hP.ham₁ hP.R₁_subset hloop (fun e e' x y he he' hne hxy hj hj' ↦
      hP.no_parallel₁ he he' hne hxy hj hj') hd had.symm he₄ j₄.symm
  obtain ⟨gb, hgb, hgbe, kb, hkb, hgbV, hgb₁, hgb₂⟩ :=
    other_rim_edge hP.ham₂ hP.R₂_subset hloop (fun e e' x y he he' hne hxy hj hj' ↦
      hP.no_parallel₂ hcl he he' hne hxy hj hj') hb hbc he₂ j₂.symm
  obtain ⟨gc, hgc, hgce, kc, hkc, hgcV, hgc₁, hgc₂⟩ :=
    other_rim_edge hP.ham₂ hP.R₂_subset hloop (fun e e' x y he he' hne hxy hj hj' ↦
      hP.no_parallel₂ hcl he he' hne hxy hj hj') hc hbc.symm he₂ j₂
  have hgaX : Γ.ends ga (Fin.rev ka) ∉ X := by
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hga₁ h
    · exact hb₁ (h ▸ hgaV)
    · exact hc₁ (h ▸ hgaV)
    · exact hga₂ h
  have hgdX : Γ.ends gd (Fin.rev kd) ∉ X := by
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hgd₂ h
    · exact hb₁ (h ▸ hgdV)
    · exact hc₁ (h ▸ hgdV)
    · exact hgd₁ h
  have hgbX : Γ.ends gb (Fin.rev kb) ∉ X := by
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact ha₂ (h ▸ hgbV)
    · exact hgb₁ h
    · exact hgb₂ h
    · exact hd₂ (h ▸ hgbV)
  have hgcX : Γ.ends gc (Fin.rev kc) ∉ X := by
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact ha₂ (h ▸ hgcV)
    · exact hgc₂ h
    · exact hgc₁ h
    · exact hd₂ (h ▸ hgcV)
  have hgaE : ga ∈ Γ.Es := hP.R₁_subset hga
  have hgdE : gd ∈ Γ.Es := hP.R₁_subset hgd
  have hgbE : gb ∈ Γ.Es := hP.R₂_subset hgb
  have hgcE : gc ∈ Γ.Es := hP.R₂_subset hgc
  -- the three edges at each vertex
  have at_a : ∀ y ∈ Γ.Es, ∀ j, Γ.ends y j = a → y = e₄ ∨ y = ga ∨ y = e₁ := by
    obtain ⟨i₄, hi₄⟩ := Joins.exists_end j₄.symm
    obtain ⟨x, hx, ⟨k, hk⟩, hx₄, hxg, hall⟩ := third_edge hcub hloop haV he₄E hgaE hgae.symm hi₄ hka
    obtain ⟨i₁, hi₁⟩ := Joins.exists_end j₁
    have hx₁ : x = e₁ := by
      rcases hall e₁ he₁E i₁ hi₁ with h | h | h
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₁ (h' ▸ he₄) he₁)
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₁ (h' ▸ hga) he₁)
      · exact h.symm
    intro y hy j hj
    rcases hall y hy j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hx₁))
  have at_d : ∀ y ∈ Γ.Es, ∀ j, Γ.ends y j = d → y = e₄ ∨ y = gd ∨ y = e₃ := by
    obtain ⟨i₄, hi₄⟩ := Joins.exists_end j₄
    obtain ⟨x, hx, ⟨k, hk⟩, hx₄, hxg, hall⟩ := third_edge hcub hloop hdV he₄E hgdE hgde.symm hi₄ hkd
    obtain ⟨i₃, hi₃⟩ := Joins.exists_end j₃.symm
    have hx₃ : x = e₃ := by
      rcases hall e₃ he₃E i₃ hi₃ with h | h | h
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₁ (h' ▸ he₄) he₃)
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₁ (h' ▸ hgd) he₃)
      · exact h.symm
    intro y hy j hj
    rcases hall y hy j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hx₃))
  have at_b : ∀ y ∈ Γ.Es, ∀ j, Γ.ends y j = b → y = e₂ ∨ y = gb ∨ y = e₁ := by
    obtain ⟨i₂, hi₂⟩ := Joins.exists_end j₂
    obtain ⟨x, hx, ⟨k, hk⟩, hx₂, hxg, hall⟩ := third_edge hcub hloop hbV he₂E hgbE hgbe.symm hi₂ hkb
    obtain ⟨i₁, hi₁⟩ := Joins.exists_end j₁.symm
    have hx₁ : x = e₁ := by
      rcases hall e₁ he₁E i₁ hi₁ with h | h | h
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₂ hcl (h' ▸ he₂) he₁)
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₂ hcl (h' ▸ hgb) he₁)
      · exact h.symm
    intro y hy j hj
    rcases hall y hy j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hx₁))
  have at_c : ∀ y ∈ Γ.Es, ∀ j, Γ.ends y j = c → y = e₂ ∨ y = gc ∨ y = e₃ := by
    obtain ⟨i₂, hi₂⟩ := Joins.exists_end j₂.symm
    obtain ⟨x, hx, ⟨k, hk⟩, hx₂, hxg, hall⟩ := third_edge hcub hloop hcV he₂E hgcE hgce.symm hi₂ hkc
    obtain ⟨i₃, hi₃⟩ := Joins.exists_end j₃
    have hx₃ : x = e₃ := by
      rcases hall e₃ he₃E i₃ hi₃ with h | h | h
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₂ hcl (h' ▸ he₂) he₃)
      · exact absurd h (fun h' ↦ hP.rim_not_spoke₂ hcl (h' ▸ hgc) he₃)
      · exact h.symm
    intro y hy j hj
    rcases hall y hy j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hx₃))
  -- the pendant edges are on the boundary, the cycle edges inside
  have hg_bd : ∀ (g : ℕ) (k : Fin 2), g ∈ Γ.Es → Γ.ends g k ∈ X → Γ.ends g (Fin.rev k) ∉ X →
      g ∈ Γ.bd X := by
    intro g k hg hk hk'
    rw [mem_bd]
    refine ⟨hg, ?_⟩
    have hk0 : k = 0 ∨ k = 1 := by omega
    rcases hk0 with rfl | rfl
    · rw [Iso.rev_zero'] at hk'; exact fun h ↦ hk' (h.mp hk)
    · rw [Iso.rev_one'] at hk'; exact fun h ↦ hk' (h.mpr hk)
  have hgabd := hg_bd ga ka hgaE (hka ▸ haX) hgaX
  have hgdbd := hg_bd gd kd hgdE (hkd ▸ hdX) hgdX
  have hgbbd := hg_bd gb kb hgbE (hkb ▸ hbX) hgbX
  have hgcbd := hg_bd gc kc hgcE (hkc ▸ hcX) hgcX
  have he_in : ∀ (e x y : ℕ), e ∈ Γ.Es → x ∈ X → y ∈ X → Γ.Joins e x y → e ∈ Γ.edgesIn X :=
    fun e x y he hx hy hj ↦ mem_edgesIn.mpr ⟨he, Joins.ends_mem hj hx hy⟩
  have he₁in := he_in e₁ a b he₁E haX hbX j₁
  have he₂in := he_in e₂ b c he₂E hbX hcX j₂
  have he₃in := he_in e₃ c d he₃E hcX hdX j₃
  have he₄in := he_in e₄ d a he₄E hdX haX j₄
  -- every edge with an end in `X` is one of the eight
  have hall : ∀ y ∈ Γ.Es, ∀ j, Γ.ends y j ∈ X →
      y = e₁ ∨ y = e₂ ∨ y = e₃ ∨ y = e₄ ∨ y = ga ∨ y = gb ∨ y = gc ∨ y = gd := by
    intro y hy j hj
    simp only [hXdef, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h | h | h
    · rcases at_a y hy j h with h' | h' | h' <;> simp [h']
    · rcases at_b y hy j h with h' | h' | h' <;> simp [h']
    · rcases at_c y hy j h with h' | h' | h' <;> simp [h']
    · rcases at_d y hy j h with h' | h' | h' <;> simp [h']
  have hEin : Γ.edgesIn X = {e₁, e₂, e₃, e₄} := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hy
      have hyE := (mem_edgesIn.mp hy).1
      rcases hall y hyE 0 ((mem_edgesIn.mp hy).2 0) with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      all_goals exfalso; subst h
      · exact Finset.disjoint_left.mp (disjoint_edgesIn_bd X) hy hgabd
      · exact Finset.disjoint_left.mp (disjoint_edgesIn_bd X) hy hgbbd
      · exact Finset.disjoint_left.mp (disjoint_edgesIn_bd X) hy hgcbd
      · exact Finset.disjoint_left.mp (disjoint_edgesIn_bd X) hy hgdbd
    · rintro (rfl | rfl | rfl | rfl) <;> assumption
  have hbdX : Γ.bd X = {ga, gb, gc, gd} := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hy
      obtain ⟨i, hi, -⟩ := bd_side hy
      rcases hall y (bd_subset X hy) i hi with h | h | h | h | h | h | h | h
      all_goals first
        | (exfalso; subst h; exact Finset.disjoint_left.mp (disjoint_edgesIn_bd X) ‹_› hy)
        | simp [h]
    · rintro (rfl | rfl | rfl | rfl) <;> assumption
  -- distinctness of the eight edges
  have hs₁ : e₁ ∉ R₁ := fun h ↦ hP.rim_not_spoke₁ h he₁
  have hs₁' : e₁ ∉ R₂ := fun h ↦ hP.rim_not_spoke₂ hcl h he₁
  have hs₃ : e₃ ∉ R₁ := fun h ↦ hP.rim_not_spoke₁ h he₃
  have hs₃' : e₃ ∉ R₂ := fun h ↦ hP.rim_not_spoke₂ hcl h he₃
  have h12 : ∀ x ∈ R₁, x ∉ R₂ := fun x hx hx' ↦ Finset.disjoint_left.mp hP.disjoint_rims hx hx'
  have he13 : e₁ ≠ e₃ := by
    intro h
    subst h
    rcases Joins.eq_of_eq j₁ j₃ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hac h1
    · exact had h1
  have hEcard : ({e₁, e₂, e₃, e₄} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hs₁' (h ▸ he₂)
        · exact he13 h
        · exact hs₁ (h ▸ he₄)),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact hs₃' (h ▸ he₂)
        · exact h12 e₄ he₄ (h ▸ he₂)),
      Finset.card_pair (fun h ↦ hs₃ (by rw [h]; exact he₄))]
  have hgad : ga ≠ gd := by
    intro h
    subst h
    -- `ga` has ends `a` and a vertex outside `X`, but `d` is an end
    have hkd' : ∀ j, Γ.ends ga j = a ∨ Γ.ends ga j ∉ X := by
      intro j
      by_cases hj : j = ka
      · exact Or.inl (hj ▸ hka)
      · rw [fin2_eq_rev_of_ne hj]; exact Or.inr hgaX
    rcases hkd' kd with h | h
    · exact had (h ▸ hkd)
    · exact h (hkd ▸ hdX)
  have hgbc : gb ≠ gc := by
    intro h
    subst h
    have hkc' : ∀ j, Γ.ends gb j = b ∨ Γ.ends gb j ∉ X := by
      intro j
      by_cases hj : j = kb
      · exact Or.inl (hj ▸ hkb)
      · rw [fin2_eq_rev_of_ne hj]; exact Or.inr hgbX
    rcases hkc' kc with h | h
    · exact hbc (h ▸ hkc)
    · exact h (hkc ▸ hcX)
  have hbdcard : ({ga, gb, gc, gd} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact h12 ga hga (h ▸ hgb)
        · exact h12 ga hga (h ▸ hgc)
        · exact hgad h),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact hgbc h
        · exact h12 gd hgd (h ▸ hgb)),
      Finset.card_pair (fun h ↦ h12 gd hgd (by rw [← h]; exact hgc))]
  have hbd4 : (Γ.bd X).card = 4 := by rw [hbdX, hbdcard]
  have hEs : (Γ.pole X).Es = {e₁, e₂, e₃, e₄, ga, gb, gc, gd} := by
    rw [pole_Es, hEin, hbdX]
    simp only [Finset.insert_union, Finset.singleton_union]
  -- both poles are colourable, and a pairing exists
  have hP4 : (Γ.pole X).IsPole4 := pole_isPole4 hcub hX hbd4
  have hP4c : (Γ.pole (Γ.Vs \ X)).IsPole4 :=
    pole_isPole4 hcub Finset.sdiff_subset (by rw [bd_compl hcl]; exact hbd4)
  have hcolX := hP.pole_colourable_of_cut hcl hga hgabd hgb hgbbd
  have hcolXc := hP.pole_colourable_of_cut hcl hga (by rw [bd_compl hcl]; exact hgabd) hgb
    (by rw [bd_compl hcl]; exact hgbbd)
  obtain ⟨m, hm⟩ := exists_pairing hcl hnc hP4 hP4c hcolX hcolXc
  have := fourCycle_types rfl hab hac had hbc hbd hcd j₁ j₂ j₃ j₄ ⟨ka, hka, hgaX⟩ ⟨kb, hkb, hgbX⟩
    ⟨kc, hkc, hgcX⟩ ⟨kd, hkd, hgdX⟩ hEs hP4 m
  rcases hm with ⟨h, -⟩ | ⟨h, -⟩
  · exact this.1 h
  · exact this.2 h

omit hcub hnc in
/-- The other end of a spoke at a vertex of `V₁` lies in `V₂`, and conversely. -/
theorem spoke_other_end₁ {s : ℕ} (hs : s ∈ Γ.bd V₁) {i : Fin 2} (hi : Γ.ends s i ∈ V₁) :
    Γ.ends s (Fin.rev i) ∈ V₂ := by
  obtain ⟨j, hj, hj'⟩ := bd_side hs
  have hsE : s ∈ Γ.Es := bd_subset _ hs
  have hji : j = i := by
    by_contra h
    rw [fin2_eq_rev_of_ne h, Fin.rev_rev] at hj'
    exact hj' hi
  subst hji
  exact (hP.mem_V₂_iff (hcl s hsE _)).mpr hj'

omit hcub hnc in
omit hcl in
theorem spoke_other_end₂ {s : ℕ} (hs : s ∈ Γ.bd V₁) {i : Fin 2} (hi : Γ.ends s i ∈ V₂) :
    Γ.ends s (Fin.rev i) ∈ V₁ := by
  obtain ⟨j, hj, hj'⟩ := bd_side hs
  have hsE : s ∈ Γ.Es := bd_subset _ hs
  have hji : j ≠ i := by
    rintro rfl
    exact Finset.disjoint_left.mp hP.disj hj hi
  rw [fin2_eq_rev_of_ne hji] at hj
  exact hj

omit hP hcl hcub hnc in
theorem joins_of_rev {e : ℕ} {i : Fin 2} : Γ.Joins e (Γ.ends e i) (Γ.ends e (Fin.rev i)) := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [Iso.rev_zero']; exact Or.inl ⟨rfl, rfl⟩
  · rw [Iso.rev_one']; exact Or.inr ⟨rfl, rfl⟩

/-- A rim of length three forces a rung quadrilateral. -/
theorem no_three (h3 : V₁.card = 3) : False := by
  classical
  have hloop := hP.no_loop hcl
  -- a vertex `a ∈ V₁` and its spoke to `b ∈ V₂`
  obtain ⟨a, ha⟩ : V₁.Nonempty := by rw [← Finset.card_pos, h3]; omega
  have haV := hP.V₁_subset ha
  obtain ⟨⟨s, is⟩, hs⟩ : (Γ.halfEdgesIn (Γ.bd V₁) a).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hP.spoke a haV]; omega
  rw [mem_halfEdgesIn] at hs
  dsimp only at hs
  set b := Γ.ends s (Fin.rev is) with hbdef
  have hb : b ∈ V₂ := hP.spoke_other_end₁ hcl hs.1 (hs.2 ▸ ha)
  have hbV := hP.V₂_subset hb
  have jab : Γ.Joins s a b := by rw [← hs.2]; exact joins_of_rev
  -- a rim neighbour `c` of `b`
  obtain ⟨g₁, i₁, g₂, i₂, -, hset⟩ := halfEdges_two (hP.ham₂.deg b hb)
  have hg₁ : (g₁, i₁) ∈ Γ.halfEdgesIn R₂ b := by rw [hset]; exact Finset.mem_insert_self _ _
  rw [mem_halfEdgesIn] at hg₁
  dsimp only at hg₁
  set c := Γ.ends g₁ (Fin.rev i₁) with hcdef
  have hc : c ∈ V₂ := (mem_edgesIn.mp (hP.ham₂.subset hg₁.1)).2 _
  have hcV := hP.V₂_subset hc
  have hbc : b ≠ c := by
    intro h
    exact fin2_rev_ne i₁ (idx_eq_of_ends_eq_single (hloop g₁ (hP.R₂_subset hg₁.1)) (h.symm.trans hg₁.2.symm))
  have jbc : Γ.Joins g₁ b c := by rw [← hg₁.2]; exact joins_of_rev
  -- the spoke at `c` to `d ∈ V₁`
  obtain ⟨⟨t, it⟩, ht⟩ : (Γ.halfEdgesIn (Γ.bd V₁) c).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hP.spoke c hcV]; omega
  rw [mem_halfEdgesIn] at ht
  dsimp only at ht
  set d := Γ.ends t (Fin.rev it) with hddef
  have hd : d ∈ V₁ := hP.spoke_other_end₂ ht.1 (ht.2 ▸ hc)
  have hdV := hP.V₁_subset hd
  have jcd : Γ.Joins t c d := by rw [← ht.2]; exact joins_of_rev
  have hab : a ≠ b := fun h ↦ Finset.disjoint_left.mp hP.disj ha (h ▸ hb)
  have hac : a ≠ c := fun h ↦ Finset.disjoint_left.mp hP.disj ha (h ▸ hc)
  have hcd : c ≠ d := fun h ↦ Finset.disjoint_left.mp hP.disj hd (h ▸ hc)
  have hbd : b ≠ d := fun h ↦ Finset.disjoint_left.mp hP.disj hd (h ▸ hb)
  have had : a ≠ d := by
    intro h
    -- two spokes at `a`
    have hst : s = t := hP.spoke_unique haV hs.1 ht.1 hs.2 (by rw [h])
    subst hst
    rcases Joins.eq_of_eq jab jcd with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hac h1
    · exact hbc.symm h2.symm
  -- the rim edge from `d` to `a`: `a` is adjacent along `R₁` to both other vertices of `V₁`
  obtain ⟨p₁, k₁, p₂, k₂, hne, hsetA⟩ := halfEdges_two (hP.ham₁.deg a ha)
  have hp₁ : (p₁, k₁) ∈ Γ.halfEdgesIn R₁ a := by rw [hsetA]; exact Finset.mem_insert_self _ _
  have hp₂ : (p₂, k₂) ∈ Γ.halfEdgesIn R₁ a := by
    rw [hsetA]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [mem_halfEdgesIn] at hp₁ hp₂
  dsimp only at hp₁ hp₂
  have hp12 : p₁ ≠ p₂ := by
    rintro rfl
    exact hne (Prod.ext rfl (idx_eq_of_ends_eq_single (hloop p₁ (hP.R₁_subset hp₁.1))
      (hp₁.2.trans hp₂.2.symm)))
  set n₁ := Γ.ends p₁ (Fin.rev k₁) with hn₁
  set n₂ := Γ.ends p₂ (Fin.rev k₂) with hn₂
  have hn₁V : n₁ ∈ V₁ := (mem_edgesIn.mp (hP.ham₁.subset hp₁.1)).2 _
  have hn₂V : n₂ ∈ V₁ := (mem_edgesIn.mp (hP.ham₁.subset hp₂.1)).2 _
  have hn₁a : n₁ ≠ a := fun h ↦
    fin2_rev_ne k₁ (idx_eq_of_ends_eq_single (hloop p₁ (hP.R₁_subset hp₁.1)) (h.trans hp₁.2.symm))
  have hn₂a : n₂ ≠ a := fun h ↦
    fin2_rev_ne k₂ (idx_eq_of_ends_eq_single (hloop p₂ (hP.R₁_subset hp₂.1)) (h.trans hp₂.2.symm))
  have j₁ : Γ.Joins p₁ a n₁ := by rw [← hp₁.2]; exact joins_of_rev
  have j₂ : Γ.Joins p₂ a n₂ := by rw [← hp₂.2]; exact joins_of_rev
  have hn12 : n₁ ≠ n₂ := by
    intro h
    exact hP.no_parallel₁ hp₁.1 hp₂.1 hp12 hn₁a.symm j₁ (h ▸ j₂)
  have hV₁ : V₁.erase a = {n₁, n₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hn₁a, hn₁V⟩
      · exact Finset.mem_erase.mpr ⟨hn₂a, hn₂V⟩
    · rw [Finset.card_erase_of_mem ha, h3, Finset.card_pair hn12]
  have hdmem : d ∈ ({n₁, n₂} : Finset ℕ) := by rw [← hV₁]; exact Finset.mem_erase.mpr ⟨had.symm, hd⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at hdmem
  rcases hdmem with h | h
  · exact hP.no_rung hcl hcub hnc hab hbc hcd had hac hbd ha hd hb hc hs.1 hg₁.1 ht.1 hp₁.1
      jab jbc jcd (by rw [h]; exact j₁.symm)
  · exact hP.no_rung hcl hcub hnc hab hbc hcd had hac hbd ha hd hb hc hs.1 hg₁.1 ht.1 hp₂.1
      jab jbc jcd (by rw [h]; exact j₂.symm)

omit hcub hnc in
omit hcl in
/-- A nonempty even subset of a rim is the rim; hence three rim edges of a triangle force a
rim of length three. -/
theorem tri_rim₁ {e₁ e₂ e₃ a b c : ℕ} (he₁ : e₁ ∈ R₁) (he₂ : e₂ ∈ R₁) (he₃ : e₃ ∈ R₁)
    (n12 : e₁ ≠ e₂) (n13 : e₁ ≠ e₃) (n23 : e₂ ≠ e₃) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (j₁ : Γ.Joins e₁ a b) (j₂ : Γ.Joins e₂ b c) (j₃ : Γ.Joins e₃ c a) : V₁.card = 3 := by
  have hF : ({e₁, e₂, e₃} : Finset ℕ) = R₁ := by
    apply hP.ham₁.eq_of_subset
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · exact ⟨e₁, Finset.mem_insert_self _ _⟩
    · intro v _
      rw [degIn_eq_sum, Finset.sum_insert (by simp [n12, n13]), Finset.sum_pair n23,
        endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hac.symm]
      split_ifs <;> omega
  have := hP.ham₁.card_eq
  rw [← hF, Finset.card_insert_of_notMem (by simp [n12, n13]), Finset.card_pair n23] at this
  omega

omit hcub in
theorem quad_rim₁ {e₁ e₂ e₃ e₄ a b c d : ℕ} (he₁ : e₁ ∈ R₁) (he₂ : e₂ ∈ R₁) (he₃ : e₃ ∈ R₁)
    (he₄ : e₄ ∈ R₁) (n12 : e₁ ≠ e₂) (n13 : e₁ ≠ e₃) (n14 : e₁ ≠ e₄) (n23 : e₂ ≠ e₃) (n24 : e₂ ≠ e₄)
    (n34 : e₃ ≠ e₄) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c)
    (hbd : b ≠ d)
    (j₁ : Γ.Joins e₁ a b) (j₂ : Γ.Joins e₂ b c) (j₃ : Γ.Joins e₃ c d) (j₄ : Γ.Joins e₄ d a) :
    False := by
  have hF : ({e₁, e₂, e₃, e₄} : Finset ℕ) = R₁ := by
    apply hP.ham₁.eq_of_subset
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · exact ⟨e₁, Finset.mem_insert_self _ _⟩
    · intro v _
      rw [degIn_eq_sum, Finset.sum_insert (by simp [n12, n13, n14]),
        Finset.sum_insert (by simp [n23, n24]), Finset.sum_pair n34,
        endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hcd,
        endCount_of_joins j₄ had.symm]
      split_ifs <;> omega
  have := hP.ham₁.card_eq
  rw [← hF, Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
    Finset.card_insert_of_notMem (by simp [n23, n24]), Finset.card_pair n34] at this
  have hodd := hP.odd hcl hnc
  rw [← this] at hodd
  exact absurd hodd (by decide)

set_option maxHeartbeats 4000000 in
/-- **Permutation snarks have girth at least five.** -/
theorem girth5 : Γ.Girth5 := by
  have hloop := hP.no_loop hcl
  have hP' := hP.swap hcl
  have h3' : V₂.card = 3 → False := fun h ↦ hP.no_three hcl hcub hnc (by rw [← hP.card_V₂ hcl]; exact h)
  apply girth5_of_no_short_cycles hcl hloop
  · intro e he e' he' hne a b hab j j'
    exact hP.no_parallel hcl he he' hne hab j j'
  · intro e₁ he₁ e₂ he₂ e₃ he₃ n12 n13 n23 a b c hab hbc hac j₁ j₂ j₃
    obtain ⟨i₁a, hi₁a⟩ := Joins.exists_end j₁
    obtain ⟨i₁b, hi₁b⟩ := Joins.exists_end j₁.symm
    obtain ⟨i₂b, hi₂b⟩ := Joins.exists_end j₂
    obtain ⟨i₂c, hi₂c⟩ := Joins.exists_end j₂.symm
    obtain ⟨i₃c, hi₃c⟩ := Joins.exists_end j₃
    obtain ⟨i₃a, hi₃a⟩ := Joins.exists_end j₃.symm
    have haV : a ∈ Γ.Vs := by rw [← hi₁a]; exact hcl e₁ he₁ _
    have hbV : b ∈ Γ.Vs := by rw [← hi₁b]; exact hcl e₁ he₁ _
    have hcV : c ∈ Γ.Vs := by rw [← hi₂c]; exact hcl e₂ he₂ _
    rcases hP.sides hcl he₁ j₁ with ⟨hs₁, hab'⟩ | ⟨hr₁, ha, hb⟩ | ⟨hr₁, ha, hb⟩ <;>
      rcases hP.sides hcl he₂ j₂ with ⟨hs₂, hbc'⟩ | ⟨hr₂, hb', hc⟩ | ⟨hr₂, hb', hc⟩ <;>
      rcases hP.sides hcl he₃ j₃ with ⟨hs₃, hca'⟩ | ⟨hr₃, hc', ha'⟩ | ⟨hr₃, hc', ha'⟩
    all_goals
      first
      | exact n12 (hP.spoke_unique hbV hs₁ hs₂ hi₁b hi₂b)
      | exact n23 (hP.spoke_unique hcV hs₂ hs₃ hi₂c hi₃c)
      | exact n13 (hP.spoke_unique haV hs₁ hs₃ hi₁a hi₃a)
      | exact hP.no_three hcl hcub hnc (hP.tri_rim₁ hr₁ hr₂ hr₃ n12 n13 n23 hab hbc hac j₁ j₂ j₃)
      | exact h3' (hP'.tri_rim₁ hr₁ hr₂ hr₃ n12 n13 n23 hab hbc hac j₁ j₂ j₃)
      | tauto
  · intro e₁ he₁ e₂ he₂ e₃ he₃ e₄ he₄ n12 n13 n14 n23 n24 n34 a b c d hab hbc hcd had hac hbd
      j₁ j₂ j₃ j₄
    obtain ⟨i₁a, hi₁a⟩ := Joins.exists_end j₁
    obtain ⟨i₁b, hi₁b⟩ := Joins.exists_end j₁.symm
    obtain ⟨i₂b, hi₂b⟩ := Joins.exists_end j₂
    obtain ⟨i₂c, hi₂c⟩ := Joins.exists_end j₂.symm
    obtain ⟨i₃c, hi₃c⟩ := Joins.exists_end j₃
    obtain ⟨i₃d, hi₃d⟩ := Joins.exists_end j₃.symm
    obtain ⟨i₄d, hi₄d⟩ := Joins.exists_end j₄
    obtain ⟨i₄a, hi₄a⟩ := Joins.exists_end j₄.symm
    have haV : a ∈ Γ.Vs := by rw [← hi₁a]; exact hcl e₁ he₁ _
    have hbV : b ∈ Γ.Vs := by rw [← hi₁b]; exact hcl e₁ he₁ _
    have hcV : c ∈ Γ.Vs := by rw [← hi₂c]; exact hcl e₂ he₂ _
    have hdV : d ∈ Γ.Vs := by rw [← hi₃d]; exact hcl e₃ he₃ _
    have hbd₂ := hP.bd_V₂ hcl
    rcases hP.sides hcl he₁ j₁ with ⟨hs₁, hab'⟩ | ⟨hr₁, ha, hb⟩ | ⟨hr₁, ha, hb⟩ <;>
      rcases hP.sides hcl he₂ j₂ with ⟨hs₂, hbc'⟩ | ⟨hr₂, hb', hc⟩ | ⟨hr₂, hb', hc⟩ <;>
      rcases hP.sides hcl he₃ j₃ with ⟨hs₃, hcd'⟩ | ⟨hr₃, hc', hd⟩ | ⟨hr₃, hc', hd⟩ <;>
      rcases hP.sides hcl he₄ j₄ with ⟨hs₄, hda'⟩ | ⟨hr₄, hd', ha'⟩ | ⟨hr₄, hd', ha'⟩
    all_goals
      first
      | exact n12 (hP.spoke_unique hbV hs₁ hs₂ hi₁b hi₂b)
      | exact n23 (hP.spoke_unique hcV hs₂ hs₃ hi₂c hi₃c)
      | exact n34 (hP.spoke_unique hdV hs₃ hs₄ hi₃d hi₄d)
      | exact n14 (hP.spoke_unique haV hs₁ hs₄ hi₁a hi₄a)
      | exact hP.quad_rim₁ hcl hnc hr₁ hr₂ hr₃ hr₄ n12 n13 n14 n23 n24 n34 hab hbc hcd had hac hbd
          j₁ j₂ j₃ j₄
      | exact hP'.quad_rim₁ hcl hnc hr₁ hr₂ hr₃ hr₄ n12 n13 n14 n23 n24 n34 hab hbc hcd had hac hbd
          j₁ j₂ j₃ j₄
      | exact hP.no_rung hcl hcub hnc hab hbc hcd had hac hbd ha' hd' ((hP.mem_V₂_iff hbV).mpr hb')
          ((hP.mem_V₂_iff hcV).mpr hc) hs₁ hr₂ hs₃ hr₄ j₁ j₂ j₃ j₄
      | exact hP'.no_rung hcl hcub hnc hab hbc hcd had hac hbd ((hP.mem_V₂_iff haV).mpr ha')
          ((hP.mem_V₂_iff hdV).mpr hd') hb' hc (by rw [hbd₂]; exact hs₁) hr₂
          (by rw [hbd₂]; exact hs₃) hr₄ j₁ j₂ j₃ j₄
      | exact hP.no_rung hcl hcub hnc hbc hcd had.symm hab.symm hbd hac.symm hb ha
          ((hP.mem_V₂_iff hcV).mpr hc') ((hP.mem_V₂_iff hdV).mpr hd) hs₂ hr₃ hs₄ hr₁ j₂ j₃ j₄ j₁
      | exact hP'.no_rung hcl hcub hnc hbc hcd had.symm hab.symm hbd hac.symm
          ((hP.mem_V₂_iff hbV).mpr hb) ((hP.mem_V₂_iff haV).mpr ha) hc' hd
          (by rw [hbd₂]; exact hs₂) hr₃ (by rw [hbd₂]; exact hs₄) hr₁ j₂ j₃ j₄ j₁
      | tauto

end IsPermGraph

end FinGraph
end GraphPuzzles
