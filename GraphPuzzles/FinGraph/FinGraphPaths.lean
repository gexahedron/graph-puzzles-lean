import GraphPuzzles.FinGraph.FinGraphCycles
import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap
import GraphPuzzles.Factorization.Bicritical.FactorCutEdges

/-!
# Connected edge sets, cycles and paths in `FinGraph`

* `AdjIn F e f`: two edges of `F` sharing an end; `IsConnected F`: any two edges of `F` are
  joined by a chain of adjacent edges.
* `IsHamCycle S F`: a connected edge set inside `S` with degree two at every vertex of `S`.
* `isConnected_erase_pendant`: removing a pendant edge keeps an edge set connected.
* `isConnected_erase_of_cycle`: removing an edge from a cycle keeps it connected (handshake on
  the component of one end).
* `exists_two_colouring`: a path has a proper two-edge-colouring, whose end edges agree exactly
  when the path has odd length.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section Defs

/-- Two edges of `F` sharing an end. -/
def AdjIn (Γ : FinGraph) (F : Finset ℕ) (e f : ℕ) : Prop :=
  e ∈ F ∧ f ∈ F ∧ ∃ i j, Γ.ends e i = Γ.ends f j

/-- An edge set is connected when any two of its edges are joined by a chain of adjacent edges. -/
def IsConnected (Γ : FinGraph) (F : Finset ℕ) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, Relation.ReflTransGen (Γ.AdjIn F) e f

/-- A Hamilton cycle of the subgraph induced on `S`: a connected edge set inside `S` with degree
two at every vertex of `S`. -/
structure IsHamCycle (Γ : FinGraph) (S : Finset ℕ) (F : Finset ℕ) : Prop where
  subset : F ⊆ Γ.edgesIn S
  deg : ∀ v ∈ S, Γ.degIn F v = 2
  connected : Γ.IsConnected F

/-- Hamiltonian: a Hamilton cycle through all vertices. -/
def IsHamiltonian (Γ : FinGraph) : Prop := ∃ F, Γ.IsHamCycle Γ.Vs F

/-- Hypohamiltonian: not Hamiltonian, but every vertex-deleted subgraph is. -/
def IsHypohamiltonian (Γ : FinGraph) : Prop :=
  ¬ Γ.IsHamiltonian ∧ ∀ u ∈ Γ.Vs, ∃ F, Γ.IsHamCycle (Γ.Vs.erase u) F

theorem AdjIn.symm {F : Finset ℕ} {e f : ℕ} (h : Γ.AdjIn F e f) : Γ.AdjIn F f e := by
  obtain ⟨he, hf, i, j, hij⟩ := h
  exact ⟨hf, he, j, i, hij.symm⟩

theorem adjIn_symmetric (F : Finset ℕ) : Std.Symm (Γ.AdjIn F) := ⟨fun _ _ h ↦ h.symm⟩

theorem AdjIn.mono {F F' : Finset ℕ} (h : F ⊆ F') {e f : ℕ} (hef : Γ.AdjIn F e f) :
    Γ.AdjIn F' e f :=
  ⟨h hef.1, h hef.2.1, hef.2.2⟩

theorem AdjIn.of_mem {F : Finset ℕ} {e f : ℕ} (he : e ∈ F) (hf : f ∈ F) {i j : Fin 2}
    (h : Γ.ends e i = Γ.ends f j) : Γ.AdjIn F e f := ⟨he, hf, i, j, h⟩

theorem AdjIn.mem_left {F : Finset ℕ} {e f : ℕ} (h : Γ.AdjIn F e f) : e ∈ F := h.1
theorem AdjIn.mem_right {F : Finset ℕ} {e f : ℕ} (h : Γ.AdjIn F e f) : f ∈ F := h.2.1

theorem reflTransGen_adjIn_symm {F : Finset ℕ} {e f : ℕ}
    (h : Relation.ReflTransGen (Γ.AdjIn F) e f) : Relation.ReflTransGen (Γ.AdjIn F) f e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact Relation.ReflTransGen.head hlast.symm ih

theorem fin2_eq_of_ne_rev {i l : Fin 2} (h : l ≠ Fin.rev i) : l = i := by
  revert i l; decide

theorem fin2_rev_ne (i : Fin 2) : Fin.rev i ≠ i := by
  revert i; decide

theorem fin2_sub_eq_iff (x y : Fin 2) : 1 - x = y ↔ ¬ x = y := by
  revert x y; decide

/-- The index of an end of a non-loop edge is determined by the vertex. -/
theorem idx_eq_of_ends_eq_single {e : ℕ} (hloop : Γ.ends e 0 ≠ Γ.ends e 1) {i j : Fin 2}
    (h : Γ.ends e i = Γ.ends e j) : i = j := by
  by_contra hij
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hij rfl
  · exact hloop h
  · exact hloop h.symm
  · exact hij rfl

theorem reflTransGen_adjIn_mem {F : Finset ℕ} {e f : ℕ} (he : e ∈ F)
    (h : Relation.ReflTransGen (Γ.AdjIn F) e f) : f ∈ F := by
  induction h with
  | refl => exact he
  | tail _ hlast ih => exact hlast.mem_right

/-- The degree of a vertex in `F` counts the half-edges of `F` at it. -/
theorem degIn_eq_card (F : Finset ℕ) (v : ℕ) : Γ.degIn F v = (Γ.halfEdgesIn F v).card := rfl

theorem halfEdgesIn_mono {F F' : Finset ℕ} (h : F ⊆ F') (v : ℕ) :
    Γ.halfEdgesIn F v ⊆ Γ.halfEdgesIn F' v := by
  intro x hx
  rw [mem_halfEdgesIn] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

/-- A vertex of degree one in `F` carries a unique half-edge of `F`. -/
theorem eq_of_degIn_eq_one {F : Finset ℕ} {v : ℕ} (h : Γ.degIn F v = 1) {e f : ℕ} {i j : Fin 2}
    (he : e ∈ F) (hf : f ∈ F) (hi : Γ.ends e i = v) (hj : Γ.ends f j = v) : e = f ∧ i = j := by
  rw [degIn_eq_card, Finset.card_eq_one] at h
  obtain ⟨x, hx⟩ := h
  have h1 : (e, i) ∈ Γ.halfEdgesIn F v := mem_halfEdgesIn.mpr ⟨he, hi⟩
  have h2 : (f, j) ∈ Γ.halfEdgesIn F v := mem_halfEdgesIn.mpr ⟨hf, hj⟩
  rw [hx, Finset.mem_singleton] at h1 h2
  exact Prod.mk.inj (h1.trans h2.symm)

/-- Two distinct half-edges of `F` at `v` give degree at least two. -/
theorem two_le_degIn {F : Finset ℕ} {v : ℕ} {e f : ℕ} {i j : Fin 2} (he : e ∈ F) (hf : f ∈ F)
    (hi : Γ.ends e i = v) (hj : Γ.ends f j = v) (hne : (e, i) ≠ (f, j)) : 2 ≤ Γ.degIn F v := by
  rw [degIn_eq_card]
  have : ({(e, i), (f, j)} : Finset (ℕ × Fin 2)) ⊆ Γ.halfEdgesIn F v := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_halfEdgesIn.mpr ⟨he, hi⟩
    · exact mem_halfEdgesIn.mpr ⟨hf, hj⟩
  have := Finset.card_le_card this
  rw [Finset.card_pair hne] at this
  exact this

/-- The degree of a vertex in a single non-loop edge at it is one. -/
theorem degIn_singleton_of_ends {e : ℕ} (hloop : Γ.ends e 0 ≠ Γ.ends e 1) (i : Fin 2) :
    Γ.degIn {e} (Γ.ends e i) = 1 := by
  rw [degIn_eq_sum, Finset.sum_singleton]
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [if_pos rfl, if_neg (Ne.symm hloop)]
  · rw [if_neg hloop, if_pos rfl]

/-- The degree in `F.erase e` at an end of a non-loop edge `e` drops by one. -/
theorem degIn_erase_of_ends {F : Finset ℕ} {e : ℕ} (he : e ∈ F) (hloop : Γ.ends e 0 ≠ Γ.ends e 1)
    (i : Fin 2) : Γ.degIn (F.erase e) (Γ.ends e i) + 1 = Γ.degIn F (Γ.ends e i) := by
  have hsplit : F = {e} ∪ F.erase e := by
    rw [← Finset.insert_eq, Finset.insert_erase he]
  have hdisj : Disjoint ({e} : Finset ℕ) (F.erase e) := by
    rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase e F
  conv_rhs => rw [hsplit]
  rw [degIn_union_of_disjoint hdisj, degIn_singleton_of_ends hloop, add_comm]

/-- The degree in `F.erase e` at a vertex not an end of `e` is unchanged. -/
theorem degIn_erase_of_not_ends {F : Finset ℕ} {e : ℕ} (he : e ∈ F) {v : ℕ}
    (hv : ∀ i, Γ.ends e i ≠ v) : Γ.degIn (F.erase e) v = Γ.degIn F v := by
  have hsplit : F = {e} ∪ F.erase e := by
    rw [← Finset.insert_eq, Finset.insert_erase he]
  have hdisj : Disjoint ({e} : Finset ℕ) (F.erase e) := by
    rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase e F
  conv_rhs => rw [hsplit]
  rw [degIn_union_of_disjoint hdisj, degIn_eq_sum {e}, Finset.sum_singleton, if_neg (hv 0),
    if_neg (hv 1)]
  simp

/-- A loop contributes two to the degree of its vertex. -/
theorem two_le_degIn_of_loop {F : Finset ℕ} {e : ℕ} (he : e ∈ F) (hloop : Γ.ends e 0 = Γ.ends e 1) :
    2 ≤ Γ.degIn F (Γ.ends e 0) :=
  two_le_degIn he he rfl hloop.symm (by simp)

end Defs

section Pendant

/-- **Removing a pendant edge keeps an edge set connected.** -/
theorem isConnected_erase_pendant {F : Finset ℕ} (hF : Γ.IsConnected F) {e : ℕ} (he : e ∈ F)
    {i : Fin 2} (hv : Γ.degIn F (Γ.ends e i) = 1) : Γ.IsConnected (F.erase e) := by
  intro f hf f' hf'
  have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
  have hf'e : f' ≠ e := (Finset.mem_erase.mp hf').1
  -- an edge of `F` other than `e` sharing a vertex with `e` shares its other end
  have hshare : ∀ z ∈ F, z ≠ e → ∀ k l, Γ.ends z k = Γ.ends e l → l = Fin.rev i := by
    intro z hz hze k l hkl
    by_contra hli
    have := fin2_eq_of_ne_rev hli
    subst this
    exact hze (eq_of_degIn_eq_one hv hz he hkl rfl).1
  have key : ∀ z, Relation.ReflTransGen (Γ.AdjIn F) f z →
      (z ≠ e → Relation.ReflTransGen (Γ.AdjIn (F.erase e)) f z) ∧
      (z = e → ∃ z₀ ∈ F, z₀ ≠ e ∧ Relation.ReflTransGen (Γ.AdjIn (F.erase e)) f z₀ ∧
        ∃ k, Γ.ends z₀ k = Γ.ends e (Fin.rev i)) := by
    intro z hz
    induction hz with
    | refl => exact ⟨fun _ ↦ Relation.ReflTransGen.refl, fun h ↦ absurd h hfe⟩
    | @tail b c _ hlast ih =>
      obtain ⟨hbF, hcF, k, l, hkl⟩ := hlast
      refine ⟨fun hce ↦ ?_, fun hce ↦ ?_⟩
      · by_cases hbe : b = e
        · subst hbe
          obtain ⟨z₀, hz₀, hz₀e, hpath, k₀, hk₀⟩ := ih.2 rfl
          have hl : k = Fin.rev i := by
            have := hshare c hcF hce l k hkl.symm
            exact this
          refine hpath.tail ⟨Finset.mem_erase.mpr ⟨hz₀e, hz₀⟩, Finset.mem_erase.mpr ⟨hce, hcF⟩,
            k₀, l, ?_⟩
          rw [hk₀, ← hl, hkl]
        · exact (ih.1 hbe).tail ⟨Finset.mem_erase.mpr ⟨hbe, hbF⟩,
            Finset.mem_erase.mpr ⟨hce, hcF⟩, k, l, hkl⟩
      · subst hce
        by_cases hbe : b = c
        · subst hbe
          exact ih.2 rfl
        · have hl : l = Fin.rev i := hshare b hbF hbe k l hkl
          exact ⟨b, hbF, hbe, ih.1 hbe, k, by rw [hkl, hl]⟩
  exact (key f' (hF f (Finset.mem_of_mem_erase hf) f' (Finset.mem_of_mem_erase hf'))).1 hf'e

end Pendant

section Cycle

/-- Adjacency in a subset transfers from a superset when both edges lie in the subset. -/
theorem reflTransGen_mono {F F' : Finset ℕ} (h : F ⊆ F') {e f : ℕ}
    (hef : Relation.ReflTransGen (Γ.AdjIn F) e f) : Relation.ReflTransGen (Γ.AdjIn F') e f :=
  Relation.ReflTransGen.mono (fun _ _ hab ↦ hab.mono h) hef

/-- **Removing an edge from a cycle keeps it connected.** -/
theorem isConnected_erase_of_cycle {S C : Finset ℕ} (hC : C ⊆ Γ.edgesIn S)
    (hdeg : ∀ v ∈ S, Γ.degIn C v = 2) (hconn : Γ.IsConnected C)
    (hloop : ∀ f ∈ C, Γ.ends f 0 ≠ Γ.ends f 1) {e : ℕ} (he : e ∈ C) :
    Γ.IsConnected (C.erase e) := by
  classical
  have hC'C : C.erase e ⊆ C := Finset.erase_subset e C
  have heS : ∀ i, Γ.ends e i ∈ S := (mem_edgesIn.mp (hC he)).2
  -- the other edge of `C` at an end of `e`
  have hother : ∀ i : Fin 2, ∃ f ∈ C.erase e, ∃ k, Γ.ends f k = Γ.ends e i := by
    intro i
    have h1 := degIn_erase_of_ends he (hloop e he) i
    rw [hdeg _ (heS i)] at h1
    have hpos : 0 < Γ.degIn (C.erase e) (Γ.ends e i) := by omega
    rw [degIn_eq_card, Finset.card_pos] at hpos
    obtain ⟨⟨f, k⟩, hfk⟩ := hpos
    rw [mem_halfEdgesIn] at hfk
    exact ⟨f, hfk.1, k, hfk.2⟩
  obtain ⟨f₀, hf₀, k₀, hk₀⟩ := hother 0
  -- the component of `f₀` in `C'`
  set D := (C.erase e).filter (fun f ↦ Relation.ReflTransGen (Γ.AdjIn (C.erase e)) f₀ f)
    with hDdef
  have hDC' : D ⊆ C.erase e := Finset.filter_subset _ _
  have hf₀D : f₀ ∈ D := Finset.mem_filter.mpr ⟨hf₀, Relation.ReflTransGen.refl⟩
  have hDclosed : ∀ f ∈ D, ∀ g ∈ C.erase e, (∃ k l, Γ.ends f k = Γ.ends g l) → g ∈ D := by
    intro f hf g hg hkl
    rw [Finset.mem_filter] at hf ⊢
    obtain ⟨k, l, hkl⟩ := hkl
    exact ⟨hg, hf.2.tail ⟨hf.1, hg, k, l, hkl⟩⟩
  -- at a vertex other than the ends of `e`, the degree in `D` is `0` or `2`
  have hdegD : ∀ v ∈ S, (∀ i, Γ.ends e i ≠ v) → Γ.degIn D v = 0 ∨ Γ.degIn D v = 2 := by
    intro v hv hve
    by_cases h0 : Γ.degIn D v = 0
    · exact Or.inl h0
    · right
      -- some edge of `D` is at `v`, so all edges of `C` at `v` are in `D`
      have hpos : 0 < Γ.degIn D v := Nat.pos_of_ne_zero h0
      rw [degIn_eq_card, Finset.card_pos] at hpos
      obtain ⟨⟨f, k⟩, hfk⟩ := hpos
      rw [mem_halfEdgesIn] at hfk
      have hall : Γ.halfEdgesIn D v = Γ.halfEdgesIn C v := by
        apply Finset.Subset.antisymm (halfEdgesIn_mono (hDC'.trans hC'C) v)
        intro ⟨g, l⟩ hg
        rw [mem_halfEdgesIn] at hg ⊢
        refine ⟨hDclosed f hfk.1 g (Finset.mem_erase.mpr ⟨?_, hg.1⟩) ⟨k, l, by rw [hfk.2, hg.2]⟩,
          hg.2⟩
        rintro rfl
        exact hve l hg.2
      rw [degIn_eq_card, hall, ← degIn_eq_card, hdeg v hv]
  -- the degree of `D` at the first end of `e` is one
  have hdegD0 : Γ.degIn D (Γ.ends e 0) = 1 := by
    have h1 := degIn_erase_of_ends he (hloop e he) 0
    rw [hdeg _ (heS 0)] at h1
    have hle : Γ.degIn D (Γ.ends e 0) ≤ Γ.degIn (C.erase e) (Γ.ends e 0) := degIn_mono hDC' _
    have hge : 0 < Γ.degIn D (Γ.ends e 0) := by
      rw [degIn_eq_card, Finset.card_pos]
      exact ⟨(f₀, k₀), mem_halfEdgesIn.mpr ⟨hf₀D, hk₀⟩⟩
    omega
  -- the second end of `e` carries an edge of `D`, by the handshake lemma
  have hend1 : ∃ f ∈ D, ∃ k, Γ.ends f k = Γ.ends e 1 := by
    by_contra hno
    push Not at hno
    have hzero : Γ.degIn D (Γ.ends e 1) = 0 := by
      rw [degIn_eq_zero_iff]
      intro f hf k hk
      exact hno f hf k hk
    have hsum : ∑ v ∈ S, Γ.degIn D v = 2 * D.card := by
      rw [sum_degIn_eq]
      rw [Finset.sum_congr rfl (fun f hf ↦ endsIn_of_mem_edgesIn (hC (hC'C (hDC' hf)))),
        Finset.sum_const, smul_eq_mul, mul_comm]
    -- split the sum at the two ends of `e`
    have hne01 : Γ.ends e 0 ≠ Γ.ends e 1 := hloop e he
    have hS' : S = insert (Γ.ends e 0) (insert (Γ.ends e 1) ((S.erase (Γ.ends e 0)).erase (Γ.ends e 1))) := by
      rw [Finset.insert_erase, Finset.insert_erase (heS 0)]
      rw [Finset.mem_erase]
      exact ⟨hne01.symm, heS 1⟩
    rw [hS', Finset.sum_insert (by
        rw [Finset.mem_insert, Finset.mem_erase, Finset.mem_erase]
        rintro (h | ⟨-, h, -⟩)
        · exact hne01 h
        · exact h rfl),
      Finset.sum_insert (by
        rw [Finset.mem_erase, Finset.mem_erase]
        rintro ⟨h, -⟩
        exact h rfl), hdegD0, hzero] at hsum
    -- the remaining sum is even
    have heven : Even (∑ v ∈ (S.erase (Γ.ends e 0)).erase (Γ.ends e 1), Γ.degIn D v) := by
      apply Finset.even_sum
      intro v hv
      rw [Finset.mem_erase, Finset.mem_erase] at hv
      rcases hdegD v hv.2.2 (by
          intro i hi
          have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · exact hv.2.1 hi.symm
          · exact hv.1 hi.symm) with h | h
      · rw [h]; exact ⟨0, rfl⟩
      · rw [h]; exact ⟨1, rfl⟩
    obtain ⟨t, ht⟩ := heven
    omega
  -- hence both `C`-edges at the ends of `e` lie in `D`, and `D ∪ {e}` is closed under adjacency
  have hclosed : ∀ f ∈ D ∪ {e}, ∀ g ∈ C, Γ.AdjIn C f g → g ∈ D ∪ {e} := by
    intro f hf g hg hadj
    obtain ⟨-, -, k, l, hkl⟩ := hadj
    rw [Finset.mem_union, Finset.mem_singleton] at hf ⊢
    by_cases hge : g = e
    · exact Or.inr hge
    · left
      rcases hf with hf | rfl
      · exact hDclosed f hf g (Finset.mem_erase.mpr ⟨hge, hg⟩) ⟨k, l, hkl⟩
      · -- `g` is at an end of `e`, hence is the other `C`-edge there, which lies in `D`
        have hk0 : k = 0 ∨ k = 1 := by omega
        rcases hk0 with rfl | rfl
        · -- at the first end: `g` and `f₀` are the unique other edge
          have h1 := degIn_erase_of_ends he (hloop f he) 0
          rw [hdeg _ (heS 0)] at h1
          have hone : Γ.degIn (C.erase f) (Γ.ends f 0) = 1 := by omega
          have := eq_of_degIn_eq_one hone (Finset.mem_erase.mpr ⟨hge, hg⟩) hf₀ hkl.symm hk₀
          rw [this.1]; exact hf₀D
        · obtain ⟨f₁, hf₁D, k₁, hk₁⟩ := hend1
          have h1 := degIn_erase_of_ends he (hloop f he) 1
          rw [hdeg _ (heS 1)] at h1
          have hone : Γ.degIn (C.erase f) (Γ.ends f 1) = 1 := by omega
          have := eq_of_degIn_eq_one hone (Finset.mem_erase.mpr ⟨hge, hg⟩) (hDC' hf₁D)
            hkl.symm hk₁
          rw [this.1]; exact hf₁D
  have hall : ∀ g ∈ C, g ∈ D ∪ {e} := by
    intro g hg
    have hwalk := hconn f₀ (hC'C hf₀) g hg
    induction hwalk with
    | refl => exact Finset.mem_union.mpr (Or.inl hf₀D)
    | @tail b c _ hlast ih =>
      exact hclosed b (ih hlast.mem_left) c hlast.mem_right hlast
  -- every edge of `C'` lies in the component of `f₀`
  intro f hf g hg
  have hfD : f ∈ D := by
    have := hall f (hC'C hf)
    rw [Finset.mem_union, Finset.mem_singleton] at this
    exact this.resolve_right (Finset.mem_erase.mp hf).1
  have hgD : g ∈ D := by
    have := hall g (hC'C hg)
    rw [Finset.mem_union, Finset.mem_singleton] at this
    exact this.resolve_right (Finset.mem_erase.mp hg).1
  exact (reflTransGen_adjIn_symm (Finset.mem_filter.mp hfD).2).trans (Finset.mem_filter.mp hgD).2

end Cycle

section TwoColouring

/-- **Paths have proper two-edge-colourings**, whose end edges receive the same colour exactly
when the number of edges is odd. -/
theorem exists_two_colouring {S : Finset ℕ} : ∀ (n : ℕ) (F : Finset ℕ), F.card = n →
    F ⊆ Γ.edgesIn S → (∀ v ∈ S, Γ.degIn F v ≤ 2) → Γ.IsConnected F →
    (∀ f ∈ F, Γ.ends f 0 ≠ Γ.ends f 1) →
    ∀ a b, a ∈ S → b ∈ S → a ≠ b → Γ.degIn F a = 1 → Γ.degIn F b = 1 →
    ∃ c : ℕ → Fin 2, (∀ e ∈ F, ∀ f ∈ F, e ≠ f → Γ.AdjIn F e f → c e ≠ c f) ∧
      ∀ e ∈ F, ∀ f ∈ F, (∃ i, Γ.ends e i = a) → (∃ j, Γ.ends f j = b) →
        (c e = c f ↔ Odd F.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hn hF hdeg hconn hloop a b haS hbS hab hda hdb
  -- the edge at `a`
  have hpos : 0 < Γ.degIn F a := by omega
  rw [degIn_eq_card, Finset.card_pos] at hpos
  obtain ⟨⟨e, i⟩, hei⟩ := hpos
  rw [mem_halfEdgesIn] at hei
  obtain ⟨he, hi⟩ := hei
  have hloop_e := hloop e he
  -- the other end `w` of `e`
  set w := Γ.ends e (Fin.rev i) with hwdef
  have hwa : w ≠ a := by
    intro h
    exact fin2_rev_ne i (idx_eq_of_ends_eq_single hloop_e (h.trans hi.symm))
  have hwS : w ∈ S := (mem_edgesIn.mp (hF he)).2 _
  set F' := F.erase e with hF'def
  have hF'F : F' ⊆ F := Finset.erase_subset e F
  have hcard' : F'.card + 1 = F.card := by
    rw [hF'def, Finset.card_erase_of_mem he]
    have : 0 < F.card := Finset.card_pos.mpr ⟨e, he⟩
    omega
  -- the only edge of `F` at `a` is `e`
  have hat_a : ∀ f ∈ F, ∀ j, Γ.ends f j = a → f = e := by
    intro f hf j hj
    exact (eq_of_degIn_eq_one hda hf he hj hi).1
  by_cases hF' : F' = ∅
  · -- a single edge from `a` to `b`
    have hFe : F = {e} := by
      rw [← Finset.insert_erase he, ← hF'def, hF', Finset.insert_empty]
    refine ⟨fun _ ↦ 0, fun e' he' f hf hne hadj ↦ ?_, fun e' he' f hf _ _ ↦ ?_⟩
    · rw [hFe, Finset.mem_singleton] at he' hf
      exact absurd (he'.trans hf.symm) hne
    · rw [hFe, Finset.card_singleton]
      simp
  · -- the remainder is a path from `w` to `b`
    have hne' : F'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF'
    have hconn' : Γ.IsConnected F' := isConnected_erase_pendant hconn he (i := i) (hi ▸ hda)
    -- `w ≠ b`, since otherwise `F'` would have no edge at `w` while being connected to `e`
    have hdegw : Γ.degIn F' w = 1 := by
      have h1 := degIn_erase_of_ends he hloop_e (Fin.rev i)
      rw [← hwdef, ← hF'def] at h1
      have hle := hdeg w hwS
      -- some edge of `F'` is at `w`: take an edge of `F'` and the walk to `e`
      obtain ⟨f, hf⟩ := hne'
      have hwalk := hconn f (hF'F hf) e he
      have hexists : ∃ g ∈ F', ∃ k, Γ.ends g k = w := by
        -- the last step of the walk into `e` comes from an edge of `F'` at an end of `e`
        have key : ∀ z, Relation.ReflTransGen (Γ.AdjIn F) f z → z = e →
            ∃ g ∈ F', ∃ k, Γ.ends g k = w := by
          intro z hz
          induction hz with
          | refl => intro h; exact absurd h (Finset.mem_erase.mp hf).1
          | @tail b' c _ hlast ih =>
            intro hce
            subst hce
            by_cases hb'e : b' = c
            · exact ih hb'e
            · obtain ⟨hb'F, -, k, l, hkl⟩ := hlast
              have hl : l = Fin.rev i := by
                by_contra hli
                have := fin2_eq_of_ne_rev hli
                subst this
                exact hb'e (hat_a b' hb'F k (hkl.trans hi))
              exact ⟨b', Finset.mem_erase.mpr ⟨hb'e, hb'F⟩, k, by rw [hkl, hl]⟩
        exact key e hwalk rfl
      obtain ⟨g, hg, k, hk⟩ := hexists
      have hpos' : 0 < Γ.degIn F' w := by
        rw [degIn_eq_card, Finset.card_pos]; exact ⟨(g, k), mem_halfEdgesIn.mpr ⟨hg, hk⟩⟩
      omega
    have hwb : w ≠ b := by
      intro h
      rw [h] at hdegw
      have h1 := degIn_erase_of_ends he hloop_e (Fin.rev i)
      rw [← hwdef, ← hF'def, h, hdb] at h1
      omega
    have hdegb' : Γ.degIn F' b = 1 := by
      rw [degIn_erase_of_not_ends he]
      · exact hdb
      · intro j hj
        have hj0 : j = 0 ∨ j = 1 := by omega
        have hi0 : i = 0 ∨ i = 1 := by omega
        rcases hj0 with rfl | rfl <;> rcases hi0 with rfl | rfl
        · exact hab (hi.symm.trans hj)
        · exact hwb (by rw [hwdef, Iso.rev_one']; exact hj)
        · exact hwb (by rw [hwdef, Iso.rev_zero']; exact hj)
        · exact hab (hi.symm.trans hj)
    obtain ⟨c', hc'prop, hc'end⟩ := ih F'.card (by omega) F' rfl (hF'F.trans hF)
      (fun v hv ↦ (degIn_mono hF'F v).trans (hdeg v hv)) hconn' (fun f hf ↦ hloop f (hF'F hf))
      w b hwS hbS hwb hdegw hdegb'
    -- the edge of `F'` at `w`
    have hpos' : 0 < Γ.degIn F' w := by omega
    rw [degIn_eq_card, Finset.card_pos] at hpos'
    obtain ⟨⟨g, k⟩, hgk⟩ := hpos'
    rw [mem_halfEdgesIn] at hgk
    obtain ⟨hg, hk⟩ := hgk
    refine ⟨fun f ↦ if f = e then 1 - c' g else c' f, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne hadj
      obtain ⟨-, -, k₁, k₂, hk₁₂⟩ := hadj
      by_cases h₁ : e₁ = e <;> by_cases h₂ : e₂ = e
      · exact absurd (h₁.trans h₂.symm) hne
      · subst h₁
        simp only [if_true, h₂, if_false]
        -- `e₂` shares `w` with `e`, so `e₂ = g`
        have hk₂ : Γ.ends e₂ k₂ = w := by
          rw [← hk₁₂]
          by_cases hk : k₁ = Fin.rev i
          · rw [hk, hwdef]
          · have := fin2_eq_of_ne_rev hk
            subst this
            exact absurd (hat_a e₂ he₂ k₂ (hk₁₂.symm.trans hi)) (Ne.symm hne)
        have := (eq_of_degIn_eq_one hdegw (Finset.mem_erase.mpr ⟨h₂, he₂⟩) hg hk₂ hk).1
        subst this
        intro h
        have : c' e₂ = 0 ∨ c' e₂ = 1 := by omega
        rcases this with h' | h' <;> rw [h'] at h <;> simp at h
      · subst h₂
        simp only [if_true, h₁, if_false]
        have hk₁ : Γ.ends e₁ k₁ = w := by
          rw [hk₁₂]
          by_cases hk : k₂ = Fin.rev i
          · rw [hk, hwdef]
          · have := fin2_eq_of_ne_rev hk
            subst this
            exact absurd (hat_a e₁ he₁ k₁ (hk₁₂.trans hi)) hne
        have := (eq_of_degIn_eq_one hdegw (Finset.mem_erase.mpr ⟨h₁, he₁⟩) hg hk₁ hk).1
        subst this
        intro h
        have : c' e₁ = 0 ∨ c' e₁ = 1 := by omega
        rcases this with h' | h' <;> rw [h'] at h <;> simp at h
      · simp only [h₁, h₂, if_false]
        exact hc'prop e₁ (Finset.mem_erase.mpr ⟨h₁, he₁⟩) e₂ (Finset.mem_erase.mpr ⟨h₂, he₂⟩) hne
          ⟨Finset.mem_erase.mpr ⟨h₁, he₁⟩, Finset.mem_erase.mpr ⟨h₂, he₂⟩, k₁, k₂, hk₁₂⟩
    · intro e₁ he₁ f hf ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩
      have he₁e : e₁ = e := hat_a e₁ he₁ j₁ hj₁
      subst e₁
      have hfe : f ≠ e := by
        rintro rfl
        have hj0 : j₂ = 0 ∨ j₂ = 1 := by omega
        have hi0 : i = 0 ∨ i = 1 := by omega
        rcases hj0 with rfl | rfl <;> rcases hi0 with rfl | rfl
        · exact hab (hi.symm.trans hj₂)
        · exact hwb (by rw [hwdef, Iso.rev_one']; exact hj₂)
        · exact hwb (by rw [hwdef, Iso.rev_zero']; exact hj₂)
        · exact hab (hi.symm.trans hj₂)
      simp only [if_true, hfe, if_false]
      have := hc'end g hg f (Finset.mem_erase.mpr ⟨hfe, hf⟩) ⟨k, hk⟩ ⟨j₂, hj₂⟩
      rw [← hcard', Nat.odd_add_one, ← this]
      exact fin2_sub_eq_iff _ _

end TwoColouring

end FinGraph
end GraphPuzzles
