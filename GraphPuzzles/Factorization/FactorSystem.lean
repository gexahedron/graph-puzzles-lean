import GraphPuzzles.FinGraph.FinGraphCompletionCuts
import GraphPuzzles.Factorization.FactorChain

/-!
# The concrete decomposition system

A *valid datum* of a closed graph is a cycle-separating shore `X` together with a pairing `m`
such that the `X`-pole is isochromatic and the complementary pole heterochromatic for `m`.
The *factor* of a graph at a shore is the cap of its pole if that pole is isochromatic, the
join if it is heterochromatic.  A *step* decomposes a graph at a valid datum into the two
factors.  A *good class* is closed under taking factors and consists of closed cubic graphs of
girth at least five, cyclically `4`-edge-connected, uncolourable, whose cycle-separating poles
are colourable.  This file sets up the decomposition system on `FinGraph` and verifies the
structural fields (symmetry, size decrease, transport along isomorphisms, class closure).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- A valid datum: `X` is the isochromatic side of a cycle-separating `4`-cut with pairing `m`. -/
structure ValidDatum (Γ : FinGraph) (X : Finset ℕ) (m : Fin 3) : Prop where
  cycSep : Γ.CycSep X
  iso : ∃ hP : (Γ.pole X).IsPole4, IsoWith hP m
  het : ∃ hP : (Γ.pole (Γ.Vs \ X)).IsPole4, HetWith hP m

/-- The class hypotheses for unique factorisation. -/
structure GoodClass (P : FinGraph → Prop) : Prop where
  closed : ∀ Γ, P Γ → Γ.IsClosed
  cubic : ∀ Γ, P Γ → Γ.IsCubic
  girth : ∀ Γ, P Γ → Γ.Girth5
  cyc4 : ∀ Γ, P Γ → Γ.Cyc4Conn
  snark : ∀ Γ, P Γ → ¬ Γ.Colourable
  pole_colourable : ∀ Γ, P Γ → ∀ X, Γ.CycSep X → (Γ.pole X).Colourable
  cap_mem : ∀ Γ, P Γ → ∀ X m (hP : (Γ.pole X).IsPole4), ValidDatum Γ X m → P (cap hP m)
  join_mem : ∀ Γ, P Γ → ∀ X m (hP : (Γ.pole (Γ.Vs \ X)).IsPole4), ValidDatum Γ X m →
    P (join hP m)

open Classical in
/-- The factor of a graph at a shore: the cap of an isochromatic pole, the join of a
heterochromatic one. -/
noncomputable def factorOf (Δ : FinGraph) (Z : Finset ℕ) : FinGraph :=
  if h : ∃ (hP : (Δ.pole Z).IsPole4) (m : Fin 3), IsoWith hP m then
    cap h.choose h.choose_spec.choose
  else if h' : ∃ (hP : (Δ.pole Z).IsPole4) (m : Fin 3), HetWith hP m then
    join h'.choose h'.choose_spec.choose
  else Δ

theorem factorOf_eq_cap {Δ : FinGraph} {Z : Finset ℕ} (hP : (Δ.pole Z).IsPole4) {m : Fin 3}
    (hcol : (Δ.pole Z).Colourable) (hiso : IsoWith hP m) : factorOf Δ Z = cap hP m := by
  unfold factorOf
  have h : ∃ (hP : (Δ.pole Z).IsPole4) (m : Fin 3), IsoWith hP m := ⟨hP, m, hiso⟩
  rw [dif_pos h]
  have hm : h.choose_spec.choose = m := IsoWith.unique _ hcol h.choose_spec.choose_spec hiso
  rw [hm]

theorem factorOf_eq_join {Δ : FinGraph} {Z : Finset ℕ} (hP : (Δ.pole Z).IsPole4) {m : Fin 3}
    (hcol : (Δ.pole Z).Colourable) (hhet : HetWith hP m) : factorOf Δ Z = join hP m := by
  unfold factorOf
  have h : ¬ ∃ (hP : (Δ.pole Z).IsPole4) (m : Fin 3), IsoWith hP m := by
    rintro ⟨hP', m', hiso⟩
    exact not_isoWith_hetWith hP hcol hiso hhet
  rw [dif_neg h]
  have h' : ∃ (hP : (Δ.pole Z).IsPole4) (m : Fin 3), HetWith hP m := ⟨hP, m, hhet⟩
  rw [dif_pos h']
  have hm : h'.choose_spec.choose = m := HetWith.unique _ hcol h'.choose_spec.choose_spec hhet
  rw [hm]

/-- A decomposition step: the two factors of a valid datum, in either order. -/
def Step (Δ C D : FinGraph) : Prop :=
  ∃ Z m, Δ.IsClosed ∧ Δ.IsCubic ∧ Δ.Girth5 ∧ (Δ.pole Z).Colourable ∧
    (Δ.pole (Δ.Vs \ Z)).Colourable ∧ ValidDatum Δ Z m ∧
    ((C = factorOf Δ Z ∧ D = factorOf Δ (Δ.Vs \ Z)) ∨
      (C = factorOf Δ (Δ.Vs \ Z) ∧ D = factorOf Δ Z))

theorem Step.symm {Δ C D : FinGraph} (h : Step Δ C D) : Step Δ D C := by
  obtain ⟨Z, m, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨Z, m, h1, h2, h3, h4, h5, h6, h7.symm.imp (fun h ↦ ⟨h.2, h.1⟩) (fun h ↦ ⟨h.2, h.1⟩)⟩

section Basic

variable {Δ : FinGraph}

/-- The pole of a cycle-separating shore of a cubic graph is a `4`-pole. -/
theorem CycSep.isPole4 (hcub : Δ.IsCubic) {Z : Finset ℕ} (hZ : Δ.CycSep Z) :
    (Δ.pole Z).IsPole4 :=
  pole_isPole4 hcub hZ.1 hZ.2.1

/-- A cycle-separating shore of a closed cubic graph of girth five has at least four vertices,
and so does its complement. -/
theorem CycSep.four_le_card (_hcl : Δ.IsClosed) (hcub : Δ.IsCubic) (hg : Δ.Girth5)
    {Z : Finset ℕ} (hZ : Δ.CycSep Z) : 4 ≤ Z.card := by
  have h1 := three_mul_card_eq hcub hZ.1
  have h2 := five_le_card_edgesIn hg hZ.2.2.1
  omega

theorem ValidDatum.compl_card {X : Finset ℕ} {m : Fin 3} (hX : Δ.ValidDatum X m) :
    (Δ.Vs \ X).card + X.card = Δ.Vs.card := by
  rw [Finset.card_sdiff_add_card_eq_card hX.cycSep.1]

/-- Sizes decrease along steps. -/
theorem Step.size_lt {C D : FinGraph} (h : Step Δ C D) :
    C.Vs.card < Δ.Vs.card ∧ D.Vs.card < Δ.Vs.card := by
  obtain ⟨Z, m, hcl, hcub, hg, hcolZ, hcolZc, hv, h7⟩ := h
  have hZ := hv.cycSep
  have hZc := cycSep_compl hcl hZ
  have hPZ := hZ.isPole4 hcub
  have hPZc := hZc.isPole4 hcub
  obtain ⟨_, hiso⟩ := hv.iso
  obtain ⟨_, hhet⟩ := hv.het
  have e1 : factorOf Δ Z = cap hPZ m := factorOf_eq_cap hPZ hcolZ hiso
  have e2 : factorOf Δ (Δ.Vs \ Z) = join hPZc m := factorOf_eq_join hPZc hcolZc hhet
  have c1 : (cap hPZ m).Vs.card = Z.card + 2 := by
    have h₂ : freshV (Δ.pole Z) + 1 ∉ (Δ.pole Z).Vs := freshV_succ_notMem
    have h₁ : freshV (Δ.pole Z) ∉ insert (freshV (Δ.pole Z) + 1) (Δ.pole Z).Vs := by
      rw [Finset.mem_insert, not_or]
      exact ⟨by omega, freshV_notMem⟩
    rw [cap_Vs, Finset.card_insert_of_notMem h₁, Finset.card_insert_of_notMem h₂]
    show Z.card + 1 + 1 = Z.card + 2
    omega
  have c2 : (join hPZc m).Vs.card = (Δ.Vs \ Z).card := by rw [join_Vs, pole_Vs]
  have h4 := hZ.four_le_card hcl hcub hg
  have h4' := hZc.four_le_card hcl hcub hg
  have hsum := hv.compl_card
  rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [e1, e2, c1, c2]
    omega
  · rw [e1, e2, c1, c2]
    omega

/-- Class closure under steps. -/
theorem Step.class_mem {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ) {C D : FinGraph}
    (h : Step Δ C D) : P C ∧ P D := by
  obtain ⟨Z, m, hcl, hcub, hg, hcolZ, hcolZc, hv, h7⟩ := h
  have hZ := hv.cycSep
  have hZc := cycSep_compl hcl hZ
  have hPZ := hZ.isPole4 hcub
  have hPZc := hZc.isPole4 hcub
  obtain ⟨_, hiso⟩ := hv.iso
  obtain ⟨_, hhet⟩ := hv.het
  have e1 : factorOf Δ Z = cap hPZ m := factorOf_eq_cap hPZ hcolZ hiso
  have e2 : factorOf Δ (Δ.Vs \ Z) = join hPZc m := factorOf_eq_join hPZc hcolZc hhet
  have p1 := hG.cap_mem Δ hΔ Z m hPZ hv
  have p2 := hG.join_mem Δ hΔ Z m hPZc hv
  rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [e1, e2]; exact ⟨p1, p2⟩
  · rw [e1, e2]; exact ⟨p2, p1⟩

/-- In a good class every cycle-separating shore carries a step. -/
theorem exists_step_of_cycSep {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ) {Z : Finset ℕ}
    (hZ : Δ.CycSep Z) : Step Δ (factorOf Δ Z) (factorOf Δ (Δ.Vs \ Z)) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hZc := cycSep_compl hcl hZ
  have hPZ := hZ.isPole4 hcub
  have hPZc := hZc.isPole4 hcub
  have hcolZ := hG.pole_colourable Δ hΔ Z hZ
  have hcolZc := hG.pole_colourable Δ hΔ _ hZc
  obtain ⟨m, hm⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPZ hPZc hcolZ hcolZc
  rcases hm with ⟨hiso, hhet⟩ | ⟨hhet, hiso⟩
  · exact ⟨Z, m, hcl, hcub, hG.girth Δ hΔ, hcolZ, hcolZc, ⟨hZ, ⟨hPZ, hiso⟩, ⟨hPZc, hhet⟩⟩,
      Or.inl ⟨rfl, rfl⟩⟩
  · have e : Δ.Vs \ (Δ.Vs \ Z) = Z := Finset.sdiff_sdiff_eq_self hZ.1
    refine ⟨Δ.Vs \ Z, m, hcl, hcub, hG.girth Δ hΔ, hcolZc, by rw [e]; exact hcolZ,
      ⟨hZc, ⟨hPZc, hiso⟩, ⟨by rw [e]; exact hPZ, by
        have := hhet
        rw [← e] at hPZ
        convert this⟩⟩, ?_⟩
    right
    rw [e]
    exact ⟨rfl, rfl⟩

/-- A graph of a good class is terminal iff it has no cycle-separating `4`-cut. -/
theorem terminal_iff {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ) :
    (¬ ∃ C D, Step Δ C D) ↔ ¬ ∃ Z, Δ.CycSep Z := by
  constructor
  · rintro h ⟨Z, hZ⟩
    exact h ⟨_, _, exists_step_of_cycSep hG hΔ hZ⟩
  · rintro h ⟨C, D, Z, m, -, -, -, -, -, hv, -⟩
    exact h ⟨Z, hv.cycSep⟩

end Basic

end FinGraph
end GraphPuzzles
