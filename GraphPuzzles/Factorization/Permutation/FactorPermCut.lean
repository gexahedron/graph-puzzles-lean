import GraphPuzzles.Factorization.Permutation.FactorPermGirth
import GraphPuzzles.Factorization.FactorCuts

/-!
# Cuts in permutation snarks

* A connected edge set with no cut edge lies on one side.
* A cycle-separating cut of size at most four cuts both rims; hence permutation snarks are
  cyclically `4`-edge-connected, and a cycle-separating `4`-cut cuts each rim exactly twice and
  contains no spoke.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section OneSide

/-- A connected edge set of a closed graph with no cut edge lies on one side of the cut. -/
theorem isConnected_side (hcl : Γ.IsClosed) {C Y : Finset ℕ} (hC : C ⊆ Γ.Es)
    (hconn : Γ.IsConnected C) (hno : ∀ e ∈ C, e ∉ Γ.bd Y) :
    C ⊆ Γ.edgesIn Y ∨ C ⊆ Γ.edgesIn (Γ.Vs \ Y) := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · exact Or.inl (Finset.empty_subset _)
  have hside : ∀ e ∈ C, e ∈ Γ.edgesIn Y ∨ e ∈ Γ.edgesIn (Γ.Vs \ Y) := by
    intro e he
    by_cases h : Γ.ends e 0 ∈ Y
    · rcases mem_edgesIn_or_bd (hC he) h with h' | h'
      · exact Or.inl h'
      · exact absurd h' (hno e he)
    · rcases mem_edgesIn_or_bd (hC he) (i := 0) (Finset.mem_sdiff.mpr ⟨hcl e (hC he) 0, h⟩) with h' | h'
      · exact Or.inr h'
      · rw [bd_compl hcl] at h'
        exact absurd h' (hno e he)
  -- adjacency preserves the side
  have hstep : ∀ e f, Γ.AdjIn C e f → e ∈ Γ.edgesIn Y → f ∈ Γ.edgesIn Y := by
    rintro e f ⟨-, hf, i, j, hij⟩ he
    have := (mem_edgesIn.mp he).2 i
    rw [hij] at this
    rcases mem_edgesIn_or_bd (hC hf) this with h | h
    · exact h
    · exact absurd h (hno f hf)
  have hstep' : ∀ e f, Γ.AdjIn C e f → e ∈ Γ.edgesIn (Γ.Vs \ Y) → f ∈ Γ.edgesIn (Γ.Vs \ Y) := by
    rintro e f ⟨-, hf, i, j, hij⟩ he
    have := (mem_edgesIn.mp he).2 i
    rw [hij] at this
    rcases mem_edgesIn_or_bd (hC hf) this with h | h
    · exact h
    · rw [bd_compl hcl] at h
      exact absurd h (hno f hf)
  rcases hside e₀ he₀ with h₀ | h₀
  · left
    intro f hf
    have hwalk := hconn e₀ he₀ f hf
    induction hwalk with
    | refl => exact h₀
    | @tail b c _ hlast ih => exact hstep b c hlast (ih hlast.mem_left)
  · right
    intro f hf
    have hwalk := hconn e₀ he₀ f hf
    induction hwalk with
    | refl => exact h₀
    | @tail b c _ hlast ih => exact hstep' b c hlast (ih hlast.mem_left)

/-- A shore carrying a cycle in a cubic graph of girth at least five has at least four
vertices. -/
theorem four_le_card_of_hasCycle (hcub : Γ.IsCubic) (hg5 : Γ.Girth5) {X : Finset ℕ}
    (hX : X ⊆ Γ.Vs) (hc : Γ.HasCycle X) : 4 ≤ X.card := by
  obtain ⟨F, hF, hne, hev⟩ := hc
  have h5 := hg5 F (hF.trans (edgesIn_subset X)) hne hev
  have hle := Finset.card_le_card hF
  have := three_mul_card_eq hcub hX
  omega

end OneSide

section PermCut

variable {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂) (hcl : Γ.IsClosed)
  (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable)
include hP hcl hcub hnc

omit hcub hnc in
omit hcl in
/-- If a rim lies inside `Y`, every vertex outside `Y` sends its spoke across the cut, so there
are at most as many vertices outside `Y` as spokes in the cut. -/
theorem IsPermGraph.card_le_of_rim_inside {Y : Finset ℕ} (_hY : Y ⊆ Γ.Vs)
    (hR : R₁ ⊆ Γ.edgesIn Y) : (Γ.Vs \ Y).card ≤ (Γ.bd Y ∩ Γ.bd V₁).card := by
  classical
  have hV₁Y : V₁ ⊆ Y := hP.ham₁.subset_of_subset_edgesIn hR
  have hspoke : ∀ v ∈ Γ.Vs \ Y, ∃ s ∈ Γ.bd Y ∩ Γ.bd V₁, ∃ i, Γ.ends s i = v := by
    intro v hv
    have hvV := (Finset.mem_sdiff.mp hv).1
    obtain ⟨⟨s, i⟩, hs⟩ : (Γ.halfEdgesIn (Γ.bd V₁) v).Nonempty := by
      rw [← Finset.card_pos, ← degIn_eq_card, hP.spoke v hvV]; omega
    rw [mem_halfEdgesIn] at hs
    dsimp only at hs
    have hv₂ : v ∈ V₂ := (hP.mem_V₂_iff hvV).mpr (fun h ↦ (Finset.mem_sdiff.mp hv).2 (hV₁Y h))
    have hother : Γ.ends s (Fin.rev i) ∈ V₁ := hP.spoke_other_end₂ hs.1 (hs.2 ▸ hv₂)
    refine ⟨s, Finset.mem_inter.mpr ⟨?_, hs.1⟩, i, hs.2⟩
    rw [mem_bd]
    refine ⟨bd_subset _ hs.1, ?_⟩
    have h1 : Γ.ends s (Fin.rev i) ∈ Y := hV₁Y hother
    have h2 : Γ.ends s i ∉ Y := hs.2 ▸ (Finset.mem_sdiff.mp hv).2
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rw [Iso.rev_zero'] at h1; exact fun h ↦ h2 (h.mpr h1)
    · rw [Iso.rev_one'] at h1; exact fun h ↦ h2 (h.mp h1)
  choose f hf using hspoke
  have hinj : ∀ v (hv : v ∈ Γ.Vs \ Y) w (hw : w ∈ Γ.Vs \ Y), f v hv = f w hw → v = w := by
    intro v hv w hw hvw
    obtain ⟨hsv, i, hi⟩ := hf v hv
    obtain ⟨-, j, hj⟩ := hf w hw
    rw [hvw] at hi hsv
    by_cases hij : i = j
    · rw [hij] at hi; exact hi.symm.trans hj
    · exfalso
      rw [fin2_eq_rev_of_ne hij] at hi
      have hv₂ : v ∈ V₂ := (hP.mem_V₂_iff (Finset.mem_sdiff.mp hv).1).mpr
        (fun h ↦ (Finset.mem_sdiff.mp hv).2 (hV₁Y h))
      have hw₂ : w ∈ V₂ := (hP.mem_V₂_iff (Finset.mem_sdiff.mp hw).1).mpr
        (fun h ↦ (Finset.mem_sdiff.mp hw).2 (hV₁Y h))
      have := hP.spoke_other_end₂ (Finset.mem_inter.mp hsv).2 (hj ▸ hw₂)
      rw [hi] at this
      exact Finset.disjoint_left.mp hP.disj this hv₂
  calc (Γ.Vs \ Y).card = ((Γ.Vs \ Y).attach.image fun v ↦ f v.1 v.2).card := by
        rw [Finset.card_image_of_injective]
        · rw [Finset.card_attach]
        · intro v w hvw
          exact Subtype.ext (hinj v.1 v.2 w.1 w.2 hvw)
    _ ≤ (Γ.bd Y ∩ Γ.bd V₁).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_image] at hs
        obtain ⟨v, -, rfl⟩ := hs
        exact (hf v.1 v.2).1

omit hcl hcub hnc in
/-- The rim `R₂` on the vertices of `Y` outside `V₂` has degree zero. -/
theorem IsPermGraph.mem_or_degIn_zero {Y : Finset ℕ} : ∀ v ∈ Y, v ∈ V₂ ∨ Γ.degIn R₂ v = 0 := by
  intro v hv
  by_cases h : v ∈ V₂
  · exact Or.inl h
  · right
    rw [degIn_eq_zero_iff]
    intro e he i hi
    exact h (hi ▸ (mem_edgesIn.mp (hP.ham₂.subset he)).2 i)

/-- Rims have at least five vertices. -/
theorem IsPermGraph.five_le : 5 ≤ V₁.card := by
  have h3 := hP.three
  have hodd := hP.odd hcl hnc
  have hne3 : V₁.card ≠ 3 := fun h ↦ hP.no_three hcl hcub hnc h
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **A rim inside a shore of a small cut whose complement carries a cycle is impossible.** -/
theorem IsPermGraph.rim_inside_absurd {Y : Finset ℕ} (hY : Y ⊆ Γ.Vs) (hbd : (Γ.bd Y).card ≤ 4)
    (hcYc : Γ.HasCycle (Γ.Vs \ Y)) (hR : R₁ ⊆ Γ.edgesIn Y) : False := by
  classical
  have hg5 := hP.girth5 hcl hcub hnc
  have hYc4 := four_le_card_of_hasCycle hcub hg5 Finset.sdiff_subset hcYc
  have hle := hP.card_le_of_rim_inside hY hR
  have hV₁Y : V₁ ⊆ Y := hP.ham₁.subset_of_subset_edgesIn hR
  by_cases h2 : (R₂ ∩ Γ.bd Y).Nonempty
  · obtain ⟨e, he⟩ := h2
    have h2' := hP.ham₂.two_le_card_inter_bd hP.R₂_subset (hP.mem_or_degIn_zero)
      (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2
    -- the spokes and the `R₂`-edges of the cut are disjoint
    have hdisj : Disjoint (Γ.bd Y ∩ Γ.bd V₁) (R₂ ∩ Γ.bd Y) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact hP.rim_not_spoke₂ hcl (Finset.mem_inter.mp hx').1 (Finset.mem_inter.mp hx).2
    have hsub : (Γ.bd Y ∩ Γ.bd V₁) ∪ (R₂ ∩ Γ.bd Y) ⊆ Γ.bd Y :=
      Finset.union_subset Finset.inter_subset_left Finset.inter_subset_right
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at h2
    have hno : ∀ e ∈ R₂, e ∉ Γ.bd Y := fun e he h ↦
      Finset.notMem_empty e (h2 ▸ Finset.mem_inter.mpr ⟨he, h⟩)
    rcases isConnected_side hcl hP.R₂_subset hP.ham₂.connected hno with hside | hside
    · -- both rims inside `Y`: nothing outside
      have hV₂Y : V₂ ⊆ Y := hP.ham₂.subset_of_subset_edgesIn hside
      have : Γ.Vs \ Y = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hv
        have hvV := (Finset.mem_sdiff.mp hv).1
        rw [← hP.union, Finset.mem_union] at hvV
        rcases hvV with h | h
        · exact (Finset.mem_sdiff.mp hv).2 (hV₁Y h)
        · exact (Finset.mem_sdiff.mp hv).2 (hV₂Y h)
      rw [this, Finset.card_empty] at hYc4
      omega
    · -- `R₂` outside: every spoke crosses
      have hV₂Yc : V₂ ⊆ Γ.Vs \ Y := hP.ham₂.subset_of_subset_edgesIn hside
      have hall : Γ.bd V₁ ⊆ Γ.bd Y := by
        intro s hs
        obtain ⟨i, hi, hi'⟩ := bd_side hs
        have hsE := bd_subset _ hs
        have h1 : Γ.ends s i ∈ Y := hV₁Y hi
        have h2 : Γ.ends s (Fin.rev i) ∉ Y := by
          have := hV₂Yc ((hP.mem_V₂_iff (hcl s hsE _)).mpr hi')
          exact (Finset.mem_sdiff.mp this).2
        rw [mem_bd]
        refine ⟨hsE, ?_⟩
        have hi0 : i = 0 ∨ i = 1 := by omega
        rcases hi0 with rfl | rfl
        · rw [Iso.rev_zero'] at h2; exact fun h ↦ h2 (h.mp h1)
        · rw [Iso.rev_one'] at h2; exact fun h ↦ h2 (h.mpr h1)
      have := Finset.card_le_card hall
      rw [hP.card_bd] at this
      have := hP.five_le hcl hcub hnc
      omega

/-- **A cycle-separating cut of size at most four cuts the first rim.** -/
theorem IsPermGraph.rim_cut {Y : Finset ℕ} (hY : Y ⊆ Γ.Vs) (hbd : (Γ.bd Y).card ≤ 4)
    (hcY : Γ.HasCycle Y) (hcYc : Γ.HasCycle (Γ.Vs \ Y)) : (R₁ ∩ Γ.bd Y).Nonempty := by
  by_contra hno
  rw [Finset.not_nonempty_iff_eq_empty] at hno
  have hno' : ∀ e ∈ R₁, e ∉ Γ.bd Y := fun e he h ↦
    Finset.notMem_empty e (hno ▸ Finset.mem_inter.mpr ⟨he, h⟩)
  rcases isConnected_side hcl hP.R₁_subset hP.ham₁.connected hno' with hside | hside
  · exact hP.rim_inside_absurd hcl hcub hnc hY hbd hcYc hside
  · have hbd' : (Γ.bd (Γ.Vs \ Y)).card ≤ 4 := by rw [bd_compl hcl]; exact hbd
    have hcY' : Γ.HasCycle (Γ.Vs \ (Γ.Vs \ Y)) := by rw [Finset.sdiff_sdiff_eq_self hY]; exact hcY
    exact hP.rim_inside_absurd hcl hcub hnc Finset.sdiff_subset hbd' hcY' hside

/-- Both rims are cut. -/
theorem IsPermGraph.rims_cut {Y : Finset ℕ} (hY : Y ⊆ Γ.Vs) (hbd : (Γ.bd Y).card ≤ 4)
    (hcY : Γ.HasCycle Y) (hcYc : Γ.HasCycle (Γ.Vs \ Y)) :
    (R₁ ∩ Γ.bd Y).Nonempty ∧ (R₂ ∩ Γ.bd Y).Nonempty :=
  ⟨hP.rim_cut hcl hcub hnc hY hbd hcY hcYc, (hP.swap hcl).rim_cut hcl hcub hnc hY hbd hcY hcYc⟩

/-- **Permutation snarks are cyclically `4`-edge-connected.** -/
theorem IsPermGraph.cyc4Conn : Γ.Cyc4Conn := by
  intro X hX hcX hcXc
  by_contra hlt
  push Not at hlt
  obtain ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩ := hP.rims_cut hcl hcub hnc hX (by omega) hcX hcXc
  have h1 := hP.ham₁.two_le_card_inter_bd hP.R₁_subset (hP.swap hcl).mem_or_degIn_zero
    (Finset.mem_inter.mp he₁).1 (Finset.mem_inter.mp he₁).2
  have h2 := hP.ham₂.two_le_card_inter_bd hP.R₂_subset hP.mem_or_degIn_zero
    (Finset.mem_inter.mp he₂).1 (Finset.mem_inter.mp he₂).2
  have hdisj : Disjoint (R₁ ∩ Γ.bd X) (R₂ ∩ Γ.bd X) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp hP.disjoint_rims (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hx').1
  have hsub : (R₁ ∩ Γ.bd X) ∪ (R₂ ∩ Γ.bd X) ⊆ Γ.bd X :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

/-- **Structure of a cycle-separating `4`-cut**: each rim is cut exactly twice and no spoke is
cut. -/
theorem IsPermGraph.cycSep_structure {Y : Finset ℕ} (hY : Γ.CycSep Y) :
    (R₁ ∩ Γ.bd Y).card = 2 ∧ (R₂ ∩ Γ.bd Y).card = 2 ∧ Γ.bd Y ∩ Γ.bd V₁ = ∅ := by
  classical
  obtain ⟨hYV, hbd, hcY, hcYc⟩ := hY
  obtain ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩ := hP.rims_cut hcl hcub hnc hYV hbd.le hcY hcYc
  have h1 := hP.ham₁.two_le_card_inter_bd hP.R₁_subset (hP.swap hcl).mem_or_degIn_zero
    (Finset.mem_inter.mp he₁).1 (Finset.mem_inter.mp he₁).2
  have h2 := hP.ham₂.two_le_card_inter_bd hP.R₂_subset hP.mem_or_degIn_zero
    (Finset.mem_inter.mp he₂).1 (Finset.mem_inter.mp he₂).2
  -- the cut is partitioned into the two rim parts and the spokes
  have hpart : Γ.bd Y = (R₁ ∩ Γ.bd Y) ∪ (R₂ ∩ Γ.bd Y) ∪ (Γ.bd Y ∩ Γ.bd V₁) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      have heE := bd_subset _ he
      have h0 := hcl e heE 0
      rw [← hP.union, Finset.mem_union] at h0
      rcases h0 with h | h
      · rcases hP.edge_at_V₁ heE h with h' | h'
        · exact Or.inl (Or.inl ⟨h', he⟩)
        · exact Or.inr ⟨he, h'⟩
      · rcases hP.edge_at_V₂ hcl heE h with h' | h'
        · exact Or.inl (Or.inr ⟨h', he⟩)
        · exact Or.inr ⟨he, h'⟩
    · rintro ((h | h) | h)
      · exact h.2
      · exact h.2
      · exact h.1
  have hd12 : Disjoint (R₁ ∩ Γ.bd Y) (R₂ ∩ Γ.bd Y) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp hP.disjoint_rims (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hx').1
  have hd3 : Disjoint ((R₁ ∩ Γ.bd Y) ∪ (R₂ ∩ Γ.bd Y)) (Γ.bd Y ∩ Γ.bd V₁) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hP.rim_not_spoke₁ (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx').2
    · exact hP.rim_not_spoke₂ hcl (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx').2
  have hcard := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12, hbd] at hcard
  refine ⟨by omega, by omega, ?_⟩
  rw [← Finset.card_eq_zero]
  omega

end PermCut

end FinGraph
end GraphPuzzles
