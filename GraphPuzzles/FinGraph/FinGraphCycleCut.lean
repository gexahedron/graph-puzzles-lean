import GraphPuzzles.FinGraph.FinGraphHypo

/-!
# Cycles across a cut

Shared facts about an edge set `C` (typically a Hamilton cycle) and a vertex set `Y`:

* `even_card_inter_bd`: a set with even degrees on `Y` uses an even number of edges of `bd Y`.
* `linked_to_cut`: inside `C ∩ (edgesIn Y ∪ bd Y)` every edge is joined by a chain of adjacent
  edges to a cut edge, provided it is joined to one inside `C`.
* `IsHamCycle.eq_of_subset`: a nonempty subset of a Hamilton cycle with even degrees is the whole
  cycle.
* `exists_two_colouring_cut`: the part of a cut cycle on the `Y` side has a proper
  two-edge-colouring at the vertices of `Y`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section Parity

theorem endsIn_eq_zero_of_not {Y : Finset ℕ} {e : ℕ} (he : e ∈ Γ.Es) (h1 : e ∉ Γ.edgesIn Y)
    (h2 : e ∉ Γ.bd Y) : Γ.endsIn Y e = 0 := by
  rw [endsIn_eq]
  have h0 : Γ.ends e 0 ∉ Y := by
    intro h
    rcases mem_edgesIn_or_bd he h with h' | h'
    · exact h1 h'
    · exact h2 h'
  have h1' : Γ.ends e 1 ∉ Y := by
    intro h
    rcases mem_edgesIn_or_bd he h with h' | h'
    · exact h1 h'
    · exact h2 h'
  rw [if_neg h0, if_neg h1']

/-- **Parity across a cut.** -/
theorem even_card_inter_bd {C Y : Finset ℕ} (hC : C ⊆ Γ.Es)
    (hev : ∀ v ∈ Y, Even (Γ.degIn C v)) : Even (C ∩ Γ.bd Y).card := by
  classical
  have hsum := sum_degIn_eq (Γ := Γ) C Y
  have hL : Even (∑ v ∈ Y, Γ.degIn C v) := Finset.even_sum _ hev
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not C (fun e ↦ e ∈ Γ.edgesIn Y),
    ← Finset.sum_filter_add_sum_filter_not (C.filter fun e ↦ e ∉ Γ.edgesIn Y)
      (fun e ↦ e ∈ Γ.bd Y)] at hL
  rw [Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_edgesIn (Finset.mem_filter.mp he).2),
    Finset.sum_congr (s₂ := (C.filter fun e ↦ e ∉ Γ.edgesIn Y).filter fun e ↦ e ∈ Γ.bd Y) rfl
      (fun e he ↦ endsIn_of_mem_bd (Finset.mem_filter.mp he).2),
    Finset.sum_congr (s₂ := (C.filter fun e ↦ e ∉ Γ.edgesIn Y).filter fun e ↦ ¬ e ∈ Γ.bd Y) rfl
      (fun e he ↦ endsIn_eq_zero_of_not (hC (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2 (Finset.mem_filter.mp he).2),
    Finset.sum_const, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero] at hL
  have hfilt : (C.filter fun e ↦ e ∉ Γ.edgesIn Y).filter (fun e ↦ e ∈ Γ.bd Y) = C ∩ Γ.bd Y := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) h h2⟩, h2⟩
  rw [hfilt] at hL
  obtain ⟨t, ht⟩ := hL
  exact ⟨t - (C.filter fun e ↦ e ∈ Γ.edgesIn Y).card, by omega⟩

end Parity

section Linked

/-- The part of `C` touching `Y`. -/
def sidePart (Γ : FinGraph) (C Y : Finset ℕ) : Finset ℕ := C ∩ (Γ.edgesIn Y ∪ Γ.bd Y)

theorem mem_sidePart_iff {C Y : Finset ℕ} {e : ℕ} :
    e ∈ Γ.sidePart C Y ↔ e ∈ C ∧ (e ∈ Γ.edgesIn Y ∨ e ∈ Γ.bd Y) := by
  simp [sidePart]

theorem sidePart_subset {C Y : Finset ℕ} : Γ.sidePart C Y ⊆ C := Finset.inter_subset_left

/-- An edge of `C` with an end in `Y` lies in the side part. -/
theorem mem_sidePart_of_ends {C Y : Finset ℕ} {e : ℕ} (hC : C ⊆ Γ.Es) (he : e ∈ C) {i : Fin 2}
    (hi : Γ.ends e i ∈ Y) : e ∈ Γ.sidePart C Y :=
  mem_sidePart_iff.mpr ⟨he, mem_edgesIn_or_bd (hC he) hi⟩

/-- An edge of the side part adjacent to an edge of `C` outside it is a cut edge. -/
theorem mem_bd_of_adj_outside {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {f g : ℕ}
    (hf : f ∈ Γ.sidePart C Y) (hg : g ∉ Γ.sidePart C Y) (hadj : Γ.AdjIn C f g) : f ∈ Γ.bd Y := by
  obtain ⟨-, hgC, i, j, hij⟩ := hadj
  have hv : Γ.ends f i ∉ Y := fun h ↦ hg (mem_sidePart_of_ends hC hgC (hij ▸ h))
  rw [mem_sidePart_iff] at hf
  rcases hf.2 with h | h
  · exact absurd ((mem_edgesIn.mp h).2 i) hv
  · exact h

/-- **Linked to a cut edge.**  Inside the side part, every edge joined in `C` to a cut edge is
joined inside the side part to a cut edge. -/
theorem linked_to_cut {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {f a₀ : ℕ} (hf : f ∈ Γ.sidePart C Y)
    (ha₀ : a₀ ∈ Γ.bd Y) (hwalk : Relation.ReflTransGen (Γ.AdjIn C) f a₀) :
    ∃ b ∈ Γ.bd Y, b ∈ Γ.sidePart C Y ∧ Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C Y)) f b := by
  -- head induction: from the end of the walk backwards
  have key : ∀ z, Relation.ReflTransGen (Γ.AdjIn C) z a₀ → z ∈ Γ.sidePart C Y →
      ∃ b ∈ Γ.bd Y, b ∈ Γ.sidePart C Y ∧ Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C Y)) z b := by
    intro z hz
    induction hz using Relation.ReflTransGen.head_induction_on with
    | refl => intro hz; exact ⟨a₀, ha₀, hz, Relation.ReflTransGen.refl⟩
    | @head y y' hyy' _ ih =>
      intro hy
      by_cases hy' : y' ∈ Γ.sidePart C Y
      · obtain ⟨b, hb, hbS, hpath⟩ := ih hy'
        exact ⟨b, hb, hbS, Relation.ReflTransGen.head ⟨hy, hy', hyy'.2.2⟩ hpath⟩
      · exact ⟨y, mem_bd_of_adj_outside hC hy hy' hyy', hy, Relation.ReflTransGen.refl⟩
  exact key f hwalk hf

end Linked

section Saturation

/-- A nonempty subset of a Hamilton cycle with even degrees is the whole cycle. -/
theorem IsHamCycle.eq_of_subset {S C D : Finset ℕ} (hC : Γ.IsHamCycle S C) (hD : D ⊆ C)
    (hne : D.Nonempty) (hev : ∀ v ∈ S, Γ.degIn D v = 0 ∨ Γ.degIn D v = 2) : D = C := by
  apply Finset.Subset.antisymm hD
  obtain ⟨d, hd⟩ := hne
  -- `D` is closed under adjacency in `C`
  have hclosed : ∀ f ∈ D, ∀ g ∈ C, Γ.AdjIn C f g → g ∈ D := by
    intro f hf g hg hadj
    obtain ⟨-, -, i, j, hij⟩ := hadj
    have hv : Γ.ends f i ∈ S := (mem_edgesIn.mp (hC.subset (hD hf))).2 i
    have hpos : 0 < Γ.degIn D (Γ.ends f i) := degIn_pos_of hf
    have h2 : Γ.degIn D (Γ.ends f i) = 2 := by
      rcases hev _ hv with h | h
      · omega
      · exact h
    have hall : Γ.halfEdgesIn D (Γ.ends f i) = Γ.halfEdgesIn C (Γ.ends f i) :=
      Finset.eq_of_subset_of_card_le (halfEdgesIn_mono hD _)
        (by rw [← degIn_eq_card, ← degIn_eq_card, h2, hC.deg _ hv])
    have : (g, j) ∈ Γ.halfEdgesIn D (Γ.ends f i) := by
      rw [hall, mem_halfEdgesIn]; exact ⟨hg, hij.symm⟩
    exact (mem_halfEdgesIn.mp this).1
  intro g hg
  have hwalk := hC.connected d (hD hd) g hg
  induction hwalk with
  | refl => exact hd
  | @tail b c _ hlast ih => exact hclosed b (ih hlast.mem_left) c hlast.mem_right hlast

/-- The vertices of a Hamilton cycle inside `Y` are those of `S` when the cycle is inside `Y`. -/
theorem IsHamCycle.subset_of_subset_edgesIn {S C Y : Finset ℕ} (hC : Γ.IsHamCycle S C)
    (h : C ⊆ Γ.edgesIn Y) : S ⊆ Y := by
  intro v hv
  have hpos : 0 < Γ.degIn C v := by rw [hC.deg v hv]; omega
  rw [degIn_eq_card, Finset.card_pos] at hpos
  obtain ⟨⟨e, i⟩, hei⟩ := hpos
  rw [mem_halfEdgesIn] at hei
  have := (mem_edgesIn.mp (h hei.1)).2 i
  rwa [hei.2] at this

/-- A Hamilton cycle with a cut edge has at least two cut edges. -/
theorem IsHamCycle.two_le_card_inter_bd {S C Y : Finset ℕ} (hC : Γ.IsHamCycle S C)
    (hCE : C ⊆ Γ.Es) (hY : ∀ v ∈ Y, v ∈ S ∨ Γ.degIn C v = 0) {e : ℕ} (he : e ∈ C)
    (heY : e ∈ Γ.bd Y) : 2 ≤ (C ∩ Γ.bd Y).card := by
  have hev := even_card_inter_bd hCE (C := C) (Y := Y) (fun v hv ↦ by
    rcases hY v hv with h | h
    · rw [hC.deg v h]; exact ⟨1, rfl⟩
    · rw [h]; exact ⟨0, rfl⟩)
  have hpos : 0 < (C ∩ Γ.bd Y).card := Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨he, heY⟩⟩
  obtain ⟨t, ht⟩ := hev
  omega

end Saturation

section CutColouring

/-- **Two-colouring the side of a cut cycle.**  If a Hamilton cycle `C` has a cut edge `e`, its
side part has a proper two-edge-colouring at the vertices of `Y`. -/
theorem exists_two_colouring_cut {S C Y : Finset ℕ} (hC : Γ.IsHamCycle S C) (h2 : 2 ≤ S.card)
    {e : ℕ} (he : e ∈ C) (heY : e ∈ Γ.bd Y) :
    ∃ c : ℕ → Fin 2, ∀ f ∈ Γ.sidePart C Y, ∀ g ∈ Γ.sidePart C Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c f ≠ c g := by
  classical
  have hloop := hC.no_loop h2
  have hCE : C ⊆ Γ.Es := hC.subset.trans (edgesIn_subset S)
  have hab : Γ.ends e 0 ≠ Γ.ends e 1 := hloop e he
  have haS : Γ.ends e 0 ∈ S := (mem_edgesIn.mp (hC.subset he)).2 0
  have hbS : Γ.ends e 1 ∈ S := (mem_edgesIn.mp (hC.subset he)).2 1
  have hconnP := isConnected_erase_of_cycle hC.subset hC.deg hC.connected hloop he
  have hPE : C.erase e ⊆ Γ.edgesIn S := (Finset.erase_subset e C).trans hC.subset
  have hdegP : ∀ v ∈ S, Γ.degIn (C.erase e) v ≤ 2 :=
    fun v hv ↦ (degIn_mono (Finset.erase_subset e C) v).trans (hC.deg v hv).le
  have hdega : Γ.degIn (C.erase e) (Γ.ends e 0) = 1 := by
    have := degIn_erase_of_ends he hab 0
    rw [hC.deg _ haS] at this; omega
  have hdegb : Γ.degIn (C.erase e) (Γ.ends e 1) = 1 := by
    have := degIn_erase_of_ends he hab 1
    rw [hC.deg _ hbS] at this; omega
  obtain ⟨c₀, hprop, -⟩ := exists_two_colouring (C.erase e).card (C.erase e) rfl hPE hdegP
    hconnP (fun f hf ↦ hloop f (Finset.erase_subset e C hf)) _ _ haS hbS hab hdega hdegb
  -- the end of `e` in `Y` and the other edge of `C` there
  obtain ⟨iy, hiy, hiy'⟩ := bd_side heY
  have hyS : Γ.ends e iy ∈ S := (mem_edgesIn.mp (hC.subset he)).2 iy
  have hdegy : Γ.degIn (C.erase e) (Γ.ends e iy) = 1 := by
    have := degIn_erase_of_ends he hab iy
    rw [hC.deg _ hyS] at this; omega
  obtain ⟨⟨g, k⟩, hgk⟩ : (Γ.halfEdgesIn (C.erase e) (Γ.ends e iy)).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdegy]; omega
  rw [mem_halfEdgesIn] at hgk
  refine ⟨fun f ↦ if f = e then 1 - c₀ g else c₀ f, ?_⟩
  intro f hf f' hf' hne v hv i j hi hj
  have hfC : f ∈ C := (mem_sidePart_iff.mp hf).1
  have hf'C : f' ∈ C := (mem_sidePart_iff.mp hf').1
  -- an edge of `C` at the `Y`-end of `e` other than `e` is `g`
  have hatY : ∀ f ∈ C, f ≠ e → ∀ i, Γ.ends f i = Γ.ends e iy → f = g := by
    intro f hf hfe i hi
    exact (eq_of_degIn_eq_one hdegy (Finset.mem_erase.mpr ⟨hfe, hf⟩) hgk.1 hi hgk.2).1
  -- an end of `e` in `Y` is its `Y`-end
  have heY' : ∀ i, Γ.ends e i ∈ Y → i = iy := by
    intro i hi
    by_contra h
    rw [fin2_eq_rev_of_ne h] at hi
    exact hiy' hi
  by_cases hfe : f = e <;> by_cases hf'e : f' = e
  · exact absurd (hfe.trans hf'e.symm) hne
  · subst hfe
    have hiiy : i = iy := heY' i (hi ▸ hv)
    subst hiiy
    have hf'g : f' = g := hatY f' hf'C hf'e j (hj.trans hi.symm)
    subst hf'g
    simp only [if_true, hf'e, if_false]
    intro h
    exact (fin2_sub_eq_iff _ _).mp h rfl
  · subst hf'e
    have hjiy : j = iy := heY' j (hj ▸ hv)
    subst hjiy
    have hfg : f = g := hatY f hfC hfe i (hi.trans hj.symm)
    subst hfg
    simp only [if_true, hfe, if_false]
    intro h
    exact (fin2_sub_eq_iff _ _).mp h.symm rfl
  · simp only [hfe, hf'e, if_false]
    exact hprop f (Finset.mem_erase.mpr ⟨hfe, hfC⟩) f' (Finset.mem_erase.mpr ⟨hf'e, hf'C⟩) hne
      ⟨Finset.mem_erase.mpr ⟨hfe, hfC⟩, Finset.mem_erase.mpr ⟨hf'e, hf'C⟩, i, j, hi.trans hj.symm⟩

end CutColouring

end FinGraph
end GraphPuzzles
