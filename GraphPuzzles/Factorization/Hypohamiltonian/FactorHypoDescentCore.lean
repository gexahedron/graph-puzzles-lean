import GraphPuzzles.FinGraph.FinGraphCycleCut

/-!
# Alternating chains of cut edges

For a connected edge set `C` and a shore `Y`, any two cut edges of `C` are joined by a chain of
cut edges in which consecutive members are linked inside the `Y`-side part or inside the
complementary side part.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- Two cut edges linked on one of the two sides. -/
def SideLink (Γ : FinGraph) (C Y : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ C ∩ Γ.bd Y ∧ b ∈ C ∩ Γ.bd Y ∧
    (Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C Y)) a b ∨
      Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C (Γ.Vs \ Y))) a b)

theorem mem_sidePart_compl_of_bd (hcl : Γ.IsClosed) {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {e : ℕ}
    (he : e ∈ C) (heY : e ∈ Γ.bd Y) : e ∈ Γ.sidePart C (Γ.Vs \ Y) := by
  obtain ⟨i, -, hi'⟩ := bd_side heY
  exact mem_sidePart_of_ends hC he (i := Fin.rev i)
    (Finset.mem_sdiff.mpr ⟨hcl e (bd_subset Y heY) _, hi'⟩)

theorem mem_sidePart_of_bd {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {e : ℕ} (he : e ∈ C)
    (heY : e ∈ Γ.bd Y) : e ∈ Γ.sidePart C Y := by
  obtain ⟨i, hi, -⟩ := bd_side heY
  exact mem_sidePart_of_ends hC he hi

/-- Every edge of `C` lies on one of the two sides. -/
theorem mem_sidePart_or (hcl : Γ.IsClosed) {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {e : ℕ} (he : e ∈ C) :
    e ∈ Γ.sidePart C Y ∨ e ∈ Γ.sidePart C (Γ.Vs \ Y) := by
  by_cases h : Γ.ends e 0 ∈ Y
  · exact Or.inl (mem_sidePart_of_ends hC he h)
  · exact Or.inr (mem_sidePart_of_ends hC he (i := 0) (Finset.mem_sdiff.mpr ⟨hcl e (hC he) 0, h⟩))

/-- An edge of one side sharing a vertex with an edge not on that side is a cut edge. -/
theorem mem_bd_of_sides {C Y : Finset ℕ} (hC : C ⊆ Γ.Es) {z z' : ℕ} (hz : z ∉ Γ.sidePart C Y)
    (hz' : z' ∈ Γ.sidePart C Y) (hadj : Γ.AdjIn C z z') : z' ∈ Γ.bd Y :=
  mem_bd_of_adj_outside hC hz' hz hadj.symm

/-- **Alternating chains.** -/
theorem alternating_chain (hcl : Γ.IsClosed) {C Y : Finset ℕ} (hC : C ⊆ Γ.Es)
    (hconn : Γ.IsConnected C) {a b : ℕ} (ha : a ∈ C ∩ Γ.bd Y) (hb : b ∈ C ∩ Γ.bd Y) :
    Relation.ReflTransGen (Γ.SideLink C Y) a b := by
  have haC := (Finset.mem_inter.mp ha).1
  have hbC := (Finset.mem_inter.mp hb).1
  have hwalk := hconn a haC b hbC
  have key : ∀ z, Relation.ReflTransGen (Γ.AdjIn C) a z →
      (z ∈ Γ.sidePart C Y → ∃ k ∈ C ∩ Γ.bd Y, Relation.ReflTransGen (Γ.SideLink C Y) a k ∧
        Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C Y)) k z) ∧
      (z ∈ Γ.sidePart C (Γ.Vs \ Y) → ∃ k ∈ C ∩ Γ.bd Y,
        Relation.ReflTransGen (Γ.SideLink C Y) a k ∧
        Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C (Γ.Vs \ Y))) k z) := by
    intro z hz
    induction hz with
    | refl =>
      exact ⟨fun _ ↦ ⟨a, ha, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
        fun _ ↦ ⟨a, ha, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩⟩
    | @tail y z _ hyz ih =>
      refine ⟨fun hzY ↦ ?_, fun hzYc ↦ ?_⟩
      · by_cases hyY : y ∈ Γ.sidePart C Y
        · obtain ⟨k, hk, hak, hky⟩ := ih.1 hyY
          exact ⟨k, hk, hak, hky.tail ⟨hyY, hzY, hyz.2.2⟩⟩
        · have hyYc : y ∈ Γ.sidePart C (Γ.Vs \ Y) :=
            (mem_sidePart_or hcl hC hyz.mem_left).resolve_left hyY
          have hzbd : z ∈ Γ.bd Y := mem_bd_of_sides hC hyY hzY hyz
          have hzYc : z ∈ Γ.sidePart C (Γ.Vs \ Y) := mem_sidePart_compl_of_bd hcl hC hyz.mem_right hzbd
          obtain ⟨k, hk, hak, hky⟩ := ih.2 hyYc
          have hkz : Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C (Γ.Vs \ Y))) k z :=
            hky.tail ⟨hyYc, hzYc, hyz.2.2⟩
          have hzK : z ∈ C ∩ Γ.bd Y := Finset.mem_inter.mpr ⟨hyz.mem_right, hzbd⟩
          exact ⟨z, hzK, hak.tail ⟨hk, hzK, Or.inr hkz⟩, Relation.ReflTransGen.refl⟩
      · by_cases hyYc : y ∈ Γ.sidePart C (Γ.Vs \ Y)
        · obtain ⟨k, hk, hak, hky⟩ := ih.2 hyYc
          exact ⟨k, hk, hak, hky.tail ⟨hyYc, hzYc, hyz.2.2⟩⟩
        · have hyY : y ∈ Γ.sidePart C Y :=
            (mem_sidePart_or hcl hC hyz.mem_left).resolve_right hyYc
          have hzbd : z ∈ Γ.bd Y := by
            have := mem_bd_of_sides hC hyYc hzYc hyz
            rwa [bd_compl hcl] at this
          have hzY : z ∈ Γ.sidePart C Y := mem_sidePart_of_bd hC hyz.mem_right hzbd
          obtain ⟨k, hk, hak, hky⟩ := ih.1 hyY
          have hkz : Relation.ReflTransGen (Γ.AdjIn (Γ.sidePart C Y)) k z :=
            hky.tail ⟨hyY, hzY, hyz.2.2⟩
          have hzK : z ∈ C ∩ Γ.bd Y := Finset.mem_inter.mpr ⟨hyz.mem_right, hzbd⟩
          exact ⟨z, hzK, hak.tail ⟨hk, hzK, Or.inl hkz⟩, Relation.ReflTransGen.refl⟩
  obtain ⟨k, hk, hak, hkb⟩ := (key b hwalk).1 (mem_sidePart_of_bd hC hbC (Finset.mem_inter.mp hb).2)
  exact hak.tail ⟨hk, hb, Or.inl hkb⟩

end FinGraph
end GraphPuzzles
