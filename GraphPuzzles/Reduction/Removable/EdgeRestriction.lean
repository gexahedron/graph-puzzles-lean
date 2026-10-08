import GraphPuzzles.Cuts.TightCutRestriction
import GraphPuzzles.Cuts.Contraction.ContractionIso

/-! Spanning edge deletion, its contractions, and matching transport. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Delete one labelled edge, retaining every vertex. -/
def deleteEdge (H : LoopMultigraph V E) (e : E) := H.restrictEdges (Finset.univ.erase e)

/-- An edge is removable when its deletion is matching covered. -/
def IsRemovable (H : LoopMultigraph V E) (e : E) : Prop := (H.deleteEdge e).IsMatchingCovered

omit [DecidableEq V] [DecidableEq E] in
theorem IsConnected.of_restrictEdges {S : Finset E}
    (hc : (H.restrictEdges S).IsConnected) : H.IsConnected := by
  intro c he
  exact hc c (fun e ↦ he e.1)

omit [DecidableEq V] [DecidableEq E] in
theorem IsBipartite.restrictEdges (hb : H.IsBipartite) (S : Finset E) :
    (H.restrictEdges S).IsBipartite := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun e ↦ hc e.1⟩

omit [DecidableEq V] [DecidableEq E] in
theorem IsBipartiteOn.restrictEdges {X : Finset V} (hb : H.IsBipartiteOn X)
    (S : Finset E) : (H.restrictEdges S).IsBipartiteOn X := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun e ↦ hc e.1⟩

omit [DecidableEq V] [DecidableEq E] in
theorem IsBipartiteOn.of_restrictEdges {S : Finset E} {X : Finset V}
    (hb : (H.restrictEdges S).IsBipartiteOn X)
    (hS : ∀ e, H.endAt e 0 ∈ X → H.endAt e 1 ∈ X → e ∈ S) :
    H.IsBipartiteOn X := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun e h0 h1 ↦ hc ⟨e, hS e h0 h1⟩ h0 h1⟩

omit [DecidableEq E] in
@[simp] theorem restrictEdges_mem_dangling (S : Finset E) (e : S) (X : Finset V) :
    e ∈ (H.restrictEdges S).dangling X ↔ e.1 ∈ H.dangling X := by
  simp only [mem_dangling, restrictEdges]

omit [DecidableEq E] in
@[simp] theorem restrictEdges_mem_meets (S : Finset E) (e : S) (X : Finset V) :
    e ∈ (H.restrictEdges S).meets X ↔ e.1 ∈ H.meets X := by
  simp only [mem_meets, restrictEdges]

theorem restrictEdges_crossing (S : Finset E) (M : Finset S) (X : Finset V) :
    ((M.image Subtype.val) ∩ H.dangling X).card =
      (M ∩ (H.restrictEdges S).dangling X).card := by
  have heq : (M.image Subtype.val) ∩ H.dangling X =
      (M ∩ (H.restrictEdges S).dangling X).image Subtype.val := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f, hf, rfl⟩, he⟩
      exact ⟨f, ⟨hf, (restrictEdges_mem_dangling S f X).mpr he⟩, rfl⟩
    · rintro ⟨f, ⟨hf, he⟩, rfl⟩
      exact ⟨⟨f, hf, rfl⟩, (restrictEdges_mem_dangling S f X).mp he⟩
  rw [heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem CutPrecedes.restrictEdges {X Y : Finset V} (hp : H.CutPrecedes X Y)
    (S : Finset E) : (H.restrictEdges S).CutPrecedes X Y := by
  intro M hM
  simpa only [restrictEdges_crossing] using hp _ hM.of_restrictEdges

/-- If a matching-covered spanning subgraph does not make the whole graph
matching covered, an omitted edge is inadmissible in the whole graph. -/
theorem IsMatchingCovered.exists_omitted_inadmissible {S : Finset E}
    (hm : (H.restrictEdges S).IsMatchingCovered) (hn : ¬ H.IsMatchingCovered) :
    ∃ e, e ∉ S ∧ ¬ ∃ M, H.IsPerfectMatching M ∧ e ∈ M := by
  have ha : ¬ ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M :=
    fun h ↦ hn ⟨hm.1.of_restrictEdges, h⟩
  push Not at ha
  obtain ⟨e, he⟩ := ha
  refine ⟨e, ?_, by rintro ⟨M, hM, heM⟩; exact he M hM heM⟩
  intro heS
  obtain ⟨M, hM, heM⟩ := hm.2 ⟨e, heS⟩
  exact he _ hM.of_restrictEdges (Finset.mem_image.mpr ⟨⟨e, heS⟩, heM, rfl⟩)

/-- Restriction and contraction commute, with the same vertex labels. -/
def restrictContractIso (S : Finset E) (X : Finset V) :
    EndpointIso ((H.restrictEdges S).contract X)
      ((H.contract X).restrictEdges (Finset.univ.filter fun e ↦ e.1 ∈ S)) where
  vertexEquiv := Equiv.refl _
  edgeEquiv :=
    { toFun := fun e ↦ ⟨⟨e.1.1, (restrictEdges_mem_meets S e.1 X).mp e.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1.2⟩⟩
      invFun := fun e ↦ ⟨⟨e.1.1, (Finset.mem_filter.mp e.2).2⟩,
        (restrictEdges_mem_meets S _ X).mpr e.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  endEquiv _ := Equiv.refl _
  map_endAt _ _ := rfl

/-- A component family remains a component family after edges are removed. -/
def ComponentFamily.restrictEdges {B : Finset V} (F : H.ComponentFamily B)
    (S : Finset E) : (H.restrictEdges S).ComponentFamily B where
  parts := F.parts
  nonempty := F.nonempty
  avoid := F.avoid
  closed := fun Q hQ e k ↦ F.closed Q hQ e.1 k
  pairwise := F.pairwise
  cover := F.cover

end GraphPuzzles.LoopMultigraph
