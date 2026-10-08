import GraphPuzzles.Reduction.Parallel.ParallelReduction
import GraphPuzzles.Cuts.CutWitness
import GraphPuzzles.Cuts.CutCharacteristic
import GraphPuzzles.Cuts.Contraction.ContractionBarrierLift

/-! The cut-preserving Petersen exception needed by the near-brick induction. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

/-- A sequence of nontrivial tight-cut contractions carrying a selected
cut to a strictly separating cut of the Petersen graph up to parallel edges.
At each step we retain a shore containing the selected cut; taking its
complement only changes the shore used to represent the same cut. -/
inductive HasTightPetersenMinor :
    {V : Type u} → {E : Type v} → [Fintype V] → [Fintype E] →
    [DecidableEq V] → [DecidableEq E] → (H : LoopMultigraph V E) → Finset V → Prop where
  | here {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {H : LoopMultigraph V E} {X : Finset V}
      (petersen : H.IsPetersenUpToParallel) (strict : H.IsStrictlySeparatingCut X) :
      HasTightPetersenMinor H X
  | contract {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {H : LoopMultigraph V E} (Y : Finset V) (tight : H.IsTightCut Y)
      (nontrivial : IsNontrivialCut Y) (X : Finset (Option Y)) (pole_not_mem : none ∉ X)
      (tail : HasTightPetersenMinor (H.contract Y) X) :
      HasTightPetersenMinor H (sourceShore Y X)
  | compl {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {H : LoopMultigraph V E} {X : Finset V} (tail : HasTightPetersenMinor H X) :
      HasTightPetersenMinor H (Finset.univ \ X)
  | iso {V W : Type u} {E F : Type v} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
      [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
      {H : LoopMultigraph V E} {K : LoopMultigraph W F} {X : Finset V}
      (f : EndpointIso H K) (tail : HasTightPetersenMinor H X) :
      HasTightPetersenMinor K (f.mapVertices X)

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A brick admits no first nontrivial tight contraction, so any such
certificate already identifies the original graph as Petersen up to parallels. -/
theorem HasTightPetersenMinor.petersen_of_brick {X : Finset V}
    (h : H.HasTightPetersenMinor X) (hb : H.IsBrick) : H.IsPetersenUpToParallel := by
  induction h with
  | here hp _ => exact hp
  | contract Y ht hY _ _ _ _ => exact (hb.tight_trivial Y ht hY).elim
  | compl _ ih => exact ih hb
  | iso f _ ih => exact f.isPetersenUpToParallel (ih (f.symm.isBrick hb))

/-- Lift a certificate through a tight contraction, allowing the selected
shore to contain its pole. Complementation handles that orientation. -/
theorem HasTightPetersenMinor.lift_contract {Y : Finset V}
    (ht : H.IsTightCut Y) (hY : IsNontrivialCut Y) {X : Finset (Option Y)}
    (h : (H.contract Y).HasTightPetersenMinor X) :
    H.HasTightPetersenMinor (expandedContractShore Y X) := by
  by_cases hp : none ∈ X
  · have hh := (HasTightPetersenMinor.contract Y ht hY (Finset.univ \ X)
      (by simp [hp]) h.compl).compl
    have he : Finset.univ \ sourceShore Y (Finset.univ \ X) =
        expandedContractShore Y X := by
      rw [← expandedContractShore_eq_source Y (Finset.univ \ X) (by simp [hp])]
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_expandedContractShore,
        not_not]
    exact he ▸ hh
  · rw [expandedContractShore_eq_source Y X hp]
    exact .contract Y ht hY X hp h

/-- The three alternatives for one selected cut in the Section 6 theorem. -/
def NearBrickCutConclusion (H : LoopMultigraph V E) (X : Finset V) : Prop :=
  H.cutCharacteristic X = 3 ∨ H.cutCharacteristic X = ⊤ ∨
    (H.cutCharacteristic X = 5 ∧ H.HasTightPetersenMinor X)

/-- The stronger theorem proved by the Section 6 induction. Keeping its
Petersen certificate is essential when an induction step produces a near-brick. -/
def NearBrickCutTheorem : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (G : LoopMultigraph V' E'), G.IsNearBrick → ∀ X : Finset V', G.IsSeparatingCut X →
      G.NearBrickCutConclusion X

theorem NearBrickCutConclusion.compl {X : Finset V} (h : H.NearBrickCutConclusion X) :
    H.NearBrickCutConclusion (Finset.univ \ X) := by
  rcases h with h | h | ⟨h, hm⟩
  · exact Or.inl ((cutCharacteristic_compl X).trans h)
  · exact Or.inr (Or.inl ((cutCharacteristic_compl X).trans h))
  · exact Or.inr (Or.inr ⟨(cutCharacteristic_compl X).trans h, hm.compl⟩)

/-- A checked reduction of the frozen simple-brick target to the stronger
near-brick theorem. This does not assume that contractions remain simple. -/
theorem camposLucchesi_of_nearBrickCutTheorem (h : NearBrickCutTheorem.{u, v}) :
    CamposLucchesi.{u, v} := by
  intro V E _ _ _ _ H hsimple hb hp X hs hX
  have ho := hs.odd_shore hb.matchingCovered.1 hX
  rcases h H hb.isNearBrick X hs with h3 | ht | ⟨_, hP⟩
  · exact (cutCharacteristic_eq_three_iff ho).mp h3
  · exact (hb.tight_trivial X ((cutCharacteristic_eq_top_iff_tight ho).mp ht) hX).elim
  · exact (hp ((hP.petersen_of_brick hb).isPetersen hsimple)).elim

end GraphPuzzles.LoopMultigraph
