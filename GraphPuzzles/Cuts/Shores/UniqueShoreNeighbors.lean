import GraphPuzzles.Petersen.Minors.TightPetersenShore
import GraphPuzzles.Matching.MatchingReachability

/-! Unique shore neighbors and their transport under graph reductions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Each vertex outside the shore has at most one distinct neighbor in it. -/
def HasUniqueCrossNeighbor (H : LoopMultigraph V E) (S : Finset V) : Prop :=
  ∀ w, w ∉ S → ∀ a ∈ S, ∀ b ∈ S, ∀ e f,
    H.Joins e w a → H.Joins f w b → a = b

omit [DecidableEq E] in
theorem HasUniqueCrossNeighbor.of_perfect_dangling {S : Finset V}
    (hm : H.IsPerfectMatching (H.dangling S)) : H.HasUniqueCrossNeighbor S := by
  intro w hw a ha b hb e f he hf
  have hem : e ∈ H.dangling S := by
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [mem_dangling, h0, h1, hw, ha]
  have hfm : f ∈ H.dangling S := by
    rcases hf with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [mem_dangling, h0, h1, hw, hb]
  exact hm.on_univ.joins_unique hem hfm he hf

omit [DecidableEq V] [DecidableEq E] in
theorem HasUniqueCrossNeighbor.of_parallelReduction
    {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    {K : LoopMultigraph W F} (f : ParallelReduction H K) {S : Finset V}
    (h : K.HasUniqueCrossNeighbor (f.mapVertices S)) : H.HasUniqueCrossNeighbor S := by
  intro w hw a ha b hb e g he hg
  apply f.vertexEquiv.injective
  exact h (f.vertexEquiv w) (fun hh ↦ hw ((f.mem_mapVertices S w).mp hh))
    _ ((f.mem_mapVertices S a).mpr ha) _ ((f.mem_mapVertices S b).mpr hb)
    (f.edgeMap e) (f.edgeMap g) ((f.joins_iff e w a).mp he) ((f.joins_iff g w b).mp hg)

omit [DecidableEq E] in
theorem Joins.contract {Y : Finset V} {e : E} {a b : V}
    (he : H.Joins e a b) (hm : e ∈ H.meets Y) :
    (H.contract Y).Joins ⟨e, hm⟩ (contractVertex Y a) (contractVertex Y b) := by
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨congrArg (contractVertex Y) h0, congrArg (contractVertex Y) h1⟩
  · exact Or.inr ⟨congrArg (contractVertex Y) h0, congrArg (contractVertex Y) h1⟩

omit [DecidableEq E] in
/-- Collapsing vertices outside the shore cannot create additional distinct
neighbors of an original exterior vertex. -/
theorem HasUniqueCrossNeighbor.of_contract {Y : Finset V} {S : Finset (Option Y)}
    (hp : none ∉ S) (h : (H.contract Y).HasUniqueCrossNeighbor S) :
    H.HasUniqueCrossNeighbor (sourceShore Y S) := by
  intro w hw a ha b hb e f he hf
  have hmem (v : V) : contractVertex Y v ∈ S ↔ v ∈ sourceShore Y S := by
    rw [← expandedContractShore_eq_source Y S hp]
    exact (mem_expandedContractShore Y S v).symm
  have hme : e ∈ H.meets Y := by
    obtain ⟨k, hk⟩ := (H.joins_comm.mp he).exists_end
    exact mem_meets.mpr ⟨k, hk.symm ▸ sourceShore_subset Y S ha⟩
  have hmf : f ∈ H.meets Y := by
    obtain ⟨k, hk⟩ := (H.joins_comm.mp hf).exists_end
    exact mem_meets.mpr ⟨k, hk.symm ▸ sourceShore_subset Y S hb⟩
  have hh := h (contractVertex Y w) (fun hh ↦ hw ((hmem w).mp hh))
    _ ((hmem a).mpr ha) _ ((hmem b).mpr hb) ⟨e, hme⟩ ⟨f, hmf⟩
    (he.contract hme) (hf.contract hmf)
  have haY := sourceShore_subset Y S ha
  have hbY := sourceShore_subset Y S hb
  simp only [contractVertex, dif_pos haY, dif_pos hbY, Option.some.injEq, Subtype.mk.injEq] at hh
  exact hh

end GraphPuzzles.LoopMultigraph
