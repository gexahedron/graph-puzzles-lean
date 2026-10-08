import GraphPuzzles.Reduction.Parallel.ParallelContraction
import GraphPuzzles.Reduction.Removable.RemovableContraction

/-! Exact endpoint isomorphisms on corresponding contractions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
  {H : LoopMultigraph V E} {K : LoopMultigraph W F}

/-- An exact endpoint isomorphism induces an exact isomorphism after contraction. -/
noncomputable def EndpointIso.contract (f : EndpointIso H K) (X : Finset V) :
    EndpointIso (H.contract X) (K.contract (f.mapVertices X)) := by
  let g := f.parallelReduction.contract X
  apply g.toEndpointIso_of_injective
  intro e d hed
  apply Subtype.ext
  exact f.edgeEquiv.injective (congrArg Subtype.val hed)

variable {J : LoopMultigraph V F}

omit [DecidableEq V] [DecidableEq E] [DecidableEq F] in
theorem EndpointIso.mapVertices_eq_of_fixed (f : EndpointIso H J)
    (hf : ∀ v, f.vertexEquiv v = v) (X : Finset V) : f.mapVertices X = X := by
  ext v
  rw [← hf v, f.mem_mapVertices, hf]

omit [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] in
theorem deleteContractIso_vertexEquiv (X : Finset V) (e : H.meets X) (v : Option X) :
    (deleteContractIso X e).vertexEquiv v = v := by
  have cast_fixed {S T : Finset (H.meets X)} (h : S = T)
      (f : EndpointIso ((H.deleteEdge e.1).contract X) ((H.contract X).restrictEdges S))
      (hf : f.vertexEquiv v = v) :
      ((congrArg (fun S ↦ EndpointIso ((H.deleteEdge e.1).contract X)
        ((H.contract X).restrictEdges S)) h).mp f).vertexEquiv v = v := by
    cases h
    exact hf
  unfold deleteContractIso
  apply cast_fixed
  · ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact not_congr Subtype.val_inj
  · rfl

omit [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] in
theorem deleteContractIso_symm_vertexEquiv (X : Finset V) (e : H.meets X) (v : Option X) :
    (deleteContractIso X e).symm.vertexEquiv v = v := by
  have hh := deleteContractIso_vertexEquiv (H := H) X e
    ((deleteContractIso X e).vertexEquiv.symm v)
  simpa only [EndpointIso.symm, Equiv.apply_symm_apply] using hh.symm

end GraphPuzzles.LoopMultigraph
