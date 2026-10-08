import GraphPuzzles.Ears.OddEarDecomposition
import GraphPuzzles.Matching.Barriers.MatchingBarrier

/-! Odd-ear decompositions on a specified shore, retaining original edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Factor-criticality on a shore is factor-criticality of its induced graph. -/
theorem IsFactorCritical.induced {S : Finset V} (hfc : H.IsFactorCritical S) :
    (H.induced S).IsFactorCritical Finset.univ := by
  intro v _
  obtain ⟨P, hP⟩ := hfc v.1 v.2
  have hPS : P ⊆ H.edgesIn S := fun e he ↦
    mem_edgesIn.mpr fun k ↦ (Finset.mem_erase.mp (hP.1 e he k)).2
  refine ⟨H.inducedMatching S P, ⟨?_, ?_⟩⟩
  · intro e he k
    have hek := hP.1 e.1 ((mem_inducedMatching S P e).mp he) k
    apply Finset.mem_erase.mpr
    refine ⟨fun hh ↦ (Finset.mem_erase.mp hek).1 ?_, Finset.mem_univ _⟩
    exact congrArg Subtype.val hh
  · intro w hw
    rw [← induced_degreeIn, image_inducedMatching S P hPS]
    exact hP.2 w.1 (Finset.mem_erase.mpr
      ⟨fun hh ↦ (Finset.mem_erase.mp hw).1 (Subtype.ext hh), w.2⟩)

omit [DecidableEq E] in
theorem EdgeChain.of_induced {S : Finset V} {a : S}
    {es : List (H.edgesIn S)} {vs : List S} (h : (H.induced S).EdgeChain a es vs) :
    H.EdgeChain a.1 (es.map Subtype.val) (vs.map Subtype.val) := by
  induction h with
  | nil => exact .nil _
  | cons he _ ih =>
    apply EdgeChain.cons _ ih
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨congrArg Subtype.val h0, congrArg Subtype.val h1⟩
    · exact Or.inr ⟨congrArg Subtype.val h0, congrArg Subtype.val h1⟩

namespace OddEar

variable {S : Finset V} {Q : Finset S} (A : (H.induced S).OddEar Q)

/-- View an ear of an induced graph in the ambient graph. -/
def of_induced : H.OddEar (Q.image Subtype.val) where
  start := A.start.1
  finish := A.finish.1
  interior := A.interior.map Subtype.val
  start_mem := Finset.mem_image.mpr ⟨A.start, A.start_mem, rfl⟩
  finish_mem := Finset.mem_image.mpr ⟨A.finish, A.finish_mem, rfl⟩
  nodup := A.nodup.map Subtype.val_injective
  avoids := by
    intro w hw hwQ
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact A.avoids v hv ((mem_image_induced_vertices Q v).mp hwQ)
  even := by simpa using A.even
  chain := by
    have hc := List.isChain_map_of_isChain (S := fun a b ↦ ∃ e, H.Joins e a b)
      Subtype.val (fun a b hab ↦ ?_) A.chain
    · simpa using hc
    · obtain ⟨e, he⟩ := hab
      refine ⟨e.1, ?_⟩
      rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨congrArg Subtype.val h0, congrArg Subtype.val h1⟩
      · exact Or.inr ⟨congrArg Subtype.val h0, congrArg Subtype.val h1⟩

omit [DecidableEq E] in
@[simp] theorem of_induced_vertices : A.of_induced.vertices = A.vertices.image Subtype.val := by
  have hl : (A.interior.map Subtype.val).toFinset = A.interior.toFinset.image Subtype.val := by
    ext v; simp
  exact (congrArg (Q.image Subtype.val ∪ ·) hl).trans (Finset.image_union _ _).symm

end OddEar

/-- Lift every prefix and edge label of an induced-graph ear decomposition. -/
theorem HasOddEarDecomposition.of_induced {S : Finset V} {r : S} {Q : Finset S}
    {F : Finset (H.edgesIn S)} (h : (H.induced S).HasOddEarDecomposition r Q F) :
    H.HasOddEarDecomposition r.1 (Q.image Subtype.val) (F.image Subtype.val) := by
  induction h with
  | start => simpa using (HasOddEarDecomposition.start (H := H) (r := r.1))
  | @attach Q F _ A es hw hf ih =>
    have hw' : H.EdgeChain A.of_induced.start (es.map Subtype.val)
        (A.of_induced.interior ++ [A.of_induced.finish]) := by
      simpa [OddEar.of_induced] using hw.of_induced
    have hf' : Disjoint (F.image Subtype.val) (es.map Subtype.val).toFinset := by
      apply Finset.disjoint_left.mpr
      intro e heF heL
      obtain ⟨f, hfF, rfl⟩ := Finset.mem_image.mp heF
      obtain ⟨g, hg, hgf⟩ := List.mem_map.mp (List.mem_toFinset.mp heL)
      have hgf' : g = f := Subtype.ext hgf
      exact Finset.disjoint_left.mp hf hfF (List.mem_toFinset.mpr (hgf' ▸ hg))
    have he : (es.map Subtype.val).toFinset = es.toFinset.image Subtype.val := by ext e; simp
    simpa only [OddEar.of_induced_vertices, he, Finset.image_union] using
      ih.attach A.of_induced (es.map Subtype.val) hw' hf'

/-- The full odd-ear theorem on any factor-critical shore, with all its
original internal edge labels and any specified starting vertex. -/
theorem IsFactorCritical.hasOddEarDecomposition_on {S : Finset V}
    (hfc : H.IsFactorCritical S) {r : V} (hr : r ∈ S) :
    H.HasOddEarDecomposition r S (H.edgesIn S) := by
  have hD := (hfc.induced.hasOddEarDecomposition ⟨r, hr⟩).of_induced
  have hv : (Finset.univ : Finset S).image Subtype.val = S := by ext v; simp
  have he : (Finset.univ : Finset (H.edgesIn S)).image Subtype.val = H.edgesIn S := by
    ext e; simp
  simpa only [hv, he] using hD

omit [DecidableEq E] in
/-- Deleting one vertex from a bicritical graph produces a factor-critical shore. -/
theorem IsBicritical.factorCritical_erase (hb : H.IsBicritical) (v : V) :
    H.IsFactorCritical (Finset.univ.erase v) := by
  intro w hw
  exact hb v w (Finset.mem_erase.mp hw).1.symm

end GraphPuzzles.LoopMultigraph
