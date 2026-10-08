import GraphPuzzles.Reduction.Wheels.OddWheelRemovability
import GraphPuzzles.Matching.FourVertexMatching

/-! The opposite removable doubleton of an un-paralleled spoke in a triangular wheel. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A labelled triangular rim starting at the prescribed rim vertex. -/
structure TriangleRim (H : LoopMultigraph V E) (v w : V) where
  a : V
  b : V
  left : E
  opposite : E
  right : E
  nodup : [v, w, a, b].Nodup
  vertices : [v, w, a, b].toFinset = Finset.univ
  left_joins : H.Joins left w a
  opposite_joins : H.Joins opposite a b
  right_joins : H.Joins right b w
  edges : H.edgesIn (Finset.univ.erase v) = {left, opposite, right}

namespace OddWheel

variable {v w : V} (W : H.OddWheel v)

theorem triangleRim (h3 : W.labels.length = 3) (hw : w ≠ v) :
    Nonempty (H.TriangleRim v w) := by
  obtain ⟨A, es, hwalk, hV, hE, hlen⟩ := W.exists_rooted_rim w hw
  have hs : A.start = w := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = w := Finset.mem_singleton.mp A.finish_mem
  have hI : A.interior.length = 2 := by
    have hh := hwalk.length
    simp only [List.length_append, List.length_singleton] at hh
    omega
  obtain ⟨a, b, hi⟩ := List.length_eq_two.mp hI
  have hwalk' : H.EdgeChain w es [a, b, w] := by
    simpa only [hs, ht, hi, List.cons_append, List.nil_append] using hwalk
  cases hwalk' with
  | @cons _ _ d es _ hd htail =>
    cases htail with
    | @cons _ _ f es _ hf htail =>
      cases htail with
      | @cons _ _ g es _ hg htail =>
        cases htail
        have hR : [w, a, b].toFinset = Finset.univ.erase v := by
          simpa only [OddEar.vertices, hi, Finset.singleton_union, List.toFinset_cons] using hV
        have hnR : [w, a, b].Nodup := by
          refine List.nodup_cons.mpr ⟨?_, by simpa only [hi] using A.nodup⟩
          intro hh
          exact A.avoids w (by simpa only [hi] using hh) (Finset.mem_singleton_self _)
        have hvnot : v ∉ [w, a, b] := by
          intro hh
          have hh' := hR ▸ List.mem_toFinset.mpr hh
          simp at hh'
        refine ⟨{
          a := a
          b := b
          left := d
          opposite := f
          right := g
          nodup := List.nodup_cons.mpr ⟨hvnot, hnR⟩
          vertices := by
            rw [List.toFinset_cons]
            rw [hR]
            exact Finset.insert_erase (Finset.mem_univ _)
          left_joins := hd
          opposite_joins := hf
          right_joins := hg
          edges := by
            rw [← W.edges_eq, ← hE]
            simp }⟩

set_option maxHeartbeats 400000 in
/-- A simple spoke of a triangular wheel and its opposite rim edge form a removable
doubleton. If the spoke avoids a vertex matching at the hub, the rim edge does too. -/
theorem exists_removableDoubleton_of_triangle_spoke
    (h3 : W.labels.length = 3) {e : E} (he : H.Joins e v w)
    (huniq : ∀ g, H.Joins g v w → g = e)
    {N : Finset E} (hN : H.IsVertexMatching v N) (heN : e ∉ N) :
    ∃ f, f ∈ H.edgesIn (Finset.univ.erase v) ∧ f ∉ N ∧ H.IsRemovableDoubleton e f := by
  have hwv : w ≠ v := by
    intro hh
    subst w
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> exact W.loopless e (h0.trans h1.symm)
  obtain ⟨T⟩ := W.triangleRim h3 hwv
  have hn := T.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or, List.nodup_nil, not_false_eq_true, and_true] at hn
  have hva : v ≠ T.a := hn.1.2.1
  have hvb : v ≠ T.b := hn.1.2.2
  have hwa : w ≠ T.a := hn.2.1.1
  have hwb : w ≠ T.b := hn.2.1.2
  have hab : T.a ≠ T.b := hn.2.2
  have haR : T.a ∈ Finset.univ.erase v := by simp [Ne.symm hva]
  have hbR : T.b ∈ Finset.univ.erase v := by simp [Ne.symm hvb]
  have hfR : T.opposite ∈ H.edgesIn (Finset.univ.erase v) := by rw [T.edges]; simp
  have hef : e ≠ T.opposite := he.ne_of_left_not_end T.opposite_joins hva hvb
  have hdf : T.left ≠ T.opposite := T.left_joins.ne_of_left_not_end T.opposite_joins hwa hwb
  have hgf : T.right ≠ T.opposite :=
    (H.joins_comm.mp T.right_joins).ne_of_left_not_end T.opposite_joins hwa hwb
  have hde : T.left ≠ e :=
    (H.joins_comm.mp T.left_joins).ne_of_left_not_end he (Ne.symm hva) (Ne.symm hwa)
  have hge : T.right ≠ e := T.right_joins.ne_of_left_not_end he (Ne.symm hvb) (Ne.symm hwb)
  have huniqf (g : E) (hg : H.Joins g T.a T.b) : g = T.opposite := by
    have hgR : g ∈ H.edgesIn (Finset.univ.erase v) := mem_edgesIn.mpr fun k ↦ by
      rcases hg.endAt_mem k with hh | hh
      · exact hh.symm ▸ haR
      · exact hh.symm ▸ hbR
    rw [T.edges] at hgR
    rcases Finset.mem_insert.mp hgR with rfl | hgR
    · exact (T.left_joins.ne_of_left_not_end hg hwa hwb rfl).elim
    · rcases Finset.mem_insert.mp hgR with hh | hgR
      · exact hh
      · have hh := Finset.mem_singleton.mp hgR
        subst g
        exact ((H.joins_comm.mp T.right_joins).ne_of_left_not_end hg hwa hwb rfl).elim
  have hperm : [T.a, T.b, v, w].Nodup := by
    simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
  have hVP : [T.a, T.b, v, w].toFinset = Finset.univ := by
    rw [← T.vertices]
    ext x
    simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
    tauto
  have hdep : H.MutuallyDependent e T.opposite := by
    intro M hM
    constructor
    · intro heM
      obtain ⟨g, hgM, hg⟩ := exists_opposite_edge_of_degree_one W.loopless T.nodup T.vertices
        he heM (hM v) (hM w) (hM T.a)
      exact huniqf g hg ▸ hgM
    · intro hfM
      obtain ⟨g, hgM, hg⟩ := exists_opposite_edge_of_degree_one W.loopless hperm hVP
        T.opposite_joins hfM (hM T.a) (hM T.b) (hM v)
      exact huniq g hg ▸ hgM
  have hfN : T.opposite ∉ N := by
    intro hfN
    have hperm' : [T.a, T.b, w, v].Nodup := by
      simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
    have hVP' : [T.a, T.b, w, v].toFinset = Finset.univ := by
      rw [← T.vertices]
      ext x
      simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
      tauto
    obtain ⟨g, hgN, hg⟩ := exists_opposite_edge_of_degree_one W.loopless hperm' hVP'
      T.opposite_joins hfN (hN T.a (Ne.symm hva)) (hN T.b (Ne.symm hvb)) (hN w hwv)
    exact heN (huniq g (H.joins_comm.mp hg) ▸ hgN)
  obtain ⟨p, hp⟩ := W.spokes T.a (Ne.symm hva)
  obtain ⟨q, hq⟩ := W.spokes T.b (Ne.symm hvb)
  have hpe : p ≠ e := (H.joins_comm.mp hp).ne_of_left_not_end he (Ne.symm hva) (Ne.symm hwa)
  have hqe : q ≠ e := (H.joins_comm.mp hq).ne_of_left_not_end he (Ne.symm hvb) (Ne.symm hwb)
  have hpf : p ≠ T.opposite := hp.ne_of_left_not_end T.opposite_joins hva hvb
  have hqf : q ≠ T.opposite := hq.ne_of_left_not_end T.opposite_joins hva hvb
  let S : Finset E := Finset.univ \ {e, T.opposite}
  have hmem {g : E} (hge : g ≠ e) (hgf : g ≠ T.opposite) : g ∈ S := by simp [S, hge, hgf]
  have hconn : (H.restrictEdges S).IsConnected := by
    intro c hc
    have edge {g : E} {x y : V} (hg : H.Joins g x y) (hgS : g ∈ S) : c x = c y := by
      have hh := hc ⟨g, hgS⟩
      change c (H.endAt g 0) = c (H.endAt g 1) at hh
      rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simpa only [h0, h1] using hh
      · simpa only [h0, h1] using hh.symm
    have hpa := edge hp (hmem hpe hpf)
    have hpb := edge hq (hmem hqe hqf)
    have hwa' := edge T.left_joins (hmem hde hdf)
    have hconst (x : V) : c x = c v := by
      have hx : x ∈ [v, w, T.a, T.b].toFinset := T.vertices.symm ▸ Finset.mem_univ _
      simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rfl
      · exact hwa'.trans hpa.symm
      · exact hpa.symm
      · exact hpb.symm
    exact fun x y ↦ (hconst x).trans (hconst y).symm
  have hcover : ∀ g ∈ S, ∃ M, H.IsPerfectMatching M ∧ M ⊆ S ∧ g ∈ M := by
    intro g hgS
    have hge' : g ≠ e := fun hh ↦ (Finset.mem_sdiff.mp hgS).2 (by simp [hh])
    have hgf' : g ≠ T.opposite := fun hh ↦ (Finset.mem_sdiff.mp hgS).2 (by simp [hh])
    have classify : H.Joins g v T.a ∨ H.Joins g v T.b ∨ g = T.left ∨ g = T.right := by
      by_cases hgR : g ∈ H.edgesIn (Finset.univ.erase v)
      · rw [T.edges] at hgR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hgR
        rcases hgR with hh | hh | hh
        · exact Or.inr (Or.inr (Or.inl hh))
        · exact (hgf' hh).elim
        · exact Or.inr (Or.inr (Or.inr hh))
      · obtain ⟨k, hk⟩ : ∃ k, H.endAt g k = v := by
          by_contra hn
          push Not at hn
          exact hgR (mem_edgesIn.mpr fun k ↦ by simp [hn k])
        have hn : H.endAt g (Fin.rev k) ≠ v := by
          intro hh
          rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
          · exact W.loopless g (hk.trans hh.symm)
          · exact W.loopless g (hh.trans hk.symm)
        have hgJ : H.Joins g v (H.endAt g (Fin.rev k)) := by
          rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
          · exact Or.inl ⟨hk, rfl⟩
          · exact Or.inr ⟨rfl, hk⟩
        have hx : H.endAt g (Fin.rev k) ∈ [v, w, T.a, T.b].toFinset :=
          T.vertices.symm ▸ Finset.mem_univ _
        simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, hn, false_or, or_false] at hx
        rcases hx with hh | hh | hh
        · exact (hge' (huniq g (hh ▸ hgJ))).elim
        · exact Or.inl (hh ▸ hgJ)
        · exact Or.inr (Or.inl (hh ▸ hgJ))
    have pair {x y z t : V} {j : E} (hgj : H.Joins g x y) (hjj : H.Joins j z t)
        (hjS : j ∈ S) (hnd : [x,y,z,t].Nodup) (hverts : [x,y,z,t].toFinset = Finset.univ) :
        ∃ M, H.IsPerfectMatching M ∧ M ⊆ S ∧ g ∈ M := by
      exact ⟨{g,j}, isPerfectMatching_pair_of_four_vertices hnd hverts hgj hjj,
        by
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact hgS
          · rw [Finset.mem_singleton.mp hk]
            exact hjS, by simp⟩
    rcases classify with hg | hg | rfl | rfl
    · apply pair hg T.right_joins (hmem hge hgf)
      · simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
      · rw [← T.vertices]; ext x
        simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
        tauto
    · apply pair hg (H.joins_comm.mp T.left_joins) (hmem hde hdf)
      · simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
      · rw [← T.vertices]; ext x
        simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
        tauto
    · apply pair T.left_joins hq (hmem hqe hqf)
      · simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
      · rw [← T.vertices]; ext x
        simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
        tauto
    · apply pair T.right_joins hp (hmem hpe hpf)
      · simpa [List.nodup_cons, ne_comm, and_comm, and_left_comm, and_assoc] using T.nodup
      · rw [← T.vertices]; ext x
        simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
        tauto
  exact ⟨T.opposite, hfR, hfN, hef, isMatchingCovered_restrictEdges_of_cover hconn hcover,
    hdep.not_removable_left hef, hdep.symm.not_removable_left hef.symm⟩

end OddWheel
end GraphPuzzles.LoopMultigraph
