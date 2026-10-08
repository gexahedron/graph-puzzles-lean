import GraphPuzzles.Cuts.Shores.VertexDeletionConnectivity

/-! An adjacent pair whose deletion preserves connectivity in a matching-covered graph. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A vertex with a nonempty complement has a neighbour such that deleting
both vertices leaves a connected graph. This is the end-block selection
step, proved by finite descent on closed parts instead of a block tree. -/
theorem IsMatchingCovered.exists_neighbor_connected_delete (hm : H.IsMatchingCovered)
    (p : V) (hS : (Finset.univ.erase p).Nonempty) :
    ∃ v, v ≠ p ∧ ∃ e, H.Joins e p v ∧ H.IsConnectedOn ((Finset.univ.erase p).erase v) := by
  classical
  let S := Finset.univ.erase p
  let J := H.induced S
  let N : Finset S := Finset.univ.filter fun v ↦ ∃ e, H.Joins e v.1 p
  have hJ : J.IsConnected := (induced_connected_iff S).mpr (hm.connectedOn_delete p)
  have hN : N.Nonempty := by
    obtain ⟨a, ha⟩ := hS
    obtain ⟨e, he⟩ := hm.1.dangling_nonempty (Finset.singleton_nonempty p)
      ⟨a, by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] using (Finset.mem_erase.mp ha).1⟩
    have hd := mem_dangling.mp he
    simp only [Finset.mem_singleton] at hd
    by_cases h0 : H.endAt e 0 = p
    · have h1 : H.endAt e 1 ≠ p := by tauto
      let v : S := ⟨H.endAt e 1, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ _⟩⟩
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, Or.inr ⟨h0, rfl⟩⟩⟩
    · have h1 : H.endAt e 1 = p := by tauto
      let v : S := ⟨H.endAt e 0, Finset.mem_erase.mpr ⟨h0, Finset.mem_univ _⟩⟩
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, Or.inl ⟨rfl, h1⟩⟩⟩
  have htouch (w : S) (_hwN : w ∈ N) (Q : Finset S) (hQ : Q.Nonempty) (hwQ : w ∉ Q)
      (hc : ∀ e : H.edgesIn S, ∀ k : Fin 2, J.endAt e k ∈ Q →
        J.endAt e (Fin.rev k) ≠ w → J.endAt e (Fin.rev k) ∈ Q) : (Q ∩ N).Nonempty := by
    let C := Q.image Subtype.val
    have hpC : p ∉ C := by
      intro hp
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_erase.mp q.2).1 hq
    have hwC : w.1 ∉ C := fun h ↦ hwQ ((mem_image_induced_vertices Q w).mp h)
    obtain ⟨a, ha⟩ := hQ
    have haC : a.1 ∈ C := (mem_image_induced_vertices Q a).mpr ha
    have haw : a.1 ≠ w.1 := fun h ↦ hwC (h ▸ haC)
    have hpw : p ≠ w.1 := ((Finset.mem_erase.mp w.2).1).symm
    obtain ⟨e, k, hkC, _, hrC, hrD⟩ := (hm.connectedOn_delete w.1).exists_boundary_within
      (Finset.mem_erase.mpr ⟨haw, Finset.mem_univ _⟩) haC
      (Finset.mem_erase.mpr ⟨hpw, Finset.mem_univ _⟩) hpC
    by_cases hrp : H.endAt e (Fin.rev k) = p
    · obtain ⟨q, hqQ, hqe⟩ := Finset.mem_image.mp hkC
      have hj : H.Joins e q.1 p := by
        fin_cases k
        · exact Or.inl ⟨hqe.symm, hrp⟩
        · exact Or.inr ⟨hrp, hqe.symm⟩
      exact ⟨q, Finset.mem_inter.mpr ⟨hqQ,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hj⟩⟩⟩
    · have hkS : H.endAt e k ∈ S := image_induced_vertices_subset Q hkC
      have hrS : H.endAt e (Fin.rev k) ∈ S := Finset.mem_erase.mpr ⟨hrp, Finset.mem_univ _⟩
      have heS : e ∈ H.edgesIn S := mem_edgesIn.mpr (fun j ↦ by
        fin_cases k <;> fin_cases j <;> assumption)
      let f : H.edgesIn S := ⟨e, heS⟩
      have hkQ : J.endAt f k ∈ Q := (mem_image_induced_vertices Q _).mp hkC
      have hrw : J.endAt f (Fin.rev k) ≠ w := fun h ↦
        (Finset.mem_erase.mp hrD).1 (congrArg Subtype.val h)
      exact (hrC ((mem_image_induced_vertices Q _).mpr (hc f k hkQ hrw))).elim
  obtain ⟨v, hvN, hv⟩ := hJ.exists_delete_connected_in N hN htouch
  obtain ⟨e, he⟩ := (Finset.mem_filter.mp hvN).2
  refine ⟨v.1, (Finset.mem_erase.mp v.2).1, e, H.joins_comm.mp he, ?_⟩
  have hh := (induced_connectedOn_iff S (Finset.univ.erase v)).mp hv
  simpa only [image_univ_erase_induced] using hh

end GraphPuzzles.LoopMultigraph
