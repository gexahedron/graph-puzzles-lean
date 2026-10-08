import GraphPuzzles.Reduction.Wheels.OddWheelStructure
import GraphPuzzles.Reduction.Wheels.TwoWheelCubic

/-! Cyclic labels for a five-vertex odd-wheel shore. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

/-- A cyclic enumeration of a five-vertex shore, with original rim labels. -/
structure PentagonalShore (H : LoopMultigraph V E) (X : Finset V) where
  vertex : Fin 5 ≃ X
  consecutive : ∀ i, ∃ e, H.Joins e (vertex i).1 (vertex (i + 1)).1

/-- A five-vertex retained shore of an odd wheel has a cyclic enumeration. -/
theorem IsOddWheel.pentagonalShore (hW : (H.contract X).IsOddWheel none)
    (hX : X.card = 5) : Nonempty (H.PentagonalShore X) := by
  classical
  obtain ⟨W⟩ := hW
  have hlen : W.labels.length = 5 := by
    have hh := W.rim_card_eq_length
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ none), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe, Nat.add_sub_cancel, hX] using hh.symm
  have hstart : W.rim.start = W.root := Finset.mem_singleton.mp W.rim.start_mem
  have hfinish : W.rim.finish = W.root := Finset.mem_singleton.mp W.rim.finish_mem
  have hfour : W.rim.interior.length = 4 := by
    have hh := W.walk.length
    simp only [List.length_append, List.length_singleton, hlen] at hh
    omega
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hfour
  let L : List (Option X) := [W.root, a, b, c, d]
  let f : Fin 5 → Option X := fun i ↦ L.get i
  have hnd : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro hh
      exact W.rim.avoids W.root (hlist.symm ▸ hh) (Finset.mem_singleton_self _)
    · exact hlist ▸ W.rim.nodup
  have hinj : Function.Injective f := hnd.injective_get
  have hcover : L.toFinset = Finset.univ.erase none := by
    simpa only [L, OddEar.vertices, hlist, List.toFinset_cons, Finset.singleton_union] using W.vertices_eq
  have hsome (i : Fin 5) : ∃ x : X, f i = some x := by
    have hh : f i ∈ Finset.univ.erase none := hcover ▸ List.mem_toFinset.mpr (L.get_mem i)
    cases hfi : f i with
    | none => exact ((Finset.mem_erase.mp hh).1 hfi).elim
    | some x => exact ⟨x, rfl⟩
  choose g hg using hsome
  have hgi : Function.Injective g := by
    intro i j hij
    apply hinj
    rw [hg, hg, hij]
  have hgs : Function.Surjective g := by
    intro x
    have hx : some x ∈ L := List.mem_toFinset.mp (hcover.symm ▸ (by simp : some x ∈ Finset.univ.erase none))
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    refine ⟨i, Option.some.inj ?_⟩
    exact (hg i).symm.trans hi
  let ev : Fin 5 ≃ X := Equiv.ofBijective g ⟨hgi, hgs⟩
  have hchain : (W.root :: [a, b, c, d, W.root]).IsChain
      (fun x y ↦ ∃ e, (H.contract X).Joins e x y) := by
    simpa only [hstart, hfinish, hlist, List.cons_append, List.nil_append] using W.walk.isChain
  have hedge (i : Fin 5) : ∃ e, (H.contract X).Joins e (f i) (f (i + 1)) := by
    fin_cases i
    · exact hchain.rel_head
    · exact hchain.tail.rel_head
    · exact hchain.tail.tail.rel_head
    · exact hchain.tail.tail.tail.rel_head
    · exact hchain.tail.tail.tail.tail.rel_head
  refine ⟨⟨ev, ?_⟩⟩
  intro i
  obtain ⟨e, he⟩ := hedge i
  rw [hg, hg] at he
  refine ⟨e.1, ?_⟩
  change H.Joins e.1 (g i).1 (g (i + 1)).1
  simpa only [Joins, contract_endAt_eq_some_iff] using he

end GraphPuzzles.LoopMultigraph
