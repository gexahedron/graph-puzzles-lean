import GraphPuzzles.Reduction.Wheels.OddWheelBicontraction
import GraphPuzzles.Cuts.Contraction.EndpointIsoContraction
import GraphPuzzles.Reduction.Wheels.OddWheelCutDeletion

/-! Original-vertex tight triples exposed by deleting a matching-cut spoke. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

/-- A local wheel bicontraction lifts to a tight original three-vertex
shore. The deleted endpoint is retained in the certificate for incidence counts. -/
theorem IsOddWheel.exists_deleted_spoke_shore
    (hw : (H.contract X).IsOddWheel none)
    (hC : H.IsPerfectMatching (H.dangling X)) (h5 : 5 ≤ X.card)
    {e : E} (he : e ∈ H.dangling X) :
    ∃ A : Finset V, A ⊆ X ∧ A.card = 3 ∧
      (H.endAt e 0 ∈ A ∨ H.endAt e 1 ∈ A) ∧
      (H.deleteEdge e).IsTightCut A ∧ ((H.deleteEdge e).contract A).IsBipartite ∧
      (((H.deleteEdge e).contract X).contract (poleShore X (Finset.univ \ A))).IsBrick := by
  classical
  obtain ⟨W⟩ := hw
  have hlen : W.labels.length = X.card := by
    have hh := W.rim_card_eq_length
    simp only [Finset.card_erase_of_mem (Finset.mem_univ none), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe, Nat.add_sub_cancel] at hh
    exact hh.symm
  have hex : ∃ k, H.endAt e k ∈ X ∧ H.endAt e (Fin.rev k) ∉ X := by
    have hh := mem_dangling.mp he
    by_cases h0 : H.endAt e 0 ∈ X
    · exact ⟨0, h0, by simpa using (show H.endAt e 1 ∉ X by tauto)⟩
    · exact ⟨1, by tauto, by simpa using h0⟩
  obtain ⟨k, hk, hko⟩ := hex
  let u : X := ⟨H.endAt e k, hk⟩
  let d : H.meets X := ⟨e, dangling_subset_meets X he⟩
  have hd : (H.contract X).Joins d none (some u) := by
    have hi := (contract_endAt_eq_some_iff X d k u).mpr rfl
    have ho := (contract_endAt_eq_none_iff X d (Fin.rev k)).mpr hko
    fin_cases k
    · exact Or.inr ⟨hi, ho⟩
    · exact Or.inl ⟨ho, hi⟩
  have huniq : ∀ f, (H.contract X).Joins f none (some u) → f = d := by
    intro f hf
    obtain ⟨z, hz, hj⟩ := (contract_joins_none_some f u).mp hf
    have hfC : f.1 ∈ H.dangling X := by
      rcases hj with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [mem_dangling, h0, h1, u.2, hz]
    obtain ⟨j, hj⟩ := (H.joins_comm.mp hj).exists_end
    apply Subtype.ext
    exact congrArg Prod.fst (eq_incidence_of_degreeIn_one (hC u.1) hfC he hj rfl)
  obtain ⟨a, b, hcard, hnone, hneighbor, ht, hbi, hb⟩ :=
    W.exists_spoke_bicontraction (by omega) hd (by simp) huniq
  cases a with
  | none => simp at hnone
  | some a =>
    cases b with
    | none => simp at hnone
    | some b =>
      let A : Finset V := {u.1, a.1, b.1}
      let L : Finset (Option X) := {some u, some a, some b}
      have hAX : A ⊆ X := by
        intro v hv
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact u.2
        · exact a.2
        · exact b.2
      have hL : contractShore X A = L := by
        ext v
        cases v with
        | none => simp [L]
        | some v =>
          simp only [some_mem_contractShore, A, L, Finset.mem_insert, Finset.mem_singleton,
            Option.some.injEq, Subtype.ext_iff]
      have hAcard : A.card = 3 := by
        change L.card = 3 at hcard
        rw [← hL, card_contractShore_of_subset hAX] at hcard
        exact hcard
      have hua : u.1 ≠ a.1 := by
        intro hh
        have hle : A.card ≤ 2 := by simpa [A, hh] using (Finset.card_le_two (a := a.1) (b := b.1))
        omega
      have hub : u.1 ≠ b.1 := by
        intro hh
        have hle : A.card ≤ 2 := by simpa [A, hh, Finset.insert_comm] using
          (Finset.card_le_two (a := a.1) (b := b.1))
        omega
      have hab : a.1 ≠ b.1 := by
        intro hh
        have hle : A.card ≤ 2 := by simpa [A, hh] using (Finset.card_le_two (a := u.1) (b := b.1))
        omega
      have hn : ∀ (f : Finset.univ.erase e) j,
          (H.deleteEdge e).endAt f j = u.1 →
          (H.deleteEdge e).endAt f (Fin.rev j) = a.1 ∨
            (H.deleteEdge e).endAt f (Fin.rev j) = b.1 := by
        intro f j hj
        let g : H.meets X := ⟨f.1, mem_meets.mpr ⟨j, hj.symm ▸ u.2⟩⟩
        have hgd : g ≠ d := fun hh ↦ (Finset.mem_erase.mp f.2).1 (congrArg Subtype.val hh)
        let g' : Finset.univ.erase d := ⟨g, by simp [hgd]⟩
        have hgu : ((H.contract X).deleteEdge d).endAt g' j = some u :=
          (contract_endAt_eq_some_iff X g j u).mpr hj
        have hh := hneighbor g' j hgu
        exact hh.imp ((contract_endAt_eq_some_iff X g (Fin.rev j) a).mp)
          ((contract_endAt_eq_some_iff X g (Fin.rev j) b).mp)
      let f := (deleteContractIso X d).symm
      have hf (z : Option X) : f.vertexEquiv z = z := deleteContractIso_symm_vertexEquiv X d z
      have hmap (S : Finset (Option X)) : f.mapVertices S = S := f.mapVertices_eq_of_fixed hf S
      have hbi' : (((H.deleteEdge e).contract X).contract (contractShore X A)).IsBipartite := by
        have hh := (f.contract L).isBipartite hbi
        rw [hmap L, ← hL] at hh
        exact hh
      have hb' : (((H.deleteEdge e).contract X).contract
          (poleShore X (Finset.univ \ A))).IsBrick := by
        have hh := (f.contract (Finset.univ \ L)).isBrick hb
        rw [hmap _, ← hL, compl_contractShore] at hh
        exact hh
      refine ⟨A, hAX, hAcard, ?_, isTightCut_neighbor_triple hua hub hab hn,
        (contractNestedIso hAX).isBipartite hbi', hb'⟩
      have huA : H.endAt e k ∈ A := by simp [A, u]
      fin_cases k
      · exact Or.inl huA
      · exact Or.inr huA

end GraphPuzzles.LoopMultigraph
