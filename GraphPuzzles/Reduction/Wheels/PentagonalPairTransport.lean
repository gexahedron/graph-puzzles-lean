import GraphPuzzles.Reduction.Wheels.PentagonalShore
import GraphPuzzles.Reduction.Wheels.PentagonalPair
import GraphPuzzles.Reduction.Parallel.SpanningSimpleIso

/-! Two five-vertex wheel shores joined by a matching form a labelled pentagonal pair. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

namespace PentagonalShore

/-- The two cyclic shore enumerations give a vertex equivalence. -/
noncomputable def pairVertexEquiv (A : H.PentagonalShore X)
    (B : H.PentagonalShore (Finset.univ \ X)) : (Fin 2 × Fin 5) ≃ V := by
  let f : Fin 2 × Fin 5 → V := fun z ↦ if z.1 = 0 then (A.vertex z.2).1 else (B.vertex z.2).1
  have hinj : Function.Injective f := by
    rintro ⟨s, i⟩ ⟨t, j⟩ hij
    fin_cases s <;> fin_cases t
    · have hh : A.vertex i = A.vertex j := Subtype.ext hij
      exact congrArg (fun k ↦ ((0 : Fin 2), k)) (A.vertex.injective hh)
    · have hh : (A.vertex i).1 = (B.vertex j).1 := hij
      exact ((Finset.mem_sdiff.mp (B.vertex j).2).2 (hh ▸ (A.vertex i).2)).elim
    · have hh : (B.vertex i).1 = (A.vertex j).1 := hij
      exact ((Finset.mem_sdiff.mp (B.vertex i).2).2 (hh.symm ▸ (A.vertex j).2)).elim
    · have hh : B.vertex i = B.vertex j := Subtype.ext hij
      exact congrArg (fun k ↦ ((1 : Fin 2), k)) (B.vertex.injective hh)
  have hsurj : Function.Surjective f := by
    intro v
    by_cases hv : v ∈ X
    · obtain ⟨i, hi⟩ := A.vertex.surjective ⟨v, hv⟩
      exact ⟨(0, i), congrArg Subtype.val hi⟩
    · obtain ⟨i, hi⟩ := B.vertex.surjective ⟨v, by simp [hv]⟩
      exact ⟨(1, i), congrArg Subtype.val hi⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

omit [DecidableEq E] in
@[simp] theorem pairVertexEquiv_zero (A : H.PentagonalShore X)
    (B : H.PentagonalShore (Finset.univ \ X)) (i : Fin 5) :
    A.pairVertexEquiv B (0, i) = (A.vertex i).1 := rfl

omit [DecidableEq E] in
@[simp] theorem pairVertexEquiv_one (A : H.PentagonalShore X)
    (B : H.PentagonalShore (Finset.univ \ X)) (i : Fin 5) :
    A.pairVertexEquiv B (1, i) = (B.vertex i).1 := rfl

omit [DecidableEq E] in
/-- The selected perfect matching determines a permutation of the two
cyclic shore labelings. -/
theorem exists_matching_permutation (A : H.PentagonalShore X)
    (B : H.PentagonalShore (Finset.univ \ X))
    (hC : H.IsPerfectMatching (H.dangling X)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i, ∃ e ∈ H.dangling X,
      H.Joins e (A.vertex i).1 (B.vertex (σ i)).1 := by
  have hex (i : Fin 5) : ∃ j, ∃ e ∈ H.dangling X,
      H.Joins e (A.vertex i).1 (B.vertex j).1 := by
    have hp : 0 < H.degreeIn (H.dangling X) (A.vertex i).1 := by rw [hC]; decide
    obtain ⟨⟨e, k⟩, hek⟩ := Finset.card_pos.mp hp
    obtain ⟨hek, hk⟩ := Finset.mem_filter.mp hek
    have he := (Finset.mem_product.mp hek).1
    have ho : H.endAt e (Fin.rev k) ∉ X := by
      have hn := mem_dangling.mp he
      have hi : H.endAt e k ∈ X := hk.symm ▸ (A.vertex i).2
      fin_cases k
      · change H.endAt e 1 ∉ X
        have hi0 : H.endAt e 0 ∈ X := hi
        exact fun ho ↦ hn ⟨fun _ ↦ ho, fun _ ↦ hi0⟩
      · change H.endAt e 0 ∉ X
        have hi1 : H.endAt e 1 ∈ X := hi
        exact fun ho ↦ hn ⟨fun _ ↦ hi1, fun _ ↦ ho⟩
    obtain ⟨j, hj⟩ := B.vertex.surjective ⟨H.endAt e (Fin.rev k), by simp [ho]⟩
    refine ⟨j, e, he, ?_⟩
    have hj' := congrArg Subtype.val hj
    fin_cases k
    · exact Or.inl ⟨hk, hj'.symm⟩
    · exact Or.inr ⟨hj'.symm, hk⟩
  choose m hm using hex
  have hmi : Function.Injective m := by
    intro i j hij
    obtain ⟨e, he, hei⟩ := hm i
    obtain ⟨f, hf, hfj⟩ := hm j
    rw [← hij] at hfj
    have hh := hC.on_univ.joins_unique he hf hei.symm hfj.symm
    exact A.vertex.injective (Subtype.ext hh)
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective m ⟨hmi, Finite.surjective_of_injective hmi⟩
  exact ⟨σ, hm⟩

end PentagonalShore

/-- A cubic graph with five vertices on each wheel shore and a
perfect-matching boundary is a permutation matching between two pentagons. -/
theorem exists_pentagonalPair_iso
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hC : H.IsPerfectMatching (H.dangling X))
    (hX : X.card = 5) (hXC : (Finset.univ \ X).card = 5) :
    ∃ σ : Equiv.Perm (Fin 5), ∃ f : EndpointIso (pentagonalPair σ) H,
      f.mapVertices pentagonalPairShore = X := by
  obtain ⟨A⟩ := hl.pentagonalShore hX
  obtain ⟨B⟩ := hr.pentagonalShore hXC
  obtain ⟨σ, hσ⟩ := A.exists_matching_permutation B hC
  let ev := A.pairVertexEquiv B
  have hc : ∀ v, H.degree v = 3 := cubic_of_oddWheel_contractions hl hr hC
  have hV : Fintype.card V = 10 := by
    have hh := Fintype.card_congr ev
    simpa using hh.symm
  have hE : Fintype.card E = 15 := by
    have hh := H.sum_degree_eq Finset.univ
    simp only [hc, H.endsIn_univ, Finset.sum_const, Finset.card_univ, smul_eq_mul, hV] at hh
    omega
  have hedge (e : Fin 3 × Fin 5) :
      ∃ d, H.Joins d (ev ((pentagonalPair σ).endAt e 0))
        (ev ((pentagonalPair σ).endAt e 1)) := by
    obtain ⟨s, i⟩ := e
    fin_cases s
    · exact A.consecutive i
    · obtain ⟨d, _, hd⟩ := hσ i
      exact ⟨d, hd⟩
    · exact B.consecutive i
  obtain ⟨f, hf⟩ := exists_endpointIso_of_spanning_simple (pentagonalPair_isSimple σ) ev
    (by simpa using hE.symm) hedge
  refine ⟨σ, f, ?_⟩
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
    have hz0 : z.1 = 0 := (Finset.mem_filter.mp hz).2
    rw [hf]
    obtain ⟨s, i⟩ := z
    cases hz0
    exact (A.vertex i).2
  · intro v hv
    obtain ⟨i, hi⟩ := A.vertex.surjective ⟨v, hv⟩
    refine Finset.mem_map.mpr ⟨(0, i), by simp [pentagonalPairShore], ?_⟩
    change f.vertexEquiv (0, i) = v
    rw [hf]
    exact congrArg Subtype.val hi

omit [DecidableEq E] in
/-- A perfect-matching cut has one endpoint on each shore for every edge. -/
theorem IsPerfectMatching.card_shore_of_matching_cut
    (hC : H.IsPerfectMatching (H.dangling X)) : X.card = (H.dangling X).card := by
  have he (e : E) (he : e ∈ H.dangling X) : H.endsIn X e = 1 := by
    have hh := mem_dangling.mp he
    unfold endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X <;>
      simp_all
  have hh := H.sum_degreeIn_eq X (H.dangling X)
  rw [Finset.sum_congr rfl (fun w _ ↦ hC w), Finset.sum_congr rfl he] at hh
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hh

/-- The five-spoke two-wheel case is either the Petersen graph or has a
perfect matching crossing the selected cut exactly three times. -/
theorem three_or_petersen_of_five_matching_spokes
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hC : H.IsPerfectMatching (H.dangling X)) (h5 : (H.dangling X).card = 5) :
    (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨ H.IsPetersen := by
  have hX := hC.card_shore_of_matching_cut.trans h5
  have hC' : H.IsPerfectMatching (H.dangling (Finset.univ \ X)) := by
    simpa only [dangling_compl] using hC
  have hXC : (Finset.univ \ X).card = 5 := by
    simpa only [dangling_compl] using hC'.card_shore_of_matching_cut.trans
      (by simpa only [dangling_compl] using h5)
  obtain ⟨σ, f, hf⟩ := exists_pentagonalPair_iso hl hr hC hX hXC
  rcases pentagonalPair_three_or_petersen σ with ⟨M, hM, hMC⟩ | hp
  · refine Or.inl ⟨f.mapEdges M, f.isPerfectMatching hM, ?_⟩
    have hh := f.crossing_map M pentagonalPairShore
    rw [hf, hMC] at hh
    exact hh
  · exact Or.inr ⟨f.symm.trans hp.some⟩

end GraphPuzzles.LoopMultigraph
