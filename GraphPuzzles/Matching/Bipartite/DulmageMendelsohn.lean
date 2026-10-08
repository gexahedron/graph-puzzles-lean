import GraphPuzzles.Matching.Barriers.PrincipalBarrier
import GraphPuzzles.Matching.Barriers.BarrierMatching

/-!
# Dulmage--Mendelsohn barriers

A maximal barrier contains a nonempty barrier whose odd components are
factor-critical and whose bipartite core is matching covered. The core is
expressed by its incidence relation; its matchings are bijections between
the odd components and the barrier vertices.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- A nonempty barrier with factor-critical odd components and a matching-covered core. -/
structure IsDMBarrier : Prop where
  isBarrier : F.IsBarrier
  nonempty : Z.Nonempty
  factorCritical : ∀ Q ∈ F.odd, H.IsFactorCritical Q
  coreMatching : ∀ (Q : F.odd) (z : Z), z ∈ F.coreNeighbors Q →
    ∃ f : F.odd → Z, Function.Bijective f ∧ (∀ R, f R ∈ F.coreNeighbors R) ∧ f Q = z
  coreConnected : ∀ (cA : F.odd → Bool) (cB : Z → Bool),
    (∀ Q z, z ∈ F.coreNeighbors Q → cA Q = cB z) → ∀ Q z, cA Q = cB z

/-- Select a DM-barrier while retaining its odd parts from the maximal barrier. -/
theorem IsMaximalBarrier.exists_DMBarrier_retaining (hm : F.IsMaximalBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hZ : Z.Nonempty) :
    ∃ B, B ⊆ Z ∧ ∃ P : H.ComponentFamily B, P.IsDMBarrier ∧ P.odd ⊆ F.odd := by
  obtain ⟨S, hSne, hcard, hthrough, hconn⟩ := hm.isBarrier.exists_principal_core F hM hZ
  let P := F.principalFamily S
  let qEq := F.principalPartsEquiv S hM hcard
  let zEq := F.principalBarrierEquiv S
  refine ⟨F.coreBarrier S, F.coreBarrier_subset S, P,
    ⟨F.principalFamily_isBarrier S hM hcard, F.coreBarrier_nonempty S hSne hcard, ?_, ?_, ?_⟩, ?_⟩
  · intro Q hQ
    have hQ' : Q ∈ F.coreParts S := (F.principalFamily_odd S hM hcard) ▸ hQ
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ'
    exact hm.factorCritical_parts F hM (F.mem_odd.mp R.2).1
  · intro Q z hz
    have hab : (zEq.symm z).1 ∈ F.coreNeighbors (qEq.symm Q).1 := by
      apply (F.principal_core_incidence S hM hcard (qEq.symm Q) (zEq.symm z)).mp
      change zEq (zEq.symm z) ∈ P.coreNeighbors (qEq (qEq.symm Q))
      simpa only [Equiv.apply_symm_apply] using hz
    obtain ⟨f, hf, hfn, hforce⟩ := hthrough (qEq.symm Q) (zEq.symm z) hab
    let g : P.odd → F.coreBarrier S := fun R ↦ zEq (f (qEq.symm R))
    refine ⟨g, zEq.bijective.comp (hf.comp qEq.symm.bijective), ?_, ?_⟩
    · intro R
      have hh : zEq (f (qEq.symm R)) ∈ P.coreNeighbors (qEq (qEq.symm R)) :=
        (F.principal_core_incidence S hM hcard (qEq.symm R) (f (qEq.symm R))).mpr (hfn _)
      simpa only [Equiv.apply_symm_apply] using hh
    · change zEq (f (qEq.symm Q)) = z
      rw [hforce, Equiv.apply_symm_apply]
  · intro cA cB hc Q z
    have hh := hconn (fun R ↦ cA (qEq R)) (fun w ↦ cB (zEq w))
      (fun R w hrw ↦ hc _ _ ((F.principal_core_incidence S hM hcard R w).mpr hrw))
      (qEq.symm Q) (zEq.symm z)
    simpa only [Equiv.apply_symm_apply] using hh
  · intro Q hQ
    have hQ' : Q ∈ F.coreParts S := (F.principalFamily_odd S hM hcard) ▸ hQ
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ'
    exact R.2

/-- Every nonempty maximal barrier contains a Dulmage--Mendelsohn barrier. -/
theorem IsMaximalBarrier.exists_DMBarrier (hm : F.IsMaximalBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hZ : Z.Nonempty) :
    ∃ B, B ⊆ Z ∧ ∃ P : H.ComponentFamily B, P.IsDMBarrier := by
  obtain ⟨B, hB, P, hP, _⟩ := hm.exists_DMBarrier_retaining F hM hZ
  exact ⟨B, hB, P, hP⟩

/-- Every labelled edge of a DM-barrier's core is admissible in the original graph. -/
theorem IsDMBarrier.edge_admissible (hd : F.IsDMBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M) {Q : Finset V} (hQ : Q ∈ F.odd)
    {e : E} (he : e ∈ H.dangling Q) : ∃ N, H.IsPerfectMatching N ∧ e ∈ N := by
  classical
  obtain ⟨k, hk, _, hz⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ).1 he
  let q : F.odd := ⟨Q, hQ⟩
  let z : Z := ⟨H.endAt e (Fin.rev k), hz⟩
  have hqz : z ∈ F.coreNeighbors q := (F.mem_coreNeighbors q z).mpr ⟨e, k, hk, rfl⟩
  obtain ⟨f, hf, hfn, hforce⟩ := hd.coreMatching q z hqz
  have hchoices (R : F.odd) : ∃ a : E, ∃ j : Fin 2,
      H.endAt a j ∈ R.1 ∧ H.endAt a (Fin.rev j) = (f R).1 ∧ (R = q → a = e) := by
    by_cases hr : R = q
    · subst R
      refine ⟨e, k, hk, ?_, fun _ ↦ rfl⟩
      exact (congrArg Subtype.val hforce).symm
    · obtain ⟨a, j, hj, hzj⟩ := (F.mem_coreNeighbors R (f R)).mp (hfn R)
      exact ⟨a, j, hj, hzj, fun h ↦ (hr h).elim⟩
  choose edge idx hin hout hkeep using hchoices
  obtain ⟨N, hN, hcontains⟩ := hd.isBarrier.exists_perfectMatching_of_core_edges F hM
    hd.factorCritical f hf edge idx hin hout
  exact ⟨N, hN, hkeep q rfl ▸ hcontains q⟩

end ComponentFamily

/-- Every nonempty graph with a perfect matching has a DM-barrier. -/
theorem IsPerfectMatching.exists_DMBarrier [Nonempty V] {M : Finset E}
    (hM : H.IsPerfectMatching M) : ∃ B, ∃ F : H.ComponentFamily B, F.IsDMBarrier := by
  classical
  obtain ⟨B, F, hm⟩ := hM.exists_maximal_barrier
  have hB : B.Nonempty := by
    by_contra hn
    have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨Q, hQ, _⟩ := F.cover v (by simp [hBe])
    have ho : Q ∈ F.odd := F.mem_odd.mpr ⟨hQ, hm.odd_parts F hM hQ⟩
    have hz : F.odd.card = 0 := by
      simpa only [hBe, Finset.card_empty] using (show F.odd.card = B.card from hm.isBarrier)
    exact (Finset.card_pos.mpr ⟨Q, ho⟩).ne' hz
  obtain ⟨D, _, P, hP⟩ := hm.exists_DMBarrier F hM hB
  exact ⟨D, P, hP⟩

end GraphPuzzles.LoopMultigraph
