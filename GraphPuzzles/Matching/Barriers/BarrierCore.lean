import GraphPuzzles.Matching.MatchingOn
import GraphPuzzles.Matching.Barriers.MaximalBarrier
import GraphPuzzles.Matching.Bipartite.HallCore

/-!
# The bipartite core of a barrier

A perfect matching pairs the odd components of a barrier bijectively with its
vertices. Hall's theorem then selects a nonempty connected core in which every
incidence extends to a bijective matching.
-/

namespace GraphPuzzles.LoopMultigraph.ComponentFamily

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)

open Classical in
/-- Barrier vertices adjacent to an odd component, with edge labels and end indices retained. -/
noncomputable def coreNeighbors (Q : F.odd) : Finset Z :=
  Finset.univ.filter fun z ↦ ∃ e : E, ∃ k : Fin 2,
    H.endAt e k ∈ Q.1 ∧ H.endAt e (Fin.rev k) = z.1

open Classical in
omit [DecidableEq E] in
@[simp] theorem mem_coreNeighbors (Q : F.odd) (z : Z) :
    z ∈ F.coreNeighbors Q ↔ ∃ e : E, ∃ k : Fin 2,
      H.endAt e k ∈ Q.1 ∧ H.endAt e (Fin.rev k) = z.1 := by
  simp [coreNeighbors]

/-- A perfect matching pairs the odd components bijectively with the barrier
vertices, using its unique edge leaving each odd component. -/
theorem IsBarrier.core_matching (hb : F.IsBarrier) {M : Finset E} (hM : H.IsPerfectMatching M) :
    ∃ f : F.odd → Z, Function.Bijective f ∧
      ∀ Q, ∃ e ∈ M, ∃ k : Fin 2, H.endAt e k ∈ Q.1 ∧ H.endAt e (Fin.rev k) = (f Q).1 := by
  classical
  have hex (Q : F.odd) : ∃ e ∈ M, ∃ k : Fin 2,
      H.endAt e k ∈ Q.1 ∧ H.endAt e (Fin.rev k) ∈ Z := by
    have hc := hb.isTightCut F Q.2 M hM
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (M ∩ H.dangling Q.1).card)
    obtain ⟨heM, heQ⟩ := Finset.mem_inter.mp he
    obtain ⟨k, hk, _, hz⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp Q.2).1 heQ
    exact ⟨e, heM, k, hk, hz⟩
  choose edge heM idx hidx hZ using hex
  let f : F.odd → Z := fun Q ↦ ⟨H.endAt (edge Q) (Fin.rev (idx Q)), hZ Q⟩
  have hfinj : Function.Injective f := by
    intro Q R hQR
    have hend : H.endAt (edge R) (Fin.rev (idx R)) = H.endAt (edge Q) (Fin.rev (idx Q)) :=
      (congrArg Subtype.val hQR).symm
    have hi := eq_incidence_of_degreeIn_one (hM _) (heM Q) (heM R) rfl hend
    have he : edge Q = edge R := congrArg Prod.fst hi
    have hk : idx Q = idx R := Fin.rev_injective (congrArg Prod.snd hi)
    apply Subtype.ext
    apply F.eq_of_mem (F.mem_odd.mp Q.2).1 (F.mem_odd.mp R.2).1 (hidx Q)
    simpa only [he, hk] using hidx R
  have hcard : Fintype.card F.odd = Fintype.card Z := by
    simpa only [Fintype.card_coe] using (show F.odd.card = Z.card from hb)
  refine ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩, ?_⟩
  exact fun Q ↦ ⟨edge Q, heM Q, idx Q, hidx Q, rfl⟩

/-- Hall's inequalities for the barrier core follow from a perfect matching of the graph. -/
theorem IsBarrier.core_hall (hb : F.IsBarrier) {M : Finset E} (hM : H.IsPerfectMatching M)
    (S : Finset F.odd) : S.card ≤ (S.biUnion F.coreNeighbors).card := by
  obtain ⟨f, hf, he⟩ := hb.core_matching F hM
  have hsub : S.image f ⊆ S.biUnion F.coreNeighbors := by
    intro z hz
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨e, _, k, hk, hz⟩ := he Q
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, (F.mem_coreNeighbors Q (f Q)).mpr ⟨e, k, hk, hz⟩⟩
  simpa only [Finset.card_image_of_injective _ hf.1] using Finset.card_le_card hsub

theorem IsBarrier.core_neighbors_univ (hb : F.IsBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) : Finset.univ.biUnion F.coreNeighbors = Finset.univ := by
  obtain ⟨f, hf, he⟩ := hb.core_matching F hM
  apply Finset.eq_univ_of_forall
  intro z
  obtain ⟨Q, rfl⟩ := hf.2 z
  obtain ⟨e, _, k, hk, hz⟩ := he Q
  exact Finset.mem_biUnion.mpr ⟨Q, Finset.mem_univ _,
    (F.mem_coreNeighbors Q (f Q)).mpr ⟨e, k, hk, hz⟩⟩

/-- A nonempty barrier has a principal core: a nonempty collection of odd
components and their equally many neighbours, connected and with every
incidence extending to a bijective matching. -/
theorem IsBarrier.exists_principal_core (hb : F.IsBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hZ : Z.Nonempty) :
    ∃ S : Finset F.odd, S.Nonempty ∧ (S.biUnion F.coreNeighbors).card = S.card ∧
      (∀ (Q : S) (z : S.biUnion F.coreNeighbors), z.1 ∈ F.coreNeighbors Q.1 →
        ∃ f : S → S.biUnion F.coreNeighbors, Function.Bijective f ∧
          (∀ R, (f R).1 ∈ F.coreNeighbors R.1) ∧ f Q = z) ∧
      (∀ (cA : S → Bool) (cB : S.biUnion F.coreNeighbors → Bool),
        (∀ Q z, z.1 ∈ F.coreNeighbors Q.1 → cA Q = cB z) → ∀ Q z, cA Q = cB z) := by
  have hodd : F.odd.Nonempty := Finset.card_pos.mp (by
    change F.odd.card = Z.card at hb
    rw [hb]
    exact Finset.card_pos.mpr hZ)
  haveI : Nonempty F.odd := hodd.to_subtype
  apply HallCore.exists_matchingCovered_core F.coreNeighbors (hb.core_hall F hM)
  rw [hb.core_neighbors_univ F hM, Finset.card_univ, Fintype.card_coe, Fintype.card_coe]
  exact hb.symm

end GraphPuzzles.LoopMultigraph.ComponentFamily
