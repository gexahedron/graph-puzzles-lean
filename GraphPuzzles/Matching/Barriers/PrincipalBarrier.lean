import GraphPuzzles.Matching.Barriers.BarrierCore
import GraphPuzzles.Matching.Barriers.ComponentRetention

/-! Principal barriers selected from the bipartite core by Hall's theorem. -/

namespace GraphPuzzles.LoopMultigraph.ComponentFamily

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)
variable (S : Finset F.odd)

/-- The selected odd components, viewed as original vertex sets. -/
def coreParts : Finset (Finset V) := S.image Subtype.val

/-- The barrier vertices neighbouring the selected components. -/
noncomputable def coreBarrier : Finset V := (S.biUnion F.coreNeighbors).image Subtype.val

omit [DecidableEq E] in
theorem coreParts_subset : F.coreParts S ⊆ F.parts := by
  intro Q hQ
  obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hQ
  exact (F.mem_odd.mp Q.2).1

omit [DecidableEq E] in
theorem coreBarrier_subset : F.coreBarrier S ⊆ Z := by
  intro z hz
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hz
  exact z.2

omit [DecidableEq E] in
theorem coreParts_odd {Q : Finset V} (hQ : Q ∈ F.coreParts S) : Odd Q.card := by
  obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hQ
  exact (F.mem_odd.mp Q.2).2

omit [DecidableEq E] in
theorem coreParts_card : (F.coreParts S).card = S.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

omit [DecidableEq E] in
theorem coreBarrier_card : (F.coreBarrier S).card = (S.biUnion F.coreNeighbors).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

omit [DecidableEq E] in
theorem coreParts_closed (Q : Finset V) (hQ : Q ∈ F.coreParts S)
    (e : E) (k : Fin 2) (hk : H.endAt e k ∈ Q) (hn : H.endAt e (Fin.rev k) ∉ F.coreBarrier S) :
    H.endAt e (Fin.rev k) ∈ Q := by
  obtain ⟨Q, hQS, rfl⟩ := Finset.mem_image.mp hQ
  apply F.closed Q.1 (F.mem_odd.mp Q.2).1 e k hk
  intro hz
  let z : Z := ⟨H.endAt e (Fin.rev k), hz⟩
  apply hn
  refine Finset.mem_image.mpr ⟨z, Finset.mem_biUnion.mpr ⟨Q, hQS, ?_⟩, rfl⟩
  exact (F.mem_coreNeighbors Q z).mpr ⟨e, k, hk, rfl⟩

/-- Retain the selected components and group the remaining vertices into one part. -/
noncomputable def principalFamily : H.ComponentFamily (F.coreBarrier S) :=
  F.retainParts (F.coreParts S) (F.coreBarrier S) (F.coreParts_subset S)
    (F.coreBarrier_subset S) (F.coreParts_closed S)

theorem principalFamily_odd {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card) :
    (F.principalFamily S).odd = F.coreParts S := by
  apply F.retainParts_odd (F.coreParts S) (F.coreBarrier S) (F.coreParts_subset S)
    (F.coreBarrier_subset S) (F.coreParts_closed S) hM (fun Q hQ ↦ F.coreParts_odd S hQ)
  rw [F.coreParts_card S, F.coreBarrier_card S, hcard]

theorem principalFamily_isBarrier {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card) : (F.principalFamily S).IsBarrier := by
  change (F.principalFamily S).odd.card = (F.coreBarrier S).card
  rw [F.principalFamily_odd S hM hcard, F.coreParts_card S, F.coreBarrier_card S, hcard]

omit [DecidableEq E] in
theorem coreBarrier_nonempty (hSne : S.Nonempty)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card) : (F.coreBarrier S).Nonempty := by
  apply Finset.card_pos.mp
  rw [F.coreBarrier_card S, hcard]
  exact Finset.card_pos.mpr hSne

/-- Identify selected component indices with the odd parts of the principal barrier. -/
noncomputable def principalPartsEquiv {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card) : S ≃ (F.principalFamily S).odd := by
  let f : S → (F.principalFamily S).odd := fun Q ↦ ⟨Q.1.1, by
    rw [F.principalFamily_odd S hM hcard]
    exact Finset.mem_image.mpr ⟨Q.1, Q.2, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro Q R he
    have hv : Q.1.1 = R.1.1 := congrArg (fun T : (F.principalFamily S).odd ↦ T.1) he
    exact Subtype.ext (Subtype.ext hv)
  · intro Q
    have hQ : Q.1 ∈ F.coreParts S := (F.principalFamily_odd S hM hcard) ▸ Q.2
    obtain ⟨R, hRS, he⟩ := Finset.mem_image.mp hQ
    exact ⟨⟨R, hRS⟩, Subtype.ext he⟩

/-- Identify neighbour indices with the actual vertices of the principal barrier. -/
noncomputable def principalBarrierEquiv : (S.biUnion F.coreNeighbors) ≃ F.coreBarrier S := by
  let f : (S.biUnion F.coreNeighbors) → F.coreBarrier S := fun z ↦
    ⟨z.1.1, Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w he
    have hv : z.1.1 = w.1.1 := congrArg (fun t : F.coreBarrier S ↦ t.1) he
    exact Subtype.ext (Subtype.ext hv)
  · intro z
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp z.2
    exact ⟨⟨w, hw⟩, Subtype.ext he⟩

theorem principalPartsEquiv_val {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card) (Q : S) :
    (F.principalPartsEquiv S hM hcard Q).1 = Q.1.1 := rfl

omit [DecidableEq E] in
theorem principalBarrierEquiv_val (z : S.biUnion F.coreNeighbors) :
    (F.principalBarrierEquiv S z).1 = z.1.1 := rfl

theorem principal_core_incidence {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcard : (S.biUnion F.coreNeighbors).card = S.card)
    (Q : S) (z : S.biUnion F.coreNeighbors) :
    F.principalBarrierEquiv S z ∈
      (F.principalFamily S).coreNeighbors (F.principalPartsEquiv S hM hcard Q) ↔
      z.1 ∈ F.coreNeighbors Q.1 := by
  rw [(F.principalFamily S).mem_coreNeighbors, F.mem_coreNeighbors,
    F.principalPartsEquiv_val, F.principalBarrierEquiv_val]

end GraphPuzzles.LoopMultigraph.ComponentFamily
