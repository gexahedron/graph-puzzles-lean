import GraphPuzzles.Matching.Barriers.BarrierBicritical
import GraphPuzzles.Cuts.TightCutTransport

/-! Lifting component families and barriers through an odd-shore contraction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- All original vertices represented by a contraction shore, including the
entire collapsed shore when the pole belongs to it. -/
def expandedContractShore (X : Finset V) (Q : Finset (Option X)) : Finset V :=
  Finset.univ.filter fun v ↦ contractVertex X v ∈ Q

@[simp] theorem mem_expandedContractShore (X : Finset V) (Q : Finset (Option X)) (v : V) :
    v ∈ expandedContractShore X Q ↔ contractVertex X v ∈ Q := by
  simp [expandedContractShore]

theorem expandedContractShore_injective (X : Finset V)
    (hX : (Finset.univ \ X).Nonempty) : Function.Injective (expandedContractShore X) := by
  intro Q R h
  ext w
  obtain ⟨v, rfl⟩ := contractVertex_surjective X hX w
  rw [← mem_expandedContractShore X Q v, h, mem_expandedContractShore]

theorem expandedContractShore_eq_source (X : Finset V) (Q : Finset (Option X))
    (hn : none ∉ Q) : expandedContractShore X Q = sourceShore X Q := by
  ext v
  simp only [mem_expandedContractShore, sourceShore, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    by_cases h : v ∈ X
    · exact ⟨⟨v, h⟩, by simpa [contractVertex, h] using hv, rfl⟩
    · exact (hn (by simpa [contractVertex, h] using hv)).elim
  · rintro ⟨w, hw, rfl⟩
    simpa only [contractVertex_some] using hw

theorem expandedContractShore_eq_union (X : Finset V) (Q : Finset (Option X))
    (hn : none ∈ Q) :
    expandedContractShore X Q = sourceShore X (Q.erase none) ∪ (Finset.univ \ X) := by
  ext v
  by_cases h : v ∈ X
  · simp only [mem_expandedContractShore, contractVertex, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_univ, true_and, h, not_true_eq_false, or_false]
    simp only [sourceShore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · exact fun hv ↦ ⟨⟨v, h⟩, ⟨by simp, hv⟩, rfl⟩
    · rintro ⟨w, ⟨_, hw⟩, he⟩
      have hwv : w = ⟨v, h⟩ := Subtype.ext he
      simpa [hwv] using hw
  · simp [expandedContractShore, contractVertex, h, hn]

/-- Replacing a pole by an odd number of original vertices preserves parity. -/
theorem expandedContractShore_odd_iff (X : Finset V) (Q : Finset (Option X))
    (hX : Odd (Finset.univ \ X).card) :
    Odd (expandedContractShore X Q).card ↔ Odd Q.card := by
  by_cases hn : none ∈ Q
  · rw [expandedContractShore_eq_union X Q hn, Finset.card_union_of_disjoint]
    · rw [card_sourceShore X (Q.erase none) (by simp), Finset.card_erase_of_mem hn]
      have hp := Finset.card_pos.mpr ⟨none, hn⟩
      rw [Nat.odd_iff] at hX ⊢
      rw [Nat.odd_iff]
      omega
    · exact Finset.disjoint_left.mpr fun v hv hh ↦
        (Finset.mem_sdiff.mp hh).2 (sourceShore_subset X _ hv)
  · rw [expandedContractShore_eq_source X Q hn, card_sourceShore X Q hn]

namespace ComponentFamily

variable {X : Finset V} {B : Finset (Option X)}
variable (F : (H.contract X).ComponentFamily B)

/-- Lift a component partition. Edges wholly in the collapsed shore stay
inside the lifted component containing the pole. -/
def of_contract (hX : (Finset.univ \ X).Nonempty) :
    H.ComponentFamily (expandedContractShore X B) where
  parts := F.parts.image (expandedContractShore X)
  nonempty := by
    intro Q hQ
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨w, hw⟩ := F.nonempty R hR
    obtain ⟨v, hv⟩ := contractVertex_surjective X hX w
    exact ⟨v, by simpa [hv] using hw⟩
  avoid := by
    intro Q hQ v hv hb
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    exact F.avoid R hR _ (mem_expandedContractShore X R v |>.mp hv)
      (mem_expandedContractShore X B v |>.mp hb)
  closed := by
    intro Q hQ e k hk hn
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    simp only [mem_expandedContractShore] at hk hn ⊢
    by_cases he : e ∈ H.meets X
    · exact F.closed R hR ⟨e, he⟩ k hk hn
    · have hout (i) : H.endAt e i ∉ X := fun hi ↦ he (mem_meets.mpr ⟨i, hi⟩)
      simpa only [contractVertex, dif_neg (hout k), dif_neg (hout (Fin.rev k))] using hk
  pairwise := by
    intro Q hQ R hR hne
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
    apply Finset.disjoint_left.mpr
    intro v hvQ hvR
    exact Finset.disjoint_left.mp (F.pairwise Q' hQ' R' hR'
      (fun h ↦ hne (congrArg _ h)))
      ((mem_expandedContractShore X Q' v).mp hvQ)
      ((mem_expandedContractShore X R' v).mp hvR)
  cover := by
    intro v hv
    obtain ⟨Q, hQ, hw⟩ := F.cover (contractVertex X v) (by simpa using hv)
    exact ⟨_, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩, by simpa using hw⟩

theorem of_contract_odd (hX : (Finset.univ \ X).Nonempty)
    (ho : Odd (Finset.univ \ X).card) :
    (F.of_contract hX).odd = F.odd.image (expandedContractShore X) := by
  ext Q
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := (F.of_contract hX).mem_odd.mp h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨R,
      F.mem_odd.mpr ⟨hR, (expandedContractShore_odd_iff X R ho).mp hq⟩, rfl⟩
  · intro h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp h
    exact (F.of_contract hX).mem_odd.mpr
      ⟨Finset.mem_image.mpr ⟨R, (F.mem_odd.mp hR).1, rfl⟩,
        (expandedContractShore_odd_iff X R ho).mpr (F.mem_odd.mp hR).2⟩

/-- A barrier avoiding the pole lifts to an equally large barrier when the
collapsed shore is odd. No matching-covered assumption is needed. -/
theorem IsBarrier.of_contract (hb : F.IsBarrier)
    (hX : (Finset.univ \ X).Nonempty) (ho : Odd (Finset.univ \ X).card)
    (hn : none ∉ B) : (F.of_contract hX).IsBarrier := by
  change (F.of_contract hX).odd.card = (expandedContractShore X B).card
  rw [F.of_contract_odd hX ho, Finset.card_image_of_injective _
    (expandedContractShore_injective X hX), expandedContractShore_eq_source X B hn,
    card_sourceShore X B hn]
  exact hb

/-- Thus any barrier with at least two vertices in such a contraction of a
bicritical graph must contain the pole. -/
theorem IsBarrier.pole_mem_of_bicritical (hb : F.IsBarrier) (hc : H.IsBicritical)
    (hX : (Finset.univ \ X).Nonempty) (ho : Odd (Finset.univ \ X).card)
    (hB : 2 ≤ B.card) : none ∈ B := by
  by_contra hn
  have h := hc.barrier_card_le_one (F.of_contract hX) (hb.of_contract F hX ho hn)
  rw [expandedContractShore_eq_source X B hn, card_sourceShore X B hn] at h
  omega

end ComponentFamily
end GraphPuzzles.LoopMultigraph
