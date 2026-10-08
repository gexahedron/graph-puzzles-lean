import GraphPuzzles.Matching.Barriers.MatchingBarrier

/-! Absence of two-vertex separations in loopless bricks. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem sum_le_sum_weightedDegree_of_meets {x : E → ℚ} (hx : ∀ e, 0 ≤ x e)
    (S : Finset E) (Z : Finset V) (hs : S ⊆ H.meets Z) :
    (∑ e ∈ S, x e) ≤ ∑ v ∈ Z, H.weightedDegree x v := by
  rw [sum_weightedDegree]
  calc
    _ ≤ ∑ e ∈ S, (H.endsIn Z e : ℚ) * x e := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨k, hk⟩ := mem_meets.mp (hs he)
      have hn : 1 ≤ H.endsIn Z e := Finset.card_pos.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
      have hn' : (1 : ℚ) ≤ H.endsIn Z e := by exact_mod_cast hn
      simpa using mul_le_mul_of_nonneg_right hn' (hx e)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (hx e))

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- A matching of the complement of a separator makes each component even. -/
theorem even_parts_of_matching {P : Finset E}
    (hP : H.IsPerfectMatchingOn (Finset.univ \ Z) P) {Q : Finset V} (hQ : Q ∈ F.parts) :
    Even Q.card := by
  have hempty : P ∩ H.dangling Q = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heP, heQ⟩ := Finset.mem_inter.mp he
    obtain ⟨k, _, _, hk⟩ := F.exists_end_of_mem_dangling hQ heQ
    exact (Finset.mem_sdiff.mp (hP.1 e heP (Fin.rev k))).2 hk
  have hp := card_mod_two_of_degreeIn_one (K := H) (X := Q) (L := P)
    (fun v hv ↦ hP.2 v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, F.avoid Q hQ v hv⟩))
  rw [hempty, Finset.card_empty] at hp
  exact Nat.even_iff.mpr hp

variable {u v : V} (huv : u ≠ v) (F : H.ComponentFamily {u, v})

include huv

/-- Adding one separator vertex to an even component gives a tight cut. -/
theorem tight_insert_of_even {Q : Finset V} (hQ : Q ∈ F.parts) (heven : Even Q.card) :
    H.IsTightCut (insert u Q) := by
  have hu : u ∉ Q := fun h ↦ F.avoid Q hQ u h (Finset.mem_insert_self ..)
  have hs : H.dangling (insert u Q) ⊆ H.meets {u, v} := by
    intro e he
    have he' := mem_dangling.mp he
    have ex : ∃ k : Fin 2, H.endAt e k ∈ insert u Q ∧ H.endAt e (Fin.rev k) ∉ insert u Q := by
      by_cases h0 : H.endAt e 0 ∈ insert u Q
      · refine ⟨0, h0, ?_⟩
        intro h1
        exact he' ⟨fun _ ↦ h1, fun _ ↦ h0⟩
      · refine ⟨1, ?_, h0⟩
        by_contra h1
        exact he' ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
    obtain ⟨k, hk, hn⟩ := ex
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact mem_meets.mpr ⟨k, hk ▸ Finset.mem_insert_self ..⟩
    · have hz : H.endAt e (Fin.rev k) ∈ ({u, v} : Finset V) := by
        by_contra hz
        exact hn (Finset.mem_insert_of_mem (F.closed Q hQ e k hk hz))
      exact mem_meets.mpr ⟨Fin.rev k, hz⟩
  have hodd : Odd (insert u Q).card := by
    rw [Finset.card_insert_of_notMem hu, Nat.odd_add_one]
    exact Nat.not_odd_iff_even.mpr heven
  intro M hM
  have hle := sum_le_sum_weightedDegree_of_meets (H := H) hM.isFractional.nonneg
    (H.dangling (insert u Q)) {u, v} hs
  change H.cutWeight (matchingVector M) (insert u Q) ≤ _ at hle
  rw [cutWeight_matchingVector] at hle
  simp only [hM.isFractional.degree, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_pair huv] at hle
  have hle' : (M ∩ H.dangling (insert u Q)).card ≤ 2 := by exact_mod_cast hle
  have hp := hM.crossing_mod_two (insert u Q)
  rw [Nat.odd_iff] at hodd
  omega

/-- A loopless brick cannot split into two components after deleting two vertices. -/
theorem card_le_one_of_brick (hg : H.IsBrick) (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    F.parts.card ≤ 1 := by
  obtain ⟨P, hP⟩ := hg.isBicritical hloop u v huv
  have hP' : H.IsPerfectMatchingOn (Finset.univ \ {u, v}) P := by
    have heq : (Finset.univ.erase u).erase v = Finset.univ \ {u, v} := by
      ext w
      simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rwa [heq] at hP
  apply Finset.card_le_one.mpr
  intro Q hQ R hR
  by_contra hne
  have hQeven := F.even_parts_of_matching hP' hQ
  have hReven := F.even_parts_of_matching hP' hR
  have hQpos := Finset.card_pos.mpr (F.nonempty Q hQ)
  have hRpos := Finset.card_pos.mpr (F.nonempty R hR)
  have hQ2 : 2 ≤ Q.card := by rw [Nat.even_iff] at hQeven; omega
  have hR2 : 2 ≤ R.card := by rw [Nat.even_iff] at hReven; omega
  have ht := F.tight_insert_of_even huv hQ hQeven
  apply hg.tight_trivial _ ht
  constructor
  · exact hQ2.trans (Finset.card_le_card (Finset.subset_insert _ _))
  · have hsub : R ⊆ Finset.univ \ insert u Q := by
      intro w hw
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      rcases Finset.mem_insert.mp hh with hwu | hh
      · exact F.avoid R hR w hw (Finset.mem_insert.mpr (Or.inl hwu))
      · exact Finset.disjoint_left.mp (F.pairwise Q hQ R hR hne) hh hw
    exact hR2.trans (Finset.card_le_card hsub)

end ComponentFamily

omit [DecidableEq E] in
/-- Colour classes constant along surviving edges form a component family. -/
theorem exists_componentFamily_of_coloring (Z : Finset V) (c : V → Bool)
    (hc : ∀ e, H.endAt e 0 ∉ Z → H.endAt e 1 ∉ Z → c (H.endAt e 0) = c (H.endAt e 1)) :
    ∃ F : H.ComponentFamily Z,
      ∀ Q ∈ F.parts, ∀ a ∈ Q, ∀ b ∈ Q, c a = c b := by
  let part (b : Bool) := Finset.univ.filter fun v ↦ v ∉ Z ∧ c v = b
  let parts := (Finset.univ.filter fun b : Bool ↦ (part b).Nonempty).image part
  have hpart (b : Bool) (v : V) : v ∈ part b ↔ v ∉ Z ∧ c v = b := by simp [part]
  have hparts (Q : Finset V) : Q ∈ parts ↔ ∃ b, (part b).Nonempty ∧ part b = Q := by
    simp [parts]
  refine ⟨⟨parts, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨b, hb, rfl⟩ := (hparts Q).mp hQ
    exact hb
  · intro Q hQ w hw
    obtain ⟨b, _, rfl⟩ := (hparts Q).mp hQ
    exact ((hpart b w).mp hw).1
  · intro Q hQ e k hk hn
    obtain ⟨b, _, rfl⟩ := (hparts Q).mp hQ
    obtain ⟨hkZ, hkcol⟩ := (hpart b _).mp hk
    apply (hpart b _).mpr
    refine ⟨hn, ?_⟩
    have hh : c (H.endAt e (Fin.rev k)) = c (H.endAt e k) := by
      fin_cases k
      · exact (hc e hkZ hn).symm
      · exact hc e hn hkZ
    exact hh.trans hkcol
  · intro Q hQ R hR hne
    obtain ⟨b, _, rfl⟩ := (hparts Q).mp hQ
    obtain ⟨b', _, rfl⟩ := (hparts R).mp hR
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have hh : b = b' := ((hpart b w).mp hw).2.symm.trans ((hpart b' w).mp hw').2
    exact hne (congrArg part hh)
  · intro w hw
    have hm : w ∈ part (c w) := (hpart _ _).mpr ⟨hw, rfl⟩
    exact ⟨part (c w), (hparts _).mpr ⟨c w, ⟨w, hm⟩, rfl⟩, hm⟩
  · intro Q hQ a ha b hb
    obtain ⟨d, _, rfl⟩ := (hparts Q).mp hQ
    exact ((hpart d a).mp ha).2.trans ((hpart d b).mp hb).2.symm

/-- Removing two distinct vertices from a loopless brick leaves a connected graph,
expressed by the same colouring criterion as `IsConnected`. -/
theorem IsBrick.connected_delete_pair (hg : H.IsBrick)
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (u v : V) (huv : u ≠ v)
    (c : V → Bool)
    (hc : ∀ e, H.endAt e 0 ∉ ({u, v} : Finset V) → H.endAt e 1 ∉ ({u, v} : Finset V) →
      c (H.endAt e 0) = c (H.endAt e 1)) :
    ∀ a, a ∉ ({u, v} : Finset V) → ∀ b, b ∉ ({u, v} : Finset V) → c a = c b := by
  obtain ⟨F, hF⟩ := exists_componentFamily_of_coloring (H := H) {u, v} c hc
  have hs := F.card_le_one_of_brick huv hg hloop
  intro a ha b hb
  obtain ⟨Q, hQ, haQ⟩ := F.cover a ha
  obtain ⟨R, hR, hbR⟩ := F.cover b hb
  have heq := Finset.card_le_one.mp hs Q hQ R hR
  subst R
  exact hF Q hQ a haQ b hbR

/-- Connectivity after deleting any two distinct vertices, expressed by
colourings constant on every surviving edge. -/
def ConnectedAfterDeletingPairs (H : LoopMultigraph V E) : Prop :=
  ∀ (u v : V), u ≠ v → ∀ (c : V → Bool),
    (∀ e, H.endAt e 0 ∉ ({u, v} : Finset V) → H.endAt e 1 ∉ ({u, v} : Finset V) →
      c (H.endAt e 0) = c (H.endAt e 1)) →
    ∀ a, a ∉ ({u, v} : Finset V) → ∀ b, b ∉ ({u, v} : Finset V) → c a = c b

theorem IsBrick.connectedAfterDeletingPairs (hg : H.IsBrick)
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : H.ConnectedAfterDeletingPairs :=
  hg.connected_delete_pair hloop

end GraphPuzzles.LoopMultigraph
