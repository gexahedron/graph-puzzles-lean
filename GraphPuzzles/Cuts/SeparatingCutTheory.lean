import GraphPuzzles.Bricks.Brick

/-!
# Basic separating-cut theory

The elementary cut and contraction lemmas used in Campos--Lucchesi's report.
These do not assume their three-crossing theorem.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The vertex map of a shore contraction. -/
def contractVertex (X : Finset V) (v : V) : Option X :=
  if h : v ∈ X then some ⟨v, h⟩ else none

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractVertex_some (X : Finset V) (v : X) : contractVertex X v.1 = some v := by
  simp [contractVertex, v.2]

omit [Fintype E] [DecidableEq E] in
theorem contractVertex_surjective (X : Finset V) (hX : (Finset.univ \ X).Nonempty) :
    Function.Surjective (contractVertex X) := by
  intro v
  cases v with
  | none =>
    obtain ⟨w, hw⟩ := hX
    exact ⟨w, by simp [contractVertex, (Finset.mem_sdiff.mp hw).2]⟩
  | some v => exact ⟨v.1, contractVertex_some X v⟩

omit [DecidableEq E] in
/-- Contracting a nonempty shore preserves connectivity. -/
theorem IsConnected.contract (hc : H.IsConnected) (X : Finset V)
    (hX : (Finset.univ \ X).Nonempty) : (H.contract X).IsConnected := by
  intro c he u v
  let d : V → Bool := c ∘ contractVertex X
  have hd (e : E) : d (H.endAt e 0) = d (H.endAt e 1) := by
    by_cases hm : e ∈ H.meets X
    · exact he ⟨e, hm⟩
    · have h0 : H.endAt e 0 ∉ X := fun h ↦ hm (mem_meets.mpr ⟨0, h⟩)
      have h1 : H.endAt e 1 ∉ X := fun h ↦ hm (mem_meets.mpr ⟨1, h⟩)
      simp [d, contractVertex, h0, h1]
  obtain ⟨a, ha⟩ := contractVertex_surjective X hX u
  obtain ⟨b, hb⟩ := contractVertex_surjective X hX v
  simpa only [d, Function.comp_apply, ha, hb] using hc d hd a b

/-- Restriction of a matching which crosses a cut once is a matching of its contraction. -/
theorem IsPerfectMatching.contract_of_crossing_one {M : Finset E}
    (hM : H.IsPerfectMatching M) (X : Finset V) (hX : (M ∩ H.dangling X).card = 1) :
    (H.contract X).IsPerfectMatching (Finset.univ.filter fun e ↦ e.1 ∈ M) := by
  intro v
  cases v with
  | some v => rw [contract_degreeIn_some, hM]
  | none =>
    rw [contract_degreeIn_none]
    have heq : ((Finset.univ.filter fun e : H.meets X ↦ e.1 ∈ M).image Subtype.val) ∩
        H.dangling X = M ∩ H.dangling X := by
      ext e
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨f, hf, rfl⟩, hd⟩
        exact ⟨hf, hd⟩
      · rintro ⟨he, hd⟩
        exact ⟨⟨⟨e, dangling_subset_meets X hd⟩, he, rfl⟩, hd⟩
    rw [heq, hX]

/-- Campos--Lucchesi Lemma 4.1, converse: matchings crossing once cover both contractions. -/
theorem isSeparatingCut_of_crossing_one (hc : H.IsConnected) {X : Finset V}
    (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty)
    (h : ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M ∧ (M ∩ H.dangling X).card = 1) :
    H.IsSeparatingCut X := by
  have side (Y : Finset V) (hy : (Finset.univ \ Y).Nonempty)
      (hh : ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M ∧ (M ∩ H.dangling Y).card = 1) :
      (H.contract Y).IsMatchingCovered := by
    refine ⟨hc.contract Y hy, ?_⟩
    intro e
    obtain ⟨M, hM, he, hm⟩ := hh e.1
    exact ⟨_, hM.contract_of_crossing_one Y hm, by simp [he]⟩
  refine ⟨side X hXC h, side (Finset.univ \ X) ?_ ?_⟩
  · simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hX
  · simpa only [dangling_compl] using h

/-- The exact edge-wise characterization, with nonempty shores explicit. -/
theorem isSeparatingCut_iff_crossing_one (hc : H.IsConnected) {X : Finset V}
    (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty) :
    H.IsSeparatingCut X ↔
      ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M ∧ (M ∩ H.dangling X).card = 1 :=
  ⟨fun h ↦ h.exists_perfectMatching_through, isSeparatingCut_of_crossing_one hc hX hXC⟩

/-- A tight cut of a matching-covered graph is separating. -/
theorem IsTightCut.isSeparatingCut (hm : H.IsMatchingCovered) {X : Finset V}
    (ht : H.IsTightCut X) (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty) :
    H.IsSeparatingCut X := by
  apply isSeparatingCut_of_crossing_one hm.1 hX hXC
  intro e
  obtain ⟨M, hM, he⟩ := hm.2 e
  exact ⟨M, hM, he, ht M hM⟩

omit [DecidableEq E] in
theorem sum_vertexWeight_degree (p : V → ℚ) (x : E → ℚ) :
    (∑ v, p v * H.weightedDegree x v) =
      ∑ e, x e * (p (H.endAt e 0) + p (H.endAt e 1)) := by
  simp only [weightedDegree, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_two]
  simp [eq_comm, mul_comm, mul_add]

/-- A bipartite contraction fixes the number of matching edges on its boundary. -/
theorem IsBipartite.contract_cut_count {X : Finset V} (hb : (H.contract X).IsBipartite)
    {M N : Finset E} (hM : H.IsPerfectMatching M) (hN : H.IsPerfectMatching N) :
    (M ∩ H.dangling X).card = (N ∩ H.dangling X).card := by
  obtain ⟨c, hc⟩ := hb
  let p : V → ℚ := fun v ↦ if h : v ∈ X then
    (if c (some ⟨v, h⟩) = c none then -1 else 1) else 0
  have hp (e : E) : p (H.endAt e 0) + p (H.endAt e 1) =
      if e ∈ H.dangling X then (1 : ℚ) else 0 := by
    by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X
    · have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
      simp only [contract_endAt, dif_pos h0, dif_pos h1] at hh
      have hn : e ∉ H.dangling X := by simp [mem_dangling, h0, h1]
      simp only [p, dif_pos h0, dif_pos h1, if_neg hn]
      cases hc0 : c (some ⟨H.endAt e 0, h0⟩) <;>
        cases hc1 : c (some ⟨H.endAt e 1, h1⟩) <;> cases hcn : c none <;> simp_all
    · have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
      simp only [contract_endAt, dif_pos h0, dif_neg h1] at hh
      have hn : e ∈ H.dangling X := by simp [mem_dangling, h0, h1]
      simp [p, h0, h1, hh, hn]
    · have hh := hc ⟨e, mem_meets.mpr ⟨1, h1⟩⟩
      simp only [contract_endAt, dif_neg h0, dif_pos h1] at hh
      have hn : e ∈ H.dangling X := by simp [mem_dangling, h0, h1]
      simp [p, h0, h1, Ne.symm hh, hn]
    · simp [p, h0, h1, mem_dangling]
  have key {P : Finset E} (hP : H.IsPerfectMatching P) :
      ((P ∩ H.dangling X).card : ℚ) = ∑ v, p v := by
    have hh := sum_vertexWeight_degree (H := H) p (matchingVector P)
    simp only [hP.isFractional.degree, mul_one, hp] at hh
    rw [← cutWeight_matchingVector (H := H) P X]
    rw [hh, cutWeight]
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast (key hM).trans (key hN).symm

omit [DecidableEq E] in
/-- A connected graph has an edge across every cut with two nonempty shores. -/
theorem IsConnected.dangling_nonempty (hc : H.IsConnected) {X : Finset V}
    (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty) : (H.dangling X).Nonempty := by
  by_contra hn
  have he (e : E) : H.endAt e 0 ∈ X ↔ H.endAt e 1 ∈ X := by
    by_contra h
    exact hn ⟨e, mem_dangling.mpr h⟩
  let c : V → Bool := fun v ↦ decide (v ∈ X)
  have hcol (e : E) : c (H.endAt e 0) = c (H.endAt e 1) := by
    dsimp [c]
    simp only [he e]
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hXC
  have hh := hc c hcol a b
  simp [c, ha, (Finset.mem_sdiff.mp hb).2] at hh

omit [DecidableEq E] in
theorem IsSeparatingCut.compl {X : Finset V} (hs : H.IsSeparatingCut X) :
    H.IsSeparatingCut (Finset.univ \ X) := by
  refine ⟨hs.2, ?_⟩
  have heq : Finset.univ \ (Finset.univ \ X) = X := by ext v; simp
  rw [heq]
  exact hs.1

omit [Fintype E] [DecidableEq E] in
theorem IsNontrivialCut.compl {X : Finset V} (hX : IsNontrivialCut X) :
    IsNontrivialCut (Finset.univ \ X) := by
  refine ⟨hX.2, ?_⟩
  simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hX.1

/-- A nontrivial separating cut admits a matching crossing it once. -/
theorem IsSeparatingCut.exists_crossing_one {X : Finset V} (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hX : IsNontrivialCut X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 1 := by
  obtain ⟨e, _⟩ := hc.dangling_nonempty (X := X)
    (Finset.card_pos.mp (by have hh := hX.1; omega))
    (Finset.card_pos.mp (by have hh := hX.2; omega))
  obtain ⟨M, hM, _, hm⟩ := hs.exists_perfectMatching_through e
  exact ⟨M, hM, hm⟩

/-- The matching version of the odd-cut parity identity. -/
theorem IsPerfectMatching.crossing_mod_two {M : Finset E} (hM : H.IsPerfectMatching M)
    (X : Finset V) : (M ∩ H.dangling X).card % 2 = X.card % 2 := by
  have h := sum_degreeIn_mod_two (K := H) X M
  rw [Finset.sum_congr rfl (fun v _ ↦ hM v)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  exact h.symm

theorem IsSeparatingCut.odd_shore {X : Finset V} (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hX : IsNontrivialCut X) : Odd X.card := by
  obtain ⟨M, hM, hm⟩ := hs.exists_crossing_one hc hX
  have hh := hM.crossing_mod_two X
  rw [hm] at hh
  rw [Nat.odd_iff]
  exact hh.symm

/-- Campos--Lucchesi Corollary 2.2: a bipartite contraction makes a separating cut tight. -/
theorem IsSeparatingCut.tight_of_bipartite {X : Finset V} (hs : H.IsSeparatingCut X)
    (hc : H.IsConnected) (hX : IsNontrivialCut X) (hb : (H.contract X).IsBipartite) :
    H.IsTightCut X := by
  obtain ⟨N, hN, hn⟩ := hs.exists_crossing_one hc hX
  intro M hM
  exact (hb.contract_cut_count hM hN).trans hn

/-- Every nontrivial separating cut of a brick has two nonbipartite contractions. -/
theorem IsBrick.nonbipartite_contractions (hb : H.IsBrick) {X : Finset V}
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ¬ (H.contract X).IsBipartite ∧ ¬ (H.contract (Finset.univ \ X)).IsBipartite := by
  constructor
  · intro hc
    exact hb.tight_trivial X (hs.tight_of_bipartite hb.matchingCovered.1 hX hc) hX
  · intro hc
    exact hb.tight_trivial (Finset.univ \ X)
      (hs.compl.tight_of_bipartite hb.matchingCovered.1 hX.compl hc) hX.compl

/-- A nontrivial separating cut of a brick admits an odd crossing count at least three.
Reducing this count to three outside Petersen is the remaining Campos--Lucchesi theorem. -/
theorem IsBrick.exists_crossing_at_least_three (hb : H.IsBrick) {X : Finset V}
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ M, H.IsPerfectMatching M ∧ Odd (M ∩ H.dangling X).card ∧
      3 ≤ (M ∩ H.dangling X).card := by
  have hn : ¬ ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1 :=
    fun ht ↦ hb.tight_trivial X ht hX
  push Not at hn
  obtain ⟨M, hM, hm⟩ := hn
  have ho := hs.odd_shore hb.matchingCovered.1 hX
  have hp := hM.crossing_mod_two X
  rw [Nat.odd_iff] at ho
  have hoM : Odd (M ∩ H.dangling X).card := by rw [Nat.odd_iff, hp, ho]
  exact ⟨M, hM, hoM, by omega⟩

end GraphPuzzles.LoopMultigraph
