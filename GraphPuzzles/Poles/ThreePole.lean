import GraphPuzzles.Matching.FourCover

/-!
# Gluing proper four-covers of two Hamiltonian `3`-poles

The corollary `KMThreeSpokes` used by the four-cover theorem is derived in the note from
Theorem 3.1 of Karabáš–Máčajová (every Hamiltonian cubic `3`-pole has a proper four-cover) by
cutting the three joining edges and gluing.  This module states Theorem 3.1 in an ambient form,
`KMThreePole`: the pole spanned by a circuit `R` avoiding the perfect matching `S` consists of the
vertices of `R` and the edges meeting them, its dangling edges are the edges with exactly one end
on `R`, and a proper four-cover consists of `S` together with three matchings of the pole covering
every edge of the pole, each dangling edge lying in exactly one of the three.  It then formalizes
the gluing argument: `KMThreePole` implies `KMThreeSpokes`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

section Pole

variable (K : LoopMultigraph V E)

/-- The edges meeting a vertex set `X`: the edges of the pole on `X`. -/
def meets (X : Finset V) : Finset E := Finset.univ.filter fun e ↦ ∃ k, K.endAt e k ∈ X

/-- The dangling edges of `X`: the edges with exactly one end in `X`. -/
def dangling (X : Finset V) : Finset E :=
  Finset.univ.filter fun e ↦ ¬ (K.endAt e 0 ∈ X ↔ K.endAt e 1 ∈ X)

/-- The number of ends of `e` lying in `X`. -/
def endsIn (X : Finset V) (e : E) : ℕ :=
  (Finset.univ.filter fun k : Fin 2 ↦ K.endAt e k ∈ X).card

/-- A perfect matching of the pole on `X`: edges meeting `X` covering every vertex of `X` exactly
once.  A dangling edge covers only its end in `X`. -/
def IsPoleMatching (X : Finset V) (L : Finset E) : Prop :=
  L ⊆ K.meets X ∧ ∀ v ∈ X, K.degreeIn L v = 1

/-- A proper four-cover of the pole on `X` whose chord-and-dangling class is `S`: three pole
matchings covering with `S` every edge of the pole, each dangling edge lying in exactly one of
the three (so it is covered exactly twice, once by `S`). -/
structure ProperFourCover (S : Finset E) (X : Finset V) where
  L : Fin 3 → Finset E
  matching : ∀ i, K.IsPoleMatching X (L i)
  cover : ∀ e ∈ K.meets X, e ∈ S ∨ ∃ i, e ∈ L i
  dangling_once : ∀ e ∈ K.dangling X, ∃ i, e ∈ L i ∧ ∀ j, e ∈ L j → j = i

variable {K}

omit [DecidableEq E] in
theorem mem_meets {X : Finset V} {e : E} : e ∈ K.meets X ↔ ∃ k, K.endAt e k ∈ X := by
  simp [meets]

omit [DecidableEq E] in
theorem mem_dangling {X : Finset V} {e : E} :
    e ∈ K.dangling X ↔ ¬ (K.endAt e 0 ∈ X ↔ K.endAt e 1 ∈ X) := by
  simp [dangling]

omit [DecidableEq E] in
theorem mem_edgeSupport_iff_pos {F : Finset E} {v : V} :
    v ∈ K.edgeSupport F ↔ 0 < K.degreeIn F v := by
  rw [K.mem_edgeSupport_iff]
  unfold degreeIn
  rw [Finset.card_pos]
  constructor
  · rintro ⟨e, he, k, hk⟩
    exact ⟨(e, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, hk⟩⟩
  · rintro ⟨⟨e, k⟩, h⟩
    obtain ⟨hm, hk⟩ := Finset.mem_filter.mp h
    exact ⟨e, (Finset.mem_product.mp hm).1, k, hk⟩

theorem degreeIn_le_degree (F : Finset E) (v : V) : K.degreeIn F v ≤ K.degree v := by
  have := degreeIn_add_compl (H := K) F v
  omega

/-- Adding edges none of whose ends at `v` are new does not change the degree at `v`. -/
theorem degreeIn_union_eq_left_of {F G : Finset E} {v : V}
    (h : ∀ e ∈ G, (∃ k, K.endAt e k = v) → e ∈ F) :
    K.degreeIn (F ∪ G) v = K.degreeIn F v := by
  unfold degreeIn
  congr 1
  ext ⟨e, k⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_union]
  constructor
  · rintro ⟨hF | hG, hk⟩
    · exact ⟨hF, hk⟩
    · exact ⟨h e hG ⟨k, hk⟩, hk⟩
  · rintro ⟨hF, hk⟩
    exact ⟨Or.inl hF, hk⟩

theorem endsIn_mod_two (X : Finset V) (e : E) :
    K.endsIn X e % 2 = if e ∈ K.dangling X then 1 else 0 := by
  unfold endsIn
  rw [Finset.card_filter, Fin.sum_univ_two]
  have hc := (mem_dangling (K := K) (X := X) (e := e))
  rcases Classical.em (K.endAt e 0 ∈ X) with h0 | h0 <;>
    rcases Classical.em (K.endAt e 1 ∈ X) with h1 | h1
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩), if_pos h0, if_pos h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h1 (h.mp h0)), if_pos h0, if_neg h1]; rfl
  · rw [if_pos (hc.mpr fun h ↦ h0 (h.mpr h1)), if_neg h0, if_pos h1]; rfl
  · rw [if_neg (fun h ↦ (hc.mp h) ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩), if_neg h0,
      if_neg h1]; rfl

omit [DecidableEq E] in
/-- Handshake: the degrees of an edge set at the vertices of `X` add up to the number of ends of
its edges lying in `X`. -/
theorem sum_degreeIn_eq (X : Finset V) (L : Finset E) :
    ∑ v ∈ X, K.degreeIn L v = ∑ e ∈ L, K.endsIn X e := by
  have h1 : ((L ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ K.endAt h.1 h.2 ∈ X).card =
      ∑ v ∈ X, K.degreeIn L v := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun h : E × Fin 2 ↦ K.endAt h.1 h.2) (t := X)]
    · apply Finset.sum_congr rfl
      intro v hv
      unfold degreeIn
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨⟨hL, -⟩, h2⟩
        exact ⟨hL, h2⟩
      · rintro ⟨hL, h2⟩
        exact ⟨⟨hL, h2 ▸ hv⟩, h2⟩
    · intro h hh
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hh)).2
  rw [← h1, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro e _
  unfold endsIn
  rw [Finset.card_filter]

theorem sum_degreeIn_mod_two (X : Finset V) (L : Finset E) :
    (∑ v ∈ X, K.degreeIn L v) % 2 = (L ∩ K.dangling X).card % 2 := by
  rw [sum_degreeIn_eq, Finset.sum_nat_mod]
  have : ∑ e ∈ L, K.endsIn X e % 2 = ∑ e ∈ L, if e ∈ K.dangling X then 1 else 0 :=
    Finset.sum_congr rfl fun e _ ↦ endsIn_mod_two X e
  rw [this, Finset.sum_boole, Finset.filter_mem_eq_inter]
  rfl

/-- The parity of a vertex set covered exactly once by an edge set is the parity of the number
of dangling edges used. -/
theorem card_mod_two_of_degreeIn_one {X : Finset V} {L : Finset E}
    (h : ∀ v ∈ X, K.degreeIn L v = 1) : X.card % 2 = (L ∩ K.dangling X).card % 2 := by
  rw [← sum_degreeIn_mod_two, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_one]

omit [DecidableEq E] in
/-- An edge meeting `Y` with an end in `X`, where `X` and `Y` are disjoint, is dangling for `X`. -/
theorem mem_dangling_of_mem_meets {X Y : Finset V} (hXY : ∀ v, v ∈ X → v ∉ Y) {e : E}
    (he : e ∈ K.meets Y) {k : Fin 2} (hk : K.endAt e k ∈ X) : e ∈ K.dangling X := by
  obtain ⟨k', hk'⟩ := mem_meets.mp he
  rw [mem_dangling]
  have hne : k ≠ k' := fun h ↦ hXY _ hk (h ▸ hk')
  have hk'X : K.endAt e k' ∉ X := fun h ↦ hXY _ h hk'
  rcases fin2_cases k with rfl | rfl <;> rcases fin2_cases k' with rfl | rfl
  · exact absurd rfl hne
  · exact fun h ↦ hk'X (h.mp hk)
  · exact fun h ↦ hk'X (h.mpr hk)
  · exact absurd rfl hne

namespace ProperFourCover

variable {S : Finset E} {X : Finset V} (P : K.ProperFourCover S X)

/-- The three matchings of a proper four-cover use each dangling edge exactly once in total. -/
theorem sum_card_inter : ∑ i, (P.L i ∩ K.dangling X).card = (K.dangling X).card := by
  have h1 : ∀ i, (P.L i ∩ K.dangling X).card = ∑ d ∈ K.dangling X, if d ∈ P.L i then 1 else 0 := by
    intro i
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun i _ ↦ h1 i), Finset.sum_comm, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨i, hi, huniq⟩ := P.dangling_once d hd
  rw [Finset.sum_eq_single i]
  · rw [if_pos hi]
  · intro j _ hji
    exact if_neg (fun h ↦ hji (huniq j h))
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- With three dangling edges and an odd pole, each of the three matchings uses exactly one
dangling edge. -/
theorem card_inter_dangling (hD : (K.dangling X).card = 3) (hX : X.card % 2 = 1) (i : Fin 3) :
    (P.L i ∩ K.dangling X).card = 1 := by
  have hodd : ∀ j, (P.L j ∩ K.dangling X).card % 2 = 1 := fun j ↦ by
    rw [← card_mod_two_of_degreeIn_one (P.matching j).2, hX]
  have hsum := P.sum_card_inter
  rw [hD, Fin.sum_univ_three] at hsum
  have h0 := hodd 0
  have h1 := hodd 1
  have h2 := hodd 2
  rcases fin3_cases i with rfl | rfl | rfl <;> omega

end ProperFourCover

end Pole

/-- **Karabáš–Máčajová Theorem 3.1** in ambient form: in a loopless cubic
endpoint multigraph `K` with a perfect matching `S`, every circuit `R` avoiding `S` whose vertex
set has exactly three dangling edges spans a Hamiltonian cubic `3`-pole, and that pole has a
proper four-cover with matching class `S`.  Any cubic `3`-pole with a spanning circuit arises this
way. The proof of this proposition is `kmThreePole` in `ThreePoleTransfer.lean`. -/
def KMThreePole : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (K : LoopMultigraph V' E'), (∀ v, K.degree v = 3) → (∀ e, K.endAt e 0 ≠ K.endAt e 1) →
    ∀ S : Finset E', K.IsPerfectMatching S → ∀ R : K.OrdinaryCircuit, Disjoint R.edges S →
      (K.dangling (K.edgeSupport R.edges)).card = 3 →
      Nonempty (K.ProperFourCover S (K.edgeSupport R.edges))

section Glue

variable {K : LoopMultigraph V E} (hCubic : ∀ v : V, K.degree v = 3) {S : Finset E}
  (hS : K.IsPerfectMatching S) (A B : K.OrdinaryCircuit)
  (hdisj : Disjoint A.edges B.edges) (hunion : A.edges ∪ B.edges = Finset.univ \ S)

include hunion in
theorem disjoint_left_S : Disjoint A.edges S :=
  Finset.disjoint_left.mpr fun _ hA heS ↦
    (Finset.mem_sdiff.mp (hunion ▸ Finset.mem_union_left _ hA)).2 heS

include hunion in
theorem disjoint_right_S : Disjoint B.edges S :=
  Finset.disjoint_left.mpr fun _ hB heS ↦
    (Finset.mem_sdiff.mp (hunion ▸ Finset.mem_union_right _ hB)).2 heS

include hCubic hdisj in
/-- The two circuits of `K − S` are vertex-disjoint. -/
theorem supports_disjoint (v : V) :
    v ∈ K.edgeSupport A.edges → v ∉ K.edgeSupport B.edges := by
  intro hA hB
  have h := degreeIn_le_degree (K := K) (A.edges ∪ B.edges) v
  rw [degreeIn_union_of_disjoint hdisj, A.twoRegular v hA, B.twoRegular v hB, hCubic v] at h
  omega

include hCubic hS hdisj hunion in
/-- Every vertex lies on one of the two circuits of `K − S`. -/
theorem supports_cover (v : V) :
    v ∈ K.edgeSupport A.edges ∨ v ∈ K.edgeSupport B.edges := by
  have h := degreeIn_add_compl (H := K) S v
  rw [hS v, hCubic v, ← hunion, degreeIn_union_of_disjoint hdisj] at h
  by_contra hcon
  push Not at hcon
  rw [mem_edgeSupport_iff_pos, mem_edgeSupport_iff_pos] at hcon
  omega

include hCubic hdisj hunion in
/-- The dangling edges of the first circuit are the edges of `S` joining the two circuits. -/
theorem dangling_eq_filter :
    K.dangling (K.edgeSupport A.edges) = S.filter fun e ↦
      ¬ (K.endAt e 0 ∈ K.edgeSupport A.edges ↔ K.endAt e 1 ∈ K.edgeSupport A.edges) := by
  ext e
  rw [mem_dangling, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra heS
    have heAB : e ∈ A.edges ∪ B.edges := by
      rw [hunion]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heS⟩
    rcases Finset.mem_union.mp heAB with hA | hB
    · exact h ⟨fun _ ↦ K.mem_edgeSupport_iff.mpr ⟨e, hA, 1, rfl⟩,
        fun _ ↦ K.mem_edgeSupport_iff.mpr ⟨e, hA, 0, rfl⟩⟩
    · have h0 : K.endAt e 0 ∉ K.edgeSupport A.edges := fun h' ↦
        supports_disjoint hCubic A B hdisj _ h' (K.mem_edgeSupport_iff.mpr ⟨e, hB, 0, rfl⟩)
      have h1 : K.endAt e 1 ∉ K.edgeSupport A.edges := fun h' ↦
        supports_disjoint hCubic A B hdisj _ h' (K.mem_edgeSupport_iff.mpr ⟨e, hB, 1, rfl⟩)
      exact h ⟨fun h' ↦ absurd h' h0, fun h' ↦ absurd h' h1⟩
  · exact fun h ↦ h.2

include hCubic hS hdisj hunion in
/-- Both circuits have the same dangling edges. -/
theorem dangling_right_eq :
    K.dangling (K.edgeSupport B.edges) = K.dangling (K.edgeSupport A.edges) := by
  ext e
  rw [mem_dangling, mem_dangling]
  have hB : ∀ w, w ∈ K.edgeSupport B.edges ↔ w ∉ K.edgeSupport A.edges := fun w ↦
    ⟨fun h h' ↦ supports_disjoint hCubic A B hdisj w h' h,
      fun h ↦ (supports_cover hCubic hS A B hdisj hunion w).resolve_left h⟩
  rw [hB, hB]
  exact not_congr not_iff_not

include hCubic hS hdisj hunion in
/-- **The gluing step.**  Proper four-covers of the two poles cut along the three joining edges
glue to a cover of `K` by `S` and three perfect matchings. -/
theorem exists_fourCover_of_properFourCovers
    (PA : K.ProperFourCover S (K.edgeSupport A.edges))
    (PB : K.ProperFourCover S (K.edgeSupport B.edges))
    (hD : (K.dangling (K.edgeSupport A.edges)).card = 3) :
    ∃ L₁ L₂ L₃ : Finset E, K.IsPerfectMatching L₁ ∧ K.IsPerfectMatching L₂ ∧
      K.IsPerfectMatching L₃ ∧ S ∪ L₁ ∪ L₂ ∪ L₃ = Finset.univ := by
  have hDB := dangling_right_eq hCubic hS A B hdisj hunion
  have hDS : K.dangling (K.edgeSupport A.edges) ⊆ S := by
    rw [dangling_eq_filter hCubic A B hdisj hunion]
    exact Finset.filter_subset _ _
  have hXA : (K.edgeSupport A.edges).card % 2 = 1 := by
    rw [card_mod_two_of_degreeIn_one (fun v _ ↦ hS v), Finset.inter_eq_right.mpr hDS, hD]
  have hXB : (K.edgeSupport B.edges).card % 2 = 1 := by
    rw [card_mod_two_of_degreeIn_one (fun v _ ↦ hS v), hDB, Finset.inter_eq_right.mpr hDS, hD]
  have hA1 : ∀ i, (PA.L i ∩ K.dangling (K.edgeSupport A.edges)).card = 1 :=
    PA.card_inter_dangling hD hXA
  have hB1 : ∀ j, (PB.L j ∩ K.dangling (K.edgeSupport A.edges)).card = 1 := by
    intro j
    have := PB.card_inter_dangling (by rw [hDB]; exact hD) hXB j
    rwa [hDB] at this
  choose dA hdA using fun i ↦ Finset.card_eq_one.mp (hA1 i)
  have hdAL : ∀ i, dA i ∈ PA.L i := fun i ↦
    (Finset.mem_inter.mp (by rw [hdA i]; exact Finset.mem_singleton_self _)).1
  have hdAD : ∀ i, dA i ∈ K.dangling (K.edgeSupport A.edges) := fun i ↦
    (Finset.mem_inter.mp (by rw [hdA i]; exact Finset.mem_singleton_self _)).2
  have hσ' : ∀ i, ∃ j, dA i ∈ PB.L j ∧ ∀ j', dA i ∈ PB.L j' → j' = j := fun i ↦
    PB.dangling_once (dA i) (by rw [hDB]; exact hdAD i)
  choose σ hσ using hσ'
  have hσinj : Function.Injective σ := by
    intro i i' h
    have h1 : dA i ∈ PB.L (σ i) ∩ K.dangling (K.edgeSupport A.edges) :=
      Finset.mem_inter.mpr ⟨(hσ i).1, hdAD i⟩
    have h2 : dA i' ∈ PB.L (σ i) ∩ K.dangling (K.edgeSupport A.edges) :=
      Finset.mem_inter.mpr ⟨by rw [h]; exact (hσ i').1, hdAD i'⟩
    have heq : dA i = dA i' := Finset.card_le_one.mp (hB1 (σ i)).le _ h1 _ h2
    have hmem : dA i' ∈ PA.L i := heq ▸ hdAL i
    obtain ⟨i₀, -, huniq⟩ := PA.dangling_once (dA i') (hdAD i')
    exact (huniq i hmem).trans (huniq i' (hdAL i')).symm
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  have hperf : ∀ i, K.IsPerfectMatching (PA.L i ∪ PB.L (σ i)) := by
    intro i v
    rcases supports_cover hCubic hS A B hdisj hunion v with hvA | hvB
    · rw [degreeIn_union_eq_left_of]
      · exact (PA.matching i).2 v hvA
      · rintro e he ⟨k, hk⟩
        have heD : e ∈ K.dangling (K.edgeSupport A.edges) :=
          mem_dangling_of_mem_meets (supports_disjoint hCubic A B hdisj)
            ((PB.matching (σ i)).1 he) (hk ▸ hvA)
        have heq : e = dA i := Finset.card_le_one.mp (hB1 (σ i)).le _
          (Finset.mem_inter.mpr ⟨he, heD⟩) _ (Finset.mem_inter.mpr ⟨(hσ i).1, hdAD i⟩)
        rw [heq]
        exact hdAL i
    · rw [Finset.union_comm, degreeIn_union_eq_left_of]
      · exact (PB.matching (σ i)).2 v hvB
      · rintro e he ⟨k, hk⟩
        have heD : e ∈ K.dangling (K.edgeSupport A.edges) := by
          rw [← hDB]
          exact mem_dangling_of_mem_meets
            (fun w hw hw' ↦ supports_disjoint hCubic A B hdisj w hw' hw)
            ((PA.matching i).1 he) (hk ▸ hvB)
        have heq : e = dA i := Finset.card_le_one.mp (hA1 i).le _
          (Finset.mem_inter.mpr ⟨he, heD⟩) _ (Finset.mem_inter.mpr ⟨hdAL i, hdAD i⟩)
        rw [heq]
        exact (hσ i).1
  refine ⟨PA.L 0 ∪ PB.L (σ 0), PA.L 1 ∪ PB.L (σ 1), PA.L 2 ∪ PB.L (σ 2), hperf 0, hperf 1,
    hperf 2, ?_⟩
  apply Finset.eq_univ_of_forall
  intro e
  simp only [Finset.mem_union]
  have key : ∀ i, e ∈ PA.L i ∪ PB.L (σ i) →
      ((e ∈ S ∨ e ∈ PA.L 0 ∪ PB.L (σ 0)) ∨ e ∈ PA.L 1 ∪ PB.L (σ 1)) ∨
        e ∈ PA.L 2 ∪ PB.L (σ 2) := by
    intro i hi
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inr hi))
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  simp only [Finset.mem_union] at key
  by_cases heS : e ∈ S
  · exact Or.inl (Or.inl (Or.inl heS))
  have heAB : e ∈ A.edges ∪ B.edges := by
    rw [hunion]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heS⟩
  rcases Finset.mem_union.mp heAB with hA | hB
  · have hm : e ∈ K.meets (K.edgeSupport A.edges) :=
      mem_meets.mpr ⟨0, K.mem_edgeSupport_iff.mpr ⟨e, hA, 0, rfl⟩⟩
    rcases PA.cover e hm with h | ⟨i, hi⟩
    · exact absurd h heS
    · exact key i (Or.inl hi)
  · have hm : e ∈ K.meets (K.edgeSupport B.edges) :=
      mem_meets.mpr ⟨0, K.mem_edgeSupport_iff.mpr ⟨e, hB, 0, rfl⟩⟩
    rcases PB.cover e hm with h | ⟨j, hj⟩
    · exact absurd h heS
    · obtain ⟨i, rfl⟩ := hσsurj j
      exact key i (Or.inr hj)

end Glue

/-- **The Karabáš–Máčajová corollary from their Theorem 3.1**: the three-spoke corollary
`KMThreeSpokes` follows from the ambient form `KMThreePole` of Theorem 3.1 by cutting the
three joining edges and gluing the proper four-covers of the two poles. -/
theorem KMThreePole.kmThreeSpokes (h : KMThreePole.{u, v}) : KMThreeSpokes.{u, v} := by
  intro V' E' _ _ _ _ K hCubic hloop S hS A B hdisj hunion _ _ hcross
  have hD : (K.dangling (K.edgeSupport A.edges)).card = 3 := by
    rw [dangling_eq_filter hCubic A B hdisj hunion]
    exact hcross
  obtain ⟨PA⟩ := h K hCubic hloop S hS A (disjoint_left_S A B hunion) hD
  obtain ⟨PB⟩ := h K hCubic hloop S hS B (disjoint_right_S A B hunion)
    (by rw [dangling_right_eq hCubic hS A B hdisj hunion]; exact hD)
  exact exists_fourCover_of_properFourCovers hCubic hS A B hdisj hunion PA PB hD

/-- The four-cover theorem with Karabáš–Máčajová Theorem 3.1 (in ambient form) in place of its
corollary. -/
theorem TwoCircuitFactor.exists_fourCover_of_kmThreePole {H : LoopMultigraph V E}
    (F : H.TwoCircuitFactor) (hCubic : ∀ v : V, H.degree v = 3)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hCL : ∃ N, H.IsPerfectMatching N ∧ (N ∩ F.cross).card = 3) (hKM : KMThreePole.{u, v}) :
    ∃ M₁ M₂ M₃ : Finset E, H.IsPerfectMatching M₁ ∧ H.IsPerfectMatching M₂ ∧
      H.IsPerfectMatching M₃ ∧ F.compl ∪ M₁ ∪ M₂ ∪ M₃ = Finset.univ :=
  F.exists_fourCover hCubic hloopless hCL hKM.kmThreeSpokes

end LoopMultigraph
end GraphPuzzles
