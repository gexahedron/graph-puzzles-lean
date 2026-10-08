import GraphPuzzles.Matching.TutteBridge

/-!
# The hub lemma

The note's Lemma (hub), a consequence of Tutte's theorem: a connected bridgeless loopless graph
with a distinguished vertex `b` of odd degree, all other vertices cubic, and `H − b`
factor-critical, is matching covered.  Edges at `b` are adjoined to a perfect matching of
`H − b − u`.  For an edge `uv` avoiding `b`, if `H − u − v` had no perfect matching, Tutte's theorem
would give a set `X` with more than `|X|` odd components in `H − u − v − X`; by parity at least
`|X| + 2`.  If `b ∈ X`, a perfect matching of `H − b − u` sends every odd component to a distinct
vertex of `(X ∖ {b}) ∪ {v}`, so there are at most `|X|` of them.  If `b ∉ X`, every odd component
has an odd, hence at least three-element, edge boundary inside the boundary of `R = X ∪ {u, v}`,
and these boundaries are disjoint, while `|δ(R)| ≤ 3|X| + 4`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem mod_two_eq_of_odd_iff {a b : ℕ} (h : Odd a ↔ Odd b) : a % 2 = b % 2 := by
  rcases Nat.even_or_odd a with ha | ha
  · have hb : ¬ Odd b := fun hb ↦ (Nat.not_even_iff_odd.mpr (h.mpr hb)) ha
    rw [Nat.not_odd_iff_even] at hb
    rw [Nat.even_iff] at ha hb
    omega
  · have hb := h.mp ha
    rw [Nat.odd_iff] at ha hb
    omega

section Counting

variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem degreeIn_singleton (e : E) (w : V) :
    H.degreeIn {e} w = (Finset.univ.filter fun k : Fin 2 ↦ H.endAt e k = w).card := by
  unfold degreeIn
  apply Finset.card_bij (fun h _ ↦ h.2)
  · intro h hh
    obtain ⟨hm, hk⟩ := Finset.mem_filter.mp hh
    have he : h.1 = e := Finset.mem_singleton.mp (Finset.mem_product.mp hm).1
    rw [he] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  · intro h hh h' hh' heq
    have he : h.1 = e := Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_filter.mp hh).1).1
    have he' : h'.1 = e :=
      Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_filter.mp hh').1).1
    exact Prod.ext (he.trans he'.symm) heq
  · intro k hk
    exact ⟨(e, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
      Finset.mem_univ _⟩, (Finset.mem_filter.mp hk).2⟩, rfl⟩

omit [DecidableEq E] in
theorem degreeIn_singleton_of_joins {e : E} {a b : V} (h : H.Joins e a b) (hab : a ≠ b) :
    H.degreeIn {e} a = 1 := by
  rw [degreeIn_singleton, Finset.card_eq_one]
  obtain ⟨k, hk⟩ := h.exists_end
  refine ⟨k, ?_⟩
  ext k'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hk' ↦ h.end_unique hab hk' hk, fun hk' ↦ hk' ▸ hk⟩

omit [DecidableEq E] in
theorem degreeIn_singleton_eq_zero {e : E} {w : V} (h : ∀ k, H.endAt e k ≠ w) :
    H.degreeIn {e} w = 0 :=
  degreeIn_eq_zero_of fun f hf k ↦ by
    rw [Finset.mem_singleton.mp hf]
    exact h k

/-- Adjoining an edge `uv` to a perfect matching of `H − u − v` gives a perfect matching of
`H`. -/
theorem IsPerfectMatchingOn.insert_perfect {u v : V} {P : Finset E}
    (hP : H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P) {e : E} (he : H.Joins e u v)
    (huv : u ≠ v) : H.IsPerfectMatching (insert e P) := by
  have heP : e ∉ P := fun h ↦ by
    have h0 := hP.1 e h 0
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at h0
    rcases he.endAt_mem 0 with h' | h'
    · exact h0.2 h'
    · exact h0.1 h'
  intro w
  rw [Finset.insert_eq, degreeIn_union_of_disjoint (Finset.disjoint_singleton_left.mpr heP)]
  by_cases hw : w = u ∨ w = v
  · have h1 : H.degreeIn {e} w = 1 := by
      rcases hw with rfl | rfl
      · exact degreeIn_singleton_of_joins he huv
      · exact degreeIn_singleton_of_joins (H.joins_comm.mp he) huv.symm
    have h0 : H.degreeIn P w = 0 := degreeIn_eq_zero_of fun f hf k hk ↦ by
      have := hP.1 f hf k
      rw [hk] at this
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at this
      rcases hw with rfl | rfl
      · exact this.2 rfl
      · exact this.1 rfl
    omega
  · push Not at hw
    have h0 : H.degreeIn {e} w = 0 := degreeIn_singleton_eq_zero fun k hk ↦ by
      rcases he.endAt_mem k with h | h
      · exact hw.1 (hk.symm.trans h)
      · exact hw.2 (hk.symm.trans h)
    have h1 := hP.2 w (by simp [Finset.mem_erase, hw.1, hw.2])
    omega

omit [DecidableEq E] in
theorem sum_degree_eq (X : Finset V) : ∑ w ∈ X, H.degree w = ∑ e, H.endsIn X e := by
  rw [← sum_degreeIn_eq (K := H) X Finset.univ]
  exact Finset.sum_congr rfl fun w _ ↦ (degreeIn_univ' w).symm

omit [DecidableEq E] in
theorem endsIn_univ (e : E) : H.endsIn Finset.univ e = 2 := by
  unfold endsIn
  simp

omit [DecidableEq E] in
/-- A graph all of whose degrees are odd has an even number of vertices. -/
theorem card_even_of_odd_degrees (hodd : ∀ w, Odd (H.degree w)) : Even (Fintype.card V) := by
  have h := sum_degree_eq (H := H) Finset.univ
  rw [Finset.sum_congr rfl (fun e _ ↦ endsIn_univ e), Finset.sum_const, smul_eq_mul] at h
  have hodd' := Finset.odd_sum_iff_odd_card_odd (s := (Finset.univ : Finset V)) (fun w ↦ H.degree w)
  rw [Finset.filter_true_of_mem (fun w _ ↦ hodd w), Finset.card_univ, h] at hodd'
  by_contra hcon
  rw [Nat.not_even_iff_odd] at hcon
  exact (Nat.not_odd_iff_even.mpr (even_two.mul_left _)) (hodd'.mpr hcon)

/-- An odd vertex set in a graph with all degrees odd has an odd number of dangling edges. -/
theorem odd_card_dangling (hodd : ∀ w, Odd (H.degree w)) {Q : Finset V} (hQ : Odd Q.card) :
    Odd (H.dangling Q).card := by
  have h := sum_degreeIn_mod_two (K := H) Q (Finset.univ : Finset E)
  rw [Finset.univ_inter, Finset.sum_congr rfl (fun w _ ↦ degreeIn_univ' w)] at h
  have hodd' := Finset.odd_sum_iff_odd_card_odd (s := Q) (fun w ↦ H.degree w)
  rw [Finset.filter_true_of_mem (fun w _ ↦ hodd w)] at hodd'
  have : Odd (∑ w ∈ Q, H.degree w) := hodd'.mpr hQ
  rw [Nat.odd_iff] at this ⊢
  omega

omit [DecidableEq E] in
/-- In a bridgeless graph no vertex set has exactly one dangling edge. -/
theorem card_dangling_ne_one (hb : H.IsBridgeless) (Q : Finset V) : (H.dangling Q).card ≠ 1 := by
  intro h1
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
  have hcol := hb e (fun w ↦ decide (w ∈ Q)) (fun f hf ↦ by
    have hfd : f ∉ H.dangling Q := fun h ↦ hf (Finset.mem_singleton.mp (he ▸ h))
    rw [mem_dangling, not_not] at hfd
    rw [decide_eq_decide]
    exact hfd)
  have hed : e ∈ H.dangling Q := he ▸ Finset.mem_singleton_self e
  rw [mem_dangling] at hed
  rw [decide_eq_decide] at hcol
  exact hed hcol

/-- The boundary of a set of cubic vertices spanning an edge has at most `3|R| − 2` edges. -/
theorem card_dangling_add_two_le {R : Finset V} (hdeg : ∀ w ∈ R, H.degree w = 3) {e₀ : E}
    (h0 : H.endAt e₀ 0 ∈ R) (h1 : H.endAt e₀ 1 ∈ R) : (H.dangling R).card + 2 ≤ 3 * R.card := by
  have hsum := sum_degree_eq (H := H) R
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, smul_eq_mul, mul_comm] at hsum
  have hle : ∑ e, ((if e ∈ H.dangling R then 1 else 0) + if e = e₀ then 2 else 0) ≤
      ∑ e, H.endsIn R e := by
    apply Finset.sum_le_sum
    intro e _
    by_cases he : e = e₀
    · subst he
      rw [if_pos rfl, if_neg (fun h ↦ (mem_dangling.mp h) ⟨fun _ ↦ h1, fun _ ↦ h0⟩)]
      unfold endsIn
      rw [Finset.card_filter, Fin.sum_univ_two, if_pos h0, if_pos h1]
    · rw [if_neg he]
      have := endsIn_mod_two (K := H) R e
      split_ifs at this ⊢ <;> omega
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_ite_eq' Finset.univ e₀, if_pos (Finset.mem_univ _), Nat.cast_id] at hle
  omega

end Counting

/-- A family of vertex sets behaving like the components of `H − Z`: nonempty, pairwise disjoint
sets avoiding `Z`, closed under adjacency outside `Z`, and covering the complement of `Z`. -/
structure ComponentFamily (H : LoopMultigraph V E) (Z : Finset V) where
  parts : Finset (Finset V)
  nonempty : ∀ Q ∈ parts, Q.Nonempty
  avoid : ∀ Q ∈ parts, ∀ w ∈ Q, w ∉ Z
  closed : ∀ Q ∈ parts, ∀ e : E, ∀ k : Fin 2, H.endAt e k ∈ Q → H.endAt e (Fin.rev k) ∉ Z →
    H.endAt e (Fin.rev k) ∈ Q
  pairwise : ∀ Q ∈ parts, ∀ Q' ∈ parts, Q ≠ Q' → Disjoint Q Q'
  cover : ∀ w, w ∉ Z → ∃ Q ∈ parts, w ∈ Q

namespace ComponentFamily

variable {H : LoopMultigraph V E} {Z : Finset V} (F : H.ComponentFamily Z)

/-- The odd members of the family. -/
def odd : Finset (Finset V) := F.parts.filter fun Q ↦ Odd Q.card

omit [DecidableEq V] [DecidableEq E] in
theorem mem_odd {Q : Finset V} : Q ∈ F.odd ↔ Q ∈ F.parts ∧ Odd Q.card := by
  simp [odd]

omit [DecidableEq E] in
theorem biUnion_eq : F.parts.biUnion id = Finset.univ \ Z := by
  ext w
  simp only [Finset.mem_biUnion, id, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Q, hQ, hw⟩
    exact F.avoid Q hQ w hw
  · exact F.cover w

omit [DecidableEq E] in
theorem sum_card : ∑ Q ∈ F.parts, Q.card = (Finset.univ \ Z).card := by
  rw [← F.biUnion_eq, Finset.card_biUnion]
  · rfl
  · intro Q hQ Q' hQ' hne
    exact F.pairwise Q hQ Q' hQ' hne

omit [DecidableEq E] in
theorem odd_card_mod_two : F.odd.card % 2 = (Finset.univ \ Z).card % 2 := by
  have h := Finset.odd_sum_iff_odd_card_odd (s := F.parts) (fun Q ↦ Q.card)
  rw [F.sum_card] at h
  exact (mod_two_eq_of_odd_iff h).symm

omit [DecidableEq E] in
/-- A member of the family contains no vertex of another member. -/
theorem eq_of_mem {Q Q' : Finset V} (hQ : Q ∈ F.parts) (hQ' : Q' ∈ F.parts) {w : V} (hw : w ∈ Q)
    (hw' : w ∈ Q') : Q = Q' := by
  by_contra hne
  exact Finset.disjoint_left.mp (F.pairwise Q hQ Q' hQ' hne) hw hw'

omit [DecidableEq E] in
/-- A dangling edge of a member of the family leaves it through `Z`. -/
theorem exists_end_of_mem_dangling {Q : Finset V} (hQ : Q ∈ F.parts) {e : E}
    (he : e ∈ H.dangling Q) :
    ∃ k, H.endAt e k ∈ Q ∧ H.endAt e (Fin.rev k) ∉ Q ∧ H.endAt e (Fin.rev k) ∈ Z := by
  rw [mem_dangling] at he
  have key : ∀ k, H.endAt e k ∈ Q → H.endAt e (Fin.rev k) ∉ Q → H.endAt e (Fin.rev k) ∈ Z := by
    intro k hk hk'
    by_contra hZ
    exact hk' (F.closed Q hQ e k hk hZ)
  by_cases h0 : H.endAt e 0 ∈ Q
  · have h1 : H.endAt e 1 ∉ Q := fun h1 ↦ he ⟨fun _ ↦ h1, fun _ ↦ h0⟩
    exact ⟨0, h0, h1, key 0 h0 h1⟩
  · have h1 : H.endAt e 1 ∈ Q := by
      by_contra h1
      exact he ⟨fun h ↦ absurd h h0, fun h ↦ absurd h h1⟩
    exact ⟨1, h1, h0, key 1 h1 h0⟩

end ComponentFamily

section Hub

variable {H : LoopMultigraph V E} (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) {b : V}
  (hdeg : ∀ w, w ≠ b → H.degree w = 3) (hb : Odd (H.degree b)) {u v : V} (hu : u ≠ b) (hv : v ≠ b)
  (huv : u ≠ v) {X₀ : Finset V} (hu0 : u ∉ X₀) (hv0 : v ∉ X₀)
  (F : H.ComponentFamily (X₀ ∪ {u, v}))

omit [DecidableEq E] [DecidableEq V] in
theorem endAt_rev_ne (e : E) (k : Fin 2) (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    H.endAt e k ≠ H.endAt e (Fin.rev k) := by
  rcases fin2_cases k with rfl | rfl
  · exact hloop e
  · exact (hloop e).symm

include hu in
/-- **Case `b ∈ X`.** -/
theorem hub_b_mem (hfc : H.IsFactorCritical (Finset.univ.erase b)) (hb0 : b ∈ X₀)
    (hcount : X₀.card + 2 ≤ F.odd.card) : False := by
  obtain ⟨P, hP⟩ := hfc u (Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩)
  have hPdeg : ∀ w, w ≠ b → w ≠ u → H.degreeIn P w = 1 := fun w hwb hwu ↦
    hP.2 w (by simp [Finset.mem_erase, hwb, hwu])
  -- every odd member sends a matching edge into `Y`
  have hexit : ∀ Q ∈ F.odd, ∃ w', w' ∈ (X₀.erase b) ∪ {v} ∧
      ∃ e ∈ P, ∃ k, H.endAt e k ∈ Q ∧ H.endAt e (Fin.rev k) = w' := by
    intro Q hQ
    obtain ⟨hQp, hQodd⟩ := F.mem_odd.mp hQ
    have hdeg1 : ∀ w ∈ Q, H.degreeIn P w = 1 := fun w hw ↦ by
      have hwZ := F.avoid Q hQp w hw
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hwZ
      exact hPdeg w (fun h ↦ hwZ.1 (h ▸ hb0)) hwZ.2.1
    have hpar := card_mod_two_of_degreeIn_one hdeg1
    have hne : (P ∩ H.dangling Q).Nonempty := by
      rw [← Finset.card_pos]
      rw [Nat.odd_iff] at hQodd
      omega
    obtain ⟨e, he⟩ := hne
    obtain ⟨heP, heD⟩ := Finset.mem_inter.mp he
    obtain ⟨k, hk, hk', hkZ⟩ := F.exists_end_of_mem_dangling hQp heD
    refine ⟨H.endAt e (Fin.rev k), ?_, e, heP, k, hk, rfl⟩
    have hend := hP.1 e heP (Fin.rev k)
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hend
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hkZ
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    rcases hkZ with hX | hu' | hv'
    · exact Or.inl ⟨hend.2, hX⟩
    · exact absurd hu' hend.1
    · exact Or.inr hv'
  choose exit hexit using hexit
  let f : Finset V → V := fun Q ↦ if h : Q ∈ F.odd then exit Q h else u
  have hf : ∀ Q ∈ F.odd, f Q ∈ (X₀.erase b) ∪ {v} := fun Q hQ ↦ by
    simp only [f, dif_pos hQ]
    exact (hexit Q hQ).1
  have hinj : Set.InjOn f F.odd := by
    intro Q hQ Q' hQ' heq
    simp only [Finset.mem_coe] at hQ hQ'
    simp only [f, dif_pos hQ, dif_pos hQ'] at heq
    obtain ⟨-, e, heP, k, hk, hke⟩ := hexit Q hQ
    obtain ⟨-, e', heP', k', hk', hke'⟩ := hexit Q' hQ'
    have hw' : H.endAt e' (Fin.rev k') = H.endAt e (Fin.rev k) := hke'.trans (heq.symm.trans hke.symm)
    -- the two matching edges share the end `exit Q`, so they coincide
    have hwZ : exit Q hQ ∈ (X₀.erase b) ∪ {v} := (hexit Q hQ).1
    have hdeg1 : H.degreeIn P (H.endAt e (Fin.rev k)) = 1 := by
      have hend := hP.1 e heP (Fin.rev k)
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hend
      exact hPdeg _ hend.2 hend.1
    have hhalf : (⟨(e, Fin.rev k), rfl⟩ : H.halfEdgesAt (H.endAt e (Fin.rev k))) =
        ⟨(e', Fin.rev k'), hw'⟩ := by
      by_contra hne
      have := H.two_le_degreeIn_of_ne (M := P) (v := H.endAt e (Fin.rev k)) ⟨(e, Fin.rev k), rfl⟩
        ⟨(e', Fin.rev k'), hw'⟩ hne heP heP'
      omega
    have hee : e = e' := congrArg (fun x ↦ x.1.1) hhalf
    have hkk : Fin.rev k = Fin.rev k' := congrArg (fun x ↦ x.1.2) hhalf
    have hkk' : k = k' := Fin.rev_injective hkk
    subst hee
    subst hkk'
    exact F.eq_of_mem (F.mem_odd.mp hQ).1 (F.mem_odd.mp hQ').1 hk hk'
  have hle := Finset.card_le_card_of_injOn f hf hinj
  have hY : ((X₀.erase b) ∪ {v}).card ≤ X₀.card := by
    calc ((X₀.erase b) ∪ {v}).card ≤ (X₀.erase b).card + ({v} : Finset V).card :=
          Finset.card_union_le _ _
      _ = (X₀.card - 1) + 1 := by rw [Finset.card_erase_of_mem hb0, Finset.card_singleton]
      _ ≤ X₀.card := by
          have := Finset.card_pos.mpr ⟨b, hb0⟩
          omega
  omega

include huv hu0 hv0 in
/-- **Case `b ∉ X`**, stated for any graph with odd degrees that is cubic on `X ∪ {u, v}`. -/
theorem hub_notMem (hodd : ∀ w, Odd (H.degree w)) (hbridge : H.IsBridgeless)
    (hdegR : ∀ w ∈ X₀ ∪ {u, v}, H.degree w = 3) (hcount : X₀.card + 2 ≤ F.odd.card) {e₀ : E}
    (he₀ : H.Joins e₀ u v) : False := by
  -- the boundary of `R = X₀ ∪ {u, v}`
  have hR : (H.dangling (X₀ ∪ {u, v})).card + 2 ≤ 3 * (X₀ ∪ {u, v}).card := by
    apply card_dangling_add_two_le hdegR
    · rcases he₀.endAt_mem 0 with h | h <;> rw [h] <;> simp
    · rcases he₀.endAt_mem 1 with h | h <;> rw [h] <;> simp
  have hRcard : (X₀ ∪ {u, v}).card = X₀.card + 2 := by
    rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hu0, hv0⟩
  -- each odd member has at least three dangling edges, all in the boundary of `R`
  have hthree : ∀ Q ∈ F.odd, 3 ≤ (H.dangling Q).card := fun Q hQ ↦ by
    have h1 := odd_card_dangling hodd (F.mem_odd.mp hQ).2
    have h2 := card_dangling_ne_one hbridge Q
    rw [Nat.odd_iff] at h1
    omega
  have hsub : ∀ Q ∈ F.odd, H.dangling Q ⊆ H.dangling (X₀ ∪ {u, v}) := fun Q hQ e he ↦ by
    obtain ⟨k, hk, -, hkZ⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ).1 he
    have hkR : H.endAt e k ∉ X₀ ∪ {u, v} := F.avoid Q (F.mem_odd.mp hQ).1 _ hk
    rw [mem_dangling]
    rcases fin2_cases k with rfl | rfl
    · exact fun h ↦ hkR (h.mpr hkZ)
    · exact fun h ↦ hkR (h.mp hkZ)
  have hdisj : ∀ Q ∈ F.odd, ∀ Q' ∈ F.odd, Q ≠ Q' → Disjoint (H.dangling Q) (H.dangling Q') := by
    intro Q hQ Q' hQ' hne
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨k, hk, -, hkZ⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ).1 he
    obtain ⟨k', hk', -, hkZ'⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ').1 he'
    have hkR : H.endAt e k ∉ X₀ ∪ {u, v} := F.avoid Q (F.mem_odd.mp hQ).1 _ hk
    have hkR' : H.endAt e k' ∉ X₀ ∪ {u, v} := F.avoid Q' (F.mem_odd.mp hQ').1 _ hk'
    have hkk : k = k' := by
      by_contra hkk
      have : k' = Fin.rev k := by
        rcases fin2_cases k with rfl | rfl <;> rcases fin2_cases k' with rfl | rfl <;>
          first | rfl | exact absurd rfl hkk
      rw [this] at hkR'
      exact hkR' hkZ
    subst hkk
    exact hne (F.eq_of_mem (F.mem_odd.mp hQ).1 (F.mem_odd.mp hQ').1 hk hk')
  have hbig : 3 * F.odd.card ≤ (H.dangling (X₀ ∪ {u, v})).card := by
    calc 3 * F.odd.card = F.odd.card • 3 := by rw [smul_eq_mul, mul_comm]
      _ ≤ ∑ Q ∈ F.odd, (H.dangling Q).card := Finset.card_nsmul_le_sum _ _ _ hthree
      _ = (F.odd.biUnion fun Q ↦ H.dangling Q).card := by
          rw [Finset.card_biUnion]
          intro Q hQ Q' hQ' hne
          exact hdisj Q hQ Q' hQ' hne
      _ ≤ (H.dangling (X₀ ∪ {u, v})).card := by
          apply Finset.card_le_card
          exact Finset.biUnion_subset.mpr hsub
  omega

end Hub

section Normalize

variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- **Normalizing a Tutte set.**  A Tutte violator `X` of the cut graph of `uv` yields a set
`X₀ ⊆ V ∖ {u, v}` and a component family of `H − X₀ − u − v` with more than `|X₀|` odd members. -/
theorem exists_componentFamily_of_violator (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) {u v : V}
    (huv : u ≠ v) (X : Finset V)
    (hviol : X.card <
      ((⊤ : (H.cutGraph u v huv).Subgraph).deleteVerts (X : Set V)).coe.oddComponents.ncard) :
    ∃ X₀ : Finset V, u ∉ X₀ ∧ v ∉ X₀ ∧
      ∃ F : H.ComponentFamily (X₀ ∪ {u, v}), X₀.card < F.odd.card := by
  classical
  obtain ⟨Ps, hcardodd, hne, havoid, hclosed, hpair, hcover, hmin⟩ :=
    SimpleGraph.exists_components_finsets (H.cutGraph u v huv) X
  -- a member containing `u` or `v` is `{u}` or `{v}` (or the even set `{u, v}`)
  have hu_mem : ∀ Q ∈ Ps, u ∈ Q → (v ∈ X ∧ Q = {u}) ∨ (v ∉ X ∧ Q = {u, v}) := by
    intro Q hQ hu
    by_cases hvX : v ∈ X
    · left
      refine ⟨hvX, ?_⟩
      have hsub : Q ⊆ {u} := hmin Q hQ u hu {u} (fun x hx y hy hxy ↦ by
        rw [Finset.mem_singleton] at hx
        rw [hx] at hxy
        rcases hxy with ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd rfl h
        · exact absurd (h ▸ hvX) hy
        · exact absurd h huv) (Finset.mem_singleton_self u)
      exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hu)
    · right
      refine ⟨hvX, ?_⟩
      have hvQ : v ∈ Q := hclosed Q hQ u hu v hvX (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hsub : Q ⊆ {u, v} := hmin Q hQ u hu {u, v} (fun x hx y _ hxy ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hxy with ⟨-, hxu, hxv, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · rcases hx with rfl | rfl
          · exact absurd rfl hxu
          · exact absurd rfl hxv
        · exact Or.inr h
        · exact Or.inl h) (Finset.mem_insert_self u _)
      refine Finset.Subset.antisymm hsub ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hvQ
  have hv_mem : ∀ Q ∈ Ps, v ∈ Q → (u ∈ X ∧ Q = {v}) ∨ (u ∉ X ∧ Q = {u, v}) := by
    intro Q hQ hv
    by_cases huX : u ∈ X
    · left
      refine ⟨huX, ?_⟩
      have hsub : Q ⊆ {v} := hmin Q hQ v hv {v} (fun x hx y hy hxy ↦ by
        rw [Finset.mem_singleton] at hx
        rw [hx] at hxy
        rcases hxy with ⟨-, -, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd rfl h
        · exact absurd h huv.symm
        · exact absurd (h ▸ huX) hy) (Finset.mem_singleton_self v)
      exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hv)
    · right
      refine ⟨huX, ?_⟩
      have huQ : u ∈ Q := hclosed Q hQ v hv u huX (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have hsub : Q ⊆ {u, v} := hmin Q hQ v hv {u, v} (fun x hx y _ hxy ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hxy with ⟨-, hxu, hxv, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · rcases hx with rfl | rfl
          · exact absurd rfl hxu
          · exact absurd rfl hxv
        · exact Or.inr h
        · exact Or.inl h) (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
      refine Finset.Subset.antisymm hsub ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact huQ
      · exact hv
  have hnot_both : ∀ Q ∈ Ps, Odd Q.card → u ∈ Q → v ∈ X ∧ Q = {u} := by
    intro Q hQ hodd hu
    rcases hu_mem Q hQ hu with h | ⟨-, rfl⟩
    · exact h
    · rw [Finset.card_pair huv] at hodd
      exact absurd hodd (by decide)
  have hnot_both' : ∀ Q ∈ Ps, Odd Q.card → v ∈ Q → u ∈ X ∧ Q = {v} := by
    intro Q hQ hodd hv
    rcases hv_mem Q hQ hv with h | ⟨-, rfl⟩
    · exact h
    · rw [Finset.card_pair huv] at hodd
      exact absurd hodd (by decide)
  set X₀ := (X.erase u).erase v with hX₀
  have hX₀X : ∀ w, w ∈ X₀ → w ∈ X := fun w hw ↦
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
  have hmemX₀ : ∀ w, w ∉ X₀ ∪ {u, v} ↔ w ∉ X ∧ w ≠ u ∧ w ≠ v := by
    intro w
    simp only [hX₀, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
      not_or, not_and]
    constructor
    · rintro ⟨h, hwu, hwv⟩
      exact ⟨fun hwX ↦ h hwv hwu hwX, hwu, hwv⟩
    · rintro ⟨hwX, hwu, hwv⟩
      exact ⟨fun _ _ hwX' ↦ hwX hwX', hwu, hwv⟩
  refine ⟨X₀, by simp [hX₀], by simp [hX₀], ⟨Ps.filter fun Q ↦ u ∉ Q ∧ v ∉ Q, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · intro Q hQ
    exact hne Q (Finset.mem_filter.mp hQ).1
  · intro Q hQ w hw
    obtain ⟨hQp, huQ, hvQ⟩ := Finset.mem_filter.mp hQ
    rw [hmemX₀]
    exact ⟨havoid Q hQp w hw, fun h ↦ huQ (h ▸ hw), fun h ↦ hvQ (h ▸ hw)⟩
  · intro Q hQ e k hk hZ
    obtain ⟨hQp, huQ, hvQ⟩ := Finset.mem_filter.mp hQ
    rw [hmemX₀] at hZ
    obtain ⟨hX, hwu, hwv⟩ := hZ
    apply hclosed Q hQp _ hk _ hX
    refine Or.inl ⟨endAt_rev_ne e k hloop, fun h ↦ huQ (h ▸ hk), fun h ↦ hvQ (h ▸ hk), hwu, hwv,
      e, ?_⟩
    rcases fin2_cases k with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · intro Q hQ Q' hQ' hne'
    exact hpair Q (Finset.mem_filter.mp hQ).1 Q' (Finset.mem_filter.mp hQ').1 hne'
  · intro w hw
    rw [hmemX₀] at hw
    obtain ⟨hwX, hwu, hwv⟩ := hw
    obtain ⟨Q, hQ, hwQ⟩ := hcover w hwX
    refine ⟨Q, Finset.mem_filter.mpr ⟨hQ, ?_, ?_⟩, hwQ⟩
    · intro huQ
      rcases hu_mem Q hQ huQ with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hwu (Finset.mem_singleton.mp hwQ)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hwQ
        rcases hwQ with rfl | rfl
        · exact hwu rfl
        · exact hwv rfl
    · intro hvQ
      rcases hv_mem Q hQ hvQ with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hwv (Finset.mem_singleton.mp hwQ)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hwQ
        rcases hwQ with rfl | rfl
        · exact hwu rfl
        · exact hwv rfl
  · -- counting
    change X₀.card < ((Ps.filter fun Q ↦ u ∉ Q ∧ v ∉ Q).filter fun Q ↦ Odd Q.card).card
    have hsplit := Finset.card_filter_add_card_filter_not (s := Ps.filter fun Q ↦ Odd Q.card)
      (fun Q ↦ u ∉ Q ∧ v ∉ Q)
    have hcomm : ((Ps.filter fun Q ↦ Odd Q.card).filter fun Q ↦ u ∉ Q ∧ v ∉ Q) =
        ((Ps.filter fun Q ↦ u ∉ Q ∧ v ∉ Q).filter fun Q ↦ Odd Q.card) := by
      rw [Finset.filter_filter, Finset.filter_filter]
      exact Finset.filter_congr fun Q _ ↦ and_comm
    let B1 : Finset (Finset V) := if v ∈ X then {{u}} else ∅
    let B2 : Finset (Finset V) := if u ∈ X then {{v}} else ∅
    have hB1 : B1.card ≤ if v ∈ X then 1 else 0 := by
      simp only [B1]
      split_ifs <;> simp
    have hB2 : B2.card ≤ if u ∈ X then 1 else 0 := by
      simp only [B2]
      split_ifs <;> simp
    have hbad : ((Ps.filter fun Q ↦ Odd Q.card).filter fun Q ↦ ¬ (u ∉ Q ∧ v ∉ Q)).card ≤
        (if v ∈ X then 1 else 0) + (if u ∈ X then 1 else 0) := by
      have hsub : ((Ps.filter fun Q ↦ Odd Q.card).filter fun Q ↦ ¬ (u ∉ Q ∧ v ∉ Q)) ⊆
          B1 ∪ B2 := by
        intro Q hQ
        obtain ⟨hQ', hbad⟩ := Finset.mem_filter.mp hQ
        obtain ⟨hQp, hodd⟩ := Finset.mem_filter.mp hQ'
        rw [Finset.mem_union]
        by_cases huQ : u ∈ Q
        · obtain ⟨hvX, rfl⟩ := hnot_both Q hQp hodd huQ
          left
          simp only [B1, if_pos hvX]
          exact Finset.mem_singleton_self _
        · have hvQ : v ∈ Q := by
            by_contra hvQ
            exact hbad ⟨huQ, hvQ⟩
          obtain ⟨huX, rfl⟩ := hnot_both' Q hQp hodd hvQ
          right
          simp only [B2, if_pos huX]
          exact Finset.mem_singleton_self _
      calc _ ≤ (B1 ∪ B2).card := Finset.card_le_card hsub
        _ ≤ B1.card + B2.card := Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add hB1 hB2
    have hXcard : X.card = X₀.card + (if u ∈ X then 1 else 0) + (if v ∈ X then 1 else 0) := by
      have h1 : (X.erase u).card = X.card - (if u ∈ X then 1 else 0) := by
        split_ifs with h
        · exact Finset.card_erase_of_mem h
        · rw [Finset.erase_eq_of_notMem h]
          rfl
      have h2 : X₀.card = (X.erase u).card - (if v ∈ X then 1 else 0) := by
        split_ifs with h
        · exact Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, h⟩)
        · simp only [hX₀, Finset.erase_eq_of_notMem (fun h' ↦ h (Finset.mem_of_mem_erase h')),
            Nat.sub_zero]
      have h3 : (if u ∈ X then 1 else 0) ≤ X.card := by
        split_ifs with h
        · exact Finset.card_pos.mpr ⟨u, h⟩
        · exact Nat.zero_le _
      have h4 : (if v ∈ X then 1 else 0) ≤ (X.erase u).card := by
        split_ifs with h
        · exact Finset.card_pos.mpr ⟨v, Finset.mem_erase.mpr ⟨huv.symm, h⟩⟩
        · exact Nat.zero_le _
      omega
    rw [hcomm] at hsplit
    rw [← hcardodd] at hviol
    omega

end Normalize

omit [DecidableEq E] in
/-- If `H − u − v` has no perfect matching, Tutte's theorem and parity give a set
`X₀ ⊆ V ∖ {u, v}` and a component family of `H − X₀ − u − v` with at least `|X₀| + 2` odd
members. -/
theorem exists_componentFamily_of_no_matching {H : LoopMultigraph V E}
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (heven : Even (Fintype.card V)) {u v : V}
    (huv : u ≠ v) (hno : ¬ ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P) :
    ∃ X₀ : Finset V, u ∉ X₀ ∧ v ∉ X₀ ∧
      ∃ F : H.ComponentFamily (X₀ ∪ {u, v}), X₀.card + 2 ≤ F.odd.card := by
  have hnoM : ¬ ∃ M : (H.cutGraph u v huv).Subgraph, M.IsPerfectMatching := fun ⟨_, hM⟩ ↦
    hno (exists_isPerfectMatchingOn_of_cutGraph hM)
  have hviol : ∃ X : Set V, (H.cutGraph u v huv).IsTutteViolator X := by
    by_contra h
    push Not at h
    exact hnoM (SimpleGraph.tutte.mpr h)
  obtain ⟨X, hX⟩ := hviol
  unfold SimpleGraph.IsTutteViolator at hX
  classical
  rw [← Set.coe_toFinset X, Set.ncard_coe_finset] at hX
  obtain ⟨X₀, hu0, hv0, F, hcount⟩ := exists_componentFamily_of_violator hloop huv X.toFinset hX
  have hpar := F.odd_card_mod_two
  have hZ : (X₀ ∪ {u, v}).card = X₀.card + 2 := by
    rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hu0, hv0⟩
  have hZle := Finset.card_le_univ (X₀ ∪ {u, v})
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hZ] at hpar
  rw [Nat.even_iff] at heven
  exact ⟨X₀, hu0, hv0, F, by omega⟩

/-- **The hub lemma** (a consequence of Tutte's theorem).  A connected, bridgeless, loopless graph
with a distinguished vertex `b` of odd degree, every other vertex cubic, and `H − b`
factor-critical is matching covered. -/
theorem isMatchingCovered_of_hub {H : LoopMultigraph V E} (hconn : H.IsConnected)
    (hbridge : H.IsBridgeless) (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (b : V)
    (hdeg : ∀ w, w ≠ b → H.degree w = 3) (hb : Odd (H.degree b))
    (hfc : H.IsFactorCritical (Finset.univ.erase b)) : H.IsMatchingCovered := by
  refine ⟨hconn, fun e ↦ ?_⟩
  by_cases hbe : ∃ k, H.endAt e k = b
  · obtain ⟨k, hk⟩ := hbe
    have hub : H.endAt e (Fin.rev k) ≠ b := fun h ↦ endAt_rev_ne e k hloop (hk.trans h.symm)
    obtain ⟨P, hP⟩ := hfc _ (Finset.mem_erase.mpr ⟨hub, Finset.mem_univ _⟩)
    refine ⟨insert e P, hP.insert_perfect ?_ hub.symm, Finset.mem_insert_self _ _⟩
    rcases fin2_cases k with rfl | rfl
    · exact Or.inl ⟨hk, rfl⟩
    · exact Or.inr ⟨rfl, hk⟩
  · push Not at hbe
    have huv : H.endAt e 0 ≠ H.endAt e 1 := hloop e
    have hu : H.endAt e 0 ≠ b := hbe 0
    have hv : H.endAt e 1 ≠ b := hbe 1
    by_contra hno
    have hnoP : ¬ ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase (H.endAt e 0)).erase
        (H.endAt e 1)) P := fun ⟨P, hP⟩ ↦
      hno ⟨insert e P, hP.insert_perfect (Or.inl ⟨rfl, rfl⟩) huv, Finset.mem_insert_self _ _⟩
    have hodd : ∀ w, Odd (H.degree w) := fun w ↦ by
      by_cases hw : w = b
      · rw [hw]
        exact hb
      · rw [hdeg w hw]
        decide
    obtain ⟨X₀, hu0, hv0, F, hge⟩ := exists_componentFamily_of_no_matching hloop
      (card_even_of_odd_degrees hodd) huv hnoP
    by_cases hb0 : b ∈ X₀
    · exact hub_b_mem hu F hfc hb0 hge
    · refine hub_notMem huv hu0 hv0 F hodd hbridge ?_ hge (Or.inl ⟨rfl, rfl⟩)
      intro w hw
      apply hdeg
      rintro rfl
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h
      · exact hb0 h
      · exact hu h.symm
      · exact hv h.symm

/-- **Every edge of a bridgeless cubic loopless graph lies in a perfect matching**
(Petersen–Schönberger), by the same Tutte counting as the second case of the hub lemma. -/
theorem exists_perfectMatching_of_bridgeless {H : LoopMultigraph V E}
    (hCubic : ∀ v : V, H.degree v = 3) (hbridge : H.IsBridgeless)
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (e : E) : ∃ M, H.IsPerfectMatching M ∧ e ∈ M := by
  have huv : H.endAt e 0 ≠ H.endAt e 1 := hloop e
  by_contra hno
  have hnoP : ¬ ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase (H.endAt e 0)).erase
      (H.endAt e 1)) P := fun ⟨P, hP⟩ ↦
    hno ⟨insert e P, hP.insert_perfect (Or.inl ⟨rfl, rfl⟩) huv, Finset.mem_insert_self _ _⟩
  have hodd : ∀ w, Odd (H.degree w) := fun w ↦ by
    rw [hCubic w]
    decide
  obtain ⟨X₀, hu0, hv0, F, hge⟩ := exists_componentFamily_of_no_matching hloop
    (card_even_of_odd_degrees hodd) huv hnoP
  exact hub_notMem huv hu0 hv0 F hodd hbridge (fun w _ ↦ hCubic w) hge (Or.inl ⟨rfl, rfl⟩)

/-- A connected bridgeless cubic loopless graph is matching covered. -/
theorem isMatchingCovered_of_bridgeless {H : LoopMultigraph V E} (hconn : H.IsConnected)
    (hCubic : ∀ v : V, H.degree v = 3) (hbridge : H.IsBridgeless)
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : H.IsMatchingCovered :=
  ⟨hconn, exists_perfectMatching_of_bridgeless hCubic hbridge hloop⟩

end LoopMultigraph
end GraphPuzzles
