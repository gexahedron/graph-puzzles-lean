import GraphPuzzles.DefectThree.HexagonMatching

/-!
# Local structure of optimal matching triples

The matching memberships partition the three incidences at each cubic vertex. Optimality
forbids replacing one occurrence of a multiply covered edge by an uncovered parallel edge.
In particular, a triple with three uncovered edges has no triply covered edge.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
theorem halfEdge_edge_injective (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (v : V) :
    Function.Injective (fun h : H.halfEdgesAt v ↦ h.1.1) := by
  rintro ⟨⟨e, i⟩, hi⟩ ⟨⟨f, j⟩, hj⟩ hef
  dsimp at hef
  subst f
  have hij : i = j := by
    by_contra hn
    fin_cases i <;> fin_cases j <;> simp_all [vertex]
    · exact hl e (hi.trans hj.symm)
    · exact hl e (hj.trans hi.symm)
  subst j
  rfl

namespace IsPerfectMatching

theorem half_unique {P : Finset E} (hP : H.IsPerfectMatching P) {v : V}
    (x y : H.halfEdgesAt v) (hx : x.1.1 ∈ P) (hy : y.1.1 ∈ P) : x = y := by
  by_contra hn
  have := H.two_le_degreeIn_of_ne x y hn hx hy
  rw [hP v] at this
  omega

theorem exists_half {P : Finset E} (hP : H.IsPerfectMatching P) (v : V) :
    ∃ x : H.halfEdgesAt v, x.1.1 ∈ P := by
  have h := hP v
  rw [H.degreeIn_eq_card_halfEdges, Finset.card_eq_one] at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, ?_⟩
  have hx' : x ∈ Finset.univ.filter (fun y : H.halfEdgesAt v ↦ y.1.1 ∈ P) := by
    rw [hx]
    exact Finset.mem_singleton_self x
  exact (Finset.mem_filter.mp hx').2

/-- Replacing a matching edge by a parallel edge preserves the perfect matching. -/
theorem replace_parallel {P : Finset E} (hP : H.IsPerfectMatching P) {e f : E}
    (he : e ∈ P) (hf : f ∉ P) (p : Fin 2 ≃ Fin 2)
    (hp : ∀ i, H.endAt f i = H.endAt e (p i)) :
    H.IsPerfectMatching (insert f (P.erase e)) := by
  intro v
  have degree_formula (S : Finset E) :
      H.degreeIn S v = ∑ d ∈ S, ∑ i : Fin 2, if H.endAt d i = v then 1 else 0 := by
    simp only [degreeIn, Finset.card_filter, Finset.sum_product]
  have hsame : (∑ i : Fin 2, if H.endAt f i = v then 1 else 0 : ℕ) =
      ∑ i : Fin 2, if H.endAt e i = v then 1 else 0 := by
    simp only [hp]
    exact p.sum_comp (fun i ↦ if H.endAt e i = v then (1 : ℕ) else 0)
  rw [degree_formula, Finset.sum_insert (fun h ↦ hf (Finset.mem_of_mem_erase h)), hsame,
    Finset.add_sum_erase P (fun d ↦ ∑ i : Fin 2, if H.endAt d i = v then (1 : ℕ) else 0) he,
    ← degree_formula, hP v]

end IsPerfectMatching

/-- Two disjoint perfect matchings of a cubic graph give a proper three-edge-colouring. -/
theorem colourable_of_disjoint_matchings (hc : ∀ v, H.degree v = 3)
    {P Q : Finset E} (hP : H.IsPerfectMatching P) (hQ : H.IsPerfectMatching Q)
    (hd : Disjoint P Q) : ∃ g : E → Color, H.ProperOff ∅ g := by
  have outside_unique (v : V) (x y : H.halfEdgesAt v)
      (hxP : x.1.1 ∉ P) (hxQ : x.1.1 ∉ Q) (hyP : y.1.1 ∉ P) (hyQ : y.1.1 ∉ Q) :
      x = y := by
    let A := Finset.univ.filter fun z : H.halfEdgesAt v ↦ z.1.1 ∈ P
    let B := Finset.univ.filter fun z : H.halfEdgesAt v ↦ z.1.1 ∈ Q
    have hA : A.card = 1 := (H.degreeIn_eq_card_halfEdges P v).symm.trans (hP v)
    have hB : B.card = 1 := (H.degreeIn_eq_card_halfEdges Q v).symm.trans (hQ v)
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hzA).2 (Finset.mem_filter.mp hzB).2
    have hcard : (Finset.univ \ (A ∪ B)).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_union_of_disjoint hAB, hA, hB, Finset.card_univ]
      change H.degree v - (1 + 1) ≤ 1
      rw [hc]
    exact Finset.card_le_one.mp hcard x
      (by simp [A, B, hxP, hxQ]) y (by simp [A, B, hyP, hyQ])
  let g : E → Color := fun e ↦
    choiceColor (if e ∈ P then 0 else if e ∈ Q then 1 else 2)
  refine ⟨g, ⟨fun _ _ ↦ choiceColor_ne_zero _, ?_⟩⟩
  intro v _ x y _ _ heq
  have heq' := choiceColor_injective _ _ heq
  change (if x.1.1 ∈ P then (0 : Fin 3) else if x.1.1 ∈ Q then 1 else 2) =
    (if y.1.1 ∈ P then 0 else if y.1.1 ∈ Q then 1 else 2) at heq'
  by_cases hxP : x.1.1 ∈ P <;> by_cases hyP : y.1.1 ∈ P <;>
    by_cases hxQ : x.1.1 ∈ Q <;> by_cases hyQ : y.1.1 ∈ Q <;>
    simp only [hxP, hyP, hxQ, hyQ, if_true, if_false] at heq'
  all_goals first
    | exact hP.half_unique x y hxP hyP
    | exact hQ.half_unique x y hxQ hyQ
    | exact outside_unique v x y hxP hxQ hyP hyQ
    | contradiction

namespace MatchingTriple

variable (M : H.MatchingTriple)

theorem multiplicity_zero_iff (e : E) : M.multiplicity e = 0 ↔
    ∀ i, e ∉ M.matching i := by
  simp [multiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem multiplicity_three_iff (e : E) : M.multiplicity e = 3 ↔
    ∀ i, e ∈ M.matching i := by
  change (Finset.univ.filter fun i ↦ e ∈ M.matching i).card =
      (Finset.univ : Finset (Fin 3)).card ↔ _
  rw [Finset.card_filter_eq_iff]
  simp

theorem sum_multiplicity_at (v : V) : ∑ x : H.halfEdgesAt v, M.multiplicity x.1.1 = 3 := by
  simp only [multiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ i, (∑ x : H.halfEdgesAt v, if x.1.1 ∈ M.matching i then 1 else 0 : ℕ) = 1 := by
    intro i
    rw [← Finset.card_filter, ← H.degreeIn_eq_card_halfEdges]
    exact M.perfect i v
  simp only [h]
  decide

noncomputable def vertexEquiv (hc : ∀ v, H.degree v = 3) (v : V) :
    Fin 3 ≃ H.halfEdgesAt v :=
  (Fintype.equivFinOfCardEq (hc v)).symm

theorem sum_multiplicity_three (hc : ∀ v, H.degree v = 3) (v : V) :
    ∑ i : Fin 3, M.multiplicity ((vertexEquiv hc v) i).1.1 = 3 := by
  exact ((vertexEquiv hc v).sum_comp
    (fun x : H.halfEdgesAt v ↦ M.multiplicity x.1.1)).trans (M.sum_multiplicity_at v)

/-- Changing one matching along a parallel digon strictly improves the triple. -/
theorem IsOptimal.not_parallel_uncovered {M : H.MatchingTriple} (ho : M.IsOptimal)
    {e f : E} (he : 2 ≤ M.multiplicity e) (hf : M.multiplicity f = 0)
    (p : Fin 2 ≃ Fin 2) (hp : ∀ i, H.endAt f i = H.endAt e (p i)) : False := by
  have hne : e ≠ f := by intro h; subst f; omega
  obtain ⟨a, ha⟩ : ∃ a, e ∈ M.matching a := by
    by_contra hn
    push Not at hn
    have := (M.multiplicity_zero_iff e).mpr hn
    omega
  have hf' := (M.multiplicity_zero_iff f).mp hf
  let N : H.MatchingTriple :=
    { matching := fun i ↦ if i = a then insert f ((M.matching a).erase e) else M.matching i
      perfect := by
        intro i
        split_ifs with hi
        · exact (M.perfect a).replace_parallel ha (hf' a) p hp
        · exact M.perfect i }
  have hother : ∃ b, b ≠ a ∧ e ∈ M.matching b := by
    by_contra hn
    push Not at hn
    have hsub : (Finset.univ.filter fun i ↦ e ∈ M.matching i) ⊆ {a} := by
      intro b hb
      by_contra hba
      exact hn b (by simpa using hba) (Finset.mem_filter.mp hb).2
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    change M.multiplicity e ≤ 1 at hcard
    omega
  have hun : N.uncovered = M.uncovered.erase f := by
    ext d
    simp only [mem_uncovered, multiplicity_zero_iff, Finset.mem_erase]
    by_cases hd : d = f
    · subst d
      apply iff_of_false ?_ (by simp)
      intro h
      exact h a (by simp [N])
    · by_cases hde : d = e
      · subst d
        obtain ⟨b, hb, hbe⟩ := hother
        have hNb : e ∈ N.matching b := by simp [N, hb, hbe]
        exact iff_of_false (fun h ↦ h b hNb) (fun h ↦ h.2 a ha)
      · have hm : ∀ i, d ∈ N.matching i ↔ d ∈ M.matching i := by
          intro i
          by_cases hi : i = a
          · subst i; simp [N, hd, hde]
          · simp [N, hi]
        simp only [hm]
        exact ⟨fun h ↦ ⟨hd, h⟩, And.right⟩
  have hlt : N.uncovered.card < M.uncovered.card := by
    rw [hun]
    exact Finset.card_erase_lt_of_mem ((M.mem_uncovered f).mpr hf)
  exact (not_lt_of_ge (ho N)) hlt

/-- At most three uncovered edges force an optimal triple to be regular. -/
theorem IsOptimal.regular_of_uncovered_le_three {M : H.MatchingTriple}
    (ho : M.IsOptimal) (hc : ∀ v, H.degree v = 3)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (hu : M.uncovered.card ≤ 3) : M.IsRegular := by
  intro e
  by_contra hn
  have he : M.multiplicity e = 3 := by have := M.multiplicity_le_three e; omega
  have hall := (M.multiplicity_three_iff e).mp he
  let A : Fin 2 → Finset E := fun k ↦
    Finset.univ.filter fun f ↦ f ≠ e ∧ ∃ j, H.endAt f j = H.endAt e k
  have hz : ∀ k f, f ∈ A k → M.multiplicity f = 0 := by
    intro k f hf
    obtain ⟨hne, j, hj⟩ := (Finset.mem_filter.mp hf).2
    apply (M.multiplicity_zero_iff f).mpr
    intro i hi
    have hh := (M.perfect i).half_unique ⟨(f, j), hj⟩ ⟨(e, k), rfl⟩ hi (hall i)
    exact hne (congrArg (fun x ↦ x.1.1) hh)
  have hcard : ∀ k, (A k).card = 2 := by
    intro k
    let x : H.halfEdgesAt (H.endAt e k) := ⟨(e, k), rfl⟩
    have heq : A k = (Finset.univ.erase x).image (fun h : H.halfEdgesAt _ ↦ h.1.1) := by
      ext f
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_erase]
      constructor
      · rintro ⟨hne, j, hj⟩
        exact ⟨⟨(f, j), hj⟩, ⟨fun hh ↦ hne (congrArg (fun y ↦ y.1.1) hh), trivial⟩, rfl⟩
      · rintro ⟨h, ⟨hh, _⟩, rfl⟩
        exact ⟨fun heq ↦ hh (halfEdge_edge_injective hl _ heq), h.1.2, h.2⟩
    rw [heq, Finset.card_image_of_injective _ (halfEdge_edge_injective hl _),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    change H.degree (H.endAt e k) - 1 = 2
    rw [hc]
  have hdis : Disjoint (A 0) (A 1) := by
    rw [Finset.disjoint_left]
    intro f h₀ h₁
    obtain ⟨_, i, hi⟩ := (Finset.mem_filter.mp h₀).2
    obtain ⟨_, j, hj⟩ := (Finset.mem_filter.mp h₁).2
    have hij : i ≠ j := by intro h; subst j; exact hl e (hi.symm.trans hj)
    have hp : ∃ p : Fin 2 ≃ Fin 2, ∀ k, H.endAt f k = H.endAt e (p k) := by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact ⟨Equiv.refl _, by intro k; fin_cases k <;> assumption⟩
      · exact ⟨Equiv.swap 0 1, by intro k; fin_cases k <;> simpa using (by assumption : _)⟩
      · exact (hij rfl).elim
    obtain ⟨p, hp⟩ := hp
    exact ho.not_parallel_uncovered (by omega) (hz 0 f h₀) p hp
  have hsub : A 0 ∪ A 1 ⊆ M.uncovered := by
    intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact (M.mem_uncovered f).mpr (hz 0 f hf)
    · exact (M.mem_uncovered f).mpr (hz 1 f hf)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hcard, hcard] at this
  omega

theorem multiplicity_pair_le {v : V} (x y : H.halfEdgesAt v) (hxy : x ≠ y) :
    M.multiplicity x.1.1 + M.multiplicity y.1.1 ≤ 3 := by
  have h := Finset.sum_le_sum_of_subset (f := fun z : H.halfEdgesAt v ↦ M.multiplicity z.1.1)
    (Finset.subset_univ ({x, y} : Finset (H.halfEdgesAt v)))
  rw [Finset.sum_pair hxy, M.sum_multiplicity_at] at h
  exact h

theorem double_half_unique {v : V} (x y : H.halfEdgesAt v)
    (hx : 2 ≤ M.multiplicity x.1.1) (hy : 2 ≤ M.multiplicity y.1.1) : x = y := by
  by_contra hn
  have := M.multiplicity_pair_le x y hn
  omega

theorem IsRegular.zero_half_unique {M : H.MatchingTriple} (hr : M.IsRegular)
    (hc : ∀ v, H.degree v = 3) {v : V} (x y : H.halfEdgesAt v)
    (hx : M.multiplicity x.1.1 = 0) (hy : M.multiplicity y.1.1 = 0) : x = y := by
  let e := vertexEquiv hc v
  let f : Fin 3 → Fin 3 := fun i ↦ ⟨M.multiplicity (e i).1.1, by have := hr (e i).1.1; omega⟩
  have tab : ∀ (f : Fin 3 → Fin 3), (∑ i, (f i).val) = 3 →
      ∀ a b, f a = 0 → f b = 0 → a = b := by decide
  have hs : (∑ i, (f i).val) = 3 := M.sum_multiplicity_three hc v
  have hx' : f (e.symm x) = 0 := Fin.ext (by simpa [f] using hx)
  have hy' : f (e.symm y) = 0 := Fin.ext (by simpa [f] using hy)
  exact e.symm.injective (tab f hs _ _ hx' hy')

theorem IsRegular.uncovered_ends_injective {M : H.MatchingTriple} (hr : M.IsRegular)
    (hc : ∀ v, H.degree v = 3) :
    Function.Injective (fun p : {e // e ∈ M.uncovered} × Fin 2 ↦ H.endAt p.1.1 p.2) := by
  rintro ⟨⟨e, he⟩, i⟩ ⟨⟨f, hf⟩, j⟩ hp
  have h := hr.zero_half_unique hc ⟨(e, i), rfl⟩ ⟨(f, j), hp.symm⟩
    ((M.mem_uncovered e).mp he) ((M.mem_uncovered f).mp hf)
  have heq : e = f := congrArg (fun x ↦ x.1.1) h
  have hij : i = j := congrArg (fun x ↦ x.1.2) h
  subst f
  subst j
  rfl

/-- Every end of a doubly covered edge has exactly one uncovered and one simply covered edge. -/
theorem double_vertex (hc : ∀ v, H.degree v = 3) {v : V} (x : H.halfEdgesAt v)
    (hx : M.multiplicity x.1.1 = 2) :
    ∃ z s : H.halfEdgesAt v, M.multiplicity z.1.1 = 0 ∧ M.multiplicity s.1.1 = 1 ∧
      (∀ y : H.halfEdgesAt v, y = x ∨ y = z ∨ y = s) := by
  let e := vertexEquiv hc v
  obtain ⟨a, rfl⟩ := e.surjective x
  have hs := M.sum_multiplicity_three hc v
  change ∑ i, M.multiplicity (e i).1.1 = 3 at hs
  simp only [Fin.sum_univ_three] at hs
  have cases : ∀ y : H.halfEdgesAt v, y = e 0 ∨ y = e 1 ∨ y = e 2 := by
    intro y
    obtain ⟨i, rfl⟩ := e.surjective y
    fin_cases i <;> simp
  fin_cases a
  · change M.multiplicity (e 0).1.1 = 2 at hx
    have h : (M.multiplicity (e 1).1.1 = 0 ∧ M.multiplicity (e 2).1.1 = 1) ∨
        (M.multiplicity (e 2).1.1 = 0 ∧ M.multiplicity (e 1).1.1 = 1) := by omega
    rcases h with h | h
    · exact ⟨e 1, e 2, h.1, h.2, cases⟩
    · exact ⟨e 2, e 1, h.1, h.2, fun y ↦ by rcases cases y with h | h | h <;> simp [h]⟩
  · change M.multiplicity (e 1).1.1 = 2 at hx
    have h : (M.multiplicity (e 0).1.1 = 0 ∧ M.multiplicity (e 2).1.1 = 1) ∨
        (M.multiplicity (e 2).1.1 = 0 ∧ M.multiplicity (e 0).1.1 = 1) := by omega
    rcases h with h | h
    · exact ⟨e 0, e 2, h.1, h.2, fun y ↦ by rcases cases y with h | h | h <;> simp [h]⟩
    · exact ⟨e 2, e 0, h.1, h.2, fun y ↦ by rcases cases y with h | h | h <;> simp [h]⟩
  · change M.multiplicity (e 2).1.1 = 2 at hx
    have h : (M.multiplicity (e 0).1.1 = 0 ∧ M.multiplicity (e 1).1.1 = 1) ∨
        (M.multiplicity (e 1).1.1 = 0 ∧ M.multiplicity (e 0).1.1 = 1) := by omega
    rcases h with h | h
    · exact ⟨e 0, e 1, h.1, h.2, fun y ↦ by rcases cases y with h | h | h <;> simp [h]⟩
    · exact ⟨e 1, e 0, h.1, h.2, fun y ↦ by rcases cases y with h | h | h <;> simp [h]⟩

/-- In an uncolourable cubic graph, each pair of distinct matchings intersects. -/
theorem exists_common (hc : ∀ v, H.degree v = 3)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g) (a b : Fin 3) :
    ∃ e, e ∈ M.matching a ∧ e ∈ M.matching b := by
  by_contra h
  push Not at h
  exact hn (colourable_of_disjoint_matchings hc (M.perfect a) (M.perfect b)
    (Finset.disjoint_left.mpr fun e ha hb ↦ h e ha hb))

/-- A regular triple in an uncolourable graph has a doubly covered edge missing each index. -/
theorem exists_double_edges (hc : ∀ v, H.degree v = 3)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g) (hr : M.IsRegular) :
    ∃ d : Fin 3 → E, ∀ a i, d a ∈ M.matching i ↔ i ≠ a := by
  have ex : ∀ a : Fin 3, ∃ e, ∀ i, e ∈ M.matching i ↔ i ≠ a := by
    intro a
    obtain ⟨e, h₁, h₂⟩ := M.exists_common hc hn (a + 1) (a + 2)
    refine ⟨e, ?_⟩
    have hreg := hr e
    change (Finset.univ.filter fun i ↦ e ∈ M.matching i).card ≤ 2 at hreg
    have tab : ∀ (s : Finset (Fin 3)) (a : Fin 3), s.card ≤ 2 →
        a + 1 ∈ s → a + 2 ∈ s → ∀ i, i ∈ s ↔ i ≠ a := by decide
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      tab (Finset.univ.filter fun i ↦ e ∈ M.matching i) a hreg (by simpa) (by simpa)
  choose d hd using ex
  exact ⟨d, hd⟩

end MatchingTriple
end LoopMultigraph
end GraphPuzzles
