import GraphPuzzles.Reduction.Parallel.ParallelEdges
import GraphPuzzles.Matching.Bipartite.HallCore

/-! Strict Hall inequalities for bipartite endpoint multigraphs. -/

namespace GraphPuzzles.LoopMultigraph

open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {c : V → Bool}

omit [DecidableEq V] [DecidableEq E] in
theorem exists_bipartite_ends (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) (e : E) :
    ∃ (a : {v // c v = true}) (b : {v // c v = false}), H.Joins e a.1 b.1 := by
  cases h0 : c (H.endAt e 0)
  · have h1 : c (H.endAt e 1) = true := by
      have hh := hc e
      cases h : c (H.endAt e 1) <;> simp_all
    exact ⟨⟨_, h1⟩, ⟨_, h0⟩, Or.inr ⟨rfl, rfl⟩⟩
  · have h1 : c (H.endAt e 1) = false := by
      have hh := hc e
      cases h : c (H.endAt e 1) <;> simp_all
    exact ⟨⟨_, h0⟩, ⟨_, h1⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- A bipartite bijection, together with one labelled edge for each matched pair, is a
perfect matching. -/
theorem isPerfectMatching_image_of_bijection
    (f : {v // c v = true} → {v // c v = false}) (hf : Function.Bijective f)
    (pick : {v // c v = true} → E) (hp : ∀ a, H.Joins (pick a) a.1 (f a).1) :
    H.IsPerfectMatching (Finset.univ.image pick) := by
  have hne (a : {v // c v = true}) : a.1 ≠ (f a).1 := by
    intro h
    have hh := a.2
    rw [h, (f a).2] at hh
    cases hh
  have hdisj (a b : {v // c v = true}) (hab : a ≠ b) :
      Disjoint ({a.1, (f a).1} : Finset V) {b.1, (f b).1} := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvA hvB
    rcases hvA with rfl | rfl <;> rcases hvB with hvB | hvB
    · exact hab (Subtype.ext hvB)
    · have hh := a.2
      rw [hvB, (f b).2] at hh
      cases hh
    · have hh := (f a).2
      rw [hvB, b.2] at hh
      cases hh
    · exact hab (hf.1 (Subtype.ext hvB))
  have hM := IsPerfectMatchingOn.biUnion (H := H) Finset.univ
    (fun a ↦ {a.1, (f a).1}) (fun a ↦ {pick a})
    (fun a _ ↦ (hp a).isPerfectMatchingOn (hne a)) (fun a _ b _ ↦ hdisj a b)
  have hU : Finset.univ.biUnion (fun a ↦ ({a.1, (f a).1} : Finset V)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    cases hv : c v
    · obtain ⟨a, ha⟩ := hf.2 ⟨v, hv⟩
      refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩
      simp [ha]
    · exact Finset.mem_biUnion.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, by simp⟩
  rw [hU] at hM
  simpa only [Finset.biUnion_singleton] using hM.of_univ

/-- Strict Hall and balanced colour classes make a bipartite endpoint graph matching covered. -/
theorem isMatchingCovered_of_strictHall
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    (ht : HallCore.StrictHall (nbr H c Finset.univ))
    (hbal : Fintype.card {v // c v = true} = Fintype.card {v // c v = false})
    (hne : Nonempty E) : H.IsMatchingCovered := by
  have through (e : E) : ∃ M, H.IsPerfectMatching M ∧ e ∈ M := by
    obtain ⟨a, b, he⟩ := exists_bipartite_ends hc e
    obtain ⟨f, hf, hm, hab⟩ := HallCore.exists_bijective_through
      (nbr H c Finset.univ) ht hbal a b (mem_nbr.mpr ⟨e, Finset.mem_univ _, he⟩)
    have hex (x : {v // c v = true}) : ∃ g, H.Joins g x.1 (f x).1 := by
      obtain ⟨g, _, hg⟩ := mem_nbr.mp (hm x)
      exact ⟨g, hg⟩
    choose pick hp using hex
    let p := fun x ↦ if x = a then e else pick x
    have hp' : ∀ x, H.Joins (p x) x.1 (f x).1 := by
      intro x
      by_cases hx : x = a
      · subst x
        simpa only [p, if_pos rfl, hab] using he
      · simpa only [p, if_neg hx] using hp x
    exact ⟨Finset.univ.image p, isPerfectMatching_image_of_bijection f hf p hp',
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [p]⟩⟩
  refine ⟨?_, through⟩
  intro d hd
  obtain ⟨e⟩ := hne
  obtain ⟨a, b, he⟩ := exists_bipartite_ends hc e
  obtain ⟨f, hf, hm, _⟩ := HallCore.exists_bijective_through
    (nbr H c Finset.univ) ht hbal a b (mem_nbr.mpr ⟨e, Finset.mem_univ _, he⟩)
  have heq (x : {v // c v = true}) (y : {v // c v = false}) : d x.1 = d y.1 := by
    apply ht.constant_of_incidence f hf hm (fun x ↦ d x.1) (fun y ↦ d y.1)
    intro x y hxy
    obtain ⟨g, _, hg⟩ := mem_nbr.mp hxy
    rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hd g
    · simpa only [h0, h1] using (hd g).symm
  have hconst (v : V) : d v = d a.1 := by
    cases hv : c v
    · exact (heq a ⟨v, hv⟩).symm
    · exact (heq ⟨v, hv⟩ b).trans (heq a b).symm
  exact fun u v ↦ (hconst u).trans (hconst v).symm

/-- If every neighbour of a left set is in a right set, their cardinality difference
counts the matching edges leaving their union. -/
theorem IsPerfectMatching.bipartite_shore_count {M : Finset E}
    (hM : H.IsPerfectMatching M)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) {A B : Finset V}
    (hA : ∀ v ∈ A, c v = true) (hB : ∀ v ∈ B, c v = false)
    (hn : ∀ e k, H.endAt e k ∈ A → H.endAt e (Fin.rev k) ∈ B) :
    B.card = A.card + (M ∩ H.dangling (A ∪ B)).card := by
  have hedge (e : E) : H.endsIn B e = H.endsIn A e +
      if e ∈ H.dangling (A ∪ B) then 1 else 0 := by
    have ha : ¬ (H.endAt e 0 ∈ A ∧ H.endAt e 1 ∈ A) :=
      fun h ↦ hc e ((hA _ h.1).trans (hA _ h.2).symm)
    have hb : ¬ (H.endAt e 0 ∈ B ∧ H.endAt e 1 ∈ B) :=
      fun h ↦ hc e ((hB _ h.1).trans (hB _ h.2).symm)
    have h0 : ¬ (H.endAt e 0 ∈ A ∧ H.endAt e 0 ∈ B) := by
      rintro ⟨ha, hb⟩
      have hh := (hA _ ha).symm.trans (hB _ hb)
      cases hh
    have h1 : ¬ (H.endAt e 1 ∈ A ∧ H.endAt e 1 ∈ B) := by
      rintro ⟨ha, hb⟩
      have hh := (hA _ ha).symm.trans (hB _ hb)
      cases hh
    have hn0 := hn e 0
    have hn1 := hn e 1
    change H.endAt e 0 ∈ A → H.endAt e 1 ∈ B at hn0
    change H.endAt e 1 ∈ A → H.endAt e 0 ∈ B at hn1
    unfold endsIn
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_two, Fin.sum_univ_two]
    by_cases ha0 : H.endAt e 0 ∈ A <;> by_cases ha1 : H.endAt e 1 ∈ A <;>
      by_cases hb0 : H.endAt e 0 ∈ B <;> by_cases hb1 : H.endAt e 1 ∈ B <;>
      simp_all [mem_dangling, Finset.mem_union]
  have ha := H.sum_degreeIn_eq A M
  have hb := H.sum_degreeIn_eq B M
  rw [Finset.sum_congr rfl (fun v _ ↦ hM v), Finset.sum_const, smul_eq_mul, mul_one] at ha hb
  rw [hb, Finset.sum_congr rfl (fun e _ ↦ hedge e), Finset.sum_add_distrib, ← ha]
  congr 1
  rw [Finset.sum_boole]
  congr 1

/-- The vertex shore made from a left set and a right set. -/
def bipartiteShore (c : V → Bool) (S : Finset {v // c v = true})
    (T : Finset {v // c v = false}) : Finset V :=
  S.image Subtype.val ∪ T.image Subtype.val

omit [Fintype V] in
@[simp] theorem mem_bipartiteShore_left (S : Finset {v // c v = true})
    (T : Finset {v // c v = false}) (a : {v // c v = true}) :
    a.1 ∈ bipartiteShore c S T ↔ a ∈ S := by
  simp only [bipartiteShore, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨b, hb, hba⟩ | ⟨b, _, hba⟩)
    · exact (Subtype.ext hba : b = a) ▸ hb
    · have hh := b.2
      rw [hba, a.2] at hh
      cases hh
  · exact fun ha ↦ Or.inl ⟨a, ha, rfl⟩

omit [Fintype V] in
theorem card_bipartiteShore (S : Finset {v // c v = true})
    (T : Finset {v // c v = false}) : (bipartiteShore c S T).card = S.card + T.card := by
  have hd : Disjoint (S.image Subtype.val) (T.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    rintro v hvS hvT
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hvS
    obtain ⟨b, _, hba⟩ := Finset.mem_image.mp hvT
    have hh := b.2
    rw [hba, a.2] at hh
    cases hh
  exact (Finset.card_union_of_disjoint hd).trans (by
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_image_of_injective _ Subtype.val_injective])

theorem IsPerfectMatching.neighbor_shore_count {M : Finset E} (hM : H.IsPerfectMatching M)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))
    (S : Finset {v // c v = true}) :
    (S.biUnion (nbr H c Finset.univ)).card = S.card +
      (M ∩ H.dangling (bipartiteShore c S (S.biUnion (nbr H c Finset.univ)))).card := by
  have hh := hM.bipartite_shore_count hc
    (A := S.image Subtype.val) (B := (S.biUnion (nbr H c Finset.univ)).image Subtype.val)
    (by rintro v hv; obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv; exact a.2)
    (by rintro v hv; obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv; exact b.2) ?_
  · simpa only [bipartiteShore, Finset.card_image_of_injective _ Subtype.val_injective] using hh
  · intro e k hk
    obtain ⟨a, ha, hak⟩ := Finset.mem_image.mp hk
    obtain ⟨u, v, he⟩ := exists_bipartite_ends hc e
    have hak' : H.endAt e k = a.1 := hak.symm
    have hau : a = u := by
      rcases he.endAt_mem k with hu | hv
      · exact Subtype.ext (hak.trans hu)
      · have hh := a.2
        rw [hak.trans hv, v.2] at hh
        cases hh
    subst a
    have hother : H.endAt e (Fin.rev k) = v.1 := by
      rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact h1
      · have hh := u.2
        rw [← hak', h1, v.2] at hh
        cases hh
      · have hh := u.2
        rw [← hak', h0, v.2] at hh
        cases hh
      · exact h0
    exact Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr
      ⟨u, ha, mem_nbr.mpr ⟨e, Finset.mem_univ _, he⟩⟩, hother.symm⟩

theorem IsMatchingCovered.strictHall (hm : H.IsMatchingCovered)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) :
    HallCore.StrictHall (nbr H c Finset.univ) := by
  intro S hS hSU
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S := by
    by_contra h
    push Not at h
    exact hSU (Finset.eq_univ_of_forall h)
  have hab : a.1 ≠ b.1 := by
    intro h
    exact hb ((Subtype.ext h : a = b) ▸ ha)
  obtain ⟨M, hM⟩ := hm.exists_perfectMatching_of_ne hab
  have hcount := hM.neighbor_shore_count hc S
  by_contra hlt
  have hbal : (S.biUnion (nbr H c Finset.univ)).card = S.card := by omega
  let X := bipartiteShore c S (S.biUnion (nbr H c Finset.univ))
  have haX : a.1 ∈ X := (mem_bipartiteShore_left _ _ a).mpr ha
  have hbX : b.1 ∉ X := fun h ↦ hb ((mem_bipartiteShore_left _ _ b).mp h)
  obtain ⟨e, he⟩ := hm.1.dangling_nonempty ⟨a.1, haX⟩
    ⟨b.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbX⟩⟩
  obtain ⟨N, hN, heN⟩ := hm.2 e
  have hncount := hN.neighbor_shore_count hc S
  have hpos : 0 < (N ∩ H.dangling X).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨heN, he⟩⟩
  change 0 < (N ∩ H.dangling (bipartiteShore c S
    (S.biUnion (nbr H c Finset.univ)))).card at hpos
  omega

end GraphPuzzles.LoopMultigraph
