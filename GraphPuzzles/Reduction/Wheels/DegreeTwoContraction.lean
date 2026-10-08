import GraphPuzzles.Reduction.Wheels.OddWheelStructure

/-! The tight shore used when bicontracting a vertex of degree two. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
/-- A two-neighbor condition at a retained vertex lifts directly through
contraction when both neighbors are retained too. -/
theorem two_neighbors_of_contract {X : Finset V} {u a b : X}
    (hn : ∀ d k, (H.contract X).endAt d k = some u →
      (H.contract X).endAt d (Fin.rev k) = some a ∨
        (H.contract X).endAt d (Fin.rev k) = some b) :
    ∀ e k, H.endAt e k = u.1 → H.endAt e (Fin.rev k) = a.1 ∨
      H.endAt e (Fin.rev k) = b.1 := by
  intro e k hk
  have he : e ∈ H.meets X := mem_meets.mpr ⟨k, hk.symm ▸ u.2⟩
  have hh := hn ⟨e, he⟩ k ((contract_endAt_eq_some_iff X _ _ u).mpr hk)
  exact hh.imp ((contract_endAt_eq_some_iff X _ _ a).mp)
    ((contract_endAt_eq_some_iff X _ _ b).mp)

omit [DecidableEq V] [DecidableEq E] in
theorem Joins.right_unique {e : E} {u a b : V}
    (ha : H.Joins e u a) (hb : H.Joins e u b) : a = b := by
  rcases ha with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rcases hb with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> simp_all

/-- Two distinct neighbors exhaust a vertex's neighbors in a degree-two
edge set, including when the ambient graph has parallel labels. -/
theorem neighbors_of_degreeIn_le_two {F : Finset E} {u a b : V}
    (hd : H.degreeIn F u ≤ 2) (hab : a ≠ b)
    {e f : E} (he : e ∈ F) (hf : f ∈ F)
    (hea : H.Joins e u a) (hfb : H.Joins f u b)
    {g : E} {z : V} (hg : g ∈ F) (hgz : H.Joins g u z) : z = a ∨ z = b := by
  by_contra hz
  push Not at hz
  have hef : e ≠ f := fun hh ↦ hab (hea.right_unique (hh.symm ▸ hfb))
  have hge : g ≠ e := fun hh ↦ hz.1 (hgz.right_unique (hh.symm ▸ hea))
  have hgf : g ≠ f := fun hh ↦ hz.2 (hgz.right_unique (hh.symm ▸ hfb))
  obtain ⟨i, hi⟩ := hea.exists_end
  obtain ⟨j, hj⟩ := hfb.exists_end
  obtain ⟨k, hk⟩ := hgz.exists_end
  let I := (F ×ˢ Finset.univ).filter fun t : E × Fin 2 ↦ H.endAt t.1 t.2 = u
  have hmem (r : E) (t : Fin 2) (hr : r ∈ F) (ht : H.endAt r t = u) : (r, t) ∈ I := by
    simp [I, hr, ht]
  have hsub : ({(e, i), (f, j), (g, k)} : Finset (E × Fin 2)) ⊆ I := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hmem e i he hi
    · exact hmem f j hf hj
    · exact hmem g k hg hk
  have hc := Finset.card_le_card hsub
  have heq : ({(e, i), (f, j), (g, k)} : Finset (E × Fin 2)).card = 3 := by
    simp [hef, Ne.symm hge, Ne.symm hgf]
  rw [heq] at hc
  change I.card ≤ 2 at hd
  omega

/-- Handshake for an arbitrary selected edge set. -/
theorem sum_degreeIn_eq_two_mul_add (X : Finset V) (M : Finset E) :
    ∑ w ∈ X, H.degreeIn M w =
      2 * (M ∩ H.edgesIn X).card + (M ∩ H.dangling X).card := by
  rw [sum_degreeIn_eq]
  have hp (e : E) : H.endsIn X e = 2 * (if e ∈ H.edgesIn X then 1 else 0) +
      (if e ∈ H.dangling X then 1 else 0) := by
    unfold endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    have hi : e ∈ H.edgesIn X ↔ H.endAt e 0 ∈ X ∧ H.endAt e 1 ∈ X := by
      rw [mem_edgesIn]
      constructor
      · exact fun h ↦ ⟨h 0, h 1⟩
      · intro h k
        fin_cases k <;> tauto
    by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X <;>
      simp [hi, mem_dangling, h0, h1]
  rw [Finset.sum_congr rfl (fun e _ ↦ hp e), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Nat.cast_id]
  simp only [Nat.cast_id]

/-- A vertex whose only neighbors are two distinct vertices makes their
three-vertex shore tight. No matching-covered assumption is needed. -/
theorem isTightCut_neighbor_triple {u a b : V} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hn : ∀ e k, H.endAt e k = u → H.endAt e (Fin.rev k) = a ∨ H.endAt e (Fin.rev k) = b) :
    H.IsTightCut {u, a, b} := by
  intro M hM
  have hp : 0 < H.degreeIn M u := by rw [hM u]; decide
  obtain ⟨e, he, k, hk⟩ := H.mem_edgeSupport_iff.mp
    ((H.degreeIn_pos_iff_mem_edgeSupport M u).mp hp)
  have heI : e ∈ H.edgesIn {u, a, b} := by
    apply mem_edgesIn.mpr
    have ho := hn e k hk
    intro j
    fin_cases k <;> fin_cases j <;> simp_all
  have hi : 0 < (M ∩ H.edgesIn {u, a, b}).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨he, heI⟩⟩
  have hs := sum_degreeIn_eq_two_mul_add (H := H) {u, a, b} M
  rw [Finset.sum_congr rfl (fun w _ ↦ hM w)] at hs
  have hc : ({u, a, b} : Finset V).card = 3 := by simp [hua, hub, hab]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, hc] at hs
  omega

omit [DecidableEq E] in
/-- The discarded side of a degree-two bicontraction is bipartite when
the two neighbors are nonadjacent. -/
theorem isBipartite_contract_neighbor_triple {u a b : V}
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hn : ∀ e k, H.endAt e k = u → H.endAt e (Fin.rev k) = a ∨ H.endAt e (Fin.rev k) = b)
    (hab : ∀ e, ¬ H.Joins e a b) :
    (H.contract {u, a, b}).IsBipartite := by
  let c : Option ({u, a, b} : Finset V) → Bool := fun z ↦
    match z with
    | none => false
    | some z => decide (z.1 = a ∨ z.1 = b)
  have hc (z : V) : c (contractVertex {u, a, b} z) = decide (z = a ∨ z = b) := by
    by_cases hz : z ∈ ({u, a, b} : Finset V)
    · simp [contractVertex, hz, c]
    · have ha : z ≠ a := fun hh ↦ hz (by simp [hh])
      have hb : z ≠ b := fun hh ↦ hz (by simp [hh])
      simp [contractVertex, hz, c, ha, hb]
  refine ⟨c, ?_⟩
  intro f hf
  change c (contractVertex {u, a, b} (H.endAt f.1 0)) =
    c (contractVertex {u, a, b} (H.endAt f.1 1)) at hf
  rw [hc, hc, decide_eq_decide] at hf
  by_cases h0 : H.endAt f.1 0 = a ∨ H.endAt f.1 0 = b
  · have h1 := hf.mp h0
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact hl f.1 (h0.trans h1.symm)
    · exact hab f.1 (Or.inl ⟨h0, h1⟩)
    · exact hab f.1 (Or.inr ⟨h0, h1⟩)
    · exact hl f.1 (h0.trans h1.symm)
  · have h1 : ¬ (H.endAt f.1 1 = a ∨ H.endAt f.1 1 = b) := fun h ↦ h0 (hf.mpr h)
    obtain ⟨k, hk⟩ := mem_meets.mp f.2
    fin_cases k
    · have hu : H.endAt f.1 0 = u := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        tauto
      exact h1 (by simpa using hn f.1 0 hu)
    · have hu : H.endAt f.1 1 = u := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        tauto
      exact h0 (by simpa using hn f.1 1 hu)

end GraphPuzzles.LoopMultigraph
