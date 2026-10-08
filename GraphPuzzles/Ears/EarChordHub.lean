import GraphPuzzles.Ears.EarCrossingRerouting
import GraphPuzzles.Ears.EarInternalDegree

/-! A matching-tail chord cuts off an even ear segment containing a hub neighbour. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
private theorem joins_ne_of_matching_degree {M : Finset E} {e : E} {x y : V}
    (he : e ∈ M) (hj : H.Joins e x y) (hd : H.degreeIn M x ≤ 1) : x ≠ y := by
  intro hxy
  have h0 : H.endAt e 0 = x := by rcases hj with hj | hj <;> simp_all
  have h1 : H.endAt e 1 = x := by rcases hj with hj | hj <;> simp_all
  have hinc : (e, (0 : Fin 2)) = (e, (1 : Fin 2)) := by
    apply Finset.card_le_one_iff.mp hd
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, h0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, h1⟩
  have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd hinc
  norm_num at h01

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

set_option maxHeartbeats 600000 in
/-- Proposition 5.9: every matching-tail chord cuts off an even segment
whose interior contains a neighbour of the deleted hub. Strong induction
passes to a shorter chord if the first interior vertex is not such a neighbour. -/
theorem tail_edge_segment_has_hub {v : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset))
    {x y : V} (hexy : H.Joins e x y) (p m t : List V)
    (hi : L.ear.interior = p ++ x :: (m ++ y :: t)) :
    ∃ w ∈ m, ∃ a, H.Joins a v w := by
  have hGS : G ⊆ H.edgesIn T := by rw [hT, hG]
  induction hlen : m.length using Nat.strong_induction_on generalizing p m t x y e with
  | h k ih =>
    have hpar := L.tail_edge_even_segment hmax hGS hd he hexy p m t hi
    cases m with
    | nil => norm_num at hpar
    | cons w a =>
      have hw : w ∈ L.ear.interior := by simp [hi]
      have hwT : w ∈ T := L.vertices_eq ▸
        Finset.mem_union_right L.oldVertices (List.mem_toFinset.mpr hw)
      rcases L.internal_hub_or_tail hT hG hw (hdeg w hwT) with hhub | ⟨f, hf, i, hiw⟩
      · exact ⟨w, by simp, hhub⟩
      · let z := H.endAt f (Fin.rev i)
        have hfwz : H.Joins f w z := by
          fin_cases i
          · exact Or.inl ⟨hiw, rfl⟩
          · exact Or.inr ⟨rfl, hiw⟩
        have hwz : w ≠ z := joins_ne_of_matching_degree (L.tail_mem hf) hfwz (hd w hwT)
        have hzA : z ∈ L.ear.interior := L.tail_edge_ends_internal hmax hGS hd hf (Fin.rev i)
        have hz : z ∈ p ∨ z = x ∨ z = w ∨ z ∈ a ∨ z = y ∨ z ∈ t := by
          simpa only [hi, List.mem_append, List.mem_cons, or_assoc] using hzA
        rcases hz with hzp | hzx | hzw | hza | hzy | hzt
        · obtain ⟨b, c, hp⟩ := List.append_of_mem hzp
          have hsplit : L.ear.interior =
              b ++ z :: (c ++ x :: ([] ++ w :: (a ++ y :: t))) := by
            simpa only [hp, List.append_assoc, List.cons_append, List.nil_append] using hi
          have hh := L.tail_crossing_even_segments hmax hGS hd hf he
            (H.joins_comm.mp hfwz) hexy b c [] a t hsplit
          norm_num at hh
        · have hfxw : H.Joins f x w := by simpa only [hzx] using H.joins_comm.mp hfwz
          have hh := L.tail_edge_even_segment hmax hGS hd hf hfxw p [] (a ++ y :: t)
            (by simpa only [List.nil_append, List.cons_append] using hi)
          norm_num at hh
        · exact (hwz hzw.symm).elim
        · obtain ⟨b, c, ha⟩ := List.append_of_mem hza
          have hsplit : L.ear.interior =
              (p ++ [x]) ++ w :: (b ++ z :: (c ++ y :: t)) := by
            simpa only [ha, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hi
          have hlt : b.length < k := by
            simp only [ha, List.length_append, List.length_cons] at hlen
            omega
          obtain ⟨u, hub, g, hgu⟩ := ih b.length hlt hf hfwz (p ++ [x]) b (c ++ y :: t)
            hsplit rfl
          exact ⟨u, by simp [ha, hub], g, hgu⟩
        · have hfwy : H.Joins f w y := by simpa only [hzy] using hfwz
          have hh := L.tail_edge_even_segment hmax hGS hd hf hfwy (p ++ [x]) a t
            (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hi)
          rw [Nat.even_iff] at hpar hh
          simp only [List.length_cons] at hpar
          omega
        · obtain ⟨b, c, ht⟩ := List.append_of_mem hzt
          have hsplit : L.ear.interior =
              p ++ x :: ([] ++ w :: (a ++ y :: (b ++ z :: c))) := by
            simpa only [ht, List.nil_append, List.cons_append] using hi
          have hh := L.tail_crossing_even_segments hmax hGS hd he hf
            hexy hfwz p [] a b c hsplit
          norm_num at hh

/-- The endpoint order and the hub neighbour can be chosen together for
any matching-tail edge. -/
theorem tail_edge_internal_even_hub {v : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    {e : E} (he : e ∈ G \ (L.oldEdges ∪ L.labels.toFinset)) :
    ∃ (p m t : List V) (x y w : V), L.ear.interior = p ++ x :: (m ++ y :: t) ∧
      H.Joins e x y ∧ Even (m.length + 1) ∧ w ∈ m ∧ ∃ a, H.Joins a v w := by
  have hGS : G ⊆ H.edgesIn T := by rw [hT, hG]
  obtain ⟨p, m, t, x, y, hi, hj, heven⟩ := L.tail_edge_internal_even hmax hGS hd he
  obtain ⟨w, hw, hh⟩ := L.tail_edge_segment_has_hub hT hG hmax hd hdeg he hj p m t hi
  exact ⟨p, m, t, x, y, w, hi, hj, heven, hw, hh⟩

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
