import GraphPuzzles.Matching.Barriers.ClosedParts
import GraphPuzzles.Matching.Bipartite.DMBarrierShore
import GraphPuzzles.Bricks.BrickConnectivity

/-! Barriers after removing edges incident with one vertex, as used in the ELP proof. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- In a bicritical matchable graph, a family of disjoint closed odd sets
cannot almost exhaust a separator of size at least two. -/
theorem IsBicritical.closed_odd_parts_bound (hb : H.IsBicritical)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (C : Finset (Finset V)) (B : Finset V)
    (hne : ∀ Q ∈ C, Q.Nonempty)
    (ha : ∀ Q ∈ C, ∀ v ∈ Q, v ∉ B)
    (hc : ∀ Q ∈ C, ∀ e : E, ∀ k : Fin 2,
      H.endAt e k ∈ Q → H.endAt e (Fin.rev k) ∉ B → H.endAt e (Fin.rev k) ∈ Q)
    (hd : ∀ Q ∈ C, ∀ R ∈ C, Q ≠ R → Disjoint Q R)
    (ho : ∀ Q ∈ C, Odd Q.card) (hcount : B.card ≤ C.card + 1) : B.card ≤ 1 := by
  obtain ⟨F, hF⟩ := ComponentFamily.exists_barrier_of_closed_odd_parts
    C B hne ha hc hd hM ho hcount
  exact hb.barrier_card_le_one F hF

namespace ComponentFamily

variable {S : Finset E} {B : Finset V} (F : (H.restrictEdges S).ComponentFamily B)
variable {u : V}

omit [DecidableEq E] in
/-- If all removed edges meet `u`, every old part avoiding `u` remains
closed after `u` is added to the separator. -/
theorem closed_after_insert_of_restrict
    (hS : ∀ e : E, H.endAt e 0 ≠ u → H.endAt e 1 ≠ u → e ∈ S)
    {Q : Finset V} (hQ : Q ∈ F.parts) (huQ : u ∉ Q)
    (e : E) (k : Fin 2) (hk : H.endAt e k ∈ Q)
    (hn : H.endAt e (Fin.rev k) ∉ insert u B) : H.endAt e (Fin.rev k) ∈ Q := by
  have hku : H.endAt e k ≠ u := fun h ↦ huQ (h ▸ hk)
  have hru : H.endAt e (Fin.rev k) ≠ u := fun h ↦ hn (Finset.mem_insert.mpr (Or.inl h))
  have heS : e ∈ S := by
    fin_cases k
    · exact hS e hku hru
    · exact hS e hru hku
  exact F.closed Q hQ ⟨e, heS⟩ k hk (fun h ↦ hn (Finset.mem_insert_of_mem h))

/-- A barrier with a vertex outside all its odd parts, in a graph obtained
by removing edges at `u`, must put `u` in an odd part if the original graph
is bicritical. -/
theorem IsBarrier.exists_odd_part_of_restrict (hF : F.IsBarrier)
    (hb : H.IsBicritical) {M : Finset E} (hM : H.IsPerfectMatching M)
    (hB : B.Nonempty)
    (hS : ∀ e : E, H.endAt e 0 ≠ u → H.endAt e 1 ≠ u → e ∈ S)
    (hgap : ∃ a, a ∉ B ∧ ∀ Q ∈ F.odd, a ∉ Q) :
    u ∉ B ∧ ∃ Q ∈ F.odd, u ∈ Q := by
  have hcount : F.odd.card = B.card := hF
  have hp := Finset.card_pos.mpr hB
  have hunB : u ∉ B := by
    intro huB
    obtain ⟨a, haB, ha⟩ := hgap
    have hbound := hb.closed_odd_parts_bound hM F.odd (insert a B)
      (fun Q hQ ↦ F.nonempty Q (F.mem_odd.mp hQ).1)
      (fun Q hQ v hv hn ↦ by
        rcases Finset.mem_insert.mp hn with rfl | hvB
        · exact ha Q hQ hv
        · exact F.avoid Q (F.mem_odd.mp hQ).1 v hv hvB)
      (fun Q hQ e k hk hn ↦ by
        apply F.closed_after_insert_of_restrict hS (F.mem_odd.mp hQ).1
          (fun h ↦ F.avoid Q (F.mem_odd.mp hQ).1 u h huB) e k hk
        intro hh
        rcases Finset.mem_insert.mp hh with hh | hh
        · exact hn (Finset.mem_insert_of_mem (hh ▸ huB))
        · exact hn (Finset.mem_insert_of_mem hh))
      (fun Q hQ R hR hne ↦ F.pairwise Q (F.mem_odd.mp hQ).1 R (F.mem_odd.mp hR).1 hne)
      (fun Q hQ ↦ (F.mem_odd.mp hQ).2)
      (by rw [Finset.card_insert_of_notMem haB, hcount])
    rw [Finset.card_insert_of_notMem haB] at hbound
    omega
  refine ⟨hunB, ?_⟩
  by_contra hn
  push Not at hn
  have hbound := hb.closed_odd_parts_bound hM F.odd (insert u B)
    (fun Q hQ ↦ F.nonempty Q (F.mem_odd.mp hQ).1)
    (fun Q hQ v hv hvB ↦ by
      rcases Finset.mem_insert.mp hvB with rfl | hvB
      · exact hn Q hQ hv
      · exact F.avoid Q (F.mem_odd.mp hQ).1 v hv hvB)
    (fun Q hQ ↦ F.closed_after_insert_of_restrict hS (F.mem_odd.mp hQ).1 (hn Q hQ))
    (fun Q hQ R hR hne ↦ F.pairwise Q (F.mem_odd.mp hQ).1 R (F.mem_odd.mp hR).1 hne)
    (fun Q hQ ↦ (F.mem_odd.mp hQ).2)
    (by rw [Finset.card_insert_of_notMem hunB, hcount])
  rw [Finset.card_insert_of_notMem hunB] at hbound
  omega

/-- The ELP restriction argument: if the odd parts avoid the other ends of
all removed edges, the distinguished vertex has only one surviving neighbour. -/
theorem IsBarrier.unique_neighbor_of_restrict (hF : F.IsBarrier)
    (hb : H.IsBicritical) (hc : H.ConnectedAfterDeletingPairs)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hB : B.Nonempty)
    (hS : ∀ e : E, H.endAt e 0 ≠ u → H.endAt e 1 ≠ u → e ∈ S)
    (hgap : ∃ a, a ∉ B ∧ ∀ Q ∈ F.odd, a ∉ Q)
    (hout : ∀ Q ∈ F.odd, ∀ e : E, e ∉ S → ∀ k : Fin 2,
      H.endAt e k ∈ Q → H.endAt e k = u) :
    ∃ w, ∀ v, v ≠ u → (∃ e ∈ S, H.Joins e u v) → v = w := by
  classical
  obtain ⟨huB, K, hK, huK⟩ := hF.exists_odd_part_of_restrict F hb hM hB hS hgap
  have hcount : F.odd.card = B.card := hF
  have hbound := hb.closed_odd_parts_bound hM (F.odd.erase K) B
    (fun Q hQ ↦ F.nonempty Q (F.mem_odd.mp (Finset.mem_erase.mp hQ).2).1)
    (fun Q hQ ↦ F.avoid Q (F.mem_odd.mp (Finset.mem_erase.mp hQ).2).1)
    (fun Q hQ e k hk hn ↦ by
      obtain ⟨hQK, hQo⟩ := Finset.mem_erase.mp hQ
      have heS : e ∈ S := by
        by_contra heS
        have hku := hout Q hQo e heS k hk
        exact Finset.disjoint_left.mp
          (F.pairwise Q (F.mem_odd.mp hQo).1 K (F.mem_odd.mp hK).1 hQK)
          hk (hku.symm ▸ huK)
      exact F.closed Q (F.mem_odd.mp hQo).1 ⟨e, heS⟩ k hk hn)
    (fun Q hQ R hR hne ↦ F.pairwise Q (F.mem_odd.mp (Finset.mem_erase.mp hQ).2).1
      R (F.mem_odd.mp (Finset.mem_erase.mp hR).2).1 hne)
    (fun Q hQ ↦ (F.mem_odd.mp (Finset.mem_erase.mp hQ).2).2)
    (by rw [← hcount]; exact (Finset.card_erase_add_one hK).ge)
  have hBcard : B.card = 1 := by have hp := Finset.card_pos.mpr hB; omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hBcard
  have huw : u ≠ w := by simpa only [hw, Finset.mem_singleton] using huB
  have hsingle : ∀ z ∈ K, z = u := by
    intro z hz
    by_contra hzu
    obtain ⟨a, haB, ha⟩ := hgap
    have haK := ha K hK
    have haw : a ≠ w := by simpa only [hw, Finset.mem_singleton] using haB
    have hau : a ≠ u := fun h ↦ haK (h.symm ▸ huK)
    have hzw : z ≠ w := by
      have hh := F.avoid K (F.mem_odd.mp hK).1 z hz
      simpa only [hw, Finset.mem_singleton] using hh
    let c : V → Bool := fun x ↦ decide (x ∈ K)
    have he (e : E) (h0 : H.endAt e 0 ∉ ({u, w} : Finset V))
        (h1 : H.endAt e 1 ∉ ({u, w} : Finset V)) : c (H.endAt e 0) = c (H.endAt e 1) := by
      have h0u : H.endAt e 0 ≠ u := fun h ↦ h0 (Finset.mem_insert.mpr (Or.inl h))
      have h1u : H.endAt e 1 ≠ u := fun h ↦ h1 (Finset.mem_insert.mpr (Or.inl h))
      have h0B : H.endAt e 0 ∉ B := by rw [hw]; exact fun h ↦ h0 (Finset.mem_insert_of_mem h)
      have h1B : H.endAt e 1 ∉ B := by rw [hw]; exact fun h ↦ h1 (Finset.mem_insert_of_mem h)
      have heS := hS e h0u h1u
      have hh : H.endAt e 0 ∈ K ↔ H.endAt e 1 ∈ K :=
        ⟨fun h ↦ F.closed K (F.mem_odd.mp hK).1 ⟨e, heS⟩ 0 h h1B,
          fun h ↦ F.closed K (F.mem_odd.mp hK).1 ⟨e, heS⟩ 1 h h0B⟩
      simp only [c, hh]
    have hh := hc u w huw c he z (by simp [hzu, hzw]) a (by simp [hau, haw])
    simp [c, hz, haK] at hh
  refine ⟨w, ?_⟩
  intro v hv ⟨e, heS, he⟩
  by_contra hvw
  have hvB : v ∉ B := by simpa only [hw, Finset.mem_singleton] using hvw
  obtain ⟨k, hk⟩ := he.exists_end
  have hr : H.endAt e (Fin.rev k) = v := by
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases k <;> simp_all
  have hvK := F.closed K (F.mem_odd.mp hK).1 ⟨e, heS⟩ k (hk.symm ▸ huK)
    (by simpa only [restrictEdges, hr] using hvB)
  exact hv (hsingle v (hr ▸ hvK))

end ComponentFamily

end GraphPuzzles.LoopMultigraph
