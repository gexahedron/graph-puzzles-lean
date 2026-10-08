import GraphPuzzles.Cuts.Shores.ShoreConnectivity
import GraphPuzzles.Matching.Barriers.BarrierPrecedence
import GraphPuzzles.Bricks.BrickConnectivity

/-! Connectivity after one vertex deletion and a finite non-cut-vertex selection argument. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Deleting one vertex of a matching-covered graph leaves a connected shore. -/
theorem IsMatchingCovered.connectedOn_delete (hm : H.IsMatchingCovered) (v : V) :
    H.IsConnectedOn (Finset.univ.erase v) := by
  intro c he a ha b hb
  have hav : a ≠ v := (Finset.mem_erase.mp ha).1
  have hbv : b ≠ v := (Finset.mem_erase.mp hb).1
  obtain ⟨e, _⟩ := hm.1.dangling_nonempty (Finset.singleton_nonempty v)
    ⟨a, by simp [hav]⟩
  obtain ⟨M, hM, _⟩ := hm.2 e
  obtain ⟨F, hF⟩ := exists_componentFamily_of_coloring (H := H) {v} c (by
    intro e h0 h1
    exact he e (by simpa using h0) (by simpa using h1))
  have hle := F.odd_card_le_of_fractional hM.isFractional
  have hpar := F.odd_card_mod_two
  have hcard : (Finset.univ \ ({v} : Finset V)).card + 1 = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({v} : Finset V))
  have heven := hM.isFractional.card_even
  rw [Nat.even_iff] at heven
  simp only [Finset.card_singleton] at hle
  have hbar : F.IsBarrier := by
    change F.odd.card = ({v} : Finset V).card
    simp only [Finset.card_singleton]
    omega
  obtain ⟨Q, hQ, haQ⟩ := F.cover a (by simpa using hav)
  obtain ⟨R, hR, hbR⟩ := F.cover b (by simpa using hbv)
  have hQo := hbar.mem_odd_of_mem F hm (Finset.singleton_nonempty v) hQ
  have hRo := hbar.mem_odd_of_mem F hm (Finset.singleton_nonempty v) hR
  have hQR := Finset.card_le_one.mp hle Q hQo R hRo
  subst R
  exact hF Q hQ a haQ b hbR

omit [DecidableEq E] in
/-- If a vertex set has no exit except through `w`, its complement is connected
whenever the whole graph is connected. -/
theorem IsConnected.connectedOn_compl_of_closed_except (hg : H.IsConnected)
    {Q : Finset V} {w : V}
    (hclosed : ∀ e : E, ∀ k : Fin 2, H.endAt e k ∈ Q →
      H.endAt e (Fin.rev k) ≠ w → H.endAt e (Fin.rev k) ∈ Q) :
    H.IsConnectedOn (Finset.univ \ Q) := by
  intro c hc a ha b hb
  let d : V → Bool := fun x ↦ if x ∈ Q then c w else c x
  have hd (e : E) : d (H.endAt e 0) = d (H.endAt e 1) := by
    by_cases h0 : H.endAt e 0 ∈ Q <;> by_cases h1 : H.endAt e 1 ∈ Q
    · simp [d, h0, h1]
    · have h1w : H.endAt e 1 = w := by
        by_contra hn
        exact h1 (hclosed e 0 h0 hn)
      simp only [d, if_pos h0, if_neg h1]
      exact congrArg c h1w.symm
    · have h0w : H.endAt e 0 = w := by
        by_contra hn
        exact h0 (hclosed e 1 h1 hn)
      simp only [d, if_neg h0, if_pos h1]
      exact congrArg c h0w
    · simpa only [d, if_neg h0, if_neg h1] using
        hc e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h0⟩)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩)
  simpa only [d, if_neg (Finset.mem_sdiff.mp ha).2, if_neg (Finset.mem_sdiff.mp hb).2]
    using hg d hd a b

omit [DecidableEq E] in
/-- If deletion of `w` disconnects a graph, a colour class avoiding a prescribed
surviving vertex gives a nonempty part closed outside `w`. -/
theorem exists_closed_part_of_not_connected_delete {w : V} (b : V)
    (hn : ¬ H.IsConnectedOn (Finset.univ.erase w)) :
    ∃ Q : Finset V, Q.Nonempty ∧ w ∉ Q ∧ b ∉ Q ∧
      ∀ e : E, ∀ k : Fin 2, H.endAt e k ∈ Q →
        H.endAt e (Fin.rev k) ≠ w → H.endAt e (Fin.rev k) ∈ Q := by
  classical
  unfold IsConnectedOn at hn
  push Not at hn
  obtain ⟨c, hc, a, ha, d, hd, hne⟩ := hn
  let Q := Finset.univ.filter fun x ↦ x ≠ w ∧ c x ≠ c b
  have hm (x : V) : x ∈ Q ↔ x ≠ w ∧ c x ≠ c b := by simp [Q]
  have hQ : Q.Nonempty := by
    by_cases hab : c a = c b
    · exact ⟨d, (hm d).mpr ⟨(Finset.mem_erase.mp hd).1, fun h ↦ hne (hab.trans h.symm)⟩⟩
    · exact ⟨a, (hm a).mpr ⟨(Finset.mem_erase.mp ha).1, hab⟩⟩
  refine ⟨Q, hQ, by simp [Q], by simp [Q], ?_⟩
  intro e k hk hn
  obtain ⟨hkw, hkcol⟩ := (hm _).mp hk
  apply (hm _).mpr
  refine ⟨hn, ?_⟩
  have he : c (H.endAt e k) = c (H.endAt e (Fin.rev k)) := by
    fin_cases k
    · exact hc e (Finset.mem_erase.mpr ⟨hkw, Finset.mem_univ _⟩)
        (Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩)
    · exact (hc e (Finset.mem_erase.mpr ⟨hn, Finset.mem_univ _⟩)
        (Finset.mem_erase.mpr ⟨hkw, Finset.mem_univ _⟩)).symm
  exact fun h ↦ hkcol (he.trans h)

omit [DecidableEq E] in
/-- A connected finite graph has a non-cut vertex in `N` if every nonempty
part closed after deleting a vertex of `N` meets `N`. The proof minimizes
such a closed part and descends if a selected vertex still disconnects the graph. -/
theorem IsConnected.exists_delete_connected_in (hg : H.IsConnected) (N : Finset V)
    (hN : N.Nonempty)
    (htouch : ∀ w ∈ N, ∀ Q : Finset V, Q.Nonempty → w ∉ Q →
      (∀ e : E, ∀ k : Fin 2, H.endAt e k ∈ Q →
        H.endAt e (Fin.rev k) ≠ w → H.endAt e (Fin.rev k) ∈ Q) → (Q ∩ N).Nonempty) :
    ∃ v ∈ N, H.IsConnectedOn (Finset.univ.erase v) := by
  classical
  by_contra hn
  push Not at hn
  let C := Finset.univ.filter fun Q : Finset V ↦ Q.Nonempty ∧
    ∃ w ∈ N, w ∉ Q ∧ ∀ e : E, ∀ k : Fin 2, H.endAt e k ∈ Q →
      H.endAt e (Fin.rev k) ≠ w → H.endAt e (Fin.rev k) ∈ Q
  obtain ⟨w₀, hw₀⟩ := hN
  have hdel := hn w₀ hw₀
  obtain ⟨Q₀, hQ₀, hwQ₀, _, hclosed₀⟩ := exists_closed_part_of_not_connected_delete w₀ hdel
  have hQ₀C : Q₀ ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hQ₀, w₀, hw₀, hwQ₀, hclosed₀⟩
  obtain ⟨Q, hQC, hmin⟩ := C.exists_min_image Finset.card ⟨Q₀, hQ₀C⟩
  obtain ⟨hQne, w, hwN, hwQ, hclosed⟩ := (Finset.mem_filter.mp hQC).2
  obtain ⟨z, hz⟩ := htouch w hwN Q hQne hwQ hclosed
  obtain ⟨hzQ, hzN⟩ := Finset.mem_inter.mp hz
  obtain ⟨R, hRne, hzR, hwR, hRclosed⟩ := exists_closed_part_of_not_connected_delete w (hn z hzN)
  have hc := hg.connectedOn_compl_of_closed_except hclosed
  have hRQ : R ⊆ Q := by
    intro x hxR
    by_contra hxQ
    let c : V → Bool := fun y ↦ decide (y ∈ R)
    have hedge (e : E) (h0 : H.endAt e 0 ∈ Finset.univ \ Q)
        (h1 : H.endAt e 1 ∈ Finset.univ \ Q) : c (H.endAt e 0) = c (H.endAt e 1) := by
      have h0z : H.endAt e 0 ≠ z := fun he ↦ (Finset.mem_sdiff.mp h0).2 (he.symm ▸ hzQ)
      have h1z : H.endAt e 1 ≠ z := fun he ↦ (Finset.mem_sdiff.mp h1).2 (he.symm ▸ hzQ)
      have hh : H.endAt e 0 ∈ R ↔ H.endAt e 1 ∈ R :=
        ⟨fun h ↦ hRclosed e 0 h h1z, fun h ↦ hRclosed e 1 h h0z⟩
      simp only [c, hh]
    have hh := hc c hedge x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxQ⟩)
      w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwQ⟩)
    simp [c, hxR, hwR] at hh
  have hRC : R ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hRne, z, hzN, hzR, hRclosed⟩
  have hlt : R.card < Q.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hRQ, fun he ↦ hzR (he.symm ▸ hzQ)⟩)
  have hh := hmin R hRC
  omega

end GraphPuzzles.LoopMultigraph
