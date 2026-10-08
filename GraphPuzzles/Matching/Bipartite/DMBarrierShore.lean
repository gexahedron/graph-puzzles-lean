import GraphPuzzles.Matching.Bipartite.DulmageMendelsohn
import GraphPuzzles.Cuts.InadmissibleCut

/-!
# The DM-barrier shore lemma

Carvalho--Lucchesi--Murty's key lemma: a nonempty proper inadmissible cut
with both induced shores connected has a DM-barrier and all of its odd
components on the same shore.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X B : Finset V}

namespace ComponentFamily

variable (F : H.ComponentFamily B)

/-- If an odd DM component misses a vertex of each connected shore, it cannot
meet both shores of an inadmissible cut. -/
theorem IsDMBarrier.odd_part_one_shore (hd : F.IsDMBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hn : H.IsInadmissibleCut X)
    (hcX : H.IsConnectedOn X) (hcXC : H.IsConnectedOn (Finset.univ \ X))
    {Q : Finset V} (hQ : Q ∈ F.odd) {u v : V}
    (huX : u ∈ X) (huQ : u ∉ Q) (hvX : v ∉ X) (hvQ : v ∉ Q) :
    Q ⊆ X ∨ Q ⊆ Finset.univ \ X := by
  by_contra hno
  have hL : ¬ Q ⊆ X := fun h ↦ hno (Or.inl h)
  have hR : ¬ Q ⊆ Finset.univ \ X := fun h ↦ hno (Or.inr h)
  obtain ⟨a, haQ, haX⟩ := Finset.not_subset.mp hL
  obtain ⟨b, hbQ, hbXC⟩ := Finset.not_subset.mp hR
  have hbX : b ∈ X := by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hbXC
  obtain ⟨e, k, hkQ, hkX, hrQ, _⟩ := hcX.exists_boundary_within hbX hbQ huX huQ
  have heQ : e ∈ H.dangling Q := by
    apply mem_dangling.mpr
    fin_cases k <;> simp_all
  obtain ⟨N, hN, heN⟩ := hd.edge_admissible F hM hQ heQ
  have hoX := hn.odd_inter_of_tight_boundary (hd.isBarrier.isTightCut F hQ) hN heN heQ hkX
  have haXC : a ∈ Finset.univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haX⟩
  have hvXC : v ∈ Finset.univ \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvX⟩
  obtain ⟨f, j, hjQ, hjX, hrQ', _⟩ := hcXC.exists_boundary_within haXC haQ hvXC hvQ
  have hfQ : f ∈ H.dangling Q := by
    apply mem_dangling.mpr
    fin_cases j <;> simp_all
  obtain ⟨P, hP, hfP⟩ := hd.edge_admissible F hM hQ hfQ
  have hoXC := hn.compl.odd_inter_of_tight_boundary (hd.isBarrier.isTightCut F hQ) hP hfP hfQ hjX
  have hpart : Q ∩ (Finset.univ \ X) = Q \ X := by ext w; simp
  rw [hpart] at hoXC
  have hcount := Finset.card_inter_add_card_sdiff Q X
  have hoQ := (F.mem_odd.mp hQ).2
  rw [Nat.odd_iff] at hoX hoXC hoQ
  omega

/-- Once each odd component is on a shore, the connected admissible core
forces the barrier and every odd component onto one common shore. -/
theorem IsDMBarrier.one_shore_of_parts (hd : F.IsDMBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hn : H.IsInadmissibleCut X)
    (hs : ∀ Q ∈ F.odd, Q ⊆ X ∨ Q ⊆ Finset.univ \ X) :
    (B ⊆ X ∧ ∀ Q ∈ F.odd, Q ⊆ X) ∨
      (B ⊆ Finset.univ \ X ∧ ∀ Q ∈ F.odd, Q ⊆ Finset.univ \ X) := by
  classical
  let cA : F.odd → Bool := fun Q ↦ decide (Q.1 ⊆ X)
  let cB : B → Bool := fun z ↦ decide (z.1 ∈ X)
  have hc (Q : F.odd) (z : B) (hqz : z ∈ F.coreNeighbors Q) : cA Q = cB z := by
    obtain ⟨e, k, hk, hz⟩ := (F.mem_coreNeighbors Q z).mp hqz
    have hnot : H.endAt e (Fin.rev k) ∉ Q.1 := fun h ↦
      F.avoid Q.1 (F.mem_odd.mp Q.2).1 _ h (hz.symm ▸ z.2)
    have heQ : e ∈ H.dangling Q.1 := by
      apply mem_dangling.mpr
      fin_cases k <;> simp_all
    obtain ⟨N, hN, heN⟩ := hd.edge_admissible F hM Q.2 heQ
    have hedge : H.endAt e k ∈ X ↔ z.1 ∈ X := by
      have hh := hn.mem_iff hN heN
      fin_cases k
      · exact hh.trans (by rw [← hz]; rfl)
      · exact hh.symm.trans (by rw [← hz]; rfl)
    by_cases hQX : Q.1 ⊆ X
    · have hzX := hedge.mp (hQX hk)
      simp [cA, cB, hQX, hzX]
    · have hQXC : Q.1 ⊆ Finset.univ \ X := (hs Q.1 Q.2).resolve_left hQX
      have hzX : z.1 ∉ X := fun h ↦ (Finset.mem_sdiff.mp (hQXC hk)).2 (hedge.mpr h)
      simp [cA, cB, hQX, hzX]
  have hconn := hd.coreConnected cA cB hc
  obtain ⟨z₀, hz₀⟩ := hd.nonempty
  let z : B := ⟨z₀, hz₀⟩
  have hodd : F.odd.Nonempty := Finset.card_pos.mp (by
    have hb : F.odd.card = B.card := hd.isBarrier
    rw [hb]
    exact Finset.card_pos.mpr hd.nonempty)
  obtain ⟨Q₀, hQ₀⟩ := hodd
  let q : F.odd := ⟨Q₀, hQ₀⟩
  have hBcol (w : B) : cB w = cB z := (hconn q w).symm.trans (hconn q z)
  by_cases hzX : z₀ ∈ X
  · left
    constructor
    · intro w hw
      have hh := hBcol ⟨w, hw⟩
      simpa [cB, z, hzX] using hh
    · intro Q hQ
      have hh := hconn ⟨Q, hQ⟩ z
      simpa [cA, cB, z, hzX] using hh
  · right
    constructor
    · intro w hw
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hh := hBcol ⟨w, hw⟩
      simpa [cB, z, hzX] using hh
    · intro Q hQ
      have hh := hconn ⟨Q, hQ⟩ z
      have hnQ : ¬ Q ⊆ X := by
        simpa [cA, cB, z, hzX] using hh
      exact (hs Q hQ).resolve_left hnQ

end ComponentFamily

/-- Carvalho--Lucchesi--Murty's key lemma (Theorem 2.4): an inadmissible cut
with nonempty connected shores has a DM-barrier and all its odd components
contained in one of those shores. -/
theorem IsInadmissibleCut.exists_DMBarrier_in_shore (hn : H.IsInadmissibleCut X)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hX : X.Nonempty)
    (hXC : (Finset.univ \ X).Nonempty)
    (hcX : H.IsConnectedOn X) (hcXC : H.IsConnectedOn (Finset.univ \ X)) :
    ∃ B, ∃ F : H.ComponentFamily B, F.IsDMBarrier ∧
      ((B ⊆ X ∧ ∀ Q ∈ F.odd, Q ⊆ X) ∨
        (B ⊆ Finset.univ \ X ∧ ∀ Q ∈ F.odd, Q ⊆ Finset.univ \ X)) := by
  obtain ⟨Z₀, hZ₀X, hZ₀XC, F₀, hF₀⟩ := hn.exists_barrier_meets_shores hM hX hXC
  obtain ⟨Z, hZ₀Z, F, hm⟩ := hF₀.exists_maximal
  obtain ⟨u, hu⟩ := hZ₀X
  obtain ⟨v, hv⟩ := hZ₀XC
  obtain ⟨huZ₀, huX⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvZ₀, hvX⟩ := Finset.mem_sdiff.mp hv
  have huZ := hZ₀Z huZ₀
  have hvZ := hZ₀Z hvZ₀
  obtain ⟨B, _, P, hd, hparts⟩ := hm.exists_DMBarrier_retaining F hM ⟨u, huZ⟩
  refine ⟨B, P, hd, hd.one_shore_of_parts P hM hn ?_⟩
  intro Q hQ
  have hQF := (F.mem_odd.mp (hparts hQ)).1
  exact hd.odd_part_one_shore P hM hn hcX hcXC hQ huX
    (fun h ↦ F.avoid Q hQF u h huZ) hvX (fun h ↦ F.avoid Q hQF v h hvZ)

end GraphPuzzles.LoopMultigraph
