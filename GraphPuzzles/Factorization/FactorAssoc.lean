import GraphPuzzles.Factorization.FactorNineTwo

/-!
# Cuts associated with an atom

For an atom `A` and a cycle-separating shore `Y ⊇ A` of a graph of a good class, the cut `∂Y`
meets `∂A` in `0`, `1`, `2` or `4` edges.  If it contains a couple of `∂A`, then `Y = A`: a
couple of `∂A` inside `∂Y` is a couple of `∂Y` (couple transfer), which Lemma 9.2 forbids when
`|∂A ∩ ∂Y| = 2`; three common edges are excluded by Lemma 9.1.  A shore `Y ⊇ A` is
*quasiatomic* when `Y \ A` consists of two adjacent vertices each joined to `A` by one edge.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph}

/-- `Y` is a quasiatomic shore for `A`: it consists of `A` and two adjacent vertices, each of
which sends exactly one edge to `A`. -/
def IsQuasiatomic (Δ : FinGraph) (A Y : Finset ℕ) : Prop :=
  A ⊆ Y ∧ ∃ v₁ v₂, v₁ ≠ v₂ ∧ Y \ A = {v₁, v₂} ∧ (Δ.between {v₁} {v₂}).card = 1 ∧
    (Δ.between A {v₁}).card = 1 ∧ (Δ.between A {v₂}).card = 1

/-- The four ways a cut can be associated with an atom. -/
def IsAssociated (Δ : FinGraph) (A Y : Finset ℕ) : Prop :=
  Y = A ∨ Y = Δ.Vs \ A ∨ Δ.IsQuasiatomic A Y ∨ Δ.IsQuasiatomic A (Δ.Vs \ Y)

section Inter

variable {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ)
include hG hΔ

/-- Two common boundary edges of `A ⊆ Y` cannot form a couple of `∂A` (as positions of the
`A`-pole): they would be a couple of `∂Y`, contradicting Lemma 9.2. -/
theorem not_couple_of_bdA {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hPA : (Δ.pole A).IsPole4) (hPY : (Δ.pole Y).IsPole4) {i₁ i₂ : Fin 4}
    (hi : i₁ ≠ i₂) (h₁ : bdEmb hPA i₁ ∈ Δ.bd Y) (h₂ : bdEmb hPA i₂ ∈ Δ.bd Y) {mA : Fin 3}
    (hmA : IsoWith hPA mA ∨ HetWith hPA mA) (hpair : pairing mA i₁ = i₂) : False := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  have hc4 := hG.cyc4 Δ hΔ
  -- the positions in the `Y`-pole
  obtain ⟨k₁, hk₁⟩ := exists_bdEmb_eq hPY (dangling_pole Y ▸ h₁)
  obtain ⟨k₂, hk₂⟩ := exists_bdEmb_eq hPY (dangling_pole Y ▸ h₂)
  have hk : k₁ ≠ k₂ := by
    intro h
    rw [h, hk₂] at hk₁
    exact hi (bdEmb_injective hPA hk₁.symm)
  -- the intersection has exactly two edges
  have hcard : (Δ.bd A ∩ Δ.bd Y).card = 2 := by
    have h3 := IsAtom.card_inter_ne_three hcl hcub hg hc4 hA hY
    have hle : (Δ.bd A ∩ Δ.bd Y).card ≤ 4 := by
      rw [← hA.1.2.1]; exact Finset.card_le_card Finset.inter_subset_left
    have h2 : 2 ≤ (Δ.bd A ∩ Δ.bd Y).card := by
      have : ({bdEmb hPA i₁, bdEmb hPA i₂} : Finset ℕ) ⊆ Δ.bd A ∩ Δ.bd Y := by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨dangling_pole A ▸ bdEmb_mem hPA i₁, h₁⟩
        · exact Finset.mem_inter.mpr ⟨dangling_pole A ▸ bdEmb_mem hPA i₂, h₂⟩
      have := Finset.card_le_card this
      rw [Finset.card_pair (fun h ↦ hi (bdEmb_injective hPA h))] at this
      exact this
    have h4 : (Δ.bd A ∩ Δ.bd Y).card ≠ 4 := by
      intro h4
      -- then `∂A ⊆ ∂Y`, so `Y \ A` has empty boundary and `Y = A`
      have hsub : Δ.bd A ⊆ Δ.bd Y := by
        have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := Δ.bd A)
          (s₂ := Δ.bd Y)) (by rw [h4, hA.1.2.1])
        intro e he
        rw [← this] at he
        exact (Finset.mem_inter.mp he).2
      have hcard0 := card_bd_sdiff hcl hAY hY.1 hA.1.2.1 hY.2.1
      rw [Finset.inter_eq_left.mpr hsub, hA.1.2.1] at hcard0
      have hK0 : (Δ.bd (Y \ A)).card = 0 := by omega
      have hKne : (Y \ A).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h) hAY)
      have hKV : Y \ A ⊆ Δ.Vs := Finset.sdiff_subset.trans hY.1
      by_cases hKc : Δ.HasCycle (Y \ A)
      · have hcompl : Δ.HasCycle (Δ.Vs \ (Y \ A)) := by
          apply hA.1.2.2.1.mono
          intro v hv
          exact Finset.mem_sdiff.mpr ⟨hA.1.1 hv, fun h ↦ (Finset.mem_sdiff.mp h).2 hv⟩
        have := hc4 _ hKV hKc hcompl
        omega
      · have h1 := card_add_two_le_card_bd hcub hKV hKne hKc
        omega
    omega
  -- transfer the couple to the `Y`-pole
  have htr := couple_transfer hAY hPA hPY hi hk hk₁.symm hk₂.symm hpair
  rcases hmA with hiso | hhet
  · exact no_couple_in_cut hG hΔ hA.1 hY hAY hne hPY (hk₁ ▸ dangling_pole A ▸ bdEmb_mem hPA i₁)
      (hk₂ ▸ dangling_pole A ▸ bdEmb_mem hPA i₂) hcard (Or.inl (htr.1 hiso))
      (pairing_pairOf k₁ k₂ hk)
  · exact no_couple_in_cut hG hΔ hA.1 hY hAY hne hPY (hk₁ ▸ dangling_pole A ▸ bdEmb_mem hPA i₁)
      (hk₂ ▸ dangling_pole A ▸ bdEmb_mem hPA i₂) hcard (Or.inr (htr.2 hhet))
      (pairing_pairOf k₁ k₂ hk)

end Inter

end FinGraph
end GraphPuzzles

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph}

section Cases

variable {P : FinGraph → Prop} (hG : GoodClass P) (hΔ : P Δ)
include hG hΔ

/-- The factor at a cycle-separating shore of a class graph is a cap or a join, with the
corresponding datum and class membership. -/
theorem factor_cases {Y : Finset ℕ} (hY : Δ.CycSep Y) :
    ∃ (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3),
      (IsoWith hPY m ∧ HetWith hPYc m ∧ factorOf Δ Y = cap hPY m ∧ P (cap hPY m) ∧
        factorOf Δ (Δ.Vs \ Y) = join hPYc m ∧ P (join hPYc m)) ∨
      (HetWith hPY m ∧ IsoWith hPYc m ∧ factorOf Δ Y = join hPY m ∧ P (join hPY m) ∧
        factorOf Δ (Δ.Vs \ Y) = cap hPYc m ∧ P (cap hPYc m)) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hYc := cycSep_compl hcl hY
  have hPY := hY.isPole4 hcub
  have hPYc := hYc.isPole4 hcub
  have hcolY := hG.pole_colourable Δ hΔ Y hY
  have hcolYc := hG.pole_colourable Δ hΔ _ hYc
  obtain ⟨m, hm⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPY hPYc hcolY hcolYc
  refine ⟨hPY, hPYc, m, ?_⟩
  rcases hm with ⟨hiso, hhet⟩ | ⟨hhet, hiso⟩
  · left
    have hv : Δ.ValidDatum Y m := ⟨hY, ⟨hPY, hiso⟩, ⟨hPYc, hhet⟩⟩
    exact ⟨hiso, hhet, factorOf_eq_cap hPY hcolY hiso, hG.cap_mem Δ hΔ Y m hPY hv,
      factorOf_eq_join hPYc hcolYc hhet, hG.join_mem Δ hΔ Y m hPYc hv⟩
  · right
    have e : Δ.Vs \ (Δ.Vs \ Y) = Y := Finset.sdiff_sdiff_eq_self hY.1
    have hP' : (Δ.pole (Δ.Vs \ (Δ.Vs \ Y))).IsPole4 := by rw [e]; exact hPY
    have key : ∀ (X₁ X₂ : Finset ℕ) (h : X₁ = X₂) (hP₁ : (Δ.pole X₁).IsPole4)
        (hP₂ : (Δ.pole X₂).IsPole4), HetWith hP₁ m → HetWith hP₂ m := by
      intro X₁ X₂ h hP₁ hP₂ hk
      subst h
      exact hk
    have hv : Δ.ValidDatum (Δ.Vs \ Y) m := ⟨hYc, ⟨hPYc, hiso⟩, ⟨hP', key _ _ e.symm hPY hP' hhet⟩⟩
    have hj := hG.join_mem Δ hΔ (Δ.Vs \ Y) m hP' hv
    rw [join_congr e hP' hPY rfl] at hj
    exact ⟨hhet, hiso, factorOf_eq_join hPY hcolY hhet, hj, factorOf_eq_cap hPYc hcolYc hiso,
      hG.cap_mem Δ hΔ _ m hPYc hv⟩

end Cases

section Counting

variable (hcl : Δ.IsClosed) (hcub : Δ.IsCubic) (hg : Δ.Girth5) (hc4 : Δ.Cyc4Conn)
include hcl hcub hg hc4

omit hcl hcub hg hc4 in
/-- The boundary degree bounds the number of edges to the other side at a vertex. -/
theorem card_between_singleton_le {Y : Finset ℕ} {v : ℕ} (hv : v ∈ Y) :
    (Δ.between {v} (Δ.Vs \ Y)).card ≤ Δ.degIn (Δ.bd Y) v := by
  unfold degIn
  apply Finset.card_le_card_of_injOn (fun e ↦ (e, if Δ.ends e 0 = v then 0 else 1))
  · intro e he
    rw [Finset.mem_coe, mem_between] at he
    rw [Finset.mem_coe, mem_halfEdgesIn]
    refine ⟨?_, ?_⟩
    · rw [mem_bd]
      refine ⟨he.1, ?_⟩
      rcases he.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [Finset.mem_singleton] at h0
        exact fun h ↦ (Finset.mem_sdiff.mp h1).2 (h.mp (h0 ▸ hv))
      · rw [Finset.mem_singleton] at h1
        exact fun h ↦ (Finset.mem_sdiff.mp h0).2 (h.mpr (h1 ▸ hv))
    · rcases he.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [Finset.mem_singleton] at h0
        simp [h0]
      · rw [Finset.mem_singleton] at h1
        have h0' : Δ.ends e 0 ≠ v := fun h ↦ (Finset.mem_sdiff.mp h0).2 (h ▸ hv)
        simp [h0', h1]
  · intro e _ e' _ h
    exact congrArg Prod.fst h

omit hcl hcub hc4 in
/-- No two parallel edges between distinct vertices. -/
theorem card_between_singletons_le {v w : ℕ} (_hv : v ∈ Δ.Vs) (_hvw : v ≠ w) :
    (Δ.between {v} {w}).card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp h
  apply absurd (hg {e, f} ?_ (Finset.insert_nonempty _ _) ?_)
  · rw [Finset.card_pair hef]
    omega
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact between_subset _ _ he
    · exact between_subset _ _ hf
  · intro u _
    rw [degIn_eq_sum, Finset.sum_pair hef]
    rw [mem_between] at he hf
    -- both edges have one end at `v` and one at `w`
    have key : ∀ g ∈ Δ.between {v} {w},
        ((if Δ.ends g 0 = u then 1 else 0) + (if Δ.ends g 1 = u then 1 else 0)) =
          (if v = u then 1 else 0) + (if w = u then 1 else 0) := by
      intro g hg'
      rw [mem_between] at hg'
      rcases hg'.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [Finset.mem_singleton] at h0 h1
        rw [h0, h1]
      · rw [Finset.mem_singleton] at h0 h1
        rw [h0, h1, add_comm]
    rw [key e (mem_between.mpr he), key f (mem_between.mpr hf)]
    exact ⟨(if v = u then 1 else 0) + (if w = u then 1 else 0), by ring⟩

end Counting

end FinGraph
end GraphPuzzles
