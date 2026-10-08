import GraphPuzzles.Cuts.MatchingFaces

/-!
# Cohesive collections of cuts

A collection is cohesive when each edge belongs to a perfect matching crossing
every cut in the collection once. For odd cuts, this is equivalent to the existence
of a strictly positive fractional matching on their common equality face.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

def RespectsCuts (H : LoopMultigraph V E) (M : Finset E) (C : Finset (Finset V)) : Prop :=
  ∀ X ∈ C, (M ∩ H.dangling X).card = 1

/-- Campos--Lucchesi's edge-wise definition of cohesiveness. -/
def IsCohesiveCuts (H : LoopMultigraph V E) (C : Finset (Finset V)) : Prop :=
  ∀ e, ∃ M, H.IsPerfectMatching M ∧ e ∈ M ∧ H.RespectsCuts M C

theorem IsCohesiveCuts.subset {C D : Finset (Finset V)} (hC : H.IsCohesiveCuts C) (hs : D ⊆ C) :
    H.IsCohesiveCuts D := by
  intro e
  obtain ⟨M, hM, he, hc⟩ := hC e
  exact ⟨M, hM, he, fun X hX ↦ hc X (hs hX)⟩

theorem IsCohesiveCuts.union_tight {C D : Finset (Finset V)} (hC : H.IsCohesiveCuts C)
    (hD : ∀ X ∈ D, H.IsTightCut X) : H.IsCohesiveCuts (C ∪ D) := by
  intro e
  obtain ⟨M, hM, he, hc⟩ := hC e
  refine ⟨M, hM, he, fun X hX ↦ ?_⟩
  rcases Finset.mem_union.mp hX with hX | hX
  · exact hc X hX
  · exact hD X hX M hM

/-- A separating cut and any tight cut form a cohesive pair. -/
theorem IsSeparatingCut.cohesive_pair_tight {X Y : Finset V} (hs : H.IsSeparatingCut X)
    (ht : H.IsTightCut Y) : H.IsCohesiveCuts {X, Y} := by
  intro e
  obtain ⟨M, hM, he, hm⟩ := hs.exists_perfectMatching_through e
  refine ⟨M, hM, he, ?_⟩
  intro Z hZ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
  rcases hZ with rfl | rfl
  · exact hm
  · exact ht M hM

theorem cohesive_singleton_iff_separating (hc : H.IsConnected) {X : Finset V}
    (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty) :
    H.IsCohesiveCuts {X} ↔ H.IsSeparatingCut X := by
  rw [isSeparatingCut_iff_crossing_one hc hX hXC]
  constructor
  · intro h e
    obtain ⟨M, hM, he, hm⟩ := h e
    exact ⟨M, hM, he, hm X (Finset.mem_singleton_self _)⟩
  · intro h e
    obtain ⟨M, hM, he, hm⟩ := h e
    refine ⟨M, hM, he, ?_⟩
    intro Y hY
    simpa only [Finset.mem_singleton.mp hY] using hm

/-- An equality face of odd cuts is cohesive precisely when it has positive edge weights. -/
theorem cohesive_iff_positive_fractional [Nonempty E] {C : Finset (Finset V)}
    (hodd : ∀ X ∈ C, Odd X.card) :
    H.IsCohesiveCuts C ↔ ∃ x : E → ℚ, H.IsFractionalPerfectMatching x ∧
      (∀ e, 0 < x e) ∧ ∀ X ∈ C, H.cutWeight x X = 1 := by
  classical
  constructor
  · intro hc
    choose M hM using hc
    let n : ℚ := Fintype.card E
    have hn : 0 < n := by
      change (0 : ℚ) < (Fintype.card E : ℚ)
      exact_mod_cast (show 0 < Fintype.card E from Fintype.card_pos)
    let w : E → ℚ := fun _ ↦ 1 / n
    have hw : ∀ e, 0 < w e := fun _ ↦ one_div_pos.mpr hn
    have ht : ∑ e, w e = 1 := by
      simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change n * (1 / n) = 1
      field_simp
    let x : E → ℚ := fun f ↦ ∑ e, w e * matchingVector (M e) f
    let D : H.MatchingCombination x := MatchingCombination.ofFamily M w
      (fun e ↦ (hw e).le) (fun e _ ↦ (hM e).1) ht (fun _ ↦ rfl)
    refine ⟨x, D.isFractional, ?_, ?_⟩
    · intro e
      have hle : w e * matchingVector (M e) e ≤ x e :=
        Finset.single_le_sum (fun f _ ↦ mul_nonneg (hw f).le ((hM f).1.isFractional.nonneg e))
          (Finset.mem_univ e)
      have he : matchingVector (M e) e = 1 := by simp [matchingVector, (hM e).2.1]
      rw [he, mul_one] at hle
      exact (hw e).trans_le hle
    · intro X hX
      change H.cutWeight (fun f ↦ ∑ e, w e * matchingVector (M e) f) X = 1
      rw [cutWeight_family]
      have hh (e : E) : H.cutWeight (matchingVector (M e)) X = 1 := by
        rw [cutWeight_matchingVector, (hM e).2.2 X hX]
        norm_num
      simp only [hh, mul_one]
      exact ht
  · rintro ⟨x, hx, hp, ht⟩ e
    obtain ⟨D⟩ := hx.exists_matchingCombination
    obtain ⟨M, he⟩ := D.exists_support_containing (hp e)
    exact ⟨M.1, D.support_valid M, he,
      fun X hX ↦ D.support_crossing_one (hodd X hX) (ht X hX) M⟩

/-- Inclusion of the sets of perfect matchings crossing a cut once. -/
def CutFacePrecedes (H : LoopMultigraph V E) (Y X : Finset V) : Prop :=
  ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1 → (M ∩ H.dangling Y).card = 1

theorem CutFacePrecedes.refl (X : Finset V) : H.CutFacePrecedes X X := fun _ _ h ↦ h

theorem CutFacePrecedes.trans {X Y Z : Finset V} (hXY : H.CutFacePrecedes X Y)
    (hYZ : H.CutFacePrecedes Y Z) : H.CutFacePrecedes X Z :=
  fun M hM h ↦ hXY M hM (hYZ M hM h)

theorem IsCohesiveCuts.insert_of_facePrecedes {C : Finset (Finset V)} (hC : H.IsCohesiveCuts C)
    {X Y : Finset V} (hX : X ∈ C) (hp : H.CutFacePrecedes Y X) :
    H.IsCohesiveCuts (insert Y C) := by
  intro e
  obtain ⟨M, hM, he, hm⟩ := hC e
  refine ⟨M, hM, he, fun Z hZ ↦ ?_⟩
  rcases Finset.mem_insert.mp hZ with rfl | hZ
  · exact hp M hM (hm X hX)
  · exact hm Z hZ

/-- Campos--Lucchesi's precedence relation: an inequality for every perfect matching,
not just an implication between the one-crossing faces. -/
def CutPrecedes (H : LoopMultigraph V E) (Y X : Finset V) : Prop :=
  ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling Y).card ≤ (M ∩ H.dangling X).card

theorem CutPrecedes.refl (X : Finset V) : H.CutPrecedes X X := fun _ _ ↦ le_rfl

theorem CutPrecedes.trans {X Y Z : Finset V} (hXY : H.CutPrecedes X Y)
    (hYZ : H.CutPrecedes Y Z) : H.CutPrecedes X Z :=
  fun M hM ↦ (hXY M hM).trans (hYZ M hM)

theorem CutPrecedes.facePrecedes {X Y : Finset V} (hp : H.CutPrecedes Y X)
    (hY : Odd Y.card) : H.CutFacePrecedes Y X := by
  intro M hM hm
  have hlo : 1 ≤ (M ∩ H.dangling Y).card := by
    have hh := hM.isFractional.odd_cut Y hY
    rw [cutWeight_matchingVector] at hh
    exact_mod_cast hh
  have hhi := hp M hM
  omega

theorem IsCohesiveCuts.insert_of_precedes {C : Finset (Finset V)} (hC : H.IsCohesiveCuts C)
    {X Y : Finset V} (hX : X ∈ C) (hp : H.CutPrecedes Y X) (hY : Odd Y.card) :
    H.IsCohesiveCuts (insert Y C) := hC.insert_of_facePrecedes hX (hp.facePrecedes hY)

end GraphPuzzles.LoopMultigraph
