import GraphPuzzles.Factorization.Bicritical.FactorCutEdges
import GraphPuzzles.Factorization.Bicritical.FactorAdjacent
import GraphPuzzles.Factorization.Bicritical.FactorCapColouring
import GraphPuzzles.Factorization.Bicritical.FactorJoinColouring
import Mathlib.Tactic.LinearCombination

/-!
# Bicriticality of the cap factor, I: the adjacent case

Facts about the ends of the cut edges of a cycle-separating `4`-cut in a bicritical snark, the
"other couple" parity argument, and the case of a pair `{u, x}` with `x` the inner end of a cut
edge attached to the new vertex `u` (Chladný–Škoviera, Theorem 4.6).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Positions

variable (m : Fin 3)

theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, pairing m 0, other m, pairing m (other m)} := by
  revert m; decide

theorem zero_notMem_three : (0 : Fin 4) ∉ ({pairing m 0, other m, pairing m (other m)} : Finset (Fin 4)) := by
  revert m; decide

theorem pairing_zero_notMem_two : pairing m 0 ∉ ({other m, pairing m (other m)} : Finset (Fin 4)) := by
  revert m; decide

theorem other_ne_pairing_other : other m ≠ pairing m (other m) := by
  revert m; decide

theorem bdEmb_other_notMem_couple₁ {P : FinGraph} (hP : P.IsPole4) :
    bdEmb hP (other m) ∉ couple₁ hP m := by
  rw [couple₁, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · exact other_ne_zero m (bdEmb_injective hP h)
  · exact other_ne_pairing_zero m (bdEmb_injective hP h)

theorem bdEmb_pairing_other_notMem_couple₁ {P : FinGraph} (hP : P.IsPole4) :
    bdEmb hP (pairing m (other m)) ∉ couple₁ hP m := by
  rw [couple₁, Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · exact pairing_other_ne_zero m (bdEmb_injective hP h)
  · exact pairing_other_ne_pairing_zero m (bdEmb_injective hP h)

/-- The boundary sum as the sum over the four positions. -/
theorem sum_bd_four {Δ : FinGraph} {Y : Finset ℕ} (hPY : (Δ.pole Y).IsPole4) (c : ℕ → Color) :
    ∑ e ∈ Δ.bd Y, c e = c (bdEmb hPY 0) + c (bdEmb hPY (pairing m 0)) +
      c (bdEmb hPY (other m)) + c (bdEmb hPY (pairing m (other m))) := by
  rw [← dangling_pole, dangling_eq_image hPY,
    Finset.sum_image (fun a _ b _ h ↦ bdEmb_injective hPY h), univ_four m,
    Finset.sum_insert (zero_notMem_three m), Finset.sum_insert (pairing_zero_notMem_two m),
    Finset.sum_pair (other_ne_pairing_other m)]
  abel

/-- If the colours of the three cut edges other than `d` sum to zero and are nonzero, the couple
not containing `d` is coloured with two distinct colours. -/
theorem other_couple_ne {Δ : FinGraph} {Y : Finset ℕ} (hPY : (Δ.pole Y).IsPole4) {c : ℕ → Color}
    {d : ℕ} (hd : d ∈ Δ.bd Y) (hsum : ∑ e ∈ (Δ.bd Y).erase d, c e = 0)
    (hnz : ∀ e ∈ (Δ.bd Y).erase d, c e ≠ 0) :
    (d ∈ couple₁ hPY m → c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m)))) ∧
      (d ∉ couple₁ hPY m → c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0))) := by
  have htot := Finset.add_sum_erase (Δ.bd Y) c hd
  rw [hsum, add_zero, sum_bd_four m hPY] at htot
  have hdd : d ∈ (Δ.pole Y).dangling := by rw [dangling_pole]; exact hd
  have hmem : ∀ k, bdEmb hPY k ≠ d → bdEmb hPY k ∈ (Δ.bd Y).erase d := by
    intro k hk
    rw [Finset.mem_erase]
    exact ⟨hk, by rw [← dangling_pole]; exact bdEmb_mem hPY k⟩
  constructor
  · intro hd₁
    have hno : bdEmb hPY (other m) ≠ d := fun h ↦ bdEmb_other_notMem_couple₁ m hPY (h ▸ hd₁)
    have hno' : bdEmb hPY (pairing m (other m)) ≠ d :=
      fun h ↦ bdEmb_pairing_other_notMem_couple₁ m hPY (h ▸ hd₁)
    rw [couple₁, Finset.mem_insert, Finset.mem_singleton] at hd₁
    rcases hd₁ with rfl | rfl
    · have hp : bdEmb hPY (pairing m 0) ≠ bdEmb hPY 0 :=
        fun h ↦ pairing_ne m 0 (bdEmb_injective hPY h)
      have h3 : c (bdEmb hPY (pairing m 0)) + c (bdEmb hPY (other m)) +
          c (bdEmb hPY (pairing m (other m))) = 0 := by
        linear_combination (-1 : Color) * htot
      exact ne_of_add_three_eq_zero (hnz _ (hmem _ hp)) (hnz _ (hmem _ hno))
        (hnz _ (hmem _ hno')) h3
    · have hp : bdEmb hPY 0 ≠ bdEmb hPY (pairing m 0) :=
        fun h ↦ pairing_ne m 0 (bdEmb_injective hPY h.symm)
      have h3 : c (bdEmb hPY 0) + c (bdEmb hPY (other m)) +
          c (bdEmb hPY (pairing m (other m))) = 0 := by
        linear_combination (-1 : Color) * htot
      exact ne_of_add_three_eq_zero (hnz _ (hmem _ hp)) (hnz _ (hmem _ hno))
        (hnz _ (hmem _ hno')) h3
  · intro hd₁
    have hd₂ : d ∈ couple₂ hPY m := (mem_couple₂_iff hPY m hdd).mpr hd₁
    have hno : bdEmb hPY 0 ≠ d := fun h ↦ hd₁ (h ▸ Finset.mem_insert_self _ _)
    have hno' : bdEmb hPY (pairing m 0) ≠ d :=
      fun h ↦ hd₁ (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [couple₂, Finset.mem_insert, Finset.mem_singleton] at hd₂
    rcases hd₂ with rfl | rfl
    · have hp : bdEmb hPY (pairing m (other m)) ≠ bdEmb hPY (other m) :=
        fun h ↦ pairing_ne m _ (bdEmb_injective hPY h)
      have h3 : c (bdEmb hPY (pairing m (other m))) + c (bdEmb hPY 0) +
          c (bdEmb hPY (pairing m 0)) = 0 := by
        linear_combination (-1 : Color) * htot
      exact ne_of_add_three_eq_zero (hnz _ (hmem _ hp)) (hnz _ (hmem _ hno))
        (hnz _ (hmem _ hno')) h3
    · have hp : bdEmb hPY (other m) ≠ bdEmb hPY (pairing m (other m)) :=
        fun h ↦ pairing_ne m _ (bdEmb_injective hPY h.symm)
      have h3 : c (bdEmb hPY (other m)) + c (bdEmb hPY 0) +
          c (bdEmb hPY (pairing m 0)) = 0 := by
        linear_combination (-1 : Color) * htot
      exact ne_of_add_three_eq_zero (hnz _ (hmem _ hp)) (hnz _ (hmem _ hno))
        (hnz _ (hmem _ hno')) h3

end Positions

section Ends

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hY : Y ⊆ Δ.Vs)
  (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4)

include hcl in
theorem bdEmb_eq_compl (k : Fin 4) : bdEmb hPY k = bdEmb hPYc k :=
  bdEmb_congr hPY hPYc (by rw [dangling_pole, dangling_pole, bd_compl hcl]) k

theorem mem_dangling_Y {d : ℕ} (hd : d ∈ Δ.bd Y) : d ∈ (Δ.pole Y).dangling := by
  rw [dangling_pole]; exact hd

include hcl in
theorem mem_dangling_compl {d : ℕ} (hd : d ∈ Δ.bd Y) : d ∈ (Δ.pole (Δ.Vs \ Y)).dangling := by
  rw [dangling_pole, bd_compl hcl]; exact hd

theorem innerEnd_Y_mem {d : ℕ} (hd : d ∈ Δ.bd Y) : innerEnd hPY d ∈ Y :=
  innerEnd_mem hPY (mem_dangling_Y hd)

include hcl in
theorem innerEnd_compl_mem {d : ℕ} (hd : d ∈ Δ.bd Y) : innerEnd hPYc d ∈ Δ.Vs \ Y :=
  innerEnd_mem hPYc (mem_dangling_compl hcl hd)

theorem ends_innerEnd_Y {d : ℕ} (hd : d ∈ Δ.bd Y) : ∃ i, Δ.ends d i = innerEnd hPY d :=
  ⟨_, ends_innerIdx hPY (mem_dangling_Y hd)⟩

include hcl in
theorem ends_innerEnd_compl {d : ℕ} (hd : d ∈ Δ.bd Y) : ∃ i, Δ.ends d i = innerEnd hPYc d :=
  ⟨_, ends_innerIdx hPYc (mem_dangling_compl hcl hd)⟩

theorem innerEnd_Y_inj (hind : Δ.IsIndependentCut Y) {d d' : ℕ} (hd : d ∈ Δ.bd Y)
    (hd' : d' ∈ Δ.bd Y) (h : innerEnd hPY d = innerEnd hPY d') : d = d' := by
  obtain ⟨i, hi⟩ := ends_innerEnd_Y hPY hd
  obtain ⟨j, hj⟩ := ends_innerEnd_Y hPY hd'
  exact hind.eq_of_ends hd hd' (hi.trans (h.trans hj.symm))

include hcl in
theorem innerEnd_compl_inj (hind : Δ.IsIndependentCut Y) {d d' : ℕ} (hd : d ∈ Δ.bd Y)
    (hd' : d' ∈ Δ.bd Y) (h : innerEnd hPYc d = innerEnd hPYc d') : d = d' := by
  obtain ⟨i, hi⟩ := ends_innerEnd_compl hcl hPYc hd
  obtain ⟨j, hj⟩ := ends_innerEnd_compl hcl hPYc hd'
  exact hind.eq_of_ends hd hd' (hi.trans (h.trans hj.symm))

include hcl in
/-- A cut edge other than `d` is an edge of the pole avoiding a vertex of `Y` and the outer end
of `d`. -/
theorem cut_mem_pole (hind : Δ.IsIndependentCut Y) {d a x : ℕ} (hd : d ∈ Δ.bd Y) (ha : a ∈ Δ.bd Y)
    (had : a ≠ d) (hx : x ∈ Y) : a ∈ (Δ.pole (Δ.Vs \ {x, innerEnd hPYc d})).Es := by
  obtain ⟨i, hi⟩ := ends_innerEnd_compl hcl hPYc ha
  have hmem := innerEnd_compl_mem hcl hPYc ha
  rw [pole_Es, Finset.mem_union]
  apply mem_edgesIn_or_bd (bd_subset Y ha) (i := i)
  rw [hi, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨(Finset.mem_sdiff.mp hmem).1, ?_⟩
  rintro (h | h)
  · exact (Finset.mem_sdiff.mp hmem).2 (h ▸ hx)
  · exact had (innerEnd_compl_inj hcl hPYc hind ha hd h)

end Ends

section Adjacent

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hcub : Δ.IsCubic)
  (hnc : ¬ Δ.Colourable) (hg5 : Δ.Girth5) (hY : Y ⊆ Δ.Vs) (hind : Δ.IsIndependentCut Y)
  (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)
include hcl hcub hnc hg5 hY hind

/-- **The adjacent case.**  For a cut edge `d` with inner end `x` and outer end `y`, any
colouring of the pole avoiding `x` and `y` colours the couple not containing `d` with two
distinct colours. -/
theorem other_couple_ne_of_adjacent {d : ℕ} (hd : d ∈ Δ.bd Y) {c : ℕ → Color}
    (hc : (Δ.pole (Δ.Vs \ {innerEnd hPY d, innerEnd hPYc d})).IsColouring c) :
    (d ∈ couple₁ hPY m → c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m)))) ∧
      (d ∉ couple₁ hPY m → c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0))) := by
  have hloop : ∀ e ∈ Δ.Es, Δ.ends e 0 ≠ Δ.ends e 1 := fun e he ↦ hg5.no_loop he (hcl e he 0)
  set x := innerEnd hPY d with hxdef
  set y := innerEnd hPYc d with hydef
  have hxY : x ∈ Y := innerEnd_Y_mem hPY hd
  have hyV : y ∈ Δ.Vs \ Y := innerEnd_compl_mem hcl hPYc hd
  have hxy : x ≠ y := fun h ↦ (Finset.mem_sdiff.mp hyV).2 (h ▸ hxY)
  obtain ⟨jx, hjx⟩ := ends_innerEnd_Y hPY hd
  obtain ⟨jy, hjy⟩ := ends_innerEnd_compl hcl hPYc hd
  have hdE : d ∈ Δ.Es := bd_subset Y hd
  have hjxy : jx ≠ jy := by
    rintro rfl
    exact hxy (hjx.symm.trans hjy)
  have hjoin : Δ.Joins d x y := by
    have hx0 : jx = 0 ∨ jx = 1 := by omega
    rcases hx0 with rfl | rfl
    · rw [fin2_eq_rev_of_ne hjxy.symm, Iso.rev_zero'] at hjy
      exact Or.inl ⟨hjx, hjy⟩
    · rw [fin2_eq_rev_of_ne hjxy.symm, Iso.rev_one'] at hjy
      exact Or.inr ⟨hjy, hjx⟩
  -- the two other edges at `x` and the boundary of `Y.erase x`
  obtain ⟨g₁, g₂, hg₁, hg₂, h12, h1d, h2d, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, hbd⟩ :=
    bd_erase_of_cut hcub hloop hY hind hd (j := jx) (hjx ▸ hxY)
  rw [hjx] at hi₁ hi₂ hbd
  have hg₁E : g₁ ∈ Δ.Es := edgesIn_subset Y hg₁
  have hg₂E : g₂ ∈ Δ.Es := edgesIn_subset Y hg₂
  -- the two edges at `x` receive the same colour
  have heq : c g₁ = c g₂ :=
    adjacent_colour_eq hcl hcub hnc hg5 (hY hxY) (Finset.mem_sdiff.mp hyV).1 hxy hdE hjoin
      hg₁E hg₂E h12 h1d h2d hi₁ hi₂ hc
  -- the parity of the pole `Y.erase x`
  have hsub : Y.erase x ⊆ Δ.Vs \ {x, y} := by
    intro v hv
    rw [Finset.mem_erase] at hv
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hY hv.2, by rintro (rfl | rfl); exact hv.1 rfl; exact (Finset.mem_sdiff.mp hyV).2 hv.2⟩
  have hsum := (hc.restrict hsub).sum_bd_eq_zero hcub ((Finset.erase_subset x Y).trans hY)
  have hg₁bd : g₁ ∉ Δ.bd Y := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) hg₁ h
  have hg₂bd : g₂ ∉ Δ.bd Y := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) hg₂ h
  rw [hbd, Finset.sum_insert (by
      rw [Finset.mem_insert, Finset.mem_erase]; rintro (h | ⟨-, h⟩); exact h12 h; exact hg₁bd h),
    Finset.sum_insert (by rw [Finset.mem_erase]; rintro ⟨-, h⟩; exact hg₂bd h), ← add_assoc,
    heq, color_add_self, zero_add] at hsum
  -- the three other cut edges are edges of the pole
  have hnz : ∀ e ∈ (Δ.bd Y).erase d, c e ≠ 0 := by
    intro e he
    rw [Finset.mem_erase] at he
    exact hc.1 e (cut_mem_pole hcl hPYc hind hd he.2 he.1 hxY)
  exact other_couple_ne m hPY hd hsum hnz

end Adjacent

end FinGraph
end GraphPuzzles
