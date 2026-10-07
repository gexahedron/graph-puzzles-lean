import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap
import GraphPuzzles.Factorization.Diamond.FactorCanon

/-!
# Factors are snarks; the join-side colouring transfer

* `not_colourable_cap_of_isoWith`: the cap of an isochromatic pole is uncolourable.
* `not_colourable_join_of_hetWith`: the join of a heterochromatic pole is uncolourable.
* `join_transfer`: a colouring of a pole `W ⊇ X` of `Δ`, with `X` isochromatic, yields a
  colouring of the pole `W \ X` of the join of the complementary pole (Chladný–Škoviera,
  Proposition 4.3, one direction).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Factors

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

/-- The boundary position of a dangling edge. -/
noncomputable def bdIdx (d : ℕ) : Fin 4 :=
  if h : d ∈ P.dangling then (exists_bdEmb_eq hP h).choose else 0

theorem bdEmb_bdIdx {d : ℕ} (hd : d ∈ P.dangling) : bdEmb hP (bdIdx hP d) = d := by
  unfold bdIdx
  rw [dif_pos hd]
  exact (exists_bdEmb_eq hP hd).choose_spec

theorem bdIdx_bdEmb (k : Fin 4) : bdIdx hP (bdEmb hP k) = k :=
  bdEmb_injective hP (bdEmb_bdIdx hP (bdEmb_mem hP k))

/-- **The cap of an isochromatic pole is uncolourable.** -/
theorem not_colourable_cap_of_isoWith (hiso : IsoWith hP m) : ¬ (cap hP m).Colourable := by
  rintro ⟨c, hc⟩
  have hcP : P.IsColouring c := by
    refine ⟨fun e he ↦ hc.1 e (by rw [cap_Es]; exact Finset.mem_insert_of_mem he), ?_⟩
    intro v hv h₁ h₁m h₂ h₂m heq
    rw [← cap_halfEdges_old hP m hv] at h₁m h₂m
    exact hc.2 v (by rw [cap_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
      h₁ h₁m h₂ h₂m heq
  have ht := hiso (tvec hP c) ⟨c, hcP, rfl⟩ 0
  have hu : freshV P ∈ (cap hP m).Vs := by rw [cap_Vs]; exact Finset.mem_insert_self _ _
  have h₁m : (bdEmb hP 0, outerIdx hP (bdEmb hP 0)) ∈
      (cap hP m).halfEdgesIn (cap hP m).Es (freshV P) := by
    rw [cap_halfEdges_u]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  have h₂m : (bdEmb hP (pairing m 0), outerIdx hP (bdEmb hP (pairing m 0))) ∈
      (cap hP m).halfEdgesIn (cap hP m).Es (freshV P) := by
    rw [cap_halfEdges_u]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have := hc.unique_halfEdge hu h₁m h₂m ht
  exact pairing_ne m 0 (bdEmb_injective hP (congrArg Prod.fst this)).symm

/-- **The join of a heterochromatic pole is uncolourable.** -/
theorem not_colourable_join_of_hetWith (hhet : HetWith hP m) : ¬ (join hP m).Colourable := by
  classical
  rintro ⟨c, hc⟩
  let c' : ℕ → Color := fun e ↦
    if e ∈ P.dangling then c (newHalf (P := P) m (bdIdx hP e)).1 else c e
  let φ : ℕ × Fin 2 → ℕ × Fin 2 := fun h ↦
    if h.1 ∈ P.dangling then newHalf (P := P) m (bdIdx hP h.1) else h
  have hcJ : ((join hP m).pole (join hP m).Vs).IsColouring c := hc.pole_self
  have hnew : ∀ k, (newHalf (P := P) m k).1 ∈ (join hP m).Es := by
    intro k
    rw [join_Es]
    rcases newHalf_fst_mem m k with h | h <;> rw [h] <;> simp
  have hcP : (P.pole P.Vs).IsColouring c' := by
    refine isColouring_of_halfEdge_map hcJ φ ?_ ?_ ?_ ?_
    · intro v hv _ h hh
      rw [mem_halfEdgesIn] at hh
      obtain ⟨he, hend⟩ := hh
      by_cases hd : h.1 ∈ P.dangling
      · refine ⟨?_, by simp [φ, c', hd]⟩
        simp only [φ, hd, if_true]
        rw [mem_halfEdgesIn]
        refine ⟨hnew _, ?_⟩
        rw [join_ends_newHalf, bdEmb_bdIdx hP hd, ← hend]
        have : h.2 = innerIdx hP hd := (ends_mem_iff_inner hP hd h.2).mp (hend ▸ hv)
        rw [this, ends_innerIdx]
      · refine ⟨?_, by simp [φ, c', hd]⟩
        simp only [φ, hd, if_false]
        rw [mem_halfEdgesIn]
        refine ⟨?_, ?_⟩
        · rw [join_Es]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨he, hd⟩))
        · rw [join_ends_old hP m he]; exact hend
    · rintro v hv _ ⟨e₁, i₁⟩ h₁m ⟨e₂, i₂⟩ h₂m heq
      rw [mem_halfEdgesIn] at h₁m h₂m
      by_cases hd₁ : e₁ ∈ P.dangling <;> by_cases hd₂ : e₂ ∈ P.dangling
      · simp only [φ, hd₁, hd₂, if_true] at heq
        have hk := newHalf_injective m heq
        have he : e₁ = e₂ := by rw [← bdEmb_bdIdx hP hd₁, ← bdEmb_bdIdx hP hd₂, hk]
        subst he
        have hi₁ : i₁ = innerIdx hP hd₁ := (ends_mem_iff_inner hP hd₁ i₁).mp (h₁m.2 ▸ hv)
        have hi₂ : i₂ = innerIdx hP hd₁ := (ends_mem_iff_inner hP hd₁ i₂).mp (h₂m.2 ▸ hv)
        rw [hi₁, hi₂]
      · exfalso
        simp only [φ, hd₁, hd₂, if_true, if_false] at heq
        have := newHalf_fst_mem (P := P) m (bdIdx hP e₁)
        rw [heq] at this
        rcases this with h | h
        · exact freshE_notMem (h ▸ h₂m.1)
        · exact freshE_succ_notMem (h ▸ h₂m.1)
      · exfalso
        simp only [φ, hd₁, hd₂, if_true, if_false] at heq
        have := newHalf_fst_mem (P := P) m (bdIdx hP e₂)
        rw [← heq] at this
        rcases this with h | h
        · exact freshE_notMem (h ▸ h₁m.1)
        · exact freshE_succ_notMem (h ▸ h₁m.1)
      · simpa [φ, hd₁, hd₂] using heq
    · intro v hv hvW
      exact absurd hv hvW
    · intro e he hall
      exfalso
      have heP : e ∈ P.Es := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
      obtain ⟨i, hi⟩ := hP.has_inner e heP
      exact hall i hi hi
  have hcP' : P.IsColouring c' := hP.isColouring_iff.mpr hcP
  apply hhet (tvec hP c') ⟨c', hcP', rfl⟩ 0
  show c' (bdEmb hP 0) = c' (bdEmb hP (pairing m 0))
  simp only [c', bdEmb_mem, if_true, bdIdx_bdEmb, newHalf_zero, newHalf_pairing_zero]

end Factors

section JoinTransfer

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPX : (Δ.pole X).IsPole4) (hPXc : (Δ.pole (Δ.Vs \ X)).IsPole4) (mX : Fin 3)
  (hiso : IsoWith hPX mX)
include hcl hXW hW hPX hPXc hiso

/-- The boundary position attached to a new half-edge of the join. -/
def newPos (P : FinGraph) (m : Fin 3) (h : ℕ × Fin 2) : Fin 4 :=
  if h.1 = freshE P then (if h.2 = 0 then 0 else pairing m 0)
  else (if h.2 = 0 then other m else pairing m (other m))

omit hcl hXW hW hPX hPXc hiso in
theorem newHalf_newPos {P : FinGraph} (m : Fin 3) (h : ℕ × Fin 2)
    (hh : h.1 = freshE P ∨ h.1 = freshE P + 1) : newHalf (P := P) m (newPos P m h) = h := by
  obtain ⟨e, i⟩ := h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hh with rfl | rfl <;> rcases hi with rfl | rfl
  · simp [newPos, newHalf_zero]
  · simp [newPos, newHalf_pairing_zero]
  · simp [newPos, newHalf_other]
  · simp [newPos, newHalf_pairing_other]

omit hW in
/-- **Colouring transfer, join case.** -/
theorem join_transfer {c : ℕ → Color} (hc : (Δ.pole W).IsColouring c) :
    ∃ c' : ℕ → Color, ((join hPXc mX).pole (W \ X)).IsColouring c' ∧
      ∀ d ∈ Δ.bd W, c' d = c d := by
  classical
  have hemb : ∀ k, bdEmb hPX k = bdEmb hPXc k :=
    bdEmb_congr hPX hPXc (by rw [dangling_pole, dangling_pole, bd_compl hcl])
  have hcX : (Δ.pole X).IsColouring c := hc.restrict hXW
  have hisoc : ∀ k, c (bdEmb hPXc (pairing mX k)) = c (bdEmb hPXc k) := by
    intro k
    have := hiso (tvec hPX c) ⟨c, hcX, rfl⟩ k
    simp only [tvec, hemb] at this
    exact this.symm
  have hbdW : Δ.bd W ⊆ (Δ.pole (Δ.Vs \ X)).Es := by
    intro d hd
    obtain ⟨i, hi, hi'⟩ := bd_side hd
    have := hcl d (bd_subset W hd) (Fin.rev i)
    rw [pole_Es, Finset.mem_union]
    exact mem_edgesIn_or_bd (bd_subset W hd) (Finset.mem_sdiff.mpr ⟨this, fun h ↦ hi' (hXW h)⟩)
  have hPE : ∀ e ∈ (Δ.pole (Δ.Vs \ X)).Es, e ∈ Δ.Es := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he
    exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
  set P := Δ.pole (Δ.Vs \ X) with hPdef
  let c' : ℕ → Color := fun e ↦ if e = freshE P then c (bdEmb hPXc 0)
    else if e = freshE P + 1 then c (bdEmb hPXc (other mX)) else c e
  let φ : ℕ × Fin 2 → ℕ × Fin 2 := fun h ↦
    if h.1 = freshE P ∨ h.1 = freshE P + 1 then
      (bdEmb hPXc (newPos P mX h), innerIdx hPXc (bdEmb_mem hPXc (newPos P mX h))) else h
  refine ⟨c', isColouring_of_halfEdge_map hc φ ?_ ?_ ?_ ?_, fun d hd ↦ ?_⟩
  · intro v hv hvW h hh
    rw [mem_halfEdgesIn, join_Es, Finset.mem_insert, Finset.mem_insert] at hh
    obtain ⟨he, hend⟩ := hh
    by_cases hnew : h.1 = freshE P ∨ h.1 = freshE P + 1
    · simp only [φ, hnew, if_true]
      have hjoin : (join hPXc mX).ends h.1 h.2 = innerEnd hPXc (bdEmb hPXc (newPos P mX h)) := by
        conv_lhs => rw [← newHalf_newPos mX h hnew]
        exact join_ends_newHalf hPXc mX _
      refine ⟨?_, ?_⟩
      · rw [mem_halfEdgesIn]
        refine ⟨hPE _ (mem_dangling.mp (bdEmb_mem hPXc (newPos P mX h))).1, ?_⟩
        show P.ends _ _ = v
        rw [ends_innerIdx, ← hjoin, hend]
      · -- the colour of the new edge is the colour of any edge of its couple
        obtain ⟨e, i⟩ := h
        have hi : i = 0 ∨ i = 1 := by omega
        simp only at hnew
        rcases hnew with rfl | rfl <;> rcases hi with rfl | rfl
        · simp [c', newPos]
        · simp [c', newPos, hisoc]
        · simp [c', newPos]
        · simp [c', newPos, hisoc]
    · simp only [φ, hnew, if_false]
      push Not at hnew
      have heP : h.1 ∈ P.Es \ P.dangling := by
        rcases he with h1 | h1 | h1
        · exact absurd h1 hnew.1
        · exact absurd h1 hnew.2
        · exact h1
      refine ⟨?_, ?_⟩
      · rw [mem_halfEdgesIn]
        refine ⟨hPE _ (Finset.mem_sdiff.mp heP).1, ?_⟩
        rw [← hend, join_ends_old hPXc mX (Finset.mem_sdiff.mp heP).1]
        rfl
      · simp only [c', hnew.1, hnew.2, if_false]
  · rintro v hv hvW ⟨e₁, i₁⟩ h₁m ⟨e₂, i₂⟩ h₂m heq
    rw [mem_halfEdgesIn] at h₁m h₂m
    have hold : ∀ e ∈ (join hPXc mX).Es, ¬ (e = freshE P ∨ e = freshE P + 1) →
        e ∈ P.Es \ P.dangling := by
      intro e he hn
      rw [join_Es, Finset.mem_insert, Finset.mem_insert] at he
      rcases he with h1 | h1 | h1
      · exact absurd (Or.inl h1) hn
      · exact absurd (Or.inr h1) hn
      · exact h1
    by_cases hn₁ : e₁ = freshE P ∨ e₁ = freshE P + 1 <;>
      by_cases hn₂ : e₂ = freshE P ∨ e₂ = freshE P + 1
    · simp only [φ, hn₁, hn₂, if_true, Prod.mk.injEq] at heq
      have hk := bdEmb_injective hPXc heq.1
      have h1 := newHalf_newPos (P := P) mX (e₁, i₁) hn₁
      have h2 := newHalf_newPos (P := P) mX (e₂, i₂) hn₂
      rw [← h1, ← h2, hk]
    · exfalso
      simp only [φ, hn₁, hn₂, if_true, if_false, Prod.mk.injEq] at heq
      have := (Finset.mem_sdiff.mp (hold e₂ h₂m.1 hn₂)).2
      rw [← heq.1] at this
      exact this (bdEmb_mem hPXc _)
    · exfalso
      simp only [φ, hn₁, hn₂, if_true, if_false, Prod.mk.injEq] at heq
      have := (Finset.mem_sdiff.mp (hold e₁ h₁m.1 hn₁)).2
      rw [heq.1] at this
      exact this (bdEmb_mem hPXc _)
    · simpa [φ, hn₁, hn₂] using heq
  · intro v hv hvW
    exact absurd (Finset.mem_sdiff.mp hv).1 hvW
  · intro e he hall
    exfalso
    have hend : ∃ i, (join hPXc mX).ends e i ∈ W \ X := by
      rw [pole_Es, Finset.mem_union] at he
      rcases he with he | he
      · exact ⟨0, (mem_edgesIn.mp he).2 0⟩
      · obtain ⟨i, hi, _⟩ := bd_side he
        exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hend
    exact hall i hi (Finset.mem_sdiff.mp hi).1
  · have hdP : d ∈ P.Es := hbdW hd
    have h1 : d ≠ freshE P := fun h ↦ freshE_notMem (h ▸ hdP)
    have h2 : d ≠ freshE P + 1 := fun h ↦ freshE_succ_notMem (h ▸ hdP)
    simp only [c', h1, h2, if_false]

end JoinTransfer

end FinGraph
end GraphPuzzles
