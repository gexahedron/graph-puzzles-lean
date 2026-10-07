import GraphPuzzles.Factorization.Bicritical.FactorJoinTransfer

/-!
# Colourings of poles of a join

`join_colouring`: a colouring of a pole `W` of `Δ` yields a colouring of a pole `Z` of the join of
the complementary pole of `Y`, the new edges receiving prescribed colours `γ₁`, `γ₂` that agree
with the colours of the couple edges at the old vertices of `Z ∩ W`; properness at the vertices
of `Z` outside `W` is assumed directly.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- The colouring of a join from a colouring of old edges and colours for the two new edges. -/
def joinCol (P : FinGraph) (c : ℕ → Color) (γ₁ γ₂ : Color) (e : ℕ) : Color :=
  if e = freshE P then γ₁ else if e = freshE P + 1 then γ₂ else c e

theorem joinCol_old {P : FinGraph} {c : ℕ → Color} {γ₁ γ₂ : Color} {e : ℕ} (he : e ∈ P.Es) :
    joinCol P c γ₁ γ₂ e = c e := by
  unfold joinCol
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ freshE_succ_notMem (h ▸ he))]

theorem joinCol_new₁ (P : FinGraph) (c : ℕ → Color) (γ₁ γ₂ : Color) :
    joinCol P c γ₁ γ₂ (freshE P) = γ₁ := by
  unfold joinCol; rw [if_pos rfl]

theorem joinCol_new₂ (P : FinGraph) (c : ℕ → Color) (γ₁ γ₂ : Color) :
    joinCol P c γ₁ γ₂ (freshE P + 1) = γ₂ := by
  unfold joinCol; rw [if_neg (by omega), if_pos rfl]

variable {Δ : FinGraph} {Y W : Finset ℕ} (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4) (m : Fin 3)

/-- **Join colouring.** -/
theorem join_colouring {c : ℕ → Color} (hc : (Δ.pole W).IsColouring c) {Z : Finset ℕ}
    (_hZ : Z ⊆ Δ.Vs \ Y) {γ₁ γ₂ : Color} (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0)
    (hc₁ : ∀ k, (k = 0 ∨ k = pairing m 0) → innerEnd hPYc (bdEmb hPYc k) ∈ Z →
      innerEnd hPYc (bdEmb hPYc k) ∈ W → c (bdEmb hPYc k) = γ₁)
    (hc₂ : ∀ k, (k = other m ∨ k = pairing m (other m)) → innerEnd hPYc (bdEmb hPYc k) ∈ Z →
      innerEnd hPYc (bdEmb hPYc k) ∈ W → c (bdEmb hPYc k) = γ₂)
    (hsp : ∀ v ∈ Z, v ∉ W → ∀ h₁ ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es v,
      ∀ h₂ ∈ (join hPYc m).halfEdgesIn (join hPYc m).Es v,
      joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ h₁.1 = joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂ h₂.1 →
      h₁ = h₂)
    (hnz : ∀ e ∈ (Δ.pole (Δ.Vs \ Y)).Es \ (Δ.pole (Δ.Vs \ Y)).dangling,
      (∀ i, Δ.ends e i ∈ Z → Δ.ends e i ∉ W) → c e ≠ 0) :
    ((join hPYc m).pole Z).IsColouring (joinCol (Δ.pole (Δ.Vs \ Y)) c γ₁ γ₂) := by
  classical
  have hPE : ∀ e ∈ (Δ.pole (Δ.Vs \ Y)).Es, e ∈ Δ.Es := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he
    exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
  set P := Δ.pole (Δ.Vs \ Y) with hPdef
  let φ : ℕ × Fin 2 → ℕ × Fin 2 := fun h ↦
    if h.1 = freshE P ∨ h.1 = freshE P + 1 then
      (bdEmb hPYc (newPos P m h), innerIdx hPYc (bdEmb_mem hPYc (newPos P m h))) else h
  have hold : ∀ e ∈ (join hPYc m).Es, ¬ (e = freshE P ∨ e = freshE P + 1) →
      e ∈ P.Es \ P.dangling := by
    intro e he hn
    rw [join_Es, Finset.mem_insert, Finset.mem_insert] at he
    rcases he with h1 | h1 | h1
    · exact absurd (Or.inl h1) hn
    · exact absurd (Or.inr h1) hn
    · exact h1
  refine isColouring_of_halfEdge_map hc φ ?_ ?_ hsp ?_
  · intro v hv hvW h hh
    rw [mem_halfEdgesIn] at hh
    obtain ⟨he, hend⟩ := hh
    by_cases hnew : h.1 = freshE P ∨ h.1 = freshE P + 1
    · simp only [φ, hnew, if_true]
      have hjoin : (join hPYc m).ends h.1 h.2 = innerEnd hPYc (bdEmb hPYc (newPos P m h)) := by
        conv_lhs => rw [← newHalf_newPos m h hnew]
        exact join_ends_newHalf hPYc m _
      have hin : innerEnd hPYc (bdEmb hPYc (newPos P m h)) = v := by rw [← hjoin, hend]
      refine ⟨?_, ?_⟩
      · rw [mem_halfEdgesIn]
        refine ⟨hPE _ (mem_dangling.mp (bdEmb_mem hPYc (newPos P m h))).1, ?_⟩
        show P.ends _ _ = v
        rw [ends_innerIdx, hin]
      · obtain ⟨e, i⟩ := h
        have hi : i = 0 ∨ i = 1 := by omega
        simp only at hnew
        rcases hnew with rfl | rfl <;> rcases hi with rfl | rfl
        · rw [joinCol_new₁]
          exact (hc₁ _ (Or.inl (by simp [newPos])) (by simpa using hin ▸ hv)
            (by simpa using hin ▸ hvW)).symm
        · rw [joinCol_new₁]
          exact (hc₁ _ (Or.inr (by simp [newPos])) (by simpa using hin ▸ hv)
            (by simpa using hin ▸ hvW)).symm
        · rw [joinCol_new₂]
          exact (hc₂ _ (Or.inl (by simp [newPos])) (by simpa using hin ▸ hv)
            (by simpa using hin ▸ hvW)).symm
        · rw [joinCol_new₂]
          exact (hc₂ _ (Or.inr (by simp [newPos])) (by simpa using hin ▸ hv)
            (by simpa using hin ▸ hvW)).symm
    · simp only [φ, hnew, if_false]
      have heP := hold _ he hnew
      refine ⟨?_, ?_⟩
      · rw [mem_halfEdgesIn]
        refine ⟨hPE _ (Finset.mem_sdiff.mp heP).1, ?_⟩
        rw [← hend, join_ends_old hPYc m (Finset.mem_sdiff.mp heP).1]
        rfl
      · exact joinCol_old (Finset.mem_sdiff.mp heP).1
  · rintro v hv hvW ⟨e₁, i₁⟩ h₁m ⟨e₂, i₂⟩ h₂m heq
    rw [mem_halfEdgesIn] at h₁m h₂m
    by_cases hn₁ : e₁ = freshE P ∨ e₁ = freshE P + 1 <;>
      by_cases hn₂ : e₂ = freshE P ∨ e₂ = freshE P + 1
    · simp only [φ, hn₁, hn₂, if_true, Prod.mk.injEq] at heq
      have hk := bdEmb_injective hPYc heq.1
      have h1 := newHalf_newPos (P := P) m (e₁, i₁) hn₁
      have h2 := newHalf_newPos (P := P) m (e₂, i₂) hn₂
      rw [← h1, ← h2, hk]
    · exfalso
      simp only [φ, hn₁, hn₂, if_true, if_false, Prod.mk.injEq] at heq
      have := (Finset.mem_sdiff.mp (hold e₂ h₂m.1 hn₂)).2
      rw [← heq.1] at this
      exact this (bdEmb_mem hPYc _)
    · exfalso
      simp only [φ, hn₁, hn₂, if_true, if_false, Prod.mk.injEq] at heq
      have := (Finset.mem_sdiff.mp (hold e₁ h₁m.1 hn₁)).2
      rw [heq.1] at this
      exact this (bdEmb_mem hPYc _)
    · simpa [φ, hn₁, hn₂] using heq
  · intro e he hall
    have heQ : e ∈ (join hPYc m).Es := by
      rw [pole_Es, Finset.mem_union] at he
      exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
    by_cases hnew : e = freshE P ∨ e = freshE P + 1
    · rcases hnew with rfl | rfl
      · rw [joinCol_new₁]; exact hγ₁
      · rw [joinCol_new₂]; exact hγ₂
    · have heP := hold e heQ hnew
      rw [joinCol_old (Finset.mem_sdiff.mp heP).1]
      apply hnz e heP
      intro i hi
      have := hall i
      rw [join_ends_old hPYc m (Finset.mem_sdiff.mp heP).1] at this
      exact this hi

end FinGraph
end GraphPuzzles
