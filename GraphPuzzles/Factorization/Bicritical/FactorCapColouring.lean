import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap
import GraphPuzzles.Factorization.Diamond.FactorCanon

/-!
# Colourings of poles of a cap

`cap_colouring`: a colouring of a pole `W` of `Δ` extends to the pole of the cap of `Y` at a
shore consisting of old vertices `Z₀ ⊆ Y ∩ W` together with some of the two new vertices,
provided the couple attached to each present new vertex is coloured with two distinct colours.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y W : Finset ℕ} (hPY : (Δ.pole Y).IsPole4) (m : Fin 3)

/-- The colouring of a cap from a colouring `c` of old edges and a colour `γ` for the new edge. -/
def capCol (P : FinGraph) (c : ℕ → Color) (γ : Color) (e : ℕ) : Color :=
  if e = freshE P then γ else c e

theorem capCol_old {P : FinGraph} {c : ℕ → Color} {γ : Color} {e : ℕ} (he : e ∈ P.Es) :
    capCol P c γ e = c e := by
  unfold capCol
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he))]

theorem capCol_new (P : FinGraph) (c : ℕ → Color) (γ : Color) : capCol P c γ (freshE P) = γ := by
  unfold capCol; rw [if_pos rfl]

/-- **Cap colouring.** -/
theorem cap_colouring {c : ℕ → Color} (hc : (Δ.pole W).IsColouring c) {Z₀ S : Finset ℕ}
    (hZ₀ : Z₀ ⊆ Y) (hZW : Z₀ ⊆ W)
    (hS : S ⊆ {freshV (Δ.pole Y), freshV (Δ.pole Y) + 1}) {γ : Color} (hγ : γ ≠ 0)
    (hu : freshV (Δ.pole Y) ∈ S → c (bdEmb hPY 0) ≠ 0 ∧ c (bdEmb hPY (pairing m 0)) ≠ 0 ∧
      c (bdEmb hPY 0) ≠ c (bdEmb hPY (pairing m 0)) ∧
      γ = c (bdEmb hPY 0) + c (bdEmb hPY (pairing m 0)))
    (hw : freshV (Δ.pole Y) + 1 ∈ S → c (bdEmb hPY (other m)) ≠ 0 ∧
      c (bdEmb hPY (pairing m (other m))) ≠ 0 ∧
      c (bdEmb hPY (other m)) ≠ c (bdEmb hPY (pairing m (other m))) ∧
      γ = c (bdEmb hPY (other m)) + c (bdEmb hPY (pairing m (other m)))) :
    ((cap hPY m).pole (S ∪ Z₀)).IsColouring (capCol (Δ.pole Y) c γ) := by
  classical
  set P := Δ.pole Y with hPdef
  set u := freshV P with hudef
  set w := freshV P + 1 with hwdef
  -- restrict `c` away from the new labels
  set W' := W \ {u, w} with hW'def
  have hc' : (Δ.pole W').IsColouring c := hc.restrict Finset.sdiff_subset
  have huY : u ∉ Y := freshV_notMem (P := P)
  have hwY : w ∉ Y := freshV_succ_notMem (P := P)
  have hZW' : Z₀ ⊆ W' := by
    intro v hv
    rw [hW'def, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hZW hv, by rintro (rfl | rfl); exact huY (hZ₀ hv); exact hwY (hZ₀ hv)⟩
  have hSW' : ∀ v ∈ S, v ∉ W' := by
    intro v hv hvW
    rw [hW'def, Finset.mem_sdiff] at hvW
    exact hvW.2 (hS hv)
  have hPE : ∀ e ∈ P.Es, e ∈ Δ.Es := by
    intro e he
    rw [hPdef, pole_Es, Finset.mem_union] at he
    exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
  -- the generic argument at a new vertex attached to the couple `{k₀, pairing m k₀}`
  have key : ∀ (k₀ : Fin 4) (C : Finset ℕ) (j : Fin 2),
      C = {bdEmb hPY k₀, bdEmb hPY (pairing m k₀)} →
      c (bdEmb hPY k₀) ≠ 0 → c (bdEmb hPY (pairing m k₀)) ≠ 0 →
      c (bdEmb hPY k₀) ≠ c (bdEmb hPY (pairing m k₀)) →
      γ = c (bdEmb hPY k₀) + c (bdEmb hPY (pairing m k₀)) →
      ∀ h₁ h₂ : ℕ × Fin 2,
      h₁ ∈ insert (freshE P, j) (C.image fun d ↦ (d, outerIdx hPY d)) →
      h₂ ∈ insert (freshE P, j) (C.image fun d ↦ (d, outerIdx hPY d)) →
      capCol P c γ h₁.1 = capCol P c γ h₂.1 → h₁ = h₂ := by
    intro k₀ C j hC h0 h0' hne hγ' h₁ h₂ hm₁ hm₂ heq
    have hCd : ∀ d ∈ C, d ∈ P.Es := by
      intro d hd
      rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl <;> exact (mem_dangling.mp (bdEmb_mem hPY _)).1
    have hsum := add_ne_of_ne h0 h0' hne
    rw [← hγ'] at hsum
    rw [Finset.mem_insert, Finset.mem_image] at hm₁ hm₂
    rcases hm₁ with rfl | ⟨d₁, hd₁, rfl⟩ <;> rcases hm₂ with rfl | ⟨d₂, hd₂, rfl⟩
    · rfl
    · exfalso
      simp only [capCol_new, capCol_old (hCd d₂ hd₂)] at heq
      rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₂
      rcases hd₂ with rfl | rfl
      · exact hsum.2.1 heq
      · exact hsum.2.2 heq
    · exfalso
      simp only [capCol_new, capCol_old (hCd d₁ hd₁)] at heq
      rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁
      rcases hd₁ with rfl | rfl
      · exact hsum.2.1 heq.symm
      · exact hsum.2.2 heq.symm
    · simp only [capCol_old (hCd d₁ hd₁), capCol_old (hCd d₂ hd₂)] at heq
      rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁ hd₂
      rcases hd₁ with rfl | rfl <;> rcases hd₂ with rfl | rfl
      · rfl
      · exact absurd heq hne
      · exact absurd heq.symm hne
      · rfl
  refine isColouring_of_halfEdge_map hc' id ?_ ?_ ?_ ?_
  · intro v hv hvW h hh
    have hvZ : v ∈ Z₀ := by
      rw [Finset.mem_union] at hv
      exact hv.elim (fun h ↦ absurd hvW (hSW' v h)) id
    have hvY : v ∈ Y := hZ₀ hvZ
    rw [cap_halfEdges_old hPY m hvY, halfEdgesIn_pole_eq (Q := Δ) hvY] at hh
    refine ⟨hh, ?_⟩
    rw [mem_halfEdgesIn] at hh
    show capCol P c γ h.1 = c h.1
    exact capCol_old (by rw [hPdef, pole_Es, Finset.mem_union]; exact mem_edgesIn_or_bd hh.1 (hh.2 ▸ hvY))
  · intro v _ _ h₁ _ h₂ _ heq
    exact heq
  · intro v hv hvW h₁ h₁m h₂ h₂m heq
    have hvS : v ∈ S := by
      rw [Finset.mem_union] at hv
      exact hv.elim id (fun h ↦ absurd (hZW' h) hvW)
    have hv' := hS hvS
    rw [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · rw [cap_halfEdges_u] at h₁m h₂m
      obtain ⟨h0, h0', hne, hγ'⟩ := hu hvS
      exact key 0 (couple₁ hPY m) 0 rfl h0 h0' hne hγ' h₁ h₂ h₁m h₂m heq
    · rw [cap_halfEdges_w] at h₁m h₂m
      obtain ⟨h0, h0', hne, hγ'⟩ := hw hvS
      exact key (other m) (couple₂ hPY m) 1 rfl h0 h0' hne hγ' h₁ h₂ h₁m h₂m heq
  · intro e he hall
    have heQ : e ∈ (cap hPY m).Es := by
      rw [pole_Es, Finset.mem_union] at he
      exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
    rw [cap_Es, Finset.mem_insert] at heQ
    rcases heQ with rfl | heP
    · rw [capCol_new]; exact hγ
    · rw [capCol_old heP]
      -- an end of `e` in the shore lies at a new vertex, so `e` is a couple edge
      have hend : ∃ i, (cap hPY m).ends e i ∈ S ∪ Z₀ := by
        rw [pole_Es, Finset.mem_union] at he
        rcases he with he | he
        · exact ⟨0, (mem_edgesIn.mp he).2 0⟩
        · obtain ⟨i, hi, _⟩ := bd_side he
          exact ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hend
      have hiS : (cap hPY m).ends e i ∈ S := by
        have hnW := hall i hi
        rw [Finset.mem_union] at hi
        exact hi.elim id (fun h ↦ absurd (hZW' h) hnW)
      rw [cap_ends_eq hPY m heP] at hiS
      split_ifs at hiS with hin hc₁
      · exfalso
        have := hS hiS
        rw [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact huY (h ▸ hin)
        · exact hwY (h ▸ hin)
      · obtain ⟨h0, h0', -, -⟩ := hu hiS
        rw [couple₁, Finset.mem_insert, Finset.mem_singleton] at hc₁
        rcases hc₁ with rfl | rfl
        · exact h0
        · exact h0'
      · have hd : e ∈ P.dangling := mem_dangling.mpr ⟨heP, i, hin⟩
        have hc₂ : e ∈ couple₂ hPY m := (mem_couple₂_iff hPY m hd).mpr hc₁
        obtain ⟨h0, h0', -, -⟩ := hw hiS
        rw [couple₂, Finset.mem_insert, Finset.mem_singleton] at hc₂
        rcases hc₂ with rfl | rfl
        · exact h0
        · exact h0'

end FinGraph
end GraphPuzzles
