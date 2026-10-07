import GraphPuzzles.Factorization.FactorGlue
import GraphPuzzles.Factorization.Bicritical.FactorParity

/-!
# Colourings transported along half-edge maps

`isColouring_of_halfEdge_map`: a candidate colouring of a pole of `Q` is proper provided that at
every vertex of the shore lying in a coloured shore `W` of `Δ` the half-edges of `Q` inject into
the half-edges of `Δ` compatibly with the colours, and at the remaining (new) vertices properness
is checked directly.  Also: colourings of a graph versus of its pole at its own vertex set, the
sum form of the parity lemma, and small helpers.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

section HalfEdgeMap

/-- **Colouring transport along half-edge maps.** -/
theorem isColouring_of_halfEdge_map {Q Δ : FinGraph} {Z W : Finset ℕ} {c c' : ℕ → Color}
    (hc : (Δ.pole W).IsColouring c) (φ : ℕ × Fin 2 → ℕ × Fin 2)
    (hφ : ∀ v ∈ Z, v ∈ W → ∀ h ∈ Q.halfEdgesIn Q.Es v,
      φ h ∈ Δ.halfEdgesIn Δ.Es v ∧ c' h.1 = c (φ h).1)
    (hinj : ∀ v ∈ Z, v ∈ W → ∀ h₁ ∈ Q.halfEdgesIn Q.Es v, ∀ h₂ ∈ Q.halfEdgesIn Q.Es v,
      φ h₁ = φ h₂ → h₁ = h₂)
    (hsp : ∀ v ∈ Z, v ∉ W → ∀ h₁ ∈ Q.halfEdgesIn Q.Es v, ∀ h₂ ∈ Q.halfEdgesIn Q.Es v,
      c' h₁.1 = c' h₂.1 → h₁ = h₂)
    (hnz : ∀ e ∈ (Q.pole Z).Es, (∀ i, Q.ends e i ∈ Z → Q.ends e i ∉ W) → c' e ≠ 0) :
    (Q.pole Z).IsColouring c' := by
  refine ⟨?_, ?_⟩
  · intro e he
    have heQ : e ∈ Q.Es := by
      rw [pole_Es, Finset.mem_union] at he
      exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
    by_cases hW : ∃ i, Q.ends e i ∈ Z ∧ Q.ends e i ∈ W
    · obtain ⟨i, hiZ, hiW⟩ := hW
      obtain ⟨hm, hcol⟩ := hφ _ hiZ hiW (e, i) (mem_halfEdgesIn.mpr ⟨heQ, rfl⟩)
      rw [hcol]
      rw [mem_halfEdgesIn] at hm
      apply hc.1
      rw [pole_Es, Finset.mem_union]
      exact mem_edgesIn_or_bd hm.1 (hm.2 ▸ hiW)
    · push Not at hW
      exact hnz e he hW
  · intro v hv h₁ h₁m h₂ h₂m heq
    have hv' : v ∈ Z := hv
    rw [halfEdgesIn_pole_eq hv'] at h₁m h₂m
    by_cases hW : v ∈ W
    · obtain ⟨m₁, c₁⟩ := hφ v hv' hW h₁ h₁m
      obtain ⟨m₂, c₂⟩ := hφ v hv' hW h₂ h₂m
      rw [c₁, c₂] at heq
      rw [← halfEdgesIn_pole_eq (Q := Δ) hW] at m₁ m₂
      exact hinj v hv' hW h₁ h₁m h₂ h₂m (hc.unique_halfEdge hW m₁ m₂ heq)
    · exact hsp v hv' hW h₁ h₁m h₂ h₂m heq

/-- A colouring of a graph is a colouring of its pole at its own vertex set. -/
theorem IsColouring.pole_self {c : ℕ → Color} (hc : Γ.IsColouring c) :
    (Γ.pole Γ.Vs).IsColouring c := by
  refine ⟨fun e he ↦ hc.1 e ?_, fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  · rw [pole_Es, Finset.mem_union] at he
    exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
  · have hv' : v ∈ Γ.Vs := hv
    rw [halfEdgesIn_pole_eq hv'] at h₁m h₂m
    exact hc.2 v hv' h₁ h₁m h₂ h₂m heq

/-- Conversely, when every edge has an end at a vertex. -/
theorem IsColouring.of_pole_self {c : ℕ → Color} (hin : ∀ e ∈ Γ.Es, ∃ i, Γ.ends e i ∈ Γ.Vs)
    (hc : (Γ.pole Γ.Vs).IsColouring c) : Γ.IsColouring c := by
  refine ⟨fun e he ↦ hc.1 e ?_, fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hin e he
    rw [pole_Es, Finset.mem_union]
    exact mem_edgesIn_or_bd he hi
  · have hv' : v ∈ (Γ.pole Γ.Vs).Vs := hv
    rw [← halfEdgesIn_pole_eq hv] at h₁m h₂m
    exact hc.2 v hv' h₁ h₁m h₂ h₂m heq

theorem IsPole4.isColouring_iff {c : ℕ → Color} (hP : Γ.IsPole4) :
    Γ.IsColouring c ↔ (Γ.pole Γ.Vs).IsColouring c :=
  ⟨IsColouring.pole_self, IsColouring.of_pole_self hP.has_inner⟩

theorem IsClosed.isColouring_iff {c : ℕ → Color} (hcl : Γ.IsClosed) :
    Γ.IsColouring c ↔ (Γ.pole Γ.Vs).IsColouring c :=
  ⟨IsColouring.pole_self, IsColouring.of_pole_self fun e he ↦ ⟨0, hcl e he 0⟩⟩

end HalfEdgeMap

section SumParity

theorem two_nsmul_color (κ : Color) : 2 • κ = 0 := by
  revert κ; decide

theorem nsmul_color_mod (n : ℕ) (κ : Color) : n • κ = (n % 2) • κ := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [add_nsmul, mul_comm, mul_nsmul, two_nsmul_color, add_zero]

theorem sum_color_parity (p : ℕ) (hp : p < 2) :
    ∑ κ : Color, (if κ = 0 then (0 : Color) else p • κ) = 0 := by
  interval_cases p <;> decide

/-- **Parity lemma, sum form**: the boundary colours of a pole sum to zero. -/
theorem IsColouring.sum_bd_eq_zero (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs)
    {c : ℕ → Color} (hc : (Γ.pole X).IsColouring c) : ∑ e ∈ Γ.bd X, c e = 0 := by
  rw [← Finset.sum_fiberwise (Γ.bd X) c (fun e ↦ c e)]
  have hterm : ∀ κ : Color, ∑ e ∈ Γ.bd X with c e = κ, c e =
      if κ = 0 then 0 else ((Γ.bd X).card % 2) • κ := by
    intro κ
    rw [Finset.sum_congr rfl (fun e he ↦ (Finset.mem_filter.mp he).2), Finset.sum_const,
      nsmul_color_mod]
    split_ifs with h0
    · rw [h0, nsmul_zero]
    · rw [hc.card_bd_color hcub hX h0]
  rw [Finset.sum_congr rfl (fun κ _ ↦ hterm κ)]
  exact sum_color_parity _ (Nat.mod_lt _ (by norm_num))

theorem ne_of_add_three_eq_zero {x y z : Color} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : x + y + z = 0) : y ≠ z := by
  revert x y z; decide

theorem color_add_self (κ : Color) : κ + κ = 0 := by
  revert κ; decide

end SumParity

section Small

theorem exists_pairing_eq {k₁ k₂ : Fin 4} (h : k₁ ≠ k₂) : ∃ m, pairing m k₁ = k₂ := by
  revert k₁ k₂; decide

end Small

end FinGraph
end GraphPuzzles
