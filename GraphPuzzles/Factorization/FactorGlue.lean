import GraphPuzzles.Factorization.FactorPoleIso

/-!
# Substituting a sub-pole by its gadget preserves colourings (one direction)

Let `X ⊆ W` be shores of a closed cubic graph, and let `Δ'` be the completion of the complement
pole of `X` (the cap if the `X`-pole is heterochromatic, the join if it is isochromatic).  Every
colouring of the pole of `W` extends to a colouring of the pole of `W' = (W \ X) ∪ New` in `Δ'`
with the same colours on corresponding boundary edges: the cap gadget is coloured by giving the
fresh edge the third colour, and the join gadget by giving each new edge the common colour of
its couple.  Consequently the type of the `W`-cut is inherited by the `W'`-cut
(Chladný–Škoviera, Substitution Lemma 4.1, in the form needed for Lemma 10.1).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

set_option maxRecDepth 100000

/-- The third colour of a heterochromatic couple is the sum; it is the same for both couples. -/
theorem het_sum (m : Fin 3) (t : Fin 4 → Color) (hv : Valid t) (hn : Nonzero4 t)
    (hh : ∀ i, t i ≠ t (pairing m i)) :
    t 0 + t (pairing m 0) = t (other m) + t (pairing m (other m)) := by
  revert m t
  decide

theorem add_ne_of_ne {a b : Color} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a + b ≠ 0 ∧ a + b ≠ a ∧ a + b ≠ b := by
  revert a b
  decide

/-- In a closed graph, the half-edges at a vertex of `Z` of the pole of `Z` are all half-edges
at that vertex. -/
theorem halfEdgesIn_pole_eq {Q : FinGraph} {Z : Finset ℕ} {v : ℕ} (hv : v ∈ Z) :
    (Q.pole Z).halfEdgesIn (Q.pole Z).Es v = Q.halfEdgesIn Q.Es v := by
  ext h
  rw [mem_halfEdgesIn, mem_halfEdgesIn, pole_Es, Finset.mem_union, pole_ends]
  constructor
  · rintro ⟨he, hv'⟩
    exact ⟨he.elim (fun h ↦ edgesIn_subset Z h) (fun h ↦ bd_subset Z h), hv'⟩
  · rintro ⟨he, hv'⟩
    exact ⟨mem_edgesIn_or_bd he (hv' ▸ hv), hv'⟩

variable {Δ : FinGraph} {X W : Finset ℕ}

section CapTransfer

variable (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
  (hPX : (Δ.pole X).IsPole4) (hPXc : (Δ.pole (Δ.Vs \ X)).IsPole4) (mX : Fin 3)
  (hhet : HetWith hPX mX)
include hcl hXW hW hPX hPXc hhet

/-- **Colouring transfer, cap case.** -/
theorem cap_transfer {c : ℕ → Color} (hc : (Δ.pole W).IsColouring c) :
    ∃ c' : ℕ → Color, ((cap hPXc mX).pole
      (insert (freshV (Δ.pole (Δ.Vs \ X))) (insert (freshV (Δ.pole (Δ.Vs \ X)) + 1)
        (W \ X)))).IsColouring c' ∧ ∀ d ∈ Δ.bd W, c' d = c d := by
  have hemb : ∀ k, bdEmb hPX k = bdEmb hPXc k :=
    bdEmb_congr hPX hPXc (by rw [dangling_pole, dangling_pole, bd_compl hcl])
  -- the restriction of `c` to the `X`-pole and its boundary vector
  have hcX : (Δ.pole X).IsColouring c := hc.restrict hXW
  have htCol : tvec hPX c ∈ Col hPX := ⟨c, hcX, rfl⟩
  have hthet : ∀ i, tvec hPX c i ≠ tvec hPX c (pairing mX i) := hhet _ htCol
  have htv := Col.valid hPX htCol
  have htn := Col.nonzero hPX htCol
  have hsum := het_sum mX _ htv htn hthet
  -- notation
  have hε' : ∀ e ∈ (Δ.pole (Δ.Vs \ X)).Es, e ≠ freshE (Δ.pole (Δ.Vs \ X)) :=
    fun e he h ↦ freshE_notMem (h ▸ he)
  have hbdW : Δ.bd W ⊆ (Δ.pole (Δ.Vs \ X)).Es := by
    intro d hd
    obtain ⟨i, hi, hi'⟩ := bd_side hd
    have := hcl d (bd_subset W hd) (Fin.rev i)
    rw [pole_Es, Finset.mem_union]
    exact mem_edgesIn_or_bd (bd_subset W hd) (Finset.mem_sdiff.mpr ⟨this, fun h ↦ hi' (hXW h)⟩)
  have hbdX : Δ.bd X ⊆ (Δ.pole W).Es := by
    intro d hd
    obtain ⟨i, hi, _⟩ := bd_side hd
    rw [pole_Es, Finset.mem_union]
    exact mem_edgesIn_or_bd (bd_subset X hd) (hXW hi)
  -- old edges of the cap with an end at an old vertex are edges of the `W`-pole
  have hold : ∀ e ∈ (Δ.pole (Δ.Vs \ X)).Es, ∀ i, Δ.ends e i ∈ W \ X → e ∈ (Δ.pole W).Es := by
    intro e he i hi
    have heΔ : e ∈ Δ.Es := by
      rw [pole_Es, Finset.mem_union] at he
      exact he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
    rw [pole_Es, Finset.mem_union]
    exact mem_edgesIn_or_bd heΔ (Finset.mem_sdiff.mp hi).1
  refine ⟨fun e ↦ if e = freshE (Δ.pole (Δ.Vs \ X)) then
      tvec hPX c 0 + tvec hPX c (pairing mX 0) else c e, ⟨?_, ?_⟩, fun d hd ↦ ?_⟩
  · -- nonzero colours
    intro e he
    dsimp only
    split_ifs with h
    · exact (add_ne_of_ne (htn 0) (htn _) (hthet 0)).1
    · -- an old edge with an end in the new pole
      rw [pole_Es, Finset.mem_union] at he
      have heQ : e ∈ (cap hPXc mX).Es :=
        he.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
      rw [cap_Es, Finset.mem_insert] at heQ
      have heP : e ∈ (Δ.pole (Δ.Vs \ X)).Es := heQ.resolve_left h
      apply hc.1
      -- `e` has an end in the new pole's vertex set
      have hend : ∃ i, (cap hPXc mX).ends e i ∈
          insert (freshV (Δ.pole (Δ.Vs \ X))) (insert (freshV (Δ.pole (Δ.Vs \ X)) + 1) (W \ X)) := by
        rcases he with he | he
        · exact ⟨0, (mem_edgesIn.mp he).2 0⟩
        · obtain ⟨i, hi, _⟩ := bd_side he
          exact ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hend
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      by_cases hin : Δ.ends e i ∈ Δ.Vs \ X
      · rw [cap_ends_old hPXc mX heP hin] at hi
        rcases hi with hi | hi | hi
        · exact absurd (hi ▸ hin) (freshV_notMem (P := Δ.pole (Δ.Vs \ X)))
        · exact absurd (hi ▸ hin) (freshV_succ_notMem (P := Δ.pole (Δ.Vs \ X)))
        · exact hold e heP i hi
      · -- the end at a fresh vertex: `e` is a dangling edge of the complement pole
        have hd : e ∈ (Δ.pole (Δ.Vs \ X)).dangling := mem_dangling.mpr ⟨heP, i, hin⟩
        rw [dangling_pole, bd_compl hcl] at hd
        exact hbdX hd
  · -- properness
    intro v hv h₁ h₁m h₂ h₂m heq
    dsimp only at heq
    have hv' : v ∈ insert (freshV (Δ.pole (Δ.Vs \ X)))
        (insert (freshV (Δ.pole (Δ.Vs \ X)) + 1) (W \ X)) := hv
    rw [halfEdgesIn_pole_eq (Q := cap hPXc mX) hv'] at h₁m h₂m
    have hu : freshV (Δ.pole (Δ.Vs \ X)) ∉ Δ.Vs \ X := freshV_notMem
    have hw : freshV (Δ.pole (Δ.Vs \ X)) + 1 ∉ Δ.Vs \ X := freshV_succ_notMem
    have hcne : ∀ d ∈ (Δ.pole (Δ.Vs \ X)).dangling, d ≠ freshE (Δ.pole (Δ.Vs \ X)) :=
      fun d hd ↦ hε' d (mem_dangling.mp hd).1
    -- the colours of the couple edges
    have hcol : ∀ k, c (bdEmb hPXc k) = tvec hPX c k := by
      intro k
      simp [tvec, hemb]
    -- the generic argument at a fresh vertex attached to the couple `{k₀, pairing mX k₀}`
    have key : ∀ (k₀ : Fin 4) (C : Finset ℕ) (j : Fin 2),
        C = {bdEmb hPXc k₀, bdEmb hPXc (pairing mX k₀)} →
        tvec hPX c 0 + tvec hPX c (pairing mX 0) = tvec hPX c k₀ + tvec hPX c (pairing mX k₀) →
        h₁ ∈ insert (freshE (Δ.pole (Δ.Vs \ X)), j) (C.image fun d ↦ (d, outerIdx hPXc d)) →
        h₂ ∈ insert (freshE (Δ.pole (Δ.Vs \ X)), j) (C.image fun d ↦ (d, outerIdx hPXc d)) →
        h₁ = h₂ := by
      intro k₀ C j hC hs hm₁ hm₂
      have hCd : ∀ d ∈ C, d ∈ (Δ.pole (Δ.Vs \ X)).dangling := by
        intro d hd
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl <;> exact bdEmb_mem hPXc _
      have hne := add_ne_of_ne (htn k₀) (htn _) (hthet k₀)
      rw [← hs] at hne
      rw [Finset.mem_insert, Finset.mem_image] at hm₁ hm₂
      rcases hm₁ with rfl | ⟨d₁, hd₁, rfl⟩ <;> rcases hm₂ with rfl | ⟨d₂, hd₂, rfl⟩
      · rfl
      · exfalso
        simp only [if_true, hcne d₂ (hCd d₂ hd₂), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₂
        rcases hd₂ with rfl | rfl <;> rw [hcol] at heq
        · exact hne.2.1 heq
        · exact hne.2.2 heq
      · exfalso
        simp only [if_true, hcne d₁ (hCd d₁ hd₁), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁
        rcases hd₁ with rfl | rfl <;> rw [hcol] at heq
        · exact hne.2.1 heq.symm
        · exact hne.2.2 heq.symm
      · simp only [hcne d₁ (hCd d₁ hd₁), hcne d₂ (hCd d₂ hd₂), if_false] at heq
        rw [hC, Finset.mem_insert, Finset.mem_singleton] at hd₁ hd₂
        rcases hd₁ with rfl | rfl <;> rcases hd₂ with rfl | rfl
        · rfl
        · rw [hcol, hcol] at heq
          exact absurd heq (hthet k₀)
        · rw [hcol, hcol] at heq
          exact absurd heq.symm (hthet k₀)
        · rfl
    rw [Finset.mem_insert, Finset.mem_insert] at hv'
    rcases hv' with rfl | rfl | hv'
    · rw [cap_halfEdges_u] at h₁m h₂m
      exact key 0 (couple₁ hPXc mX) 0 rfl rfl h₁m h₂m
    · rw [cap_halfEdges_w] at h₁m h₂m
      exact key (other mX) (couple₂ hPXc mX) 1 rfl hsum h₁m h₂m
    · -- an old vertex: both half-edges are old edges of `Δ` at `v`
      have hvV : v ∈ Δ.Vs \ X := Finset.mem_sdiff.mpr ⟨hW (Finset.mem_sdiff.mp hv').1,
        (Finset.mem_sdiff.mp hv').2⟩
      have conv : ∀ h ∈ (cap hPXc mX).halfEdgesIn (cap hPXc mX).Es v,
          h ∈ Δ.halfEdgesIn (Δ.pole W).Es v ∧ h.1 ≠ freshE (Δ.pole (Δ.Vs \ X)) := by
        intro h hh
        rw [mem_halfEdgesIn, cap_Es, Finset.mem_insert] at hh
        rcases hh with ⟨hfe | he, hend⟩
        · exfalso
          rw [hfe, cap_ends_new] at hend
          split_ifs at hend
          · exact hu (hend ▸ hvV)
          · exact hw (hend ▸ hvV)
        · have hin : Δ.ends h.1 h.2 ∈ Δ.Vs \ X := by
            by_contra hnin
            have hd : h.1 ∈ (Δ.pole (Δ.Vs \ X)).dangling := mem_dangling.mpr ⟨he, h.2, hnin⟩
            have hio : h.2 = outerIdx hPXc h.1 := by
              rcases idx_eq_inner_or_outer hPXc hd h.2 with h' | h'
              · exact absurd (h' ▸ (innerIdx_spec hPXc hd).1) hnin
              · exact h'
            rw [hio, cap_ends_outer hPXc mX hd] at hend
            split_ifs at hend
            · exact hu (hend ▸ hvV)
            · exact hw (hend ▸ hvV)
          rw [cap_ends_old hPXc mX he hin] at hend
          refine ⟨mem_halfEdgesIn.mpr ⟨hold h.1 he h.2 (hend ▸ hv'), hend⟩, hε' h.1 he⟩
      obtain ⟨m₁, n₁⟩ := conv h₁ h₁m
      obtain ⟨m₂, n₂⟩ := conv h₂ h₂m
      simp only [n₁, n₂, if_false] at heq
      exact hc.unique_halfEdge (Finset.mem_sdiff.mp hv').1 m₁ m₂ heq
  · dsimp only
    rw [if_neg (hε' d (hbdW hd))]

end CapTransfer

end FinGraph
end GraphPuzzles
