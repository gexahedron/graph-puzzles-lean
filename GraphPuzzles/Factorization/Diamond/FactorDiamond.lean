import GraphPuzzles.Factorization.Diamond.FactorDblCC
import GraphPuzzles.Factorization.Diamond.FactorDblJJ
import GraphPuzzles.Factorization.Diamond.FactorDblCJ
import GraphPuzzles.Factorization.Diamond.FactorDblJC

/-!
# The outer double completion is the canonical double completion

In a good class, the second factor of a factor along nested cuts `X ⊆ W` is isomorphic to the
canonical double completion.  The type of the projected cut is determined by the class (the
factor is a snark whose pole at `X` is isomorphic to the pole of `X` in `Δ`), and the pairing
transports along the pole isomorphism.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Congr

theorem IsPole4.congr {Γ₁ Γ₂ : FinGraph} (h : Γ₁ = Γ₂) (hP : Γ₁.IsPole4) : Γ₂.IsPole4 := by
  subst h; exact hP

theorem IsoWith.congr {Γ₁ Γ₂ : FinGraph} (h : Γ₁ = Γ₂) (hP₁ : Γ₁.IsPole4) (hP₂ : Γ₂.IsPole4)
    (m : Fin 3) (hi : IsoWith hP₁ m) : IsoWith hP₂ m := by
  subst h; exact hi

theorem HetWith.congr {Γ₁ Γ₂ : FinGraph} (h : Γ₁ = Γ₂) (hP₁ : Γ₁.IsPole4) (hP₂ : Γ₂.IsPole4)
    (m : Fin 3) (hi : HetWith hP₁ m) : HetWith hP₂ m := by
  subst h; exact hi

theorem cap_congr' {P₁ P₂ : FinGraph} (h : P₁ = P₂) (hP₁ : P₁.IsPole4) (hP₂ : P₂.IsPole4)
    (m : Fin 3) : cap hP₁ m = cap hP₂ m := by
  subst h; rfl

theorem join_congr' {P₁ P₂ : FinGraph} (h : P₁ = P₂) (hP₁ : P₁.IsPole4) (hP₂ : P₂.IsPole4)
    (m : Fin 3) : join hP₁ m = join hP₂ m := by
  subst h; rfl

theorem pole_congr {Γ : FinGraph} {Z₁ Z₂ : Finset ℕ} (h : Z₁ = Z₂) : Γ.pole Z₁ = Γ.pole Z₂ := by
  rw [h]

/-- The transport of the partner function along an isomorphism of poles. -/
theorem partner_conj {Γ₁ Γ₂ : FinGraph} (g : Iso Γ₂ Γ₁) (hP₂ : Γ₂.IsPole4) (hP₁ : Γ₁.IsPole4)
    (m : Fin 3) {c : ℕ} (hc : c ∈ Γ₁.dangling) :
    partner hP₁ (conj (g.bdPerm hP₂ hP₁) m) c = g.fe (partner hP₂ m (g.ge c)) := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP₁ hc
  obtain ⟨i, rfl⟩ := (g.bdPerm hP₂ hP₁).surjective k
  rw [partner_bdEmb, pairing_conj, g.bdEmb_bdPerm, g.bdEmb_bdPerm,
    g.ge_fe _ (a_mem_Es (bdEmb_mem hP₂ i)), partner_bdEmb]

theorem cap_Vs_sdiff {Δ : FinGraph} {X W : Finset ℕ} (hXW : X ⊆ W) (hP : (Δ.pole W).IsPole4)
    (m : Fin 3) : (cap hP m).Vs \ X =
      insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X)) := by
  have h1 : freshV (Δ.pole W) ∉ X := fun h ↦ freshV_notMem (P := Δ.pole W) (hXW h)
  have h2 : freshV (Δ.pole W) + 1 ∉ X := fun h ↦ freshV_succ_notMem (P := Δ.pole W) (hXW h)
  rw [cap_Vs, pole_Vs]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨(rfl | rfl | hv), hX⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hv, hX⟩)
  · rintro (rfl | rfl | ⟨hv, hX⟩)
    · exact ⟨Or.inl rfl, h1⟩
    · exact ⟨Or.inr (Or.inl rfl), h2⟩
    · exact ⟨Or.inr (Or.inr hv), hX⟩

theorem join_Vs_sdiff {Δ : FinGraph} {X W : Finset ℕ} (hP : (Δ.pole W).IsPole4) (m : Fin 3) :
    (join hP m).Vs \ X = W \ X := by
  rw [join_Vs, pole_Vs]

end Congr

section Class

variable {P : FinGraph → Prop} (hG : GoodClass P) {Δ : FinGraph} (hΔ : P Δ)
include hG hΔ

/-- The complementary pole of an isochromatic pole is heterochromatic. -/
theorem hetWith_compl {Z : Finset ℕ} (hZ : Δ.CycSep Z) (hPZ : (Δ.pole Z).IsPole4)
    (hPZc : (Δ.pole (Δ.Vs \ Z)).IsPole4) {m : Fin 3} (h : IsoWith hPZ m) : HetWith hPZc m := by
  have hcl := hG.closed Δ hΔ
  have hcolZ := hG.pole_colourable Δ hΔ Z hZ
  have hcolZc := hG.pole_colourable Δ hΔ _ (cycSep_compl hcl hZ)
  obtain ⟨m', hm⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPZ hPZc hcolZ hcolZc
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [IsoWith.unique hPZ hcolZ h h1]; exact h2
  · exact absurd h1 (fun h1 ↦ not_isoWith_hetWith hPZ hcolZ h h1)

/-- The complementary pole of a heterochromatic pole is isochromatic. -/
theorem isoWith_compl {Z : Finset ℕ} (hZ : Δ.CycSep Z) (hPZ : (Δ.pole Z).IsPole4)
    (hPZc : (Δ.pole (Δ.Vs \ Z)).IsPole4) {m : Fin 3} (h : HetWith hPZ m) : IsoWith hPZc m := by
  have hcl := hG.closed Δ hΔ
  have hcolZ := hG.pole_colourable Δ hΔ Z hZ
  have hcolZc := hG.pole_colourable Δ hΔ _ (cycSep_compl hcl hZ)
  obtain ⟨m', hm⟩ := exists_pairing hcl (hG.snark Δ hΔ) hPZ hPZc hcolZ hcolZc
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h (fun h ↦ not_isoWith_hetWith hPZ hcolZ h1 h)
  · rw [HetWith.unique hPZ hcolZ h h1]; exact h2

/-- **The outer double completion is the canonical double completion.** -/
theorem dbl_outer_iso {X W : Finset ℕ} (hXW : X ⊆ W) (hcsW : Δ.CycSep W)
    (hPW : (Δ.pole W).IsPole4) (hPWc : (Δ.pole (Δ.Vs \ W)).IsPole4) (mW : Fin 3)
    (hPX : (Δ.pole X).IsPole4) (mX : Fin 3)
    (hW' : (IsoWith hPW mW ∧ HetWith hPWc mW) ∨ (HetWith hPW mW ∧ IsoWith hPWc mW))
    (hX' : IsoWith hPX mX ∨ HetWith hPX mX)
    (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
    (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)
    (hcs : (factorOf Δ W).CycSep X) (gX gW : Bool)
    (hgX : gX = true ↔ HetWith hPX mX) (hgW : gW = true ↔ IsoWith hPW mW) :
    Nonempty (Iso (factorOf (factorOf Δ W) ((factorOf Δ W).Vs \ X))
      (can Δ (W \ X) (Δ.bd X) (Δ.bd W) (partner hPX mX) (partner hPW mW) gX gW)) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hW : W ⊆ Δ.Vs := hcsW.1
  have hcolW := hG.pole_colourable Δ hΔ W hcsW
  have hcolWc := hG.pole_colourable Δ hΔ _ (cycSep_compl hcl hcsW)
  -- boundary couples of the `W`-cut never lie inside `∂X`
  have hno : ∀ k, bdEmb hPW k ∈ Δ.bd X → bdEmb hPW (pairing mW k) ∈ Δ.bd X → False := by
    intro k h1 h2
    have := hnoW (bdEmb hPW k) (dangling_pole W ▸ bdEmb_mem hPW k) h1
    rw [partner_bdEmb] at this
    exact this h2
  rcases hW' with ⟨hisoW, hhetWc⟩ | ⟨hhetW, hisoWc⟩
  · -- the outer factor is a cap
    have e1 : factorOf Δ W = cap hPW mW := factorOf_eq_cap hPW hcolW hisoW
    rw [e1] at hcs ⊢
    have hgW' : gW = true := hgW.mpr hisoW
    subst hgW'
    have hP₁ : P (cap hPW mW) := hG.cap_mem Δ hΔ W mW hPW ⟨hcsW, ⟨hPW, hisoW⟩, ⟨hPWc, hhetWc⟩⟩
    have hcl₁ : (cap hPW mW).IsClosed := cap_isClosed hPW mW
    obtain ⟨hP₁X, hP₁Xc, m'', hcases⟩ := factor_cases hG hP₁ hcs
    have hcol₁X := hG.pole_colourable _ hP₁ X hcs
    let f : Iso ((cap hPW mW).pole X) (Δ.pole X) := capPoleIso hPW mW hcl hW hXW
    let g : Iso (Δ.pole X) ((cap hPW mW).pole X) := f.symm
    have hcolX' : (Δ.pole X).Colourable := f.colourable hcol₁X
    have hdang : ((cap hPW mW).pole ((cap hPW mW).Vs \ X)).dangling =
        ((cap hPW mW).pole X).dangling := by
      rw [dangling_pole, dangling_pole, bd_compl hcl₁]
    have hdangX : ((cap hPW mW).pole X).dangling = Δ.bd X := by
      rw [dangling_pole, cap_bd_old hPW mW hcl hW hXW]
    have hset : (cap hPW mW).pole ((cap hPW mW).Vs \ X) = (cap hPW mW).pole
        (insert (freshV (Δ.pole W)) (insert (freshV (Δ.pole W) + 1) (W \ X))) :=
      pole_congr (cap_Vs_sdiff hXW hPW mW)
    have hQ := IsPole4.congr hset hP₁Xc
    rcases hX' with hisoX | hhetX
    · -- `X` is isochromatic: the inner factor is a join
      have hgX' : gX = false := by
        by_contra h
        have h' : gX = true := by cases gX <;> simp_all
        exact not_isoWith_hetWith hPX hcolX' hisoX (hgX.mp h')
      subst hgX'
      have hiso' := g.isoWith hPX hP₁X mX hisoX
      set mX' := conj (g.bdPerm hPX hP₁X) mX with hmX'
      rcases hcases with ⟨h1, -, -, -, h5, -⟩ | ⟨h1, -, -, -, -, -⟩
      · have hm : m'' = mX' := IsoWith.unique hP₁X hcol₁X h1 hiso'
        rw [hm] at h5
        rw [h5, join_congr' hset hP₁Xc hQ]
        apply dblCJ_iso hcl hXW hW hPW mW hPX mX hnoX hnoW hQ mX'
        intro c hc
        have hc' : c ∈ ((cap hPW mW).pole X).dangling := by rw [hdangX]; exact hc
        rw [← partner_congr hP₁Xc mX' hQ (congrArg dangling hset) c,
          partner_congr hP₁Xc mX' hP₁X hdang c, hmX', partner_conj g hPX hP₁X mX hc']
        rfl
      · exact absurd h1 (fun h1 ↦ not_isoWith_hetWith hP₁X hcol₁X hiso' h1)
    · -- `X` is heterochromatic: the inner factor is a cap
      have hgX' : gX = true := hgX.mpr hhetX
      subst hgX'
      have hhet' := g.hetWith hPX hP₁X mX hhetX
      set mX' := conj (g.bdPerm hPX hP₁X) mX with hmX'
      rcases hcases with ⟨h1, -, -, -, -, -⟩ | ⟨h1, -, -, -, h5, -⟩
      · exact absurd h1 (fun h1 ↦ not_isoWith_hetWith hP₁X hcol₁X h1 hhet')
      · have hm : m'' = mX' := HetWith.unique hP₁X hcol₁X h1 hhet'
        rw [hm] at h5
        rw [h5, cap_congr' hset hP₁Xc hQ]
        apply dblCC_iso hcl hXW hW hPW mW hPX mX hnoX hnoW hQ mX'
        intro c hc
        have hc' : c ∈ ((cap hPW mW).pole X).dangling := by rw [hdangX]; exact hc
        rw [← partner_congr hP₁Xc mX' hQ (congrArg dangling hset) c,
          partner_congr hP₁Xc mX' hP₁X hdang c, hmX', partner_conj g hPX hP₁X mX hc']
        rfl
  · -- the outer factor is a join
    have e1 : factorOf Δ W = join hPW mW := factorOf_eq_join hPW hcolW hhetW
    rw [e1] at hcs ⊢
    have hgW' : gW = false := by
      by_contra h
      have h' : gW = true := by cases gW <;> simp_all
      exact not_isoWith_hetWith hPW hcolW (hgW.mp h') hhetW
    subst hgW'
    have eW : Δ.Vs \ (Δ.Vs \ W) = W := Finset.sdiff_sdiff_eq_self hW
    have hPW' : (Δ.pole (Δ.Vs \ (Δ.Vs \ W))).IsPole4 := IsPole4.congr (pole_congr eW.symm) hPW
    have hP₁ : P (join hPW mW) := by
      have := hG.join_mem Δ hΔ (Δ.Vs \ W) mW hPW' ⟨cycSep_compl hcl hcsW, ⟨hPWc, hisoWc⟩,
        ⟨hPW', HetWith.congr (pole_congr eW.symm) hPW hPW' mW hhetW⟩⟩
      rw [join_congr' (pole_congr eW) hPW' hPW mW] at this
      exact this
    have hcl₁ : (join hPW mW).IsClosed := join_isClosed hPW mW
    obtain ⟨hP₁X, hP₁Xc, m'', hcases⟩ := factor_cases hG hP₁ hcs
    have hcol₁X := hG.pole_colourable _ hP₁ X hcs
    let f : Iso ((join hPW mW).pole X) (Δ.pole X) := joinPoleIso hPW mW hW X hXW hno
    let g : Iso (Δ.pole X) ((join hPW mW).pole X) := f.symm
    have hcolX' : (Δ.pole X).Colourable := f.colourable hcol₁X
    have hdang : ((join hPW mW).pole ((join hPW mW).Vs \ X)).dangling =
        ((join hPW mW).pole X).dangling := by
      rw [dangling_pole, dangling_pole, bd_compl hcl₁]
    have hset : (join hPW mW).pole ((join hPW mW).Vs \ X) = (join hPW mW).pole (W \ X) :=
      pole_congr (join_Vs_sdiff hPW mW)
    have hQ := IsPole4.congr hset hP₁Xc
    have hdangQ : ((join hPW mW).pole (W \ X)).dangling = ((join hPW mW).pole X).dangling := by
      rw [← hdang, ← hset]
    rcases hX' with hisoX | hhetX
    · have hgX' : gX = false := by
        by_contra h
        have h' : gX = true := by cases gX <;> simp_all
        exact not_isoWith_hetWith hPX hcolX' hisoX (hgX.mp h')
      subst hgX'
      have hiso' := g.isoWith hPX hP₁X mX hisoX
      set mX' := conj (g.bdPerm hPX hP₁X) mX with hmX'
      rcases hcases with ⟨h1, -, -, -, h5, -⟩ | ⟨h1, -, -, -, -, -⟩
      · have hm : m'' = mX' := IsoWith.unique hP₁X hcol₁X h1 hiso'
        rw [hm] at h5
        rw [h5, join_congr' hset hP₁Xc hQ]
        apply dblJJ_iso hcl hXW hW hPW mW hPX mX hnoX hnoW hQ mX'
        intro c hc
        have hc' : c ∈ ((join hPW mW).pole X).dangling := by rw [← hdangQ]; exact hc
        rw [partner_congr hQ mX' hP₁X hdangQ c, hmX', partner_conj g hPX hP₁X mX hc']
        rfl
      · exact absurd h1 (fun h1 ↦ not_isoWith_hetWith hP₁X hcol₁X hiso' h1)
    · have hgX' : gX = true := hgX.mpr hhetX
      subst hgX'
      have hhet' := g.hetWith hPX hP₁X mX hhetX
      set mX' := conj (g.bdPerm hPX hP₁X) mX with hmX'
      rcases hcases with ⟨h1, -, -, -, -, -⟩ | ⟨h1, -, -, -, h5, -⟩
      · exact absurd h1 (fun h1 ↦ not_isoWith_hetWith hP₁X hcol₁X h1 hhet')
      · have hm : m'' = mX' := HetWith.unique hP₁X hcol₁X h1 hhet'
        rw [hm] at h5
        rw [h5, cap_congr' hset hP₁Xc hQ]
        apply dblJC_iso hcl hXW hW hPW mW hPX mX hnoX hnoW hQ mX'
        intro c hc
        have hc' : c ∈ ((join hPW mW).pole X).dangling := by rw [← hdangQ]; exact hc
        rw [partner_congr hQ mX' hP₁X hdangQ c, hmX', partner_conj g hPX hP₁X mX hc']
        rfl

end Class

end FinGraph
end GraphPuzzles
