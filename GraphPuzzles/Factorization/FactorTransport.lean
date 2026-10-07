import GraphPuzzles.Factorization.FactorSystem

/-!
# Steps transport along isomorphisms

An isomorphism of closed graphs carries a valid datum to a valid datum, and the factors to
isomorphic factors (via `capIso` and `joinIso`).  The boundary permutations induced on the two
poles of a cut coincide, so the transported pairing is the same on both sides.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ Δ' : FinGraph} (f : Iso Δ Δ')

/-- The boundary permutations of the two poles of a cut agree. -/
theorem Iso.bdPerm_compl (hcl : Δ.IsClosed) (hcl' : Δ'.IsClosed) {X : Finset ℕ} (hX : X ⊆ Δ.Vs)
    (hP : (Δ.pole X).IsPole4) (hQ : (Δ'.pole (X.image f.fv)).IsPole4)
    (hP' : (Δ.pole (Δ.Vs \ X)).IsPole4) (hQ' : (Δ'.pole ((Δ.Vs \ X).image f.fv)).IsPole4) :
    (f.pole hX).bdPerm hP hQ = (f.pole Finset.sdiff_subset).bdPerm hP' hQ' := by
  apply Equiv.ext
  intro i
  have h1 : ∀ j, bdEmb hP j = bdEmb hP' j :=
    bdEmb_congr hP hP' (by rw [dangling_pole, dangling_pole, bd_compl hcl])
  have h2 : ∀ j, bdEmb hQ j = bdEmb hQ' j :=
    bdEmb_congr hQ hQ' (by rw [dangling_pole, dangling_pole, ← f.sdiff_image hX, bd_compl hcl'])
  apply bdEmb_injective hQ'
  rw [← h2, Iso.bdEmb_bdPerm, Iso.bdEmb_bdPerm, h1]
  rfl

theorem join_congr {Γ : FinGraph} {X₁ X₂ : Finset ℕ} (h : X₁ = X₂) (hP₁ : (Γ.pole X₁).IsPole4)
    (hP₂ : (Γ.pole X₂).IsPole4) {m₁ m₂ : Fin 3} (hm : m₁ = m₂) : join hP₁ m₁ = join hP₂ m₂ := by
  subst h
  subst hm
  rfl

include f in
/-- **Steps transport along isomorphisms.** -/
theorem Step.transport {C D : FinGraph} (h : Step Δ C D) :
    ∃ C' D', Step Δ' C' D' ∧ Nonempty (Iso C C') ∧ Nonempty (Iso D D') := by
  obtain ⟨Z, m, hcl, hcub, hg, hcolZ, hcolZc, hv, h7⟩ := h
  have hZ := hv.cycSep
  have hZV := hZ.1
  have hZc := cycSep_compl hcl hZ
  have hPZ := hZ.isPole4 hcub
  have hPZc := hZc.isPole4 hcub
  obtain ⟨_, hiso⟩ := hv.iso
  obtain ⟨_, hhet⟩ := hv.het
  have e1 : factorOf Δ Z = cap hPZ m := factorOf_eq_cap hPZ hcolZ hiso
  have e2 : factorOf Δ (Δ.Vs \ Z) = join hPZc m := factorOf_eq_join hPZc hcolZc hhet
  -- the transported data
  have hcl' := f.isClosed hcl
  have hcub' := f.isCubic hcub
  have hg' := f.girth5 hg
  have hZ' : Δ'.CycSep (Z.image f.fv) := f.cycSep_image hZ
  have hZc' : Δ'.CycSep (Δ'.Vs \ Z.image f.fv) := cycSep_compl hcl' hZ'
  have hPZ' := hZ'.isPole4 hcub'
  have hPZc' := hZc'.isPole4 hcub'
  have hsd : (Δ.Vs \ Z).image f.fv = Δ'.Vs \ Z.image f.fv := (f.sdiff_image hZV).symm
  have hQc : (Δ'.pole ((Δ.Vs \ Z).image f.fv)).IsPole4 := by rw [hsd]; exact hPZc'
  set π := (f.pole hZV).bdPerm hPZ hPZ' with hπ
  set m' := conj π m with hm'
  have hcolZ' : (Δ'.pole (Z.image f.fv)).Colourable := (f.pole hZV).colourable hcolZ
  have hcolZc' : (Δ'.pole (Δ'.Vs \ Z.image f.fv)).Colourable := by
    rw [← hsd]
    exact (f.pole Finset.sdiff_subset).colourable hcolZc
  have hiso' : IsoWith hPZ' m' := (f.pole hZV).isoWith hPZ hPZ' m hiso
  have hhet' : HetWith hPZc' m' := by
    have := (f.pole Finset.sdiff_subset).hetWith hPZc hQc m hhet
    rw [← f.bdPerm_compl hcl hcl' hZV hPZ hPZ' hPZc hQc] at this
    -- transport along the equality of vertex sets
    have key : ∀ (X₁ X₂ : Finset ℕ) (h : X₁ = X₂) (hP₁ : (Δ'.pole X₁).IsPole4)
        (hP₂ : (Δ'.pole X₂).IsPole4) (k : Fin 3), HetWith hP₁ k → HetWith hP₂ k := by
      intro X₁ X₂ h hP₁ hP₂ k hk
      subst h
      exact hk
    exact key _ _ hsd hQc hPZc' m' this
  have hv' : Δ'.ValidDatum (Z.image f.fv) m' := ⟨hZ', ⟨hPZ', hiso'⟩, ⟨hPZc', hhet'⟩⟩
  have e1' : factorOf Δ' (Z.image f.fv) = cap hPZ' m' := factorOf_eq_cap hPZ' hcolZ' hiso'
  have e2' : factorOf Δ' (Δ'.Vs \ Z.image f.fv) = join hPZc' m' :=
    factorOf_eq_join hPZc' hcolZc' hhet'
  have iso1 : Nonempty (Iso (cap hPZ m) (cap hPZ' m')) := ⟨capIso (f.pole hZV) hPZ hPZ' m⟩
  have iso2 : Nonempty (Iso (join hPZc m) (join hPZc' m')) := by
    refine ⟨(joinIso (f.pole Finset.sdiff_subset) hPZc hQc m).trans ?_⟩
    have : join hQc (conjPairing (f.pole Finset.sdiff_subset) hPZc hQc m) = join hPZc' m' := by
      apply join_congr hsd
      show conj ((f.pole Finset.sdiff_subset).bdPerm hPZc hQc) m = conj π m
      rw [hπ, f.bdPerm_compl hcl hcl' hZV hPZ hPZ' hPZc hQc]
    rw [this]
    exact Iso.refl _
  have hstep : Step Δ' (factorOf Δ' (Z.image f.fv)) (factorOf Δ' (Δ'.Vs \ Z.image f.fv)) :=
    ⟨Z.image f.fv, m', hcl', hcub', hg', hcolZ', hcolZc', hv', Or.inl ⟨rfl, rfl⟩⟩
  rcases h7 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, hstep, by rw [e1, e1']; exact iso1, by rw [e2, e2']; exact iso2⟩
  · exact ⟨_, _, hstep.symm, by rw [e2, e2']; exact iso2, by rw [e1, e1']; exact iso1⟩

end FinGraph
end GraphPuzzles
