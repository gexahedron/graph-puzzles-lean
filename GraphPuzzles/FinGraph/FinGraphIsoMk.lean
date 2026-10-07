import GraphPuzzles.FinGraph.FinGraphIso

/-!
# Isomorphisms of closed graphs from forward maps

An isomorphism of closed graphs is determined by its forward maps on vertices and edges
together with the flips; the inverse maps are recovered by classical choice.
-/

namespace GraphPuzzles
namespace FinGraph
namespace Iso

variable {Γ₁ Γ₂ : FinGraph}

open Classical in
/-- Build an isomorphism of closed graphs from bijective forward maps. -/
noncomputable def mk' (hcl₁ : Γ₁.IsClosed) (fv fe : ℕ → ℕ) (flip : ℕ → Bool)
    (hV : ∀ v ∈ Γ₁.Vs, fv v ∈ Γ₂.Vs) (hVsurj : ∀ v ∈ Γ₂.Vs, ∃ u ∈ Γ₁.Vs, fv u = v)
    (hVinj : ∀ u ∈ Γ₁.Vs, ∀ v ∈ Γ₁.Vs, fv u = fv v → u = v)
    (hE : ∀ e ∈ Γ₁.Es, fe e ∈ Γ₂.Es) (hEsurj : ∀ e ∈ Γ₂.Es, ∃ d ∈ Γ₁.Es, fe d = e)
    (hEinj : ∀ d ∈ Γ₁.Es, ∀ e ∈ Γ₁.Es, fe d = fe e → d = e)
    (hends : ∀ e ∈ Γ₁.Es, ∀ i, Γ₂.ends (fe e) (sw (flip e) i) = fv (Γ₁.ends e i)) :
    Iso Γ₁ Γ₂ where
  fv := fv
  gv := fun v ↦ if h : ∃ u ∈ Γ₁.Vs, fv u = v then h.choose else v
  fe := fe
  ge := fun e ↦ if h : ∃ d ∈ Γ₁.Es, fe d = e then h.choose else e
  flip := flip
  fv_mem := hV
  gv_mem := by
    intro v hv
    have h := hVsurj v hv
    simp only [dif_pos h]
    exact h.choose_spec.1
  gv_fv := by
    intro v hv
    have h : ∃ u ∈ Γ₁.Vs, fv u = fv v := ⟨v, hv, rfl⟩
    simp only [dif_pos h]
    exact hVinj _ h.choose_spec.1 _ hv h.choose_spec.2
  fv_gv := by
    intro v hv
    have h := hVsurj v hv
    simp only [dif_pos h]
    exact h.choose_spec.2
  fe_mem := hE
  ge_mem := by
    intro e he
    have h := hEsurj e he
    simp only [dif_pos h]
    exact h.choose_spec.1
  ge_fe := by
    intro e he
    have h : ∃ d ∈ Γ₁.Es, fe d = fe e := ⟨e, he, rfl⟩
    simp only [dif_pos h]
    exact hEinj _ h.choose_spec.1 _ he h.choose_spec.2
  fe_ge := by
    intro e he
    have h := hEsurj e he
    simp only [dif_pos h]
    exact h.choose_spec.2
  ends_iff := by
    intro e he i
    refine ⟨fun _ ↦ ?_, fun _ ↦ hcl₁ e he i⟩
    rw [hends e he i]
    exact hV _ (hcl₁ e he i)
  map_ends := by
    intro e he i _
    exact (hends e he i).symm

/-- Build an isomorphism of closed graphs from bijective forward maps, where the ends of an
edge are matched as an unordered pair. -/
noncomputable def mk'' (hcl₁ : Γ₁.IsClosed) (fv fe : ℕ → ℕ)
    (hV : ∀ v ∈ Γ₁.Vs, fv v ∈ Γ₂.Vs) (hVsurj : ∀ v ∈ Γ₂.Vs, ∃ u ∈ Γ₁.Vs, fv u = v)
    (hVinj : ∀ u ∈ Γ₁.Vs, ∀ v ∈ Γ₁.Vs, fv u = fv v → u = v)
    (hE : ∀ e ∈ Γ₁.Es, fe e ∈ Γ₂.Es) (hEsurj : ∀ e ∈ Γ₂.Es, ∃ d ∈ Γ₁.Es, fe d = e)
    (hEinj : ∀ d ∈ Γ₁.Es, ∀ e ∈ Γ₁.Es, fe d = fe e → d = e)
    (hends : ∀ e ∈ Γ₁.Es,
      (Γ₂.ends (fe e) 0 = fv (Γ₁.ends e 0) ∧ Γ₂.ends (fe e) 1 = fv (Γ₁.ends e 1)) ∨
      (Γ₂.ends (fe e) 0 = fv (Γ₁.ends e 1) ∧ Γ₂.ends (fe e) 1 = fv (Γ₁.ends e 0))) :
    Iso Γ₁ Γ₂ :=
  mk' hcl₁ fv fe
    (fun e ↦ decide (¬ (Γ₂.ends (fe e) 0 = fv (Γ₁.ends e 0) ∧
      Γ₂.ends (fe e) 1 = fv (Γ₁.ends e 1))))
    hV hVsurj hVinj hE hEsurj hEinj (by
      intro e he i
      by_cases h : Γ₂.ends (fe e) 0 = fv (Γ₁.ends e 0) ∧ Γ₂.ends (fe e) 1 = fv (Γ₁.ends e 1)
      · simp only [h, sw]
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · exact h.1
        · exact h.2
      · simp only [h, not_false_eq_true, decide_true, sw, if_true]
        have h' := (hends e he).resolve_left h
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · rw [rev_zero']; exact h'.2
        · rw [rev_one']; exact h'.1)

/-- An isomorphism between graphs with the same vertices and edges, up to flips. -/
def ofEq (hV : Γ₂.Vs = Γ₁.Vs) (hE : Γ₂.Es = Γ₁.Es) (flip : ℕ → Bool)
    (hends : ∀ e ∈ Γ₁.Es, ∀ i, Γ₂.ends e (sw (flip e) i) = Γ₁.ends e i) : Iso Γ₁ Γ₂ where
  fv := id
  gv := id
  fe := id
  ge := id
  flip := flip
  fv_mem := fun v hv ↦ by rw [hV]; exact hv
  gv_mem := fun v hv ↦ by rw [← hV]; exact hv
  gv_fv := fun _ _ ↦ rfl
  fv_gv := fun _ _ ↦ rfl
  fe_mem := fun e he ↦ by rw [hE]; exact he
  ge_mem := fun e he ↦ by rw [← hE]; exact he
  ge_fe := fun _ _ ↦ rfl
  fe_ge := fun _ _ ↦ rfl
  ends_iff := fun e he i ↦ by
    show Γ₁.ends e i ∈ Γ₁.Vs ↔ Γ₂.ends e (sw (flip e) i) ∈ Γ₂.Vs
    rw [hends e he i, hV]
  map_ends := fun e he i _ ↦ by
    show Γ₁.ends e i = Γ₂.ends e (sw (flip e) i)
    rw [hends e he i]

end Iso
end FinGraph
end GraphPuzzles
