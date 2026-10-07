import GraphPuzzles.FinGraph.FinGraphIso
import Mathlib.Data.Fintype.Perm

/-!
# Transport of colourings, poles, and boundary types along isomorphisms

Colourings transport along an isomorphism, so do dangling edges and the `4`-pole property, and
an isomorphism restricts to an isomorphism of poles.  For an isomorphism of `4`-poles the
boundary edges are permuted; the induced permutation of `Fin 4` conjugates the pairing, and
the isochromatic and heterochromatic properties transport accordingly.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

namespace Iso

variable {Γ₁ Γ₂ : FinGraph} (f : Iso Γ₁ Γ₂)

section Colouring

theorem isColouring {c : ℕ → Color} (hc : Γ₁.IsColouring c) : Γ₂.IsColouring (c ∘ f.ge) := by
  refine ⟨fun e he ↦ hc.1 _ (f.ge_mem e he), fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  have hv' := f.gv_mem v hv
  have hE : Γ₂.halfEdgesIn Γ₂.Es v = (Γ₁.halfEdgesIn Γ₁.Es (f.gv v)).image f.fh := by
    rw [← f.halfEdgesIn_image (Finset.Subset.refl _) hv', f.fv_gv v hv, ← f.Es_eq_image]
  rw [hE] at h₁m h₂m
  obtain ⟨h₁', h₁'m, rfl⟩ := Finset.mem_image.mp h₁m
  obtain ⟨h₂', h₂'m, rfl⟩ := Finset.mem_image.mp h₂m
  have e₁ := (mem_halfEdgesIn.mp h₁'m).1
  have e₂ := (mem_halfEdgesIn.mp h₂'m).1
  simp only [Function.comp, fh, f.ge_fe _ e₁, f.ge_fe _ e₂] at heq
  rw [hc.unique_halfEdge hv' h₁'m h₂'m heq]

include f in
theorem colourable (h : Γ₁.Colourable) : Γ₂.Colourable := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c ∘ f.ge, f.isColouring hc⟩

include f in
theorem colourable_iff : Γ₁.Colourable ↔ Γ₂.Colourable :=
  ⟨f.colourable, f.symm.colourable⟩

theorem dangling_image : Γ₂.dangling = Γ₁.dangling.image f.fe := by
  ext e
  constructor
  · intro h
    obtain ⟨he, i, hi⟩ := mem_dangling.mp h
    refine Finset.mem_image.mpr ⟨f.ge e, mem_dangling.mpr ⟨f.ge_mem e he, sw (f.flip (f.ge e)) i,
      fun h' ↦ hi ?_⟩, f.fe_ge e he⟩
    have := (f.ends_iff (f.ge e) (f.ge_mem e he) _).mp h'
    rw [f.fe_ge e he, sw_sw] at this
    exact this
  · intro h
    obtain ⟨e', he'', rfl⟩ := Finset.mem_image.mp h
    obtain ⟨he', i, hi⟩ := mem_dangling.mp he''
    exact mem_dangling.mpr ⟨f.fe_mem e' he', sw (f.flip e') i,
      fun h' ↦ hi ((f.ends_iff e' he' i).mpr h')⟩

include f in
theorem isPole4 (h : Γ₁.IsPole4) : Γ₂.IsPole4 where
  cubic := f.isCubic h.cubic
  card_dangling := by
    rw [f.dangling_image, f.card_image_fe (fun e he ↦ (mem_dangling.mp he).1)]
    exact h.card_dangling
  has_inner := by
    intro e he
    obtain ⟨i, hi⟩ := h.has_inner (f.ge e) (f.ge_mem e he)
    refine ⟨sw (f.flip (f.ge e)) i, ?_⟩
    have := (f.ends_iff (f.ge e) (f.ge_mem e he) i).mp hi
    rw [f.fe_ge e he] at this
    exact this

end Colouring

section Pole

/-- An isomorphism restricts to the poles on corresponding vertex sets. -/
def pole {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) : Iso (Γ₁.pole X) (Γ₂.pole (X.image f.fv)) where
  fv := f.fv
  gv := f.gv
  fe := f.fe
  ge := f.ge
  flip := f.flip
  fv_mem := fun v hv ↦ Finset.mem_image_of_mem _ hv
  gv_mem := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    rw [f.gv_fv v' (hX hv')]
    exact hv'
  gv_fv := fun v hv ↦ f.gv_fv v (hX hv)
  fv_gv := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    rw [f.gv_fv v' (hX hv')]
  fe_mem := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he ⊢
    rw [f.edgesIn_image hX, f.bd_image hX]
    rcases he with he | he
    · exact Or.inl (Finset.mem_image_of_mem _ he)
    · exact Or.inr (Finset.mem_image_of_mem _ he)
  ge_mem := by
    intro e he
    rw [pole_Es, Finset.mem_union, f.edgesIn_image hX, f.bd_image hX] at he
    rw [pole_Es, Finset.mem_union]
    rcases he with he | he
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [f.ge_fe _ (edgesIn_subset X he')]
      exact Or.inl he'
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [f.ge_fe _ (bd_subset X he')]
      exact Or.inr he'
  ge_fe := by
    intro e he
    rw [pole_Es, Finset.mem_union] at he
    exact f.ge_fe e (he.elim (fun h ↦ edgesIn_subset X h) (fun h ↦ bd_subset X h))
  fe_ge := by
    intro e he
    rw [pole_Es, Finset.mem_union, f.edgesIn_image hX, f.bd_image hX] at he
    rcases he with he | he
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [f.ge_fe _ (edgesIn_subset X he')]
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [f.ge_fe _ (bd_subset X he')]
  ends_iff := by
    intro e he i
    rw [pole_Es, Finset.mem_union] at he
    exact (f.ends_mem_image_iff hX (he.elim (fun h ↦ edgesIn_subset X h) (fun h ↦ bd_subset X h)) i).symm
  map_ends := by
    intro e he i hi
    rw [pole_Es, Finset.mem_union] at he
    exact f.map_ends e (he.elim (fun h ↦ edgesIn_subset X h) (fun h ↦ bd_subset X h)) i (hX hi)

@[simp] theorem pole_fv {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) : (f.pole hX).fv = f.fv := rfl
@[simp] theorem pole_fe {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) : (f.pole hX).fe = f.fe := rfl
@[simp] theorem pole_ge {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) : (f.pole hX).ge = f.ge := rfl

end Pole

section BoundaryPerm

variable (hP₁ : Γ₁.IsPole4) (hP₂ : Γ₂.IsPole4)

/-- The image of a boundary edge is a boundary edge of the other pole. -/
theorem fe_bdEmb_mem (i : Fin 4) : f.fe (bdEmb hP₁ i) ∈ Γ₂.dangling := by
  rw [f.dangling_image]
  exact Finset.mem_image_of_mem _ (bdEmb_mem hP₁ i)

/-- The permutation of boundary positions induced by an isomorphism of `4`-poles. -/
noncomputable def bdPermFun (i : Fin 4) : Fin 4 :=
  Classical.choose (exists_bdEmb_eq hP₂ (f.fe_bdEmb_mem hP₁ i))

theorem bdEmb_bdPermFun (i : Fin 4) : bdEmb hP₂ (f.bdPermFun hP₁ hP₂ i) = f.fe (bdEmb hP₁ i) :=
  Classical.choose_spec (exists_bdEmb_eq hP₂ (f.fe_bdEmb_mem hP₁ i))

theorem bdPermFun_injective : Function.Injective (f.bdPermFun hP₁ hP₂) := by
  intro i j h
  have := congrArg (bdEmb hP₂) h
  rw [f.bdEmb_bdPermFun, f.bdEmb_bdPermFun] at this
  exact bdEmb_injective hP₁ (f.fe_inj (a_mem_Es (bdEmb_mem hP₁ i)) (a_mem_Es (bdEmb_mem hP₁ j)) this)

/-- The boundary permutation as an equivalence. -/
noncomputable def bdPerm : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨f.bdPermFun_injective hP₁ hP₂, rfl⟩)

theorem bdPerm_apply (i : Fin 4) : f.bdPerm hP₁ hP₂ i = f.bdPermFun hP₁ hP₂ i := rfl

theorem bdEmb_bdPerm (i : Fin 4) : bdEmb hP₂ (f.bdPerm hP₁ hP₂ i) = f.fe (bdEmb hP₁ i) :=
  f.bdEmb_bdPermFun hP₁ hP₂ i

theorem tvec_ge (c : ℕ → Color) (i : Fin 4) :
    tvec hP₂ (c ∘ f.ge) (f.bdPerm hP₁ hP₂ i) = tvec hP₁ c i := by
  unfold tvec
  simp only [Function.comp, f.bdEmb_bdPerm, f.ge_fe _ (a_mem_Es (bdEmb_mem hP₁ i))]

/-- Boundary vectors correspond up to the boundary permutation. -/
theorem mem_Col_iff (t : Fin 4 → Color) :
    t ∈ Col hP₂ ↔ (t ∘ f.bdPerm hP₁ hP₂) ∈ Col hP₁ := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c ∘ f.fe, f.symm.isColouring hc, ?_⟩
    funext i
    simp only [tvec, Function.comp]
    rw [f.bdEmb_bdPerm]
  · rintro ⟨c, hc, hct⟩
    refine ⟨c ∘ f.ge, f.isColouring hc, ?_⟩
    funext j
    obtain ⟨i, rfl⟩ := (f.bdPerm hP₁ hP₂).surjective j
    rw [f.tvec_ge hP₁ hP₂]
    exact congrFun hct i

end BoundaryPerm

end Iso

section Conj

/-- The pairing index whose partner of `0` is `j`. -/
def pairIdx : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2

/-- Conjugating a pairing by a permutation of the boundary positions. -/
def conj (π : Equiv.Perm (Fin 4)) (m : Fin 3) : Fin 3 := pairIdx (π (pairing m (π.symm 0)))

theorem pairing_conj (π : Equiv.Perm (Fin 4)) (m : Fin 3) (i : Fin 4) :
    pairing (conj π m) (π i) = π (pairing m i) := by
  revert π m i
  decide

theorem conj_symm_conj (π : Equiv.Perm (Fin 4)) (m : Fin 3) : conj π.symm (conj π m) = m := by
  revert π m
  decide

namespace Iso

variable {Γ₁ Γ₂ : FinGraph} (f : Iso Γ₁ Γ₂) (hP₁ : Γ₁.IsPole4) (hP₂ : Γ₂.IsPole4)

theorem isoWith (m : Fin 3) (h : IsoWith hP₁ m) : IsoWith hP₂ (conj (f.bdPerm hP₁ hP₂) m) := by
  intro t ht j
  obtain ⟨i, rfl⟩ := (f.bdPerm hP₁ hP₂).surjective j
  rw [pairing_conj]
  exact h _ ((f.mem_Col_iff hP₁ hP₂ t).mp ht) i

theorem hetWith (m : Fin 3) (h : HetWith hP₁ m) : HetWith hP₂ (conj (f.bdPerm hP₁ hP₂) m) := by
  intro t ht j
  obtain ⟨i, rfl⟩ := (f.bdPerm hP₁ hP₂).surjective j
  rw [pairing_conj]
  exact h _ ((f.mem_Col_iff hP₁ hP₂ t).mp ht) i

end Iso

end Conj

end FinGraph
end GraphPuzzles
