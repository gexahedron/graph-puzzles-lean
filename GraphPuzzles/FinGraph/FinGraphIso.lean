import GraphPuzzles.FinGraph.FinGraphColourOpen

/-!
# Isomorphisms of finite labelled multigraphs

An isomorphism relabels vertices and edges bijectively (with explicit inverses on the label
sets) and may reverse the numbered ends of an edge.  Inner ends correspond, and an end is a
vertex on one side exactly when the corresponding end is a vertex on the other side, so
dangling edges correspond.  Degrees, even edge sets, cycles, boundaries, girth, cyclic
connectivity, and colourability transport along isomorphisms; so do poles.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- Optionally reverse a numbered end. -/
def sw (b : Bool) (i : Fin 2) : Fin 2 := if b then Fin.rev i else i

@[simp] theorem sw_sw (b : Bool) (i : Fin 2) : sw b (sw b i) = i := by
  cases b <;> simp [sw]

theorem sw_injective (b : Bool) : Function.Injective (sw b) := by
  cases b <;> intro i j h <;> simp [sw] at h <;> exact h

/-- An isomorphism of finite labelled multigraphs. -/
structure Iso (Γ₁ Γ₂ : FinGraph) where
  fv : ℕ → ℕ
  gv : ℕ → ℕ
  fe : ℕ → ℕ
  ge : ℕ → ℕ
  flip : ℕ → Bool
  fv_mem : ∀ v ∈ Γ₁.Vs, fv v ∈ Γ₂.Vs
  gv_mem : ∀ v ∈ Γ₂.Vs, gv v ∈ Γ₁.Vs
  gv_fv : ∀ v ∈ Γ₁.Vs, gv (fv v) = v
  fv_gv : ∀ v ∈ Γ₂.Vs, fv (gv v) = v
  fe_mem : ∀ e ∈ Γ₁.Es, fe e ∈ Γ₂.Es
  ge_mem : ∀ e ∈ Γ₂.Es, ge e ∈ Γ₁.Es
  ge_fe : ∀ e ∈ Γ₁.Es, ge (fe e) = e
  fe_ge : ∀ e ∈ Γ₂.Es, fe (ge e) = e
  ends_iff : ∀ e ∈ Γ₁.Es, ∀ i, Γ₁.ends e i ∈ Γ₁.Vs ↔ Γ₂.ends (fe e) (sw (flip e) i) ∈ Γ₂.Vs
  map_ends : ∀ e ∈ Γ₁.Es, ∀ i, Γ₁.ends e i ∈ Γ₁.Vs →
    fv (Γ₁.ends e i) = Γ₂.ends (fe e) (sw (flip e) i)

namespace Iso

variable {Γ₁ Γ₂ Γ₃ : FinGraph}

/-- The identity isomorphism. -/
def refl (Γ : FinGraph) : Iso Γ Γ where
  fv := id
  gv := id
  fe := id
  ge := id
  flip := fun _ ↦ false
  fv_mem := fun _ h ↦ h
  gv_mem := fun _ h ↦ h
  gv_fv := fun _ _ ↦ rfl
  fv_gv := fun _ _ ↦ rfl
  fe_mem := fun _ h ↦ h
  ge_mem := fun _ h ↦ h
  ge_fe := fun _ _ ↦ rfl
  fe_ge := fun _ _ ↦ rfl
  ends_iff := fun _ _ _ ↦ by simp [sw]
  map_ends := fun _ _ _ _ ↦ by simp [sw]

variable (f : Iso Γ₁ Γ₂)

theorem fv_inj {x y : ℕ} (hx : x ∈ Γ₁.Vs) (hy : y ∈ Γ₁.Vs) (h : f.fv x = f.fv y) : x = y := by
  rw [← f.gv_fv x hx, ← f.gv_fv y hy, h]

theorem fe_inj {x y : ℕ} (hx : x ∈ Γ₁.Es) (hy : y ∈ Γ₁.Es) (h : f.fe x = f.fe y) : x = y := by
  rw [← f.ge_fe x hx, ← f.ge_fe y hy, h]

/-- The inverse isomorphism. -/
def symm : Iso Γ₂ Γ₁ where
  fv := f.gv
  gv := f.fv
  fe := f.ge
  ge := f.fe
  flip := fun e ↦ f.flip (f.ge e)
  fv_mem := f.gv_mem
  gv_mem := f.fv_mem
  gv_fv := f.fv_gv
  fv_gv := f.gv_fv
  fe_mem := f.ge_mem
  ge_mem := f.fe_mem
  ge_fe := f.fe_ge
  fe_ge := f.ge_fe
  ends_iff := by
    intro e he i
    have h := f.ends_iff (f.ge e) (f.ge_mem e he) (sw (f.flip (f.ge e)) i)
    rw [f.fe_ge e he, sw_sw] at h
    exact h.symm
  map_ends := by
    intro e he i hi
    have h := f.ends_iff (f.ge e) (f.ge_mem e he) (sw (f.flip (f.ge e)) i)
    rw [f.fe_ge e he, sw_sw] at h
    have h' := f.map_ends (f.ge e) (f.ge_mem e he) (sw (f.flip (f.ge e)) i) (h.mpr hi)
    rw [f.fe_ge e he, sw_sw] at h'
    rw [← h', f.gv_fv _ (h.mpr hi)]

/-- Composition of isomorphisms. -/
def trans (g : Iso Γ₂ Γ₃) : Iso Γ₁ Γ₃ where
  fv := g.fv ∘ f.fv
  gv := f.gv ∘ g.gv
  fe := g.fe ∘ f.fe
  ge := f.ge ∘ g.ge
  flip := fun e ↦ xor (f.flip e) (g.flip (f.fe e))
  fv_mem := fun v hv ↦ g.fv_mem _ (f.fv_mem v hv)
  gv_mem := fun v hv ↦ f.gv_mem _ (g.gv_mem v hv)
  gv_fv := fun v hv ↦ by simp [g.gv_fv _ (f.fv_mem v hv), f.gv_fv v hv]
  fv_gv := fun v hv ↦ by simp [f.fv_gv _ (g.gv_mem v hv), g.fv_gv v hv]
  fe_mem := fun e he ↦ g.fe_mem _ (f.fe_mem e he)
  ge_mem := fun e he ↦ f.ge_mem _ (g.ge_mem e he)
  ge_fe := fun e he ↦ by simp [g.ge_fe _ (f.fe_mem e he), f.ge_fe e he]
  fe_ge := fun e he ↦ by simp [f.fe_ge _ (g.ge_mem e he), g.fe_ge e he]
  ends_iff := by
    intro e he i
    have h1 := f.ends_iff e he i
    have h2 := g.ends_iff (f.fe e) (f.fe_mem e he) (sw (f.flip e) i)
    have hsw : sw (g.flip (f.fe e)) (sw (f.flip e) i) = sw (xor (f.flip e) (g.flip (f.fe e))) i := by
      cases f.flip e <;> cases g.flip (f.fe e) <;> simp [sw]
    rw [hsw] at h2
    exact h1.trans h2
  map_ends := by
    intro e he i hi
    have h1 := f.map_ends e he i hi
    have h2 := g.map_ends (f.fe e) (f.fe_mem e he) (sw (f.flip e) i) ((f.ends_iff e he i).mp hi)
    have hsw : sw (g.flip (f.fe e)) (sw (f.flip e) i) = sw (xor (f.flip e) (g.flip (f.fe e))) i := by
      cases f.flip e <;> cases g.flip (f.fe e) <;> simp [sw]
    rw [hsw] at h2
    simp only [Function.comp]
    rw [h1, h2]

section Transport

/-- The half-edge map. -/
def fh (h : ℕ × Fin 2) : ℕ × Fin 2 := (f.fe h.1, sw (f.flip h.1) h.2)

theorem fh_inj {h h' : ℕ × Fin 2} (hh : h.1 ∈ Γ₁.Es) (hh' : h'.1 ∈ Γ₁.Es) (heq : f.fh h = f.fh h') :
    h = h' := by
  unfold fh at heq
  obtain ⟨e, i⟩ := h
  obtain ⟨e', i'⟩ := h'
  simp only [Prod.mk.injEq] at heq
  have he : e = e' := f.fe_inj hh hh' heq.1
  subst he
  rw [Prod.mk.injEq]
  exact ⟨rfl, sw_injective _ heq.2⟩

/-- Half-edges of an edge set at a vertex correspond. -/
theorem halfEdgesIn_image {F : Finset ℕ} (hF : F ⊆ Γ₁.Es) {v : ℕ} (hv : v ∈ Γ₁.Vs) :
    Γ₂.halfEdgesIn (F.image f.fe) (f.fv v) = (Γ₁.halfEdgesIn F v).image f.fh := by
  ext ⟨e₂, j⟩
  constructor
  · intro h
    obtain ⟨he₂, hend⟩ := mem_halfEdgesIn.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he₂
    have hin : Γ₁.ends e (sw (f.flip e) j) ∈ Γ₁.Vs := by
      rw [f.ends_iff e (hF he), sw_sw]
      exact hend ▸ f.fv_mem v hv
    have hme := f.map_ends e (hF he) _ hin
    rw [sw_sw] at hme
    have hend' : f.fv (Γ₁.ends e (sw (f.flip e) j)) = f.fv v := hme.trans hend
    refine Finset.mem_image.mpr ⟨(e, sw (f.flip e) j), mem_halfEdgesIn.mpr ⟨he, f.fv_inj hin hv hend'⟩, ?_⟩
    simp [fh, sw_sw]
  · intro h
    obtain ⟨⟨e, i⟩, hmem, heq⟩ := Finset.mem_image.mp h
    obtain ⟨he, hend⟩ := mem_halfEdgesIn.mp hmem
    simp only [fh, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine mem_halfEdgesIn.mpr ⟨Finset.mem_image_of_mem _ he, ?_⟩
    rw [← f.map_ends e (hF he) i (hend ▸ hv), hend]

theorem degIn_image {F : Finset ℕ} (hF : F ⊆ Γ₁.Es) {v : ℕ} (hv : v ∈ Γ₁.Vs) :
    Γ₂.degIn (F.image f.fe) (f.fv v) = Γ₁.degIn F v := by
  unfold degIn
  rw [halfEdgesIn_image f hF hv]
  apply Finset.card_image_of_injOn
  intro h hh h' hh' heq
  exact f.fh_inj (hF (mem_halfEdgesIn.mp hh).1) (hF (mem_halfEdgesIn.mp hh').1) heq

theorem Es_eq_image : Γ₂.Es = Γ₁.Es.image f.fe := by
  ext e
  simp only [Finset.mem_image]
  constructor
  · intro he
    exact ⟨f.ge e, f.ge_mem e he, f.fe_ge e he⟩
  · rintro ⟨e', he', rfl⟩
    exact f.fe_mem e' he'

theorem Vs_eq_image : Γ₂.Vs = Γ₁.Vs.image f.fv := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · intro hv
    exact ⟨f.gv v, f.gv_mem v hv, f.fv_gv v hv⟩
  · rintro ⟨v', hv', rfl⟩
    exact f.fv_mem v' hv'

theorem deg_fv {v : ℕ} (hv : v ∈ Γ₁.Vs) : Γ₂.deg (f.fv v) = Γ₁.deg v := by
  unfold deg
  rw [f.Es_eq_image]
  exact f.degIn_image (Finset.Subset.refl _) hv

include f in
theorem isCubic (h : Γ₁.IsCubic) : Γ₂.IsCubic := by
  intro v hv
  rw [← f.fv_gv v hv, f.deg_fv (f.gv_mem v hv)]
  exact h _ (f.gv_mem v hv)

include f in
theorem isClosed (h : Γ₁.IsClosed) : Γ₂.IsClosed := by
  intro e he i
  have := f.ends_iff (f.ge e) (f.ge_mem e he) (sw (f.flip (f.ge e)) i)
  rw [f.fe_ge e he, sw_sw] at this
  exact this.mp (h _ (f.ge_mem e he) _)

theorem mem_image_fv {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) {v : ℕ} (hv : v ∈ Γ₁.Vs) :
    f.fv v ∈ X.image f.fv ↔ v ∈ X := by
  constructor
  · intro h
    obtain ⟨v', hv', heq⟩ := Finset.mem_image.mp h
    rw [f.fv_inj (hX hv') hv heq] at hv'
    exact hv'
  · intro h
    exact Finset.mem_image_of_mem _ h

/-- Inner ends of edges: membership in a vertex set transports. -/
theorem ends_mem_image_iff {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) {e : ℕ} (he : e ∈ Γ₁.Es) (i : Fin 2) :
    Γ₂.ends (f.fe e) (sw (f.flip e) i) ∈ X.image f.fv ↔ Γ₁.ends e i ∈ X := by
  by_cases hin : Γ₁.ends e i ∈ Γ₁.Vs
  · rw [← f.map_ends e he i hin]
    exact f.mem_image_fv hX hin
  · have hout : Γ₂.ends (f.fe e) (sw (f.flip e) i) ∉ Γ₂.Vs := fun h ↦ hin ((f.ends_iff e he i).mpr h)
    constructor
    · intro h
      exact absurd (Finset.image_subset_image hX h |> fun h ↦ f.Vs_eq_image ▸ h) hout
    · intro h
      exact absurd (hX h) hin

theorem rev_zero' : (Fin.rev 0 : Fin 2) = 1 := by decide
theorem rev_one' : (Fin.rev 1 : Fin 2) = 0 := by decide

theorem edgesIn_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    Γ₂.edgesIn (X.image f.fv) = (Γ₁.edgesIn X).image f.fe := by
  ext e
  constructor
  · intro h
    obtain ⟨he, hend⟩ := mem_edgesIn.mp h
    refine Finset.mem_image.mpr ⟨f.ge e, mem_edgesIn.mpr ⟨f.ge_mem e he, fun i ↦ ?_⟩, f.fe_ge e he⟩
    have := f.ends_mem_image_iff hX (f.ge_mem e he) i
    rw [f.fe_ge e he] at this
    exact this.mp (hend _)
  · intro h
    obtain ⟨e', he'', rfl⟩ := Finset.mem_image.mp h
    obtain ⟨he', hend⟩ := mem_edgesIn.mp he''
    refine mem_edgesIn.mpr ⟨f.fe_mem e' he', fun i ↦ ?_⟩
    have := f.ends_mem_image_iff hX he' (sw (f.flip e') i)
    rw [sw_sw] at this
    exact this.mpr (hend _)

theorem bd_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    Γ₂.bd (X.image f.fv) = (Γ₁.bd X).image f.fe := by
  ext e
  constructor
  · intro h
    obtain ⟨he, hiff⟩ := mem_bd.mp h
    refine Finset.mem_image.mpr ⟨f.ge e, mem_bd.mpr ⟨f.ge_mem e he, fun h' ↦ hiff ?_⟩, f.fe_ge e he⟩
    have h0 := f.ends_mem_image_iff hX (f.ge_mem e he) 0
    have h1 := f.ends_mem_image_iff hX (f.ge_mem e he) 1
    rw [f.fe_ge e he] at h0 h1
    rw [← h0, ← h1] at h'
    by_cases hb : f.flip (f.ge e) = true
    · simp only [sw, hb, ↓reduceIte, rev_zero', rev_one'] at h' ⊢
      exact h'.symm
    · simp only [sw, hb] at h' ⊢
      exact h'
  · intro h
    obtain ⟨e', he'', rfl⟩ := Finset.mem_image.mp h
    obtain ⟨he', hiff⟩ := mem_bd.mp he''
    refine mem_bd.mpr ⟨f.fe_mem e' he', fun h' ↦ hiff ?_⟩
    have h0 := f.ends_mem_image_iff hX he' 0
    have h1 := f.ends_mem_image_iff hX he' 1
    rw [← h0, ← h1]
    by_cases hb : f.flip e' = true
    · simp only [sw, hb, ↓reduceIte, rev_zero', rev_one'] at h' ⊢
      exact h'.symm
    · simp only [sw, hb] at h' ⊢
      exact h'

theorem card_image_fe {F : Finset ℕ} (hF : F ⊆ Γ₁.Es) : (F.image f.fe).card = F.card :=
  Finset.card_image_of_injOn fun _ hx _ hy h ↦ f.fe_inj (hF hx) (hF hy) h

theorem card_image_fv {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) : (X.image f.fv).card = X.card :=
  Finset.card_image_of_injOn fun _ hx _ hy h ↦ f.fv_inj (hX hx) (hX hy) h

theorem card_bd_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    (Γ₂.bd (X.image f.fv)).card = (Γ₁.bd X).card := by
  rw [f.bd_image hX, f.card_image_fe (bd_subset X)]

/-- Even edge sets transport. -/
theorem isEven_image {F : Finset ℕ} (hF : F ⊆ Γ₁.Es) (h : Γ₁.IsEven F) :
    Γ₂.IsEven (F.image f.fe) := by
  intro v hv
  rw [← f.fv_gv v hv, f.degIn_image hF (f.gv_mem v hv)]
  exact h _ (f.gv_mem v hv)

theorem hasCycle_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) (h : Γ₁.HasCycle X) :
    Γ₂.HasCycle (X.image f.fv) := by
  obtain ⟨F, hF, hne, hev⟩ := h
  refine ⟨F.image f.fe, ?_, hne.image _, f.isEven_image (hF.trans (edgesIn_subset X)) hev⟩
  rw [f.edgesIn_image hX]
  exact Finset.image_subset_image hF

theorem hasCycle_image_iff {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    Γ₂.HasCycle (X.image f.fv) ↔ Γ₁.HasCycle X := by
  refine ⟨fun h ↦ ?_, f.hasCycle_image hX⟩
  have := f.symm.hasCycle_image (Γ₁ := Γ₂) (X := X.image f.fv)
    (by rw [f.Vs_eq_image]; exact Finset.image_subset_image hX) h
  have hXX : (X.image f.fv).image f.symm.fv = X := by
    rw [Finset.image_image]
    refine (Finset.image_congr (g := id) ?_).trans Finset.image_id
    intro x hx
    exact f.gv_fv x (hX hx)
  rw [hXX] at this
  exact this

theorem sdiff_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    Γ₂.Vs \ X.image f.fv = (Γ₁.Vs \ X).image f.fv := by
  rw [f.Vs_eq_image]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨v', hv', rfl⟩, h⟩
    exact ⟨v', ⟨hv', fun hv'' ↦ h ⟨v', hv'', rfl⟩⟩, rfl⟩
  · rintro ⟨v', ⟨hv', hv''⟩, rfl⟩
    refine ⟨⟨v', hv', rfl⟩, ?_⟩
    rintro ⟨v'', hv''', heq⟩
    rw [f.fv_inj (hX hv''') hv' heq] at hv'''
    exact hv'' hv'''

theorem cycSep_image {X : Finset ℕ} (h : Γ₁.CycSep X) : Γ₂.CycSep (X.image f.fv) := by
  obtain ⟨hX, h4, hc, hc'⟩ := h
  refine ⟨?_, ?_, f.hasCycle_image hX hc, ?_⟩
  · rw [f.Vs_eq_image]
    exact Finset.image_subset_image hX
  · rw [f.card_bd_image hX]
    exact h4
  · rw [f.sdiff_image hX]
    exact f.hasCycle_image Finset.sdiff_subset hc'

include f in
theorem girth5 (h : Γ₁.Girth5) : Γ₂.Girth5 := by
  intro F hF hne hev
  have hF' : F.image f.symm.fe ⊆ Γ₁.Es := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact f.ge_mem e' (hF he')
  have hev' : Γ₁.IsEven (F.image f.symm.fe) := f.symm.isEven_image hF hev
  have := h _ hF' (hne.image _) hev'
  rw [Finset.card_image_of_injOn (fun x hx y hy heq ↦ f.symm.fe_inj (hF hx) (hF hy) heq)] at this
  exact this

theorem image_symm_image {X : Finset ℕ} (hX : X ⊆ Γ₁.Vs) :
    (X.image f.fv).image f.symm.fv = X := by
  rw [Finset.image_image]
  refine (Finset.image_congr (g := id) ?_).trans Finset.image_id
  intro x hx
  exact f.gv_fv x (hX hx)

include f in
theorem cyc4Conn (h : Γ₁.Cyc4Conn) : Γ₂.Cyc4Conn := by
  intro X hX hc hc'
  have hX' : X.image f.symm.fv ⊆ Γ₁.Vs := by
    intro v hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact f.gv_mem v' (hX hv')
  have e1 : (X.image f.symm.fv).image f.fv = X := f.symm.image_symm_image (Γ₁ := Γ₂) hX
  have hc1 : Γ₁.HasCycle (X.image f.symm.fv) := by
    rw [← f.hasCycle_image_iff hX', e1]
    exact hc
  have hc2 : Γ₁.HasCycle (Γ₁.Vs \ X.image f.symm.fv) := by
    rw [← f.hasCycle_image_iff Finset.sdiff_subset, ← f.sdiff_image hX', e1]
    exact hc'
  have := h _ hX' hc1 hc2
  rw [← f.card_bd_image hX', e1] at this
  exact this

end Transport

end Iso

end FinGraph
end GraphPuzzles
