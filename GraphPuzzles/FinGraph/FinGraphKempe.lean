import GraphPuzzles.FinGraph.FinGraphColouring
import GraphPuzzles.Poles.PoleKempe

/-!
# Kempe chains in a cubic pole

Starting from a dangling edge `a` of colour `α`, the `α/β` Kempe chain is the deterministic walk
of `KempeData` on the vertex labels: from a vertex follow the other end of its `α`-edge, then of
its `β`-edge, and so on, until a dangling edge is reached.  Swapping `α` and `β` on the edges at
the visited vertices produces a new colouring in which `a` has colour `β`, and the only other
dangling edges that changed colour are attached to the last vertex of the walk.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} {c : ℕ → Color}

/-- The other end of a half-edge. -/
def otherEnd (Γ : FinGraph) (h : ℕ × Fin 2) : ℕ := Γ.ends h.1 (Fin.rev h.2)

/-- Swap two colours. -/
def swapC (α β κ : Color) : Color := if κ = α then β else if κ = β then α else κ

theorem swapC_ne_zero {α β κ : Color} (hα : α ≠ 0) (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    swapC α β κ ≠ 0 := by
  unfold swapC
  split_ifs <;> assumption

theorem swapC_injective (α β : Color) : Function.Injective (swapC α β) := by
  intro x y hxy
  unfold swapC at hxy
  split_ifs at hxy <;> simp_all

theorem swapC_left (α β : Color) : swapC α β α = β := by simp [swapC]

theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : i = Fin.rev j := by
  revert i j
  decide

section Walk

variable (hcub : Γ.IsCubic) (hc : Γ.IsColouring c)
include hcub hc

/-- The half-edge of a given colour at a vertex. -/
noncomputable def colorHalf (v : ℕ) (κ : Color) : ℕ × Fin 2 :=
  if h : v ∈ Γ.Vs ∧ κ ≠ 0 then Classical.choose (hc.exists_halfEdge hcub h.1 h.2) else (0, 0)

theorem colorHalf_spec {v : ℕ} (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0) :
    colorHalf hcub hc v κ ∈ Γ.halfEdgesIn Γ.Es v ∧ c (colorHalf hcub hc v κ).1 = κ := by
  unfold colorHalf
  rw [dif_pos ⟨hv, hκ⟩]
  exact Classical.choose_spec (hc.exists_halfEdge hcub hv hκ)

theorem colorHalf_eq {v : ℕ} (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0) {h : ℕ × Fin 2}
    (hh : h ∈ Γ.halfEdgesIn Γ.Es v) (hκh : c h.1 = κ) : colorHalf hcub hc v κ = h := by
  obtain ⟨h1, h2⟩ := colorHalf_spec hcub hc hv hκ
  exact hc.unique_halfEdge hv h1 hh (h2.trans hκh.symm)

/-- The other end of the edge of a given colour at a vertex (the vertex itself outside `Vs`). -/
noncomputable def step (v : ℕ) (κ : Color) : ℕ :=
  if v ∈ Γ.Vs then Γ.otherEnd (colorHalf hcub hc v κ) else v

theorem step_eq {v : ℕ} (hv : v ∈ Γ.Vs) (κ : Color) :
    step hcub hc v κ = Γ.otherEnd (colorHalf hcub hc v κ) := by
  unfold step
  rw [if_pos hv]

omit hcub in
/-- No loops at vertices. -/
theorem IsColouring.ne_otherEnd {h : ℕ × Fin 2} {v : ℕ} (hv : v ∈ Γ.Vs)
    (hh : h ∈ Γ.halfEdgesIn Γ.Es v) : Γ.otherEnd h ≠ v := by
  intro heq
  have hh' := mem_halfEdgesIn.mp hh
  have := hc.2 v hv h hh (h.1, Fin.rev h.2) (mem_halfEdgesIn.mpr ⟨hh'.1, heq⟩) rfl
  have h2 := congrArg Prod.snd this
  simp only at h2
  revert h2
  generalize h.2 = j
  revert j
  decide

theorem step_ne {v : ℕ} (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0) : step hcub hc v κ ≠ v := by
  rw [step_eq hcub hc hv]
  exact hc.ne_otherEnd hv (colorHalf_spec hcub hc hv hκ).1

theorem step_step {v : ℕ} (hv : v ∈ Γ.Vs) {κ : Color} (hκ : κ ≠ 0)
    (hw : step hcub hc v κ ∈ Γ.Vs) : step hcub hc (step hcub hc v κ) κ = v := by
  rw [step_eq hcub hc hw, step_eq hcub hc hv]
  obtain ⟨h1, h2⟩ := colorHalf_spec hcub hc hv hκ
  rw [step_eq hcub hc hv] at hw
  have hmem : ((colorHalf hcub hc v κ).1, Fin.rev (colorHalf hcub hc v κ).2) ∈
      Γ.halfEdgesIn Γ.Es (Γ.otherEnd (colorHalf hcub hc v κ)) :=
    mem_halfEdgesIn.mpr ⟨(mem_halfEdgesIn.mp h1).1, rfl⟩
  rw [colorHalf_eq hcub hc hw hκ hmem h2]
  unfold otherEnd
  simp only [Fin.rev_rev]
  exact (mem_halfEdgesIn.mp h1).2

end Walk

section Inner

/-- The inner end index of a dangling edge. -/
noncomputable def innerIdx (hP : Γ.IsPole4) {a : ℕ} (ha : a ∈ Γ.dangling) : Fin 2 :=
  Classical.choose (hP.exists_unique_inner ha)

theorem innerIdx_spec (hP : Γ.IsPole4) {a : ℕ} (ha : a ∈ Γ.dangling) :
    Γ.ends a (innerIdx hP ha) ∈ Γ.Vs ∧ Γ.ends a (Fin.rev (innerIdx hP ha)) ∉ Γ.Vs :=
  Classical.choose_spec (hP.exists_unique_inner ha)

theorem a_mem_Es {a : ℕ} (ha : a ∈ Γ.dangling) : a ∈ Γ.Es := (mem_dangling.mp ha).1

theorem ca_ne_zero (hc : Γ.IsColouring c) {a : ℕ} (ha : a ∈ Γ.dangling) : c a ≠ 0 :=
  hc.1 a (a_mem_Es ha)

end Inner

section Chain

variable (hP : Γ.IsPole4) (hc : Γ.IsColouring c) {a : ℕ} (ha : a ∈ Γ.dangling)
  {β : Color} (hβ : β ≠ 0)
include hP hc ha hβ

/-- The Kempe data of the `c a / β` chain starting at `a`. -/
noncomputable def kempeData : KempeData where
  R := Γ.Vs
  f := fun v ↦ step hP.cubic hc v (c a)
  g := fun v ↦ step hP.cubic hc v β
  f_ne := fun v hv ↦ step_ne hP.cubic hc hv (ca_ne_zero hc ha)
  g_ne := fun v hv ↦ step_ne hP.cubic hc hv hβ
  f_f := fun v hv hw ↦ step_step hP.cubic hc hv (ca_ne_zero hc ha) hw
  g_g := fun v hv hw ↦ step_step hP.cubic hc hv hβ hw
  q₀ := Γ.ends a (innerIdx hP ha)
  q₀_mem := (innerIdx_spec hP ha).1
  f_q₀ := by
    have hv := (innerIdx_spec hP ha).1
    show step hP.cubic hc _ (c a) ∉ Γ.Vs
    rw [step_eq hP.cubic hc hv]
    have hmem : (a, innerIdx hP ha) ∈ Γ.halfEdgesIn Γ.Es (Γ.ends a (innerIdx hP ha)) :=
      mem_halfEdgesIn.mpr ⟨a_mem_Es ha, rfl⟩
    rw [colorHalf_eq hP.cubic hc hv (ca_ne_zero hc ha) hmem rfl]
    exact (innerIdx_spec hP ha).2

/-- The visited vertices. -/
noncomputable def visited : Finset ℕ := (kempeData hP hc ha hβ).visited

/-- The recoloured edge colouring. -/
noncomputable def kempeSwap (e : ℕ) : Color :=
  if (c e = c a ∨ c e = β) ∧ ∃ i, Γ.ends e i ∈ visited hP hc ha hβ then swapC (c a) β (c e)
  else c e

theorem visited_subset : visited hP hc ha hβ ⊆ Γ.Vs :=
  (kempeData hP hc ha hβ).visited_subset

theorem q₀_mem_visited : Γ.ends a (innerIdx hP ha) ∈ visited hP hc ha hβ :=
  (kempeData hP hc ha hβ).start_mem_visited

/-- The closure property: an edge of the two chain colours with an end at a visited vertex has
its other end visited too (when that end is a vertex). -/
theorem otherEnd_mem_visited {h : ℕ × Fin 2} (hh : h.1 ∈ Γ.Es)
    (hcol : c h.1 = c a ∨ c h.1 = β) (hv : Γ.ends h.1 h.2 ∈ visited hP hc ha hβ)
    (hw : Γ.otherEnd h ∈ Γ.Vs) : Γ.otherEnd h ∈ visited hP hc ha hβ := by
  have hvV : Γ.ends h.1 h.2 ∈ Γ.Vs := visited_subset hP hc ha hβ hv
  have hmem : h ∈ Γ.halfEdgesIn Γ.Es (Γ.ends h.1 h.2) := mem_halfEdgesIn.mpr ⟨hh, rfl⟩
  rcases hcol with hcol | hcol
  · have : Γ.otherEnd h = step hP.cubic hc (Γ.ends h.1 h.2) (c a) := by
      rw [step_eq hP.cubic hc hvV, colorHalf_eq hP.cubic hc hvV (ca_ne_zero hc ha) hmem hcol]
    rw [this] at hw ⊢
    exact (kempeData hP hc ha hβ).f_mem_visited hv hw
  · have : Γ.otherEnd h = step hP.cubic hc (Γ.ends h.1 h.2) β := by
      rw [step_eq hP.cubic hc hvV, colorHalf_eq hP.cubic hc hvV hβ hmem hcol]
    rw [this] at hw ⊢
    exact (kempeData hP hc ha hβ).g_mem_visited hv hw

/-- The swap condition at an edge with an end at a vertex `v` only depends on whether `v` is
visited. -/
theorem swap_iff {e : ℕ} (he : e ∈ Γ.Es) {i : Fin 2} (hv : Γ.ends e i ∈ Γ.Vs)
    (hcol : c e = c a ∨ c e = β) :
    (∃ j, Γ.ends e j ∈ visited hP hc ha hβ) ↔ Γ.ends e i ∈ visited hP hc ha hβ := by
  constructor
  · rintro ⟨j, hj⟩
    by_cases hij : j = i
    · exact hij ▸ hj
    · have hrev : i = Fin.rev j := fin2_eq_rev_of_ne (Ne.symm hij)
      have hw : Γ.otherEnd (e, j) ∈ Γ.Vs := by
        show Γ.ends e (Fin.rev j) ∈ Γ.Vs
        rw [← hrev]
        exact hv
      have := otherEnd_mem_visited hP hc ha hβ (h := (e, j)) he hcol hj hw
      unfold otherEnd at this
      rw [hrev]
      exact this
  · intro h
    exact ⟨i, h⟩

theorem kempeSwap_of_visited {e : ℕ} (_he : e ∈ Γ.Es) {i : Fin 2}
    (hv : Γ.ends e i ∈ visited hP hc ha hβ) :
    kempeSwap hP hc ha hβ e = swapC (c a) β (c e) := by
  unfold kempeSwap
  by_cases hcol : c e = c a ∨ c e = β
  · rw [if_pos ⟨hcol, i, hv⟩]
  · rw [if_neg (fun h ↦ hcol h.1)]
    unfold swapC
    rw [not_or] at hcol
    rw [if_neg hcol.1, if_neg hcol.2]

theorem kempeSwap_of_not_visited {e : ℕ} (he : e ∈ Γ.Es) {i : Fin 2} (hvV : Γ.ends e i ∈ Γ.Vs)
    (hv : Γ.ends e i ∉ visited hP hc ha hβ) : kempeSwap hP hc ha hβ e = c e := by
  unfold kempeSwap
  rw [if_neg]
  rintro ⟨hcol, hj⟩
  exact hv ((swap_iff hP hc ha hβ he hvV hcol).mp hj)

/-- The recoloured colouring is proper. -/
theorem kempeSwap_isColouring : Γ.IsColouring (kempeSwap hP hc ha hβ) := by
  refine ⟨fun e he ↦ ?_, fun v hv h₁ h₁m h₂ h₂m heq ↦ ?_⟩
  · unfold kempeSwap
    split_ifs
    · exact swapC_ne_zero (ca_ne_zero hc ha) hβ (hc.1 e he)
    · exact hc.1 e he
  · have h₁' := mem_halfEdgesIn.mp h₁m
    have h₂' := mem_halfEdgesIn.mp h₂m
    by_cases hvis : v ∈ visited hP hc ha hβ
    · rw [kempeSwap_of_visited hP hc ha hβ h₁'.1 (i := h₁.2) (h₁'.2 ▸ hvis),
        kempeSwap_of_visited hP hc ha hβ h₂'.1 (i := h₂.2) (h₂'.2 ▸ hvis)] at heq
      exact hc.unique_halfEdge hv h₁m h₂m (swapC_injective _ _ heq)
    · rw [kempeSwap_of_not_visited hP hc ha hβ h₁'.1 (i := h₁.2) (h₁'.2 ▸ hv)
        (h₁'.2 ▸ hvis), kempeSwap_of_not_visited hP hc ha hβ h₂'.1 (i := h₂.2) (h₂'.2 ▸ hv)
        (h₂'.2 ▸ hvis)] at heq
      exact hc.unique_halfEdge hv h₁m h₂m heq

theorem kempeSwap_start : kempeSwap hP hc ha hβ a = β := by
  rw [kempeSwap_of_visited hP hc ha hβ (a_mem_Es ha) (q₀_mem_visited hP hc ha hβ),
    swapC_left]

theorem kempeSwap_or (e : ℕ) :
    kempeSwap hP hc ha hβ e = c e ∨ kempeSwap hP hc ha hβ e = swapC (c a) β (c e) := by
  unfold kempeSwap
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every dangling edge other than `a` whose colour changed is attached to the last vertex of the
walk. -/
theorem kempeSwap_dangling_changed {d : ℕ} (hd : d ∈ Γ.dangling) (hda : d ≠ a)
    (hch : kempeSwap hP hc ha hβ d ≠ c d) {i : Fin 2} (hi : Γ.ends d i ∈ Γ.Vs) :
    Γ.ends d i = (kempeData hP hc ha hβ).walk (kempeData hP hc ha hβ).last := by
  have hdE := (mem_dangling.mp hd).1
  have hvis : Γ.ends d i ∈ visited hP hc ha hβ := by
    by_contra h
    exact hch (kempeSwap_of_not_visited hP hc ha hβ hdE hi h)
  have hcol : c d = c a ∨ c d = β := by
    by_contra h
    apply hch
    unfold kempeSwap
    rw [if_neg (fun h' ↦ h h'.1)]
  -- the outer end of `d`
  obtain ⟨j, hj, hj'⟩ := hP.exists_unique_inner hd
  have hij : j = i := by
    by_contra h
    have : i = Fin.rev j := fin2_eq_rev_of_ne (Ne.symm h)
    exact hj' (this ▸ hi)
  subst hij
  have hmem : (d, j) ∈ Γ.halfEdgesIn Γ.Es (Γ.ends d j) := mem_halfEdgesIn.mpr ⟨hdE, rfl⟩
  rcases hcol with hcol | hcol
  · have hstep : step hP.cubic hc (Γ.ends d j) (c a) ∉ Γ.Vs := by
      rw [step_eq hP.cubic hc hj, colorHalf_eq hP.cubic hc hj (ca_ne_zero hc ha) hmem hcol]
      exact hj'
    have hne : Γ.ends d j ≠ Γ.ends a (innerIdx hP ha) := by
      intro heq
      have hq := (innerIdx_spec hP ha).1
      have hmem' : (a, innerIdx hP ha) ∈ Γ.halfEdgesIn Γ.Es (Γ.ends d j) :=
        mem_halfEdgesIn.mpr ⟨a_mem_Es ha, heq.symm⟩
      have := hc.unique_halfEdge hj hmem hmem' hcol
      exact hda (congrArg Prod.fst this)
    exact ((kempeData hP hc ha hβ).eq_last_of_f_exit hvis hstep hne).1
  · have hstep : step hP.cubic hc (Γ.ends d j) β ∉ Γ.Vs := by
      rw [step_eq hP.cubic hc hj, colorHalf_eq hP.cubic hc hj hβ hmem hcol]
      exact hj'
    exact ((kempeData hP hc ha hβ).eq_last_of_g_exit hvis hstep).1

end Chain

/-- **Kempe lemma.**  In a coloured cubic pole, a dangling edge `a` can be recoloured with any
other colour `β` by a swap that leaves every colour outside `{c a, β}` fixed and changes the
colour of at most the dangling edges attached to a single vertex besides `a`. -/
theorem exists_kempe (hP : Γ.IsPole4) (hc : Γ.IsColouring c) {a : ℕ} (ha : a ∈ Γ.dangling)
    {β : Color} (hβ : β ≠ 0) :
    ∃ c' : ℕ → Color, Γ.IsColouring c' ∧ c' a = β ∧
      (∀ e, c' e = c e ∨ c' e = swapC (c a) β (c e)) ∧
      ∃ v, ∀ d ∈ Γ.dangling, d ≠ a → c' d ≠ c d → ∀ i, Γ.ends d i ∈ Γ.Vs → Γ.ends d i = v :=
  ⟨kempeSwap hP hc ha hβ, kempeSwap_isColouring hP hc ha hβ,
    kempeSwap_start hP hc ha hβ, kempeSwap_or hP hc ha hβ, _,
    fun _ hd hda hch _ hi ↦ kempeSwap_dangling_changed hP hc ha hβ hd hda hch hi⟩

end FinGraph
end GraphPuzzles
