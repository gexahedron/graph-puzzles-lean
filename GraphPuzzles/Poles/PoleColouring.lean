import GraphPuzzles.Poles.Pole
import GraphPuzzles.Poles.PoleKempe

/-!
# Poles with a segment having a unique exterior chord

Lemmas 3.4 and 3.5 of Karabáš–Máčajová: a Hamiltonian cubic `3`-pole with an even segment
having a unique exterior chord is `3`-edge-colourable, hence has a proper four-cover.  We prove
this directly for the segment `T₀` between the spokes `0` and `s₂`.

The region `R` of the positions `s₂ + 1, …, n - 1` carries the base colouring of the paper's
auxiliary Hamiltonian graph: its path edges alternate between the colours `0` and `1`, the two
edges leaving the region at `s₂` and at `n - 1` get colour `1`, and all chords (including the
spoke at `s₁` and the unique exterior chord at its region end `u`) get colour `2`.  The two
region-leaving circuit edges then have the same colour while the exterior chord has another, and
this pattern cannot be completed through the segment `T₀`.  A Kempe swap of the colours `1` and
`2` along the chain starting at the edge `n - 1` repairs the pattern: the chain ends at exactly one
of the three other exits (`PoleKempe`), and every resulting pattern extends through `T₀`, whose
circuit edges then alternate between the two colours different from that of the exterior chord.
-/

namespace GraphPuzzles
namespace Pole

section UniqueExterior

variable (P : Pole)

/-- The region: the positions strictly after `s₂`. -/
def region : Finset ℕ := Finset.Ico (P.s₂ + 1) P.n

/-- The base colours of the circuit edges `s₂, …, n - 1`. -/
def ce₀ (p : ℕ) : Fin 3 :=
  if p = P.s₂ ∨ p = P.n - 1 then 1 else if (p - P.s₂ - 1) % 2 = 0 then 0 else 1

/-- The other end of the circuit edge of colour `1` at a region position. -/
def fK (q : ℕ) : ℕ := if P.ce₀ (q - 1) = 1 then q - 1 else q + 1

/-- The other end of the chord at a region position; the spoke at `s₁` leaves the region. -/
def gK (q : ℕ) : ℕ := if q = P.s₁ then P.n else P.μ q

variable {P}

theorem mem_region {q : ℕ} : q ∈ P.region ↔ P.s₂ + 1 ≤ q ∧ q < P.n := Finset.mem_Ico

theorem inner_of_mem_region {q : ℕ} (hq : q ∈ P.region) (hq1 : q ≠ P.s₁) : P.Inner q := by
  rw [mem_region] at hq
  exact ⟨by omega, hq.2, by omega, hq1⟩

variable (hs₂ : Even P.s₂)

include hs₂ in
theorem s₂_add_two_lt : P.s₂ + 2 < P.n := by
  have h1 := P.s₂_lt_s₁
  have h2 := P.s₁_lt_n
  obtain ⟨k, hk⟩ := hs₂
  obtain ⟨m, hm⟩ := @n_odd P
  omega

theorem ce₀_s₂ : P.ce₀ P.s₂ = 1 := by
  unfold ce₀
  rw [if_pos (Or.inl rfl)]

theorem ce₀_last : P.ce₀ (P.n - 1) = 1 := by
  unfold ce₀
  rw [if_pos (Or.inr rfl)]

theorem ce₀_mid {p : ℕ} (h1 : P.s₂ < p) (h2 : p < P.n - 1) :
    P.ce₀ p = if (p - P.s₂ - 1) % 2 = 0 then 0 else 1 := by
  unfold ce₀
  rw [if_neg (by omega)]

theorem ce₀_ne_two {p : ℕ} : P.ce₀ p ≠ 2 := by
  unfold ce₀
  split_ifs <;> decide

include hs₂ in
theorem ce₀_pred_ne {q : ℕ} (hq : q ∈ P.region) : P.ce₀ (q - 1) ≠ P.ce₀ q := by
  have h3 := s₂_add_two_lt hs₂
  rw [mem_region] at hq
  by_cases h1 : q = P.s₂ + 1
  · subst h1
    rw [Nat.add_sub_cancel, ce₀_s₂, ce₀_mid (by omega) (by omega), Nat.add_sub_cancel_left,
      Nat.sub_self, if_pos rfl]
    decide
  by_cases h2 : q = P.n - 1
  · subst h2
    obtain ⟨m, hm⟩ := @n_odd P
    obtain ⟨k, hk⟩ := hs₂
    rw [ce₀_last, ce₀_mid (by omega) (by omega), if_pos (by omega)]
    decide
  rw [ce₀_mid (by omega) (by omega), ce₀_mid (by omega) (by omega)]
  by_cases h : (q - 1 - P.s₂ - 1) % 2 = 0
  · rw [if_pos h, if_neg (by omega)]
    decide
  · rw [if_neg h, if_pos (by omega)]
    decide

private theorem fin3_other {x y : Fin 3} (hx : x ≠ 2) (hy : y ≠ 2) (hxy : x ≠ y) (h : x ≠ 1) :
    y = 1 := by
  revert x y
  decide

theorem fK_of_one {q : ℕ} (h : P.ce₀ (q - 1) = 1) : P.fK q = q - 1 := by
  unfold fK
  rw [if_pos h]

theorem fK_of_ne_one {q : ℕ} (h : P.ce₀ (q - 1) ≠ 1) : P.fK q = q + 1 := by
  unfold fK
  rw [if_neg h]

theorem gK_of_ne {q : ℕ} (h : q ≠ P.s₁) : P.gK q = P.μ q := by
  unfold gK
  rw [if_neg h]

theorem gK_s₁ : P.gK P.s₁ = P.n := by
  unfold gK
  rw [if_pos rfl]

include hs₂ in
theorem last_mem_region : P.n - 1 ∈ P.region := by
  have := s₂_add_two_lt hs₂
  rw [mem_region]
  omega

include hs₂ in
theorem fK_last : P.fK (P.n - 1) = P.n := by
  have h3 := s₂_add_two_lt hs₂
  obtain ⟨m, hm⟩ := @n_odd P
  obtain ⟨k, hk⟩ := hs₂
  rw [fK_of_ne_one]
  · omega
  rw [ce₀_mid (by omega) (by omega), if_pos (by omega)]
  decide

theorem fK_s₂_succ : P.fK (P.s₂ + 1) = P.s₂ := by
  rw [fK_of_one]
  · rfl
  rw [Nat.add_sub_cancel]
  exact ce₀_s₂

include hs₂ in
/-- The Kempe data: the region, the two involutions and the start at `n - 1`. -/
def kd : KempeData where
  R := P.region
  f := P.fK
  g := P.gK
  f_ne := by
    intro q hq
    rw [mem_region] at hq
    unfold fK
    split_ifs <;> omega
  g_ne := by
    intro q hq
    by_cases h : q = P.s₁
    · rw [h, gK_s₁]
      have := P.s₁_lt_n
      omega
    · rw [gK_of_ne h]
      exact μ_ne_of_inner (inner_of_mem_region hq h)
  f_f := by
    intro q hq hfq
    have hq' := hq
    rw [mem_region] at hq'
    by_cases h : P.ce₀ (q - 1) = 1
    · rw [fK_of_one h] at hfq ⊢
      have hne := ce₀_pred_ne hs₂ hfq
      rw [h] at hne
      rw [fK_of_ne_one hne]
      rw [mem_region] at hfq
      omega
    · rw [fK_of_ne_one h] at hfq ⊢
      have hne := ce₀_pred_ne hs₂ hq
      have h1 : P.ce₀ q = 1 := fin3_other ce₀_ne_two ce₀_ne_two hne h
      rw [fK_of_one (by rw [Nat.add_sub_cancel]; exact h1)]
      rfl
  g_g := by
    intro q hq hgq
    by_cases h : q = P.s₁
    · rw [h, gK_s₁, mem_region] at hgq
      omega
    · rw [gK_of_ne h] at hgq ⊢
      have hi := inner_of_mem_region hq h
      rw [gK_of_ne (inner_μ hi).2.2.2, μ_μ_of_inner hi]
  q₀ := P.n - 1
  q₀_mem := last_mem_region hs₂
  f_q₀ := by
    rw [fK_last hs₂, mem_region]
    omega

/-- The vertices of the Kempe chain. -/
noncomputable def chain : Finset ℕ := (kd hs₂).visited

theorem chain_subset : chain hs₂ ⊆ P.region := (kd hs₂).visited_subset

theorem last_mem_chain : P.n - 1 ∈ chain hs₂ := (kd hs₂).start_mem_visited

theorem fK_mem_chain {q : ℕ} (hq : q ∈ chain hs₂) (hf : P.fK q ∈ P.region) : P.fK q ∈ chain hs₂ :=
  (kd hs₂).f_mem_visited hq hf

theorem gK_mem_chain {q : ℕ} (hq : q ∈ chain hs₂) (hg : P.gK q ∈ P.region) : P.gK q ∈ chain hs₂ :=
  (kd hs₂).g_mem_visited hq hg

/-- The circuit edge colours after the Kempe swap: the `1`-coloured edges at chain vertices
become `2`. -/
noncomputable def ce₁ (p : ℕ) : Fin 3 :=
  if P.ce₀ p = 1 ∧ (p ∈ chain hs₂ ∨ p + 1 ∈ chain hs₂) then 2 else P.ce₀ p

/-- The chord colours after the Kempe swap: chords at chain vertices become `1`. -/
noncomputable def cc₁ (q : ℕ) : Fin 3 := if q ∈ chain hs₂ then 1 else 2

theorem ce₁_of_mem {p : ℕ} (h1 : P.ce₀ p = 1) (h : p ∈ chain hs₂ ∨ p + 1 ∈ chain hs₂) :
    ce₁ hs₂ p = 2 := by
  unfold ce₁
  rw [if_pos ⟨h1, h⟩]

theorem ce₁_of_ne_one {p : ℕ} (h1 : P.ce₀ p ≠ 1) : ce₁ hs₂ p = P.ce₀ p := by
  unfold ce₁
  rw [if_neg (fun h ↦ h1 h.1)]

theorem ce₁_of_notMem {p : ℕ} (h : p ∉ chain hs₂) (h' : p + 1 ∉ chain hs₂) :
    ce₁ hs₂ p = P.ce₀ p := by
  unfold ce₁
  rw [if_neg (fun h'' ↦ h''.2.elim h h')]

theorem cc₁_of_mem {q : ℕ} (h : q ∈ chain hs₂) : cc₁ hs₂ q = 1 := by
  unfold cc₁
  rw [if_pos h]

theorem cc₁_of_notMem {q : ℕ} (h : q ∉ chain hs₂) : cc₁ hs₂ q = 2 := by
  unfold cc₁
  rw [if_neg h]

/-- Colours at a region vertex outside the chain are unchanged. -/
theorem ce₁_pred_of_notMem {q : ℕ} (hq : q ∈ P.region) (h : q ∉ chain hs₂) :
    ce₁ hs₂ (q - 1) = P.ce₀ (q - 1) := by
  unfold ce₁
  rw [if_neg]
  rintro ⟨h1, h2 | h2⟩
  · have hmem : q - 1 ∈ P.region := chain_subset hs₂ h2
    have hne := ce₀_pred_ne hs₂ hmem
    rw [h1] at hne
    have := fK_mem_chain hs₂ h2 (by rw [fK_of_ne_one hne]; rw [mem_region] at hq ⊢; omega)
    rw [fK_of_ne_one hne] at this
    rw [mem_region] at hq
    rw [Nat.sub_add_cancel (by omega)] at this
    exact h this
  · rw [mem_region] at hq
    rw [Nat.sub_add_cancel (by omega)] at h2
    exact h h2

theorem ce₁_of_notMem' {q : ℕ} (hq : q ∈ P.region) (h : q ∉ chain hs₂) :
    ce₁ hs₂ q = P.ce₀ q := by
  unfold ce₁
  rw [if_neg]
  rintro ⟨h1, h2 | h2⟩
  · exact h h2
  · have hmem : q + 1 ∈ P.region := chain_subset hs₂ h2
    have := fK_mem_chain hs₂ h2 (by rw [fK_of_one (by rw [Nat.add_sub_cancel]; exact h1)]; exact hq)
    rw [fK_of_one (by rw [Nat.add_sub_cancel]; exact h1), Nat.add_sub_cancel] at this
    exact h this

/-- The swapped colouring is proper at every region vertex. -/
theorem region_proper {q : ℕ} (hq : q ∈ P.region) :
    ce₁ hs₂ (q - 1) ≠ ce₁ hs₂ q ∧ ce₁ hs₂ (q - 1) ≠ cc₁ hs₂ q ∧ ce₁ hs₂ q ≠ cc₁ hs₂ q := by
  have hne := ce₀_pred_ne hs₂ hq
  have hq' := hq
  rw [mem_region] at hq'
  by_cases h : q ∈ chain hs₂
  · rw [cc₁_of_mem hs₂ h]
    by_cases h1 : P.ce₀ (q - 1) = 1
    · rw [ce₁_of_mem hs₂ h1 (Or.inr (by rw [Nat.sub_add_cancel (by omega)]; exact h))]
      have h2 : P.ce₀ q ≠ 1 := by rw [← h1]; exact hne.symm
      rw [ce₁_of_ne_one hs₂ h2]
      refine ⟨ce₀_ne_two.symm, by decide, fun h' ↦ h2 h'⟩
    · have h2 : P.ce₀ q = 1 := fin3_other ce₀_ne_two ce₀_ne_two hne h1
      rw [ce₁_of_mem hs₂ h2 (Or.inl h), ce₁_of_ne_one hs₂ h1]
      exact ⟨ce₀_ne_two, fun h' ↦ h1 h', by decide⟩
  · rw [cc₁_of_notMem hs₂ h, ce₁_pred_of_notMem hs₂ hq h, ce₁_of_notMem' hs₂ hq h]
    exact ⟨hne, ce₀_ne_two, ce₀_ne_two⟩

theorem ce₁_last : ce₁ hs₂ (P.n - 1) = 2 :=
  ce₁_of_mem hs₂ ce₀_last (Or.inl (last_mem_chain hs₂))

theorem s₂_notMem_chain : P.s₂ ∉ chain hs₂ := by
  intro h
  have := chain_subset hs₂ h
  rw [mem_region] at this
  omega

theorem ce₁_s₂ : ce₁ hs₂ P.s₂ = if P.s₂ + 1 ∈ chain hs₂ then 2 else 1 := by
  by_cases h : P.s₂ + 1 ∈ chain hs₂
  · rw [if_pos h]
    exact ce₁_of_mem hs₂ ce₀_s₂ (Or.inr h)
  · rw [if_neg h, ce₁_of_notMem hs₂ (s₂_notMem_chain hs₂) h]
    exact ce₀_s₂

/-- The exit pattern after the swap: the edge `n - 1` has colour `2`; if the edge `s₂` also has
colour `2`, then the chord at `u` keeps colour `2`. -/
theorem good_pattern {u : ℕ} (hu1 : u ≠ P.s₁) (hμu : P.μ u ∉ P.region) :
    ce₁ hs₂ (P.n - 1) ≠ ce₁ hs₂ P.s₂ ∨
      (ce₁ hs₂ (P.n - 1) = ce₁ hs₂ P.s₂ ∧ ce₁ hs₂ P.s₂ = cc₁ hs₂ u) := by
  rw [ce₁_last hs₂, ce₁_s₂ hs₂]
  by_cases h : P.s₂ + 1 ∈ chain hs₂
  · rw [if_pos h]
    right
    refine ⟨rfl, ?_⟩
    rw [cc₁_of_notMem hs₂]
    intro huc
    have h3 := s₂_add_two_lt hs₂
    have hg := (kd hs₂).eq_last_of_g_exit huc (by
      change P.gK u ∉ P.region
      rw [gK_of_ne hu1]
      exact hμu)
    have hf := (kd hs₂).eq_last_of_f_exit h (by
      change P.fK (P.s₂ + 1) ∉ P.region
      rw [fK_s₂_succ, mem_region]
      omega) (by change P.s₂ + 1 ≠ P.n - 1; omega)
    exact hf.2 hg.2
  · rw [if_neg h]
    left
    decide

theorem gK_chain_iff {q : ℕ} (hq : q ∈ P.region) (hq1 : q ≠ P.s₁) (hμ : P.μ q ∈ P.region) :
    P.μ q ∈ chain hs₂ ↔ q ∈ chain hs₂ := by
  have hi := inner_of_mem_region hq hq1
  constructor
  · intro h
    have := gK_mem_chain hs₂ h (by rw [gK_of_ne (inner_μ hi).2.2.2, μ_μ_of_inner hi]; exact hq)
    rwa [gK_of_ne (inner_μ hi).2.2.2, μ_μ_of_inner hi] at this
  · intro h
    have := gK_mem_chain hs₂ h (by rw [gK_of_ne hq1]; exact hμ)
    rwa [gK_of_ne hq1] at this

/-- The third colour, different from two given distinct colours. -/
def third (x y : Fin 3) : Fin 3 := if x ≠ 0 ∧ y ≠ 0 then 0 else if x ≠ 1 ∧ y ≠ 1 then 1 else 2

theorem third_ne {x y : Fin 3} (h : x ≠ y) : third x y ≠ x ∧ third x y ≠ y := by
  revert x y
  decide

theorem exists_αβ (p₀ p₂ γ : Fin 3) (h : p₀ ≠ p₂ ∨ (p₀ = p₂ ∧ p₂ = γ)) :
    ∃ α β : Fin 3, α ≠ γ ∧ β ≠ γ ∧ α ≠ β ∧ α ≠ p₀ ∧ β ≠ p₂ := by
  revert p₀ p₂ γ
  decide

variable {a : ℕ} (ha : a ∈ P.T₀) (hau : P.μ a ∉ P.T₀) (huniq : ∀ b ∈ P.T₀, P.μ b ∉ P.T₀ → b = a)

theorem u_mem_region (ha : a ∈ P.T₀) (hau : P.μ a ∉ P.T₀) : P.μ a ∈ P.region := by
  have hi := inner_μ (inner_of_mem_T₀ ha)
  rw [mem_T₀] at hau
  rw [mem_region]
  have := hi.1
  have := hi.2.1
  have := hi.2.2.1
  omega

include ha hau

omit hau in
theorem μu_notMem_region : P.μ (P.μ a) ∉ P.region := by
  rw [μ_μ_of_inner (inner_of_mem_T₀ ha), mem_region, mem_T₀] at *
  omega

/-- The colours `α`, `β` of the circuit edges of `T₀` at even and odd positions. -/
noncomputable def αβ : Fin 3 × Fin 3 :=
  Classical.choose (exists_αβ' hs₂ ha hau)
where
  exists_αβ' (hs₂ : Even P.s₂) (ha : a ∈ P.T₀) (hau : P.μ a ∉ P.T₀) :
      ∃ x : Fin 3 × Fin 3, x.1 ≠ cc₁ hs₂ (P.μ a) ∧ x.2 ≠ cc₁ hs₂ (P.μ a) ∧ x.1 ≠ x.2 ∧
        x.1 ≠ ce₁ hs₂ (P.n - 1) ∧ x.2 ≠ ce₁ hs₂ P.s₂ := by
    obtain ⟨α, β, h⟩ := exists_αβ (ce₁ hs₂ (P.n - 1)) (ce₁ hs₂ P.s₂) (cc₁ hs₂ (P.μ a))
      (good_pattern hs₂ (inner_μ (inner_of_mem_T₀ ha)).2.2.2 (μu_notMem_region ha))
    exact ⟨(α, β), h⟩

theorem αβ_spec :
    (αβ hs₂ ha hau).1 ≠ cc₁ hs₂ (P.μ a) ∧ (αβ hs₂ ha hau).2 ≠ cc₁ hs₂ (P.μ a) ∧
      (αβ hs₂ ha hau).1 ≠ (αβ hs₂ ha hau).2 ∧ (αβ hs₂ ha hau).1 ≠ ce₁ hs₂ (P.n - 1) ∧
        (αβ hs₂ ha hau).2 ≠ ce₁ hs₂ P.s₂ :=
  Classical.choose_spec (αβ.exists_αβ' hs₂ ha hau)

/-- The colouring of the circuit edges. -/
noncomputable def col (p : ℕ) : Fin 3 :=
  if p < P.s₂ then (if p % 2 = 0 then (αβ hs₂ ha hau).1 else (αβ hs₂ ha hau).2) else ce₁ hs₂ p

/-- The colouring of the chords and spokes. -/
noncomputable def chordcol (q : ℕ) : Fin 3 :=
  if q = 0 then third (ce₁ hs₂ (P.n - 1)) (αβ hs₂ ha hau).1
  else if q = P.s₂ then third (αβ hs₂ ha hau).2 (ce₁ hs₂ P.s₂)
  else if q < P.s₂ then cc₁ hs₂ (P.μ a) else cc₁ hs₂ q

theorem col_of_ge {p : ℕ} (h : P.s₂ ≤ p) : col hs₂ ha hau p = ce₁ hs₂ p := by
  unfold col
  rw [if_neg (by omega)]

theorem col_of_lt {p : ℕ} (h : p < P.s₂) :
    col hs₂ ha hau p = if p % 2 = 0 then (αβ hs₂ ha hau).1 else (αβ hs₂ ha hau).2 := by
  unfold col
  rw [if_pos h]

theorem chordcol_zero :
    chordcol hs₂ ha hau 0 = third (ce₁ hs₂ (P.n - 1)) (αβ hs₂ ha hau).1 := by
  unfold chordcol
  rw [if_pos rfl]

theorem chordcol_s₂ : chordcol hs₂ ha hau P.s₂ = third (αβ hs₂ ha hau).2 (ce₁ hs₂ P.s₂) := by
  unfold chordcol
  have := P.s₂_pos
  rw [if_neg (by omega), if_pos rfl]

theorem chordcol_of_T₀ {q : ℕ} (hq : q ∈ P.T₀) : chordcol hs₂ ha hau q = cc₁ hs₂ (P.μ a) := by
  unfold chordcol
  rw [mem_T₀] at hq
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem chordcol_of_region {q : ℕ} (hq : q ∈ P.region) : chordcol hs₂ ha hau q = cc₁ hs₂ q := by
  unfold chordcol
  rw [mem_region] at hq
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

include huniq in
/-- The chord colouring agrees at both ends of every chord. -/
theorem chordcol_μ {q : ℕ} (hq : P.Inner q) : chordcol hs₂ ha hau (P.μ q) = chordcol hs₂ ha hau q := by
  have hq' := hq
  by_cases hT : q ∈ P.T₀
  · rw [chordcol_of_T₀ hs₂ ha hau hT]
    by_cases hqa : q = a
    · subst hqa
      rw [chordcol_of_region hs₂ ha hau (u_mem_region ha hau)]
    · have hμ : P.μ q ∈ P.T₀ := by
        by_contra h
        exact hqa (huniq q hT h)
      rw [chordcol_of_T₀ hs₂ ha hau hμ]
  · have hR : q ∈ P.region := by
      rw [mem_region]
      rw [mem_T₀] at hT
      have := hq.1
      have := hq.2.1
      have := hq.2.2.1
      omega
    rw [chordcol_of_region hs₂ ha hau hR]
    by_cases hμ : P.μ q ∈ P.T₀
    · have hqa : P.μ q = a := huniq _ hμ (by rw [μ_μ_of_inner hq]; exact hT)
      have hqu : q = P.μ a := by rw [← hqa, μ_μ_of_inner hq]
      rw [chordcol_of_T₀ hs₂ ha hau hμ, hqu]
    · have hμR : P.μ q ∈ P.region := by
        rw [mem_region]
        rw [mem_T₀] at hμ
        have hi := inner_μ hq
        have := hi.1
        have := hi.2.1
        have := hi.2.2.1
        omega
      rw [chordcol_of_region hs₂ ha hau hμR]
      by_cases hc : q ∈ chain hs₂
      · rw [cc₁_of_mem hs₂ hc, cc₁_of_mem hs₂ ((gK_chain_iff hs₂ hR hq.2.2.2 hμR).mpr hc)]
      · rw [cc₁_of_notMem hs₂ hc,
          cc₁_of_notMem hs₂ (fun h ↦ hc ((gK_chain_iff hs₂ hR hq.2.2.2 hμR).mp h))]

/-- The colouring is proper at every position. -/
theorem proper {p : ℕ} (hp : p < P.n) :
    col hs₂ ha hau (P.prev p) ≠ col hs₂ ha hau p ∧
      col hs₂ ha hau (P.prev p) ≠ chordcol hs₂ ha hau p ∧
        col hs₂ ha hau p ≠ chordcol hs₂ ha hau p := by
  obtain ⟨hα, hβ, hαβ, hα0, hβ2⟩ := αβ_spec hs₂ ha hau
  have h3 := s₂_add_two_lt hs₂
  have hs₂0 := P.s₂_pos
  by_cases h0 : p = 0
  · subst h0
    rw [prev_zero, col_of_ge hs₂ ha hau (by omega), col_of_lt hs₂ ha hau hs₂0, if_pos rfl,
      chordcol_zero]
    obtain ⟨t1, t2⟩ := third_ne (Ne.symm hα0)
    exact ⟨Ne.symm hα0, Ne.symm t1, Ne.symm t2⟩
  rw [prev_of_pos (Nat.pos_of_ne_zero h0)]
  by_cases hlt : p < P.s₂
  · rw [col_of_lt hs₂ ha hau (by omega), col_of_lt hs₂ ha hau hlt,
      chordcol_of_T₀ hs₂ ha hau (mem_T₀.mpr ⟨by omega, hlt⟩)]
    by_cases he : p % 2 = 0
    · rw [if_pos he, if_neg (by omega)]
      exact ⟨Ne.symm hαβ, hβ, hα⟩
    · rw [if_neg he, if_pos (by omega)]
      exact ⟨hαβ, hα, hβ⟩
  by_cases heq : p = P.s₂
  · subst heq
    obtain ⟨k, hk⟩ := id hs₂
    rw [col_of_lt hs₂ ha hau (by omega), if_neg (by omega), col_of_ge hs₂ ha hau le_rfl,
      chordcol_s₂]
    obtain ⟨t1, t2⟩ := third_ne hβ2
    exact ⟨hβ2, Ne.symm t1, Ne.symm t2⟩
  have hR : p ∈ P.region := mem_region.mpr ⟨by omega, hp⟩
  rw [col_of_ge hs₂ ha hau (by omega), col_of_ge hs₂ ha hau (by omega),
    chordcol_of_region hs₂ ha hau hR]
  exact region_proper hs₂ hR

include huniq in
/-- Lemmas 3.4 and 3.5: a pole whose even segment `T₀` has a unique exterior chord has a proper
four-cover. -/
noncomputable def coverOfUniqueExterior : P.Cover :=
  Cover.ofColouring (col hs₂ ha hau) (chordcol hs₂ ha hau)
    (fun _ hp ↦ (proper hs₂ ha hau hp).1) (fun _ hp ↦ (proper hs₂ ha hau hp).2.1)
    (fun _ hp ↦ (proper hs₂ ha hau hp).2.2) (fun _ hq ↦ chordcol_μ hs₂ ha hau huniq hq)

end UniqueExterior

/-- A pole whose even segment `T₀` has exactly one exterior chord has a proper four-cover. -/
theorem exists_cover_of_ext_T₀ {P : Pole} (hs₂ : Even P.s₂) (hext : P.ext P.T₀ = 1) :
    Nonempty P.Cover := by
  unfold ext at hext
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hext
  have hmem : ∀ b, b ∈ P.T₀ ∧ P.μ b ∉ P.T₀ ↔ b = a := by
    intro b
    have : b ∈ {p ∈ P.T₀ | P.μ p ∉ P.T₀} ↔ b = a := by rw [ha, Finset.mem_singleton]
    rw [Finset.mem_filter] at this
    exact this
  have ha' := (hmem a).mpr rfl
  exact ⟨coverOfUniqueExterior hs₂ ha'.1 ha'.2 (fun b hb hμ ↦ (hmem b).mp ⟨hb, hμ⟩)⟩

end Pole
end GraphPuzzles
