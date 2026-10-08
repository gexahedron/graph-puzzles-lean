import GraphPuzzles.Poles.Pole

/-!
# Rotating an abstract pole

The segment structure of an abstract `Pole` is cyclic, but the statements about it are made
with respect to the spoke at position `0`.  This module rotates the circuit so that the spoke `s₂`
or the spoke `s₁` moves to position `0`, and transports covers and exterior-chord counts back.
-/

namespace GraphPuzzles
namespace Pole

variable (P : Pole)

/-- The position map of the rotation moving position `k` to `0`. -/
def ρ (k p : ℕ) : ℕ := if p < k then p + (P.n - k) else p - k

/-- The inverse position map. -/
def ρinv (k q : ℕ) : ℕ := if q + k < P.n then q + k else q + k - P.n

variable {P}

theorem ρinv_ρ {k p : ℕ} (hk : k ≤ P.n) (hp : p < P.n) : P.ρinv k (P.ρ k p) = p := by
  unfold ρ ρinv
  split_ifs <;> omega

theorem ρ_ρinv {k q : ℕ} (hk : k ≤ P.n) (hq : q < P.n) : P.ρ k (P.ρinv k q) = q := by
  unfold ρ ρinv
  split_ifs <;> omega

theorem ρ_lt {k p : ℕ} (hp : p < P.n) : P.ρ k p < P.n := by
  unfold ρ
  split_ifs <;> omega

theorem ρinv_lt {k q : ℕ} (hk : k ≤ P.n) (hq : q < P.n) : P.ρinv k q < P.n := by
  unfold ρinv
  split_ifs <;> omega

theorem ρ_self {k : ℕ} : P.ρ k k = 0 := by
  unfold ρ
  rw [if_neg (lt_irrefl _)]
  omega

theorem ρ_injOn {k p p' : ℕ} (hk : k ≤ P.n) (hp : p < P.n) (hp' : p' < P.n)
    (h : P.ρ k p = P.ρ k p') : p = p' := by
  rw [← ρinv_ρ hk hp, h, ρinv_ρ hk hp']

theorem ρ_prev {k p : ℕ} (hk0 : 0 < k) (hk : k < P.n) (hp : p < P.n) :
    P.ρ k (P.prev p) = P.prev (P.ρ k p) := by
  unfold ρ prev
  split_ifs <;> omega

theorem ρ_of_lt {k p : ℕ} (h : p < k) : P.ρ k p = p + (P.n - k) := by
  unfold ρ
  rw [if_pos h]

theorem ρ_of_le {k p : ℕ} (h : k ≤ p) : P.ρ k p = p - k := by
  unfold ρ
  rw [if_neg (by omega)]

/-- The data of a rotation: the spoke `k` moved to `0`, and the new spoke positions. -/
structure RotData (P : Pole) where
  /-- The position moved to `0`. -/
  k : ℕ
  /-- The new second spoke position. -/
  s₂' : ℕ
  /-- The new third spoke position. -/
  s₁' : ℕ
  k_pos : 0 < k
  k_lt : k < P.n
  s₂'_pos : 0 < s₂'
  s₂'_lt : s₂' < s₁'
  s₁'_lt : s₁' < P.n
  spoke_iff : ∀ q, q < P.n → ((q = 0 ∨ q = s₂' ∨ q = s₁') ↔ P.Spoke (P.ρinv k q))

variable (d : P.RotData)

theorem RotData.inner_iff {q : ℕ} :
    (0 < q ∧ q < P.n ∧ q ≠ d.s₂' ∧ q ≠ d.s₁') ↔ q < P.n ∧ P.Inner (P.ρinv d.k q) := by
  constructor
  · rintro ⟨h0, hq, h2, h1⟩
    refine ⟨hq, ?_⟩
    rw [Pole.inner_iff]
    refine ⟨ρinv_lt d.k_lt.le hq, ?_⟩
    rw [← d.spoke_iff q hq]
    omega
  · rintro ⟨hq, hi⟩
    have := d.spoke_iff q hq
    rw [Pole.inner_iff] at hi
    have hns : ¬ (q = 0 ∨ q = d.s₂' ∨ q = d.s₁') := fun h ↦ hi.2 (this.mp h)
    refine ⟨?_, hq, ?_, ?_⟩ <;> omega

/-- The rotated pole. -/
def rotGen : Pole where
  n := P.n
  s₂ := d.s₂'
  s₁ := d.s₁'
  μ := fun q ↦ P.ρ d.k (P.μ (P.ρinv d.k q))
  s₂_pos := d.s₂'_pos
  s₂_lt_s₁ := d.s₂'_lt
  s₁_lt_n := d.s₁'_lt
  μ_inner := by
    intro q h0 hq h2 h1
    have hi := (d.inner_iff.mp ⟨h0, hq, h2, h1⟩).2
    have hμ := inner_μ hi
    have hlt : P.ρ d.k (P.μ (P.ρinv d.k q)) < P.n := ρ_lt (inner_lt hμ)
    have := d.inner_iff (q := P.ρ d.k (P.μ (P.ρinv d.k q)))
    rw [ρinv_ρ d.k_lt.le (inner_lt hμ)] at this
    exact this.mpr ⟨hlt, hμ⟩
  μ_μ := by
    intro q h0 hq h2 h1
    have hi := (d.inner_iff.mp ⟨h0, hq, h2, h1⟩).2
    have hμ := inner_μ hi
    rw [ρinv_ρ d.k_lt.le (inner_lt hμ), μ_μ_of_inner hi, ρ_ρinv d.k_lt.le hq]
  μ_ne := by
    intro q h0 hq h2 h1 h
    have hi := (d.inner_iff.mp ⟨h0, hq, h2, h1⟩).2
    have hμ := inner_μ hi
    have := ρ_injOn d.k_lt.le (inner_lt hμ) (ρinv_lt d.k_lt.le hq) (by rw [h, ρ_ρinv d.k_lt.le hq])
    exact μ_ne_of_inner hi this

theorem rotGen_n : (P.rotGen d).n = P.n := rfl

theorem rotGen_μ (q : ℕ) : (P.rotGen d).μ q = P.ρ d.k (P.μ (P.ρinv d.k q)) := rfl

theorem rotGen_μ_ρ {p : ℕ} (hp : p < P.n) : (P.rotGen d).μ (P.ρ d.k p) = P.ρ d.k (P.μ p) := by
  rw [rotGen_μ, ρinv_ρ d.k_lt.le hp]

theorem rotGen_prev (p : ℕ) : (P.rotGen d).prev p = P.prev p := rfl

theorem rotGen_inner_iff {q : ℕ} : (P.rotGen d).Inner q ↔ q < P.n ∧ P.Inner (P.ρinv d.k q) :=
  d.inner_iff

theorem rotGen_inner_ρ {p : ℕ} (hp : p < P.n) : (P.rotGen d).Inner (P.ρ d.k p) ↔ P.Inner p := by
  rw [rotGen_inner_iff, ρinv_ρ d.k_lt.le hp]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨ρ_lt hp, h⟩⟩

theorem rotGen_spoke_ρ {p : ℕ} (hp : p < P.n) : (P.rotGen d).Spoke (P.ρ d.k p) ↔ P.Spoke p := by
  change (P.ρ d.k p = 0 ∨ P.ρ d.k p = d.s₂' ∨ P.ρ d.k p = d.s₁') ↔ _
  rw [d.spoke_iff _ (ρ_lt hp), ρinv_ρ d.k_lt.le hp]

/-- Transporting a cover of the rotated pole back. -/
def Cover.unrot (C : (P.rotGen d).Cover) : P.Cover where
  lab := fun p ↦ C.lab (P.ρ d.k p)
  clab := fun p ↦ C.clab (P.ρ d.k p)
  nonempty := fun p hp ↦ C.nonempty _ (ρ_lt hp)
  disj₁ := by
    intro p hp
    have := C.disj₁ (P.ρ d.k p) (ρ_lt hp)
    rwa [rotGen_prev, ← ρ_prev d.k_pos d.k_lt hp] at this
  disj₂ := by
    intro p hp
    have := C.disj₂ (P.ρ d.k p) (ρ_lt hp)
    rwa [rotGen_prev, ← ρ_prev d.k_pos d.k_lt hp] at this
  disj₃ := fun p hp ↦ C.disj₃ (P.ρ d.k p) (ρ_lt hp)
  union := by
    intro p hp
    have := C.union (P.ρ d.k p) (ρ_lt hp)
    rwa [rotGen_prev, ← ρ_prev d.k_pos d.k_lt hp] at this
  chord := by
    intro p hp
    have := C.chord _ ((rotGen_inner_ρ d (inner_lt hp)).mpr hp)
    rwa [rotGen_μ_ρ d (inner_lt hp)] at this
  spoke := fun p hp ↦ C.spoke _ ((rotGen_spoke_ρ d (spoke_lt hp)).mpr hp)

theorem rotGen_ext_image {T : Finset ℕ} (hT : ∀ p ∈ T, P.Inner p) :
    (P.rotGen d).ext (T.image (P.ρ d.k)) = P.ext T := by
  unfold ext
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro p hp
    rw [rotGen_μ_ρ d (inner_lt (hT p hp)), Finset.mem_image]
    constructor
    · intro h hμ
      exact h ⟨_, hμ, rfl⟩
    · rintro h ⟨q, hq, hqe⟩
      exact h (ρ_injOn d.k_lt.le (inner_lt (hT q hq)) (inner_lt (inner_μ (hT p hp))) hqe ▸ hq)
  · intro p hp q hq h
    exact ρ_injOn d.k_lt.le (inner_lt (hT p (Finset.mem_filter.mp hp).1))
      (inner_lt (hT q (Finset.mem_filter.mp hq).1)) h

/-- The rotation moving the spoke `s₂` to `0`. -/
def rotDataS₂ : P.RotData where
  k := P.s₂
  s₂' := P.s₁ - P.s₂
  s₁' := P.n - P.s₂
  k_pos := P.s₂_pos
  k_lt := by have := P.s₂_lt_s₁; have := P.s₁_lt_n; omega
  s₂'_pos := by have := P.s₂_lt_s₁; omega
  s₂'_lt := by have := P.s₂_lt_s₁; have := P.s₁_lt_n; omega
  s₁'_lt := by have := P.s₂_pos; have := P.s₂_lt_s₁; have := P.s₁_lt_n; omega
  spoke_iff := by
    intro q hq
    have := P.s₂_pos
    have := P.s₂_lt_s₁
    have := P.s₁_lt_n
    unfold Spoke ρinv
    split_ifs <;> omega

/-- The rotation moving the spoke `s₁` to `0`. -/
def rotDataS₁ : P.RotData where
  k := P.s₁
  s₂' := P.n - P.s₁
  s₁' := P.n - P.s₁ + P.s₂
  k_pos := by have := P.s₂_pos; have := P.s₂_lt_s₁; omega
  k_lt := P.s₁_lt_n
  s₂'_pos := by have := P.s₁_lt_n; omega
  s₂'_lt := by have := P.s₂_pos; omega
  s₁'_lt := by have := P.s₂_pos; have := P.s₂_lt_s₁; have := P.s₁_lt_n; omega
  spoke_iff := by
    intro q hq
    have := P.s₂_pos
    have := P.s₂_lt_s₁
    have := P.s₁_lt_n
    unfold Spoke ρinv
    split_ifs <;> omega

/-- The pole rotated so that the spoke `s₂` sits at `0`. -/
def rotS₂ : Pole := P.rotGen P.rotDataS₂

/-- The pole rotated so that the spoke `s₁` sits at `0`. -/
def rotS₁ : Pole := P.rotGen P.rotDataS₁

theorem rotS₂_n : P.rotS₂.n = P.n := rfl
theorem rotS₂_s₂ : P.rotS₂.s₂ = P.s₁ - P.s₂ := rfl
theorem rotS₂_s₁ : P.rotS₂.s₁ = P.n - P.s₂ := rfl
theorem rotS₁_n : P.rotS₁.n = P.n := rfl
theorem rotS₁_s₂ : P.rotS₁.s₂ = P.n - P.s₁ := rfl
theorem rotS₁_s₁ : P.rotS₁.s₁ = P.n - P.s₁ + P.s₂ := rfl

/-- Transporting a cover of `rotS₂` back. -/
def Cover.unrotS₂ (C : P.rotS₂.Cover) : P.Cover := C.unrot P.rotDataS₂

/-- Transporting a cover of `rotS₁` back. -/
def Cover.unrotS₁ (C : P.rotS₁.Cover) : P.Cover := C.unrot P.rotDataS₁

private theorem image_Ico_of_lt {k a b : ℕ} (hb : b ≤ k) :
    (Finset.Ico a b).image (P.ρ k) = Finset.Ico (a + (P.n - k)) (b + (P.n - k)) := by
  ext q
  rw [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_Ico] at hp
    rw [ρ_of_lt (by omega)]
    omega
  · intro h
    refine ⟨q - (P.n - k), ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · rw [ρ_of_lt (by omega)]
      omega

private theorem image_Ico_of_le {k a b : ℕ} (ha : k ≤ a) :
    (Finset.Ico a b).image (P.ρ k) = Finset.Ico (a - k) (b - k) := by
  ext q
  rw [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_Ico] at hp
    rw [ρ_of_le (by omega)]
    omega
  · intro h
    refine ⟨q + k, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · rw [ρ_of_le (by omega)]
      omega

theorem rotS₂_T₀ : P.rotS₂.T₀ = P.T₁.image (P.ρ P.s₂) := by
  have := P.s₂_lt_s₁
  unfold T₀ T₁
  rw [image_Ico_of_le (by omega), rotS₂_s₂]
  congr 1
  omega

theorem rotS₂_T₁ : P.rotS₂.T₁ = P.T₂.image (P.ρ P.s₂) := by
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  unfold T₁ T₂
  rw [image_Ico_of_le (by omega), rotS₂_s₂, rotS₂_s₁]
  congr 1
  omega

theorem rotS₂_T₂ : P.rotS₂.T₂ = P.T₀.image (P.ρ P.s₂) := by
  have := P.s₂_pos
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  unfold T₀ T₂
  rw [image_Ico_of_lt le_rfl, rotS₂_s₁]
  change Finset.Ico _ P.n = _
  congr 1 <;> omega

theorem rotS₁_T₀ : P.rotS₁.T₀ = P.T₂.image (P.ρ P.s₁) := by
  have := P.s₁_lt_n
  unfold T₀ T₂
  rw [image_Ico_of_le (by omega), rotS₁_s₂]
  congr 1
  omega

theorem rotS₁_T₁ : P.rotS₁.T₁ = P.T₀.image (P.ρ P.s₁) := by
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  unfold T₀ T₁
  rw [image_Ico_of_lt (by omega), rotS₁_s₂, rotS₁_s₁]
  congr 1 <;> omega

theorem rotS₁_T₂ : P.rotS₁.T₂ = P.T₁.image (P.ρ P.s₁) := by
  have := P.s₂_lt_s₁
  have := P.s₁_lt_n
  unfold T₁ T₂
  rw [image_Ico_of_lt (by omega), rotS₁_s₁]
  change Finset.Ico _ P.n = _
  congr 1 <;> omega

theorem rotS₂_ext_T₀ : P.rotS₂.ext P.rotS₂.T₀ = P.ext P.T₁ := by
  rw [rotS₂_T₀]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₁ hp)

theorem rotS₂_ext_T₁ : P.rotS₂.ext P.rotS₂.T₁ = P.ext P.T₂ := by
  rw [rotS₂_T₁]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₂ hp)

theorem rotS₂_ext_T₂ : P.rotS₂.ext P.rotS₂.T₂ = P.ext P.T₀ := by
  rw [rotS₂_T₂]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₀ hp)

theorem rotS₁_ext_T₀ : P.rotS₁.ext P.rotS₁.T₀ = P.ext P.T₂ := by
  rw [rotS₁_T₀]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₂ hp)

theorem rotS₁_ext_T₁ : P.rotS₁.ext P.rotS₁.T₁ = P.ext P.T₀ := by
  rw [rotS₁_T₁]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₀ hp)

theorem rotS₁_ext_T₂ : P.rotS₁.ext P.rotS₁.T₂ = P.ext P.T₁ := by
  rw [rotS₁_T₂]
  exact rotGen_ext_image _ (fun p hp ↦ inner_of_mem_T₁ hp)

end Pole
end GraphPuzzles
