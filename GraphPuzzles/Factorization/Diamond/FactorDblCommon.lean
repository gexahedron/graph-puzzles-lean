import GraphPuzzles.Factorization.Diamond.FactorCanon
import GraphPuzzles.Factorization.FactorProjection

/-!
# Common facts for the double completions

Structural facts about two nested cuts `∂X ⊆ ∂W` of a closed graph, the middle part
`M = W \ X`, and the couples of the two cuts.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Couples

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

/-- Two dangling edges lie in the same couple iff they are equal or partners. -/
theorem same_couple_iff {d d' : ℕ} (hd : d ∈ P.dangling) (hd' : d' ∈ P.dangling) :
    (d ∈ couple₁ hP m ↔ d' ∈ couple₁ hP m) ↔ (d = d' ∨ partner hP m d = d') := by
  constructor
  · intro h
    by_cases h1 : d ∈ couple₁ hP m
    · have h2 := h.mp h1
      rw [mem_couple₁_iff'] at h1 h2
      rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
      · exact Or.inl rfl
      · right; rw [← h2, partner_partner hP m hd']
      · right; exact h1
      · left; exact partner_inj hP m hd hd' (h1.trans h2.symm)
    · have h2 : d' ∉ couple₁ hP m := fun h' ↦ h1 (h.mpr h')
      rw [← mem_couple₂_iff hP m hd, mem_couple₂_iff'] at h1
      rw [← mem_couple₂_iff hP m hd', mem_couple₂_iff'] at h2
      rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
      · exact Or.inl rfl
      · right; rw [← h2, partner_partner hP m hd']
      · right; exact h1
      · left; exact partner_inj hP m hd hd' (h1.trans h2.symm)
  · rintro (rfl | rfl)
    · exact Iff.rfl
    · exact (partner_mem_couple₁_iff hP m hd).symm

/-- The token to which a dangling edge is attached, expressed through the couples. -/
theorem tok_eq_of_partner {Δ : FinGraph} {S T : Finset ℕ} (hS : P.dangling = S) (p' : ℕ → ℕ)
    (hp : ∀ d ∈ S, partner hP m d = p' d) (hne : (S \ T).Nonempty)
    {d : ℕ} (hd : d ∈ S) :
    (if d ∈ couple₁ hP m then (if first S T ∈ couple₁ hP m then tokU Δ S T else tokU Δ S T + 1)
      else (if first S T ∈ couple₁ hP m then tokU Δ S T + 1 else tokU Δ S T)) =
      tok Δ S T p' d := by
  subst hS
  have hf := first_mem P.dangling T hne
  have hfS : first P.dangling T ∈ P.dangling := (Finset.mem_sdiff.mp hf).1
  have key := same_couple_iff hP m hd hfS
  rw [hp d hd] at key
  unfold tok
  by_cases h : d = first P.dangling T ∨ p' d = first P.dangling T
  · rw [if_pos h]
    have := key.mpr h
    by_cases h1 : d ∈ couple₁ hP m
    · rw [if_pos h1, if_pos (this.mp h1)]
    · rw [if_neg h1, if_neg (fun h' ↦ h1 (this.mpr h'))]
  · rw [if_neg h]
    have : ¬ (d ∈ couple₁ hP m ↔ first P.dangling T ∈ couple₁ hP m) := fun h' ↦ h (key.mp h')
    by_cases h1 : d ∈ couple₁ hP m
    · rw [if_pos h1, if_neg (fun h' ↦ this ⟨fun _ ↦ h', fun _ ↦ h1⟩)]
    · rw [if_neg h1, if_pos (by
        by_contra h'
        exact this ⟨fun h'' ↦ absurd h'' h1, fun h'' ↦ absurd h'' h'⟩)]

/-- The token of a label `d`, expressed through the couple of a dangling edge `c` of a pole
whose couples correspond to the pairs of `p'`. -/
theorem tok_eq_of_iff {Δ : FinGraph} {S T : Finset ℕ} (p' : ℕ → ℕ) (_hne : (S \ T).Nonempty)
    {c : ℕ} (hc : c ∈ P.dangling) (hf : first S T ∈ P.dangling) {d : ℕ}
    (h : (c = first S T ∨ partner hP m c = first S T) ↔ (d = first S T ∨ p' d = first S T)) :
    (if c ∈ couple₁ hP m then (if first S T ∈ couple₁ hP m then tokU Δ S T else tokU Δ S T + 1)
      else (if first S T ∈ couple₁ hP m then tokU Δ S T + 1 else tokU Δ S T)) =
      tok Δ S T p' d := by
  have key := same_couple_iff hP m hc hf
  unfold tok
  by_cases hd : d = first S T ∨ p' d = first S T
  · rw [if_pos hd]
    have := key.mpr (h.mpr hd)
    by_cases h1 : c ∈ couple₁ hP m
    · rw [if_pos h1, if_pos (this.mp h1)]
    · rw [if_neg h1, if_neg (fun h' ↦ h1 (this.mpr h'))]
  · rw [if_neg hd]
    have : ¬ (c ∈ couple₁ hP m ↔ first S T ∈ couple₁ hP m) := fun h' ↦ hd (h.mp (key.mp h'))
    by_cases h1 : c ∈ couple₁ hP m
    · rw [if_pos h1, if_neg (fun h' ↦ this ⟨fun _ ↦ h', fun _ ↦ h1⟩)]
    · rw [if_neg h1, if_pos (by
        by_contra h'
        exact this ⟨fun h'' ↦ absurd h'' h1, fun h'' ↦ absurd h'' h'⟩)]

end Couples

section PoleFacts

/-- Membership in the edge set of a pole: an edge with an end in the shore. -/
theorem mem_pole_Es_iff' {Γ : FinGraph} {Z : Finset ℕ} {e : ℕ} :
    e ∈ (Γ.pole Z).Es ↔ e ∈ Γ.Es ∧ ∃ i, Γ.ends e i ∈ Z := by
  rw [pole_Es, Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact ⟨edgesIn_subset Z h, 0, (mem_edgesIn.mp h).2 0⟩
    · obtain ⟨i, hi, -⟩ := bd_side h
      exact ⟨bd_subset Z h, i, hi⟩
  · rintro ⟨he, i, hi⟩
    exact mem_edgesIn_or_bd he hi

/-- The ends of an old edge in a cap: unchanged inside, redirected to the fresh vertex of its
couple outside. -/
theorem cap_ends_eq {P : FinGraph} (hP : P.IsPole4) (m : Fin 3) {e : ℕ} (he : e ∈ P.Es) (i : Fin 2) :
    (cap hP m).ends e i = if P.ends e i ∈ P.Vs then P.ends e i
      else (if e ∈ couple₁ hP m then freshV P else freshV P + 1) := by
  show (if e = freshE P then _ else if e ∈ P.dangling ∧ P.ends e i ∉ P.Vs then _ else _) = _
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he))]
  by_cases h : P.ends e i ∈ P.Vs
  · rw [if_neg (fun h' ↦ h'.2 h), if_pos h]
  · rw [if_pos ⟨mem_dangling.mpr ⟨he, i, h⟩, h⟩, if_neg h]

/-- The ends of an old edge in a join are unchanged. -/
theorem join_ends_eq {P : FinGraph} (hP : P.IsPole4) (m : Fin 3) {e : ℕ} (he : e ∈ P.Es) (i : Fin 2) :
    (join hP m).ends e i = P.ends e i := join_ends_old hP m he i

end PoleFacts

section Nested

variable {Δ : FinGraph} {X W : Finset ℕ} (hcl : Δ.IsClosed) (hXW : X ⊆ W) (hW : W ⊆ Δ.Vs)
include hXW

omit hcl hW in
/-- A through edge has its `W`-end in `X`. -/
theorem thru_ends {e : ℕ} (he : e ∈ Δ.bd X ∩ Δ.bd W) (i : Fin 2) :
    Δ.ends e i ∈ X ↔ Δ.ends e i ∈ W := by
  rw [Finset.mem_inter, mem_bd, mem_bd] at he
  obtain ⟨⟨_, hX⟩, ⟨_, hW'⟩⟩ := he
  have i0 : Δ.ends e 0 ∈ X → Δ.ends e 0 ∈ W := fun h ↦ hXW h
  have i1 : Δ.ends e 1 ∈ X → Δ.ends e 1 ∈ W := fun h ↦ hXW h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> tauto

omit hcl hW in
/-- An edge of `∂X` not in `∂W` has both ends in `W`, one in `X` and one in `W \ X`. -/
theorem sdiffX_ends {d : ℕ} (hd : d ∈ Δ.bd X \ Δ.bd W) (i : Fin 2) :
    Δ.ends d i ∈ W ∧ (Δ.ends d i ∈ W \ X ↔ Δ.ends d i ∉ X) := by
  rw [Finset.mem_sdiff, mem_bd, mem_bd] at hd
  obtain ⟨⟨he, hX⟩, hW'⟩ := hd
  have i0 : Δ.ends d 0 ∈ X → Δ.ends d 0 ∈ W := fun h ↦ hXW h
  have i1 : Δ.ends d 1 ∈ X → Δ.ends d 1 ∈ W := fun h ↦ hXW h
  simp only [he, true_and, not_not] at hW'
  have hi : i = 0 ∨ i = 1 := by omega
  rw [Finset.mem_sdiff]
  rcases hi with rfl | rfl <;> constructor <;> tauto

omit hcl hW in
/-- An edge of `∂W` not in `∂X` has its `W`-end in `W \ X`. -/
theorem sdiffW_ends {d : ℕ} (hd : d ∈ Δ.bd W \ Δ.bd X) (i : Fin 2) :
    Δ.ends d i ∉ X ∧ (Δ.ends d i ∈ W \ X ↔ Δ.ends d i ∈ W) := by
  rw [Finset.mem_sdiff, mem_bd, mem_bd] at hd
  obtain ⟨⟨he, hW'⟩, hX⟩ := hd
  have i0 : Δ.ends d 0 ∈ X → Δ.ends d 0 ∈ W := fun h ↦ hXW h
  have i1 : Δ.ends d 1 ∈ X → Δ.ends d 1 ∈ W := fun h ↦ hXW h
  simp only [he, true_and, not_not] at hX
  have hi : i = 0 ∨ i = 1 := by omega
  rw [Finset.mem_sdiff]
  rcases hi with rfl | rfl <;> constructor <;> tauto

omit hcl hXW hW in
theorem edgesIn_sdiff_ends {e : ℕ} (he : e ∈ Δ.edgesIn (W \ X)) :
    e ∉ Δ.bd X ∧ e ∉ Δ.bd W := by
  rw [mem_edgesIn] at he
  have h0 := Finset.mem_sdiff.mp (he.2 0)
  have h1 := Finset.mem_sdiff.mp (he.2 1)
  rw [mem_bd, mem_bd]
  constructor
  · rintro ⟨-, h⟩; exact h ⟨fun h' ↦ absurd h' h0.2, fun h' ↦ absurd h' h1.2⟩
  · rintro ⟨-, h⟩; exact h ⟨fun _ ↦ h1.1, fun _ ↦ h0.1⟩

omit hcl hXW hW in
/-- The inner end of a boundary edge of `W \ X`. -/
theorem innerE_eq {d : ℕ} (hd : d ∈ Δ.bd (W \ X)) {i : Fin 2} (hi : Δ.ends d i ∈ W \ X) :
    innerE Δ (W \ X) d = Δ.ends d i := by
  rw [mem_bd] at hd
  unfold innerE
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · rw [if_pos hi]
  · rw [if_neg (fun h ↦ hd.2 ⟨fun _ ↦ hi, fun _ ↦ h⟩)]

omit hcl hXW hW in
theorem innerE_mem {d : ℕ} (hd : d ∈ Δ.bd (W \ X)) : innerE Δ (W \ X) d ∈ W \ X := by
  obtain ⟨i, hi, -⟩ := bd_side hd
  rw [innerE_eq hd hi]
  exact hi

omit hcl hXW hW in
theorem innerE_notMem_of_ne {d : ℕ} (hd : d ∈ Δ.bd (W \ X)) {i : Fin 2}
    (hi : Δ.ends d i ∉ W \ X) : innerE Δ (W \ X) d = Δ.ends d (Fin.rev i) := by
  obtain ⟨j, hj, hj'⟩ := bd_side hd
  rw [innerE_eq hd hj]
  have : i = Fin.rev j := by
    by_contra h
    have : i = j := by
      have hj0 : j = 0 ∨ j = 1 := by omega
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hj0 with rfl | rfl <;> rcases hi0 with rfl | rfl
      · rfl
      · exact absurd Iso.rev_zero'.symm h
      · exact absurd Iso.rev_one'.symm h
      · rfl
    exact hi (this ▸ hj)
  rw [this, Fin.rev_rev]

omit hW in
include hcl in
/-- The set of dangling edges of the middle part. -/
theorem bd_middle : Δ.bd (W \ X) = (Δ.bd X \ Δ.bd W) ∪ (Δ.bd W \ Δ.bd X) := bd_sdiff_eq hcl hXW

section NoCouple

variable (hPX : (Δ.pole X).IsPole4) (mX : Fin 3) (hPW : (Δ.pole W).IsPole4) (mW : Fin 3)
  (hnoX : ∀ d ∈ Δ.bd X, d ∈ Δ.bd W → partner hPX mX d ∉ Δ.bd W)
  (hnoW : ∀ d ∈ Δ.bd W, d ∈ Δ.bd X → partner hPW mW d ∉ Δ.bd X)

omit hcl hXW hW hPW mW hnoW in
include hnoX in
theorem sdiffX_nonempty : (Δ.bd X \ Δ.bd W).Nonempty := by
  have h0 := bdEmb_mem hPX 0
  rw [dangling_pole] at h0
  by_cases h : bdEmb hPX 0 ∈ Δ.bd W
  · refine ⟨partner hPX mX (bdEmb hPX 0), Finset.mem_sdiff.mpr ⟨?_, hnoX _ h0 h⟩⟩
    have := partner_mem hPX mX (bdEmb_mem hPX 0)
    rw [dangling_pole] at this
    exact this
  · exact ⟨_, Finset.mem_sdiff.mpr ⟨h0, h⟩⟩

omit hcl hXW hW hPX mX hnoX in
include hnoW in
theorem sdiffW_nonempty : (Δ.bd W \ Δ.bd X).Nonempty := by
  have h0 := bdEmb_mem hPW 0
  rw [dangling_pole] at h0
  by_cases h : bdEmb hPW 0 ∈ Δ.bd X
  · refine ⟨partner hPW mW (bdEmb hPW 0), Finset.mem_sdiff.mpr ⟨?_, hnoW _ h0 h⟩⟩
    have := partner_mem hPW mW (bdEmb_mem hPW 0)
    rw [dangling_pole] at this
    exact this
  · exact ⟨_, Finset.mem_sdiff.mpr ⟨h0, h⟩⟩

end NoCouple

end Nested

end FinGraph
end GraphPuzzles
