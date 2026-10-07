import GraphPuzzles.Factorization.FactorProjection

/-!
# Poles of completions are isomorphic to poles of the original graph

For a vertex set `Z` inside the pole `W` of a closed graph, the pole of `Z` in the cap of `W`
is the pole of `Z` in the original graph (the cap only redirects outer ends), and the pole of
`Z` in the join of `W` is obtained by relabelling each boundary edge of `Z` that is a dangling
edge of `W` to the join edge of its couple, provided no couple of `W` has both edges on the
boundary of `Z`.  Isomorphic colourable poles have isomorphic factors.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {W : Finset ℕ} (hP : (Δ.pole W).IsPole4) (m : Fin 3)

section CapPole

variable (hcl : Δ.IsClosed) (hW : W ⊆ Δ.Vs) {Z : Finset ℕ} (hZ : Z ⊆ W)
include hcl hW hZ

theorem capPole_Es : ((cap hP m).pole Z).Es = (Δ.pole Z).Es := by
  rw [pole_Es, pole_Es, cap_edgesIn hP m hZ, cap_bd_old hP m hcl hW hZ, pole_edgesIn W Z hZ]

omit hcl hW in
theorem cap_ends_mem_iff {e : ℕ} (he : e ∈ (Δ.pole W).Es) (i : Fin 2) :
    (cap hP m).ends e i ∈ Z ↔ Δ.ends e i ∈ Z := by
  by_cases hi : Δ.ends e i ∈ W
  · rw [cap_ends_old hP m he hi, pole_ends]
  · have hd : e ∈ (Δ.pole W).dangling := mem_dangling.mpr ⟨he, i, hi⟩
    have hio : i = outerIdx hP e := by
      rcases idx_eq_inner_or_outer hP hd i with h | h
      · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
      · exact h
    rw [hio, cap_ends_outer hP m hd]
    have hZi : Δ.ends e (outerIdx hP e) ∉ Z := fun h ↦ hi (hio ▸ hZ h)
    constructor
    · intro h
      split_ifs at h
      · exact absurd (hZ h) freshV_notMem
      · exact absurd (hZ h) freshV_succ_notMem
    · intro h
      exact absurd h hZi

/-- The pole of `Z ⊆ W` in the cap of `W` is the pole of `Z` in `Δ`, with the identity
relabelling. -/
noncomputable def capPoleIso : Iso ((cap hP m).pole Z) (Δ.pole Z) where
  fv := id
  gv := id
  fe := id
  ge := id
  flip := fun _ ↦ false
  fv_mem := fun _ h ↦ h
  gv_mem := fun _ h ↦ h
  gv_fv := fun _ _ ↦ rfl
  fv_gv := fun _ _ ↦ rfl
  fe_mem := by
    intro e he
    rw [← capPole_Es hP m hcl hW hZ]
    exact he
  ge_mem := by
    intro e he
    rw [capPole_Es hP m hcl hW hZ]
    exact he
  ge_fe := fun _ _ ↦ rfl
  fe_ge := fun _ _ ↦ rfl
  ends_iff := by
    intro e he i
    rw [capPole_Es hP m hcl hW hZ, pole_Es, Finset.mem_union] at he
    have heW : e ∈ (Δ.pole W).Es := by
      rw [pole_Es, Finset.mem_union]
      rcases he with he | he
      · exact Or.inl (edgesIn_mono hZ he)
      · obtain ⟨j, hj, _⟩ := bd_side he
        exact mem_edgesIn_or_bd (bd_subset Z he) (hZ hj)
    show (cap hP m).ends e i ∈ Z ↔ Δ.ends e i ∈ Z
    exact cap_ends_mem_iff hP m hZ heW i
  map_ends := by
    intro e he i hi
    rw [capPole_Es hP m hcl hW hZ, pole_Es, Finset.mem_union] at he
    have heW : e ∈ (Δ.pole W).Es := by
      rw [pole_Es, Finset.mem_union]
      rcases he with he | he
      · exact Or.inl (edgesIn_mono hZ he)
      · obtain ⟨j, hj, _⟩ := bd_side he
        exact mem_edgesIn_or_bd (bd_subset Z he) (hZ hj)
    show (cap hP m).ends e i = Δ.ends e i
    have hi' : Δ.ends e i ∈ Z := (cap_ends_mem_iff hP m hZ heW i).mp hi
    exact cap_ends_old hP m heW (hZ hi')

end CapPole

/-- A boundary edge of `Z ⊆ W` lies in the pole of `W`. -/
theorem mem_poleW_of_bd {Z : Finset ℕ} (hZ : Z ⊆ W) {e : ℕ} (he : e ∈ Δ.bd Z) :
    e ∈ (Δ.pole W).Es := by
  rw [pole_Es, Finset.mem_union]
  obtain ⟨i, hi, _⟩ := bd_side he
  exact mem_edgesIn_or_bd (bd_subset Z he) (hZ hi)

theorem mem_poleW_of_edgesIn {Z : Finset ℕ} (hZ : Z ⊆ W) {e : ℕ} (he : e ∈ Δ.edgesIn Z) :
    e ∈ (Δ.pole W).Es := by
  rw [pole_Es, Finset.mem_union]
  exact Or.inl (edgesIn_mono hZ he)

section JoinPole

variable (hcl : Δ.IsClosed) (hW : W ⊆ Δ.Vs) (Z : Finset ℕ) (hZ : Z ⊆ W)
  (hno : ∀ k, bdEmb hP k ∈ Δ.bd Z → bdEmb hP (pairing m k) ∈ Δ.bd Z → False)

/-- The inner index of a dangling edge, as a total function. -/
noncomputable def innerIdxOf (e : ℕ) : Fin 2 :=
  if h : e ∈ (Δ.pole W).dangling then innerIdx hP h else 0

theorem innerIdxOf_eq {e : ℕ} (h : e ∈ (Δ.pole W).dangling) : innerIdxOf hP e = innerIdx hP h := by
  unfold innerIdxOf
  rw [dif_pos h]

/-- The representative of the couple containing `k` in `{0, other m}`. -/
def rep (k : Fin 4) : Fin 4 := if k = 0 ∨ k = pairing m 0 then 0 else other m

theorem rep_spec (k : Fin 4) : k = rep m k ∨ k = pairing m (rep m k) := by
  unfold rep
  rcases four_positions m k with rfl | rfl | rfl | rfl
  · simp
  · rw [if_pos (Or.inr rfl)]; exact Or.inr rfl
  · rw [if_neg (by rw [not_or]; exact ⟨other_ne_zero m, other_ne_pairing_zero m⟩)]; exact Or.inl rfl
  · rw [if_neg (by rw [not_or]; exact ⟨pairing_other_ne_zero m, pairing_other_ne_pairing_zero m⟩)]
    exact Or.inr rfl

/-- The edge map of the join-pole isomorphism: the new edge of a crossing couple goes to the
member of the couple on the boundary of `Z`. -/
noncomputable def joinPoleFe (e : ℕ) : ℕ :=
  if e = freshE (Δ.pole W) then
    (if bdEmb hP 0 ∈ Δ.bd Z then bdEmb hP 0 else bdEmb hP (pairing m 0))
  else if e = freshE (Δ.pole W) + 1 then
    (if bdEmb hP (other m) ∈ Δ.bd Z then bdEmb hP (other m) else bdEmb hP (pairing m (other m)))
  else e

/-- The inverse: a dangling edge of `W` on the boundary of `Z` goes to the new edge of its
couple. -/
noncomputable def joinPoleGe (e : ℕ) : ℕ :=
  if e ∈ couple₁ hP m ∧ e ∈ Δ.bd Z then freshE (Δ.pole W)
  else if e ∈ couple₂ hP m ∧ e ∈ Δ.bd Z then freshE (Δ.pole W) + 1
  else e

/-- The index of a couple member in its new edge: `0` for the representative, `1` for its
partner. -/
noncomputable def newIdx (e : ℕ) : Fin 2 :=
  if e = bdEmb hP 0 ∨ e = bdEmb hP (other m) then 0 else 1

noncomputable def joinPoleFlip (e : ℕ) : Bool :=
  if e = freshE (Δ.pole W) ∨ e = freshE (Δ.pole W) + 1 then
    decide (innerIdxOf hP (joinPoleFe hP m Z e) ≠ newIdx hP m (joinPoleFe hP m Z e))
  else false

theorem joinPoleFe_old {e : ℕ} (he : e ∈ (Δ.pole W).Es) : joinPoleFe hP m Z e = e := by
  unfold joinPoleFe
  have h1 : e ≠ freshE (Δ.pole W) := fun h ↦ freshE_notMem (P := Δ.pole W) (h ▸ he)
  have h2 : e ≠ freshE (Δ.pole W) + 1 := fun h ↦ freshE_succ_notMem (P := Δ.pole W) (h ▸ he)
  rw [if_neg h1, if_neg h2]

theorem joinPoleGe_old {e : ℕ} (h : ¬ (e ∈ (Δ.pole W).dangling ∧ e ∈ Δ.bd Z)) :
    joinPoleGe hP m Z e = e := by
  unfold joinPoleGe
  rw [if_neg, if_neg]
  · rintro ⟨h1, h2⟩
    exact h ⟨couple₂_subset_dangling hP m h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact h ⟨couple₁_subset_dangling hP m h1, h2⟩

theorem joinPoleFlip_old {e : ℕ} (he : e ∈ (Δ.pole W).Es) : joinPoleFlip hP m Z e = false := by
  unfold joinPoleFlip
  rw [if_neg]
  rintro (h | h)
  · exact freshE_notMem (P := Δ.pole W) (h ▸ he)
  · exact freshE_succ_notMem (P := Δ.pole W) (h ▸ he)

/-- The new edge of the couple with representative `k ∈ {0, other m}` crosses `Z` iff exactly
one member lies on the boundary of `Z`; then `joinPoleFe` picks that member. -/
theorem joinPoleFe_new (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    joinPoleFe hP m Z (newHalf (P := Δ.pole W) m k).1 =
      if bdEmb hP k ∈ Δ.bd Z then bdEmb hP k else bdEmb hP (pairing m k) := by
  unfold joinPoleFe
  rcases hk with rfl | rfl
  · rw [newHalf_zero_fst, if_pos rfl]
  · rw [newHalf_other_fst, if_neg (by omega), if_pos rfl]

include hZ hno in
theorem crossing_iff (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    (¬ ((join hP m).ends (newHalf (P := Δ.pole W) m k).1 0 ∈ Z ↔
      (join hP m).ends (newHalf (P := Δ.pole W) m k).1 1 ∈ Z)) ↔
    (bdEmb hP k ∈ Δ.bd Z ∨ bdEmb hP (pairing m k) ∈ Δ.bd Z) := by
  have h0 : (join hP m).ends (newHalf (P := Δ.pole W) m k).1 0 = innerEnd hP (bdEmb hP k) := by
    have := join_ends_newHalf hP m k
    have hk0 : (newHalf (P := Δ.pole W) m k).2 = 0 := by
      rcases hk with rfl | rfl
      · rw [newHalf_zero]
      · rw [newHalf_other]
    rw [hk0] at this
    exact this
  have h1 : (join hP m).ends (newHalf (P := Δ.pole W) m k).1 1 =
      innerEnd hP (bdEmb hP (pairing m k)) := by
    have := join_ends_newHalf hP m (pairing m k)
    have hk1 : (newHalf (P := Δ.pole W) m (pairing m k)).1 = (newHalf (P := Δ.pole W) m k).1 :=
      (newHalf_pairing (Q := Δ.pole W) m k).1
    have hk2 : (newHalf (P := Δ.pole W) m (pairing m k)).2 = 1 := by
      rw [(newHalf_pairing (Q := Δ.pole W) m k).2]
      rcases hk with rfl | rfl
      · rw [newHalf_zero]; exact Iso.rev_zero'
      · rw [newHalf_other]; exact Iso.rev_zero'
    rw [hk1, hk2] at this
    exact this
  rw [h0, h1, ← ends_innerIdx hP (bdEmb_mem hP k), ← ends_innerIdx hP (bdEmb_mem hP _), pole_ends,
    ← mem_bd_of_dangling hP hZ (bdEmb_mem hP k), ← mem_bd_of_dangling hP hZ (bdEmb_mem hP _)]
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact h ⟨fun h' ↦ absurd h' hc.1, fun h' ↦ absurd h' hc.2⟩
  · rintro (h | h) hiff
    · exact hno k h (hiff.mp h)
    · exact hno k (hiff.mpr h) h

include hZ hno in
theorem join_edgesIn_Z : (join hP m).edgesIn Z = Δ.edgesIn Z := by
  have e := pole_edgesIn (Γ := Δ) W Z hZ
  rw [← e]
  apply join_edgesIn hP m hZ
  · rintro ⟨h1, h2⟩
    rw [← ends_innerIdx hP (bdEmb_mem hP 0), pole_ends,
      ← mem_bd_of_dangling hP hZ (bdEmb_mem hP 0)] at h1
    rw [← ends_innerIdx hP (bdEmb_mem hP _), pole_ends,
      ← mem_bd_of_dangling hP hZ (bdEmb_mem hP _)] at h2
    exact hno 0 h1 h2
  · rintro ⟨h1, h2⟩
    rw [← ends_innerIdx hP (bdEmb_mem hP _), pole_ends,
      ← mem_bd_of_dangling hP hZ (bdEmb_mem hP _)] at h1
    rw [← ends_innerIdx hP (bdEmb_mem hP _), pole_ends,
      ← mem_bd_of_dangling hP hZ (bdEmb_mem hP _)] at h2
    exact hno (other m) h1 h2

include hW hZ in
/-- The boundary of `Z` in the join, as a set. -/
theorem join_bd_Z : (join hP m).bd Z =
    ((Δ.bd Z).filter fun e ↦ e ∉ Δ.bd W) ∪
      (({freshE (Δ.pole W), freshE (Δ.pole W) + 1} : Finset ℕ).filter fun f ↦
        ¬ ((join hP m).ends f 0 ∈ Z ↔ (join hP m).ends f 1 ∈ Z)) :=
  join_bd_old hP m hZ hW

include hW hZ hno in
/-- A dangling edge of `W` on the boundary of `Z` belongs to a crossing couple, and the
new edge of that couple is a boundary edge of the join. -/
theorem newHalf_mem_join_bd {k : Fin 4} (hk : k = 0 ∨ k = other m)
    (h : bdEmb hP k ∈ Δ.bd Z ∨ bdEmb hP (pairing m k) ∈ Δ.bd Z) :
    (newHalf (P := Δ.pole W) m k).1 ∈ (join hP m).bd Z := by
  rw [join_bd_Z hP m hW Z hZ, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  right
  refine ⟨?_, (crossing_iff hP m Z hZ hno k hk).mpr h⟩
  rcases hk with rfl | rfl
  · rw [newHalf_zero_fst]; exact Finset.mem_insert_self _ _
  · rw [newHalf_other_fst]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

include hW hZ hno in
/-- Membership in the edge set of the pole of `Z` in the join. -/
theorem mem_joinPole_Es {e : ℕ} : e ∈ ((join hP m).pole Z).Es ↔
    e ∈ Δ.edgesIn Z ∨ (e ∈ Δ.bd Z ∧ e ∉ Δ.bd W) ∨
    (∃ k, (k = 0 ∨ k = other m) ∧ e = (newHalf (P := Δ.pole W) m k).1 ∧
      (bdEmb hP k ∈ Δ.bd Z ∨ bdEmb hP (pairing m k) ∈ Δ.bd Z)) := by
  rw [pole_Es, Finset.mem_union, join_edgesIn_Z hP m Z hZ hno, join_bd_Z hP m hW Z hZ,
    Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · right; right
      rcases h1 with rfl | rfl
      · refine ⟨0, Or.inl rfl, by rw [newHalf_zero_fst], ?_⟩
        rw [← newHalf_zero_fst (P' := Δ.pole W) m] at h2
        exact (crossing_iff hP m Z hZ hno 0 (Or.inl rfl)).mp h2
      · refine ⟨other m, Or.inr rfl, by rw [newHalf_other_fst], ?_⟩
        rw [← newHalf_other_fst (P' := Δ.pole W) m] at h2
        exact (crossing_iff hP m Z hZ hno (other m) (Or.inr rfl)).mp h2
  · rintro (h | ⟨h1, h2⟩ | ⟨k, hk, rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · right; right
      refine ⟨?_, (crossing_iff hP m Z hZ hno k hk).mpr h⟩
      rcases hk with rfl | rfl
      · rw [newHalf_zero_fst]; exact Or.inl rfl
      · rw [newHalf_other_fst]; exact Or.inr rfl

omit hW hcl hZ hno in
theorem mem_pole_Es_iff {e : ℕ} : e ∈ (Δ.pole Z).Es ↔
    e ∈ Δ.edgesIn Z ∨ (e ∈ Δ.bd Z ∧ e ∉ Δ.bd W) ∨ (e ∈ Δ.bd Z ∧ e ∈ Δ.bd W) := by
  rw [pole_Es, Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hW' : e ∈ Δ.bd W
      · exact Or.inr (Or.inr ⟨h, hW'⟩)
      · exact Or.inr (Or.inl ⟨h, hW'⟩)
  · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h

omit hcl hW hZ hno in
theorem join_ends_newHalf_zero (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    (join hP m).ends (newHalf (P := Δ.pole W) m k).1 0 = innerEnd hP (bdEmb hP k) := by
  have := join_ends_newHalf hP m k
  have hk0 : (newHalf (P := Δ.pole W) m k).2 = 0 := by
    rcases hk with rfl | rfl
    · rw [newHalf_zero]
    · rw [newHalf_other]
  rw [hk0] at this
  exact this

omit hcl hW hZ hno in
theorem join_ends_newHalf_one (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    (join hP m).ends (newHalf (P := Δ.pole W) m k).1 1 = innerEnd hP (bdEmb hP (pairing m k)) := by
  have := join_ends_newHalf hP m (pairing m k)
  have hk1 : (newHalf (P := Δ.pole W) m (pairing m k)).1 = (newHalf (P := Δ.pole W) m k).1 :=
    (newHalf_pairing (Q := Δ.pole W) m k).1
  have hk2 : (newHalf (P := Δ.pole W) m (pairing m k)).2 = 1 := by
    rw [(newHalf_pairing (Q := Δ.pole W) m k).2]
    rcases hk with rfl | rfl
    · rw [newHalf_zero]; exact Iso.rev_zero'
    · rw [newHalf_other]; exact Iso.rev_zero'
  rw [hk1, hk2] at this
  exact this

omit hcl hW hZ hno in
theorem newIdx_rep (k : Fin 4) (hk : k = 0 ∨ k = other m) : newIdx hP m (bdEmb hP k) = 0 := by
  unfold newIdx
  rcases hk with rfl | rfl
  · rw [if_pos (Or.inl rfl)]
  · rw [if_pos (Or.inr rfl)]

omit hcl hW hZ hno in
theorem newIdx_partner (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    newIdx hP m (bdEmb hP (pairing m k)) = 1 := by
  unfold newIdx
  rw [if_neg]
  rintro (h | h)
  · have := bdEmb_injective hP h
    rcases hk with rfl | rfl
    · exact pairing_ne m 0 this
    · exact pairing_other_ne_zero m this
  · have := bdEmb_injective hP h
    rcases hk with rfl | rfl
    · exact other_ne_pairing_zero m this.symm
    · exact pairing_ne m _ this

omit hcl hW hZ hno in
/-- The flip of a new edge sends the index of the couple member in the new edge to its inner
index. -/
theorem sw_joinPoleFlip {e a : ℕ} (he : e = freshE (Δ.pole W) ∨ e = freshE (Δ.pole W) + 1)
    (ha : joinPoleFe hP m Z e = a) :
    sw (joinPoleFlip hP m Z e) (newIdx hP m a) = innerIdxOf hP a ∧
      sw (joinPoleFlip hP m Z e) (Fin.rev (newIdx hP m a)) = Fin.rev (innerIdxOf hP a) := by
  unfold joinPoleFlip
  rw [if_pos he, ha]
  by_cases h : innerIdxOf hP a = newIdx hP m a
  · rw [h]
    simp [sw]
  · have hd : decide (innerIdxOf hP a ≠ newIdx hP m a) = true := by simp [h]
    rw [hd]
    simp only [sw, if_true, Fin.rev_rev]
    have : innerIdxOf hP a = Fin.rev (newIdx hP m a) := fin2_eq_rev_of_ne h
    rw [this, Fin.rev_rev]
    exact ⟨rfl, rfl⟩

include hcl hW hZ hno in
/-- **The pole of `Z ⊆ W` in the join of `W` is isomorphic to the pole of `Z` in `Δ`.** -/
noncomputable def joinPoleIso : Iso ((join hP m).pole Z) (Δ.pole Z) where
  fv := id
  gv := id
  fe := joinPoleFe hP m Z
  ge := joinPoleGe hP m Z
  flip := joinPoleFlip hP m Z
  fv_mem := fun _ h ↦ h
  gv_mem := fun _ h ↦ h
  gv_fv := fun _ _ ↦ rfl
  fv_gv := fun _ _ ↦ rfl
  fe_mem := by
    intro e he
    rw [mem_joinPole_Es hP m hW Z hZ hno] at he
    rw [mem_pole_Es_iff (W := W) Z]
    rcases he with he | ⟨he, hnW⟩ | ⟨k, hk, rfl, hcr⟩
    · rw [joinPoleFe_old hP m Z (mem_poleW_of_edgesIn hZ he)]
      exact Or.inl he
    · rw [joinPoleFe_old hP m Z (mem_poleW_of_bd hZ he)]
      exact Or.inr (Or.inl ⟨he, hnW⟩)
    · rw [joinPoleFe_new hP m Z k hk]
      right; right
      split_ifs with h
      · exact ⟨h, dangling_pole W ▸ bdEmb_mem hP k⟩
      · exact ⟨hcr.resolve_left h, dangling_pole W ▸ bdEmb_mem hP _⟩
  ge_mem := by
    intro e he
    rw [mem_pole_Es_iff (W := W) Z] at he
    rw [mem_joinPole_Es hP m hW Z hZ hno]
    rcases he with he | ⟨he, hnW⟩ | ⟨he, hW'⟩
    · rw [joinPoleGe_old hP m Z (fun h ↦ ?_)]
      · exact Or.inl he
      · have := (mem_edgesIn.mp he).2
        obtain ⟨-, i, hi⟩ := mem_dangling.mp h.1
        exact hi (hZ (this i))
    · rw [joinPoleGe_old hP m Z (fun h ↦ hnW (dangling_pole W ▸ h.1))]
      exact Or.inr (Or.inl ⟨he, hnW⟩)
    · have hd : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ hW'
      obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
      right; right
      unfold joinPoleGe
      by_cases hc : bdEmb hP k ∈ couple₁ hP m
      · rw [if_pos ⟨hc, he⟩]
        refine ⟨0, Or.inl rfl, by rw [newHalf_zero_fst], ?_⟩
        unfold couple₁ at hc
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with hc | hc
        · rw [← hc]; exact Or.inl he
        · rw [← hc]; exact Or.inr he
      · have hc2 : bdEmb hP k ∈ couple₂ hP m := (mem_couple₂_iff hP m hd).mpr hc
        rw [if_neg (fun h ↦ hc h.1), if_pos ⟨hc2, he⟩]
        refine ⟨other m, Or.inr rfl, by rw [newHalf_other_fst], ?_⟩
        unfold couple₂ at hc2
        rw [Finset.mem_insert, Finset.mem_singleton] at hc2
        rcases hc2 with hc2 | hc2
        · rw [← hc2]; exact Or.inl he
        · rw [← hc2]; exact Or.inr he
  ge_fe := by
    intro e he
    rw [mem_joinPole_Es hP m hW Z hZ hno] at he
    rcases he with he | ⟨he, hnW⟩ | ⟨k, hk, rfl, hcr⟩
    · rw [joinPoleFe_old hP m Z (mem_poleW_of_edgesIn hZ he)]
      apply joinPoleGe_old
      rintro ⟨h, -⟩
      have := (mem_edgesIn.mp he).2
      obtain ⟨-, i, hi⟩ := mem_dangling.mp h
      exact hi (hZ (this i))
    · rw [joinPoleFe_old hP m Z (mem_poleW_of_bd hZ he)]
      exact joinPoleGe_old hP m Z (fun h ↦ hnW (dangling_pole W ▸ h.1))
    · rw [joinPoleFe_new hP m Z k hk]
      unfold joinPoleGe
      rcases hk with rfl | rfl
      · rw [newHalf_zero_fst]
        split_ifs with h1 h2 h3 h4 h5
        · rfl
        · exact absurd h1 (fun h1 ↦ h2 ⟨Finset.mem_insert_self _ _, h1⟩)
        · exact absurd h1 (fun h1 ↦ h2 ⟨Finset.mem_insert_self _ _, h1⟩)
        · rfl
        · exact absurd (hcr.resolve_left h1)
            (fun h ↦ h4 ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩)
        · exact absurd (hcr.resolve_left h1)
            (fun h ↦ h4 ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩)
      · rw [newHalf_other_fst]
        have hd0 := bdEmb_mem hP (other m)
        have hd1 := bdEmb_mem hP (pairing m (other m))
        have hn0 : bdEmb hP (other m) ∉ couple₁ hP m :=
          (mem_couple₂_iff hP m hd0).mp (Finset.mem_insert_self _ _)
        have hn1 : bdEmb hP (pairing m (other m)) ∉ couple₁ hP m :=
          (mem_couple₂_iff hP m hd1).mp (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        split_ifs with h1 h2 h3 h4 h5
        · exact absurd h2.1 hn0
        · rfl
        · exact absurd h1 (fun h1 ↦ h3 ⟨Finset.mem_insert_self _ _, h1⟩)
        · exact absurd h4.1 hn1
        · rfl
        · exact absurd (hcr.resolve_left h1)
            (fun h ↦ h5 ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩)
  fe_ge := by
    intro e he
    rw [mem_pole_Es_iff (W := W) Z] at he
    rcases he with he | ⟨he, hnW⟩ | ⟨he, hW'⟩
    · rw [joinPoleGe_old hP m Z (fun h ↦ ?_)]
      · exact joinPoleFe_old hP m Z (mem_poleW_of_edgesIn hZ he)
      · have := (mem_edgesIn.mp he).2
        obtain ⟨-, i, hi⟩ := mem_dangling.mp h.1
        exact hi (hZ (this i))
    · rw [joinPoleGe_old hP m Z (fun h ↦ hnW (dangling_pole W ▸ h.1))]
      exact joinPoleFe_old hP m Z (mem_poleW_of_bd hZ he)
    · have hd : e ∈ (Δ.pole W).dangling := dangling_pole W ▸ hW'
      unfold joinPoleGe
      by_cases hc : e ∈ couple₁ hP m
      · rw [if_pos ⟨hc, he⟩, ← newHalf_zero_fst (P' := Δ.pole W) m,
          joinPoleFe_new hP m Z 0 (Or.inl rfl)]
        unfold couple₁ at hc
        rw [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · rw [if_pos he]
        · rw [if_neg (fun h ↦ hno 0 h he)]
      · have hc2 : e ∈ couple₂ hP m := (mem_couple₂_iff hP m hd).mpr hc
        rw [if_neg (fun h ↦ hc h.1), if_pos ⟨hc2, he⟩, ← newHalf_other_fst (P' := Δ.pole W) m,
          joinPoleFe_new hP m Z (other m) (Or.inr rfl)]
        unfold couple₂ at hc2
        rw [Finset.mem_insert, Finset.mem_singleton] at hc2
        rcases hc2 with rfl | rfl
        · rw [if_pos he]
        · rw [if_neg (fun h ↦ hno (other m) h he)]
  ends_iff := by
    intro e he i
    rw [mem_joinPole_Es hP m hW Z hZ hno] at he
    show (join hP m).ends e i ∈ Z ↔ Δ.ends (joinPoleFe hP m Z e) (sw (joinPoleFlip hP m Z e) i) ∈ Z
    rcases he with he | ⟨he, hnW⟩ | ⟨k, hk, rfl, hcr⟩
    · have heW := mem_poleW_of_edgesIn hZ he
      rw [joinPoleFe_old hP m Z heW, joinPoleFlip_old hP m Z heW, join_ends_old hP m heW]
      rfl
    · have heW := mem_poleW_of_bd hZ he
      rw [joinPoleFe_old hP m Z heW, joinPoleFlip_old hP m Z heW, join_ends_old hP m heW]
      rfl
    · -- a crossing new edge
      have hfe := joinPoleFe_new hP m Z k hk
      have hfresh : (newHalf (P := Δ.pole W) m k).1 = freshE (Δ.pole W) ∨
          (newHalf (P := Δ.pole W) m k).1 = freshE (Δ.pole W) + 1 := by
        rcases hk with rfl | rfl
        · rw [newHalf_zero_fst]; exact Or.inl rfl
        · rw [newHalf_other_fst]; exact Or.inr rfl
      have hdk := bdEmb_mem hP k
      have hdp := bdEmb_mem hP (pairing m k)
      have hin_k : innerEnd hP (bdEmb hP k) ∈ Z ↔ bdEmb hP k ∈ Δ.bd Z := by
        rw [← ends_innerIdx hP hdk, pole_ends, ← mem_bd_of_dangling hP hZ hdk]
      have hin_p : innerEnd hP (bdEmb hP (pairing m k)) ∈ Z ↔ bdEmb hP (pairing m k) ∈ Δ.bd Z := by
        rw [← ends_innerIdx hP hdp, pole_ends, ← mem_bd_of_dangling hP hZ hdp]
      have hout_k : Δ.ends (bdEmb hP k) (Fin.rev (innerIdx hP hdk)) ∉ Z :=
        fun h ↦ (innerIdx_spec hP hdk).2 (hZ h)
      have hout_p : Δ.ends (bdEmb hP (pairing m k)) (Fin.rev (innerIdx hP hdp)) ∉ Z :=
        fun h ↦ (innerIdx_spec hP hdp).2 (hZ h)
      by_cases hbk : bdEmb hP k ∈ Δ.bd Z
      · rw [if_pos hbk] at hfe
        have hnp : bdEmb hP (pairing m k) ∉ Δ.bd Z := fun h ↦ hno k hbk h
        obtain ⟨s0, s1⟩ := sw_joinPoleFlip hP m Z hfresh hfe
        rw [newIdx_rep hP m k hk] at s0 s1
        rw [innerIdxOf_eq hP hdk] at s0 s1
        rw [hfe]
        by_cases hi : i = 0
        · subst hi
          rw [s0, join_ends_newHalf_zero hP m k hk, ← ends_innerIdx hP hdk, pole_ends]
        · have hi1 : i = 1 := by omega
          subst hi1
          rw [Iso.rev_zero'] at s1
          rw [s1, join_ends_newHalf_one hP m k hk]
          exact ⟨fun h ↦ absurd (hin_p.mp h) hnp, fun h ↦ absurd h hout_k⟩
      · rw [if_neg hbk] at hfe
        have hbp : bdEmb hP (pairing m k) ∈ Δ.bd Z := hcr.resolve_left hbk
        obtain ⟨s0, s1⟩ := sw_joinPoleFlip hP m Z hfresh hfe
        rw [newIdx_partner hP m k hk] at s0 s1
        rw [innerIdxOf_eq hP hdp] at s0 s1
        rw [hfe]
        by_cases hi : i = 0
        · subst hi
          rw [Iso.rev_one'] at s1
          rw [s1, join_ends_newHalf_zero hP m k hk]
          exact ⟨fun h ↦ absurd (hin_k.mp h) hbk, fun h ↦ absurd h hout_p⟩
        · have hi1 : i = 1 := by omega
          subst hi1
          rw [s0, join_ends_newHalf_one hP m k hk, ← ends_innerIdx hP hdp, pole_ends]
  map_ends := by
    intro e he i hi
    rw [mem_joinPole_Es hP m hW Z hZ hno] at he
    show (join hP m).ends e i = Δ.ends (joinPoleFe hP m Z e) (sw (joinPoleFlip hP m Z e) i)
    rcases he with he | ⟨he, hnW⟩ | ⟨k, hk, rfl, hcr⟩
    · have heW := mem_poleW_of_edgesIn hZ he
      rw [joinPoleFe_old hP m Z heW, joinPoleFlip_old hP m Z heW, join_ends_old hP m heW]
      rfl
    · have heW := mem_poleW_of_bd hZ he
      rw [joinPoleFe_old hP m Z heW, joinPoleFlip_old hP m Z heW, join_ends_old hP m heW]
      rfl
    · have hfe := joinPoleFe_new hP m Z k hk
      have hfresh : (newHalf (P := Δ.pole W) m k).1 = freshE (Δ.pole W) ∨
          (newHalf (P := Δ.pole W) m k).1 = freshE (Δ.pole W) + 1 := by
        rcases hk with rfl | rfl
        · rw [newHalf_zero_fst]; exact Or.inl rfl
        · rw [newHalf_other_fst]; exact Or.inr rfl
      have hdk := bdEmb_mem hP k
      have hdp := bdEmb_mem hP (pairing m k)
      have hin_k : innerEnd hP (bdEmb hP k) ∈ Z ↔ bdEmb hP k ∈ Δ.bd Z := by
        rw [← ends_innerIdx hP hdk, pole_ends, ← mem_bd_of_dangling hP hZ hdk]
      have hin_p : innerEnd hP (bdEmb hP (pairing m k)) ∈ Z ↔ bdEmb hP (pairing m k) ∈ Δ.bd Z := by
        rw [← ends_innerIdx hP hdp, pole_ends, ← mem_bd_of_dangling hP hZ hdp]
      have hiZ : (join hP m).ends (newHalf (P := Δ.pole W) m k).1 i ∈ Z := hi
      by_cases hbk : bdEmb hP k ∈ Δ.bd Z
      · rw [if_pos hbk] at hfe
        have hnp : bdEmb hP (pairing m k) ∉ Δ.bd Z := fun h ↦ hno k hbk h
        obtain ⟨s0, -⟩ := sw_joinPoleFlip hP m Z hfresh hfe
        rw [newIdx_rep hP m k hk, innerIdxOf_eq hP hdk] at s0
        rw [hfe]
        by_cases hi0 : i = 0
        · subst hi0
          rw [s0, join_ends_newHalf_zero hP m k hk, ← ends_innerIdx hP hdk, pole_ends]
        · have hi1 : i = 1 := by omega
          subst hi1
          rw [join_ends_newHalf_one hP m k hk] at hiZ
          exact absurd (hin_p.mp hiZ) hnp
      · rw [if_neg hbk] at hfe
        obtain ⟨s0, -⟩ := sw_joinPoleFlip hP m Z hfresh hfe
        rw [newIdx_partner hP m k hk, innerIdxOf_eq hP hdp] at s0
        rw [hfe]
        by_cases hi0 : i = 0
        · subst hi0
          rw [join_ends_newHalf_zero hP m k hk] at hiZ
          exact absurd (hin_k.mp hiZ) hbk
        · have hi1 : i = 1 := by omega
          subst hi1
          rw [s0, join_ends_newHalf_one hP m k hk, ← ends_innerIdx hP hdp, pole_ends]

end JoinPole

section FactorTransport

/-- **Isomorphic colourable poles have isomorphic factors.** -/
theorem factorOf_iso_of_pole_iso {Δ₁ Δ₂ : FinGraph} {Z₁ Z₂ : Finset ℕ}
    (f : Iso (Δ₁.pole Z₁) (Δ₂.pole Z₂)) (hP₁ : (Δ₁.pole Z₁).IsPole4)
    (hcol : (Δ₁.pole Z₁).Colourable) {m : Fin 3} (hm : IsoWith hP₁ m ∨ HetWith hP₁ m) :
    Nonempty (Iso (factorOf Δ₁ Z₁) (factorOf Δ₂ Z₂)) := by
  have hP₂ : (Δ₂.pole Z₂).IsPole4 := f.isPole4 hP₁
  have hcol₂ : (Δ₂.pole Z₂).Colourable := f.colourable hcol
  rcases hm with hiso | hhet
  · rw [factorOf_eq_cap hP₁ hcol hiso, factorOf_eq_cap hP₂ hcol₂ (f.isoWith hP₁ hP₂ m hiso)]
    exact ⟨capIso f hP₁ hP₂ m⟩
  · rw [factorOf_eq_join hP₁ hcol hhet, factorOf_eq_join hP₂ hcol₂ (f.hetWith hP₁ hP₂ m hhet)]
    exact ⟨joinIso f hP₁ hP₂ m⟩

end FactorTransport

end FinGraph
end GraphPuzzles
