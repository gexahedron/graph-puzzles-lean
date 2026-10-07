import GraphPuzzles.FinGraph.FinGraphIsoColour

/-!
# Completions of `4`-poles

An isochromatic `4`-pole is completed by the *cap*: two fresh adjacent vertices `u`, `w`, each
attached to the outer ends of one couple of dangling edges.  A heterochromatic `4`-pole is
completed by the *join*: the two dangling edges of each couple are replaced by a single fresh
edge between their inner ends.  Both completions keep all old vertex labels and (for the cap)
all old edge labels.  This file defines the two completions and records their basic structure:
closedness, cubicness, and the edges and cycles inside old vertex sets.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {P : FinGraph}

section Defs

variable (hP : P.IsPole4)

/-- The inner end of a dangling edge (junk for other labels). -/
noncomputable def innerEnd (d : ℕ) : ℕ :=
  if h : d ∈ P.dangling then P.ends d (innerIdx hP h) else 0

/-- The outer end index of a dangling edge. -/
noncomputable def outerIdx (d : ℕ) : Fin 2 :=
  if h : d ∈ P.dangling then Fin.rev (innerIdx hP h) else 0

theorem innerEnd_mem {d : ℕ} (hd : d ∈ P.dangling) : innerEnd hP d ∈ P.Vs := by
  unfold innerEnd
  rw [dif_pos hd]
  exact (innerIdx_spec hP hd).1

theorem ends_innerIdx {d : ℕ} (hd : d ∈ P.dangling) : P.ends d (innerIdx hP hd) = innerEnd hP d := by
  unfold innerEnd
  rw [dif_pos hd]

theorem ends_outerIdx_notMem {d : ℕ} (hd : d ∈ P.dangling) : P.ends d (outerIdx hP d) ∉ P.Vs := by
  unfold outerIdx
  rw [dif_pos hd]
  exact (innerIdx_spec hP hd).2

theorem outerIdx_ne_innerIdx {d : ℕ} (hd : d ∈ P.dangling) : outerIdx hP d ≠ innerIdx hP hd := by
  unfold outerIdx
  rw [dif_pos hd]
  generalize innerIdx hP hd = j
  revert j
  decide

/-- The index of an end of a dangling edge is the inner or the outer index. -/
theorem idx_eq_inner_or_outer {d : ℕ} (hd : d ∈ P.dangling) (i : Fin 2) :
    i = innerIdx hP hd ∨ i = outerIdx hP d := by
  unfold outerIdx
  rw [dif_pos hd]
  by_cases h : i = innerIdx hP hd
  · exact Or.inl h
  · exact Or.inr (fin2_eq_rev_of_ne h)

theorem ends_mem_iff_inner {d : ℕ} (hd : d ∈ P.dangling) (i : Fin 2) :
    P.ends d i ∈ P.Vs ↔ i = innerIdx hP hd := by
  rcases idx_eq_inner_or_outer hP hd i with rfl | rfl
  · simp [(innerIdx_spec hP hd).1]
  · refine ⟨fun h ↦ absurd h (ends_outerIdx_notMem hP hd), fun h ↦ ?_⟩
    exact absurd h (outerIdx_ne_innerIdx hP hd)

/-- A fresh vertex label. -/
def freshV (P : FinGraph) : ℕ := P.Vs.sup id + 1

/-- A fresh edge label. -/
def freshE (P : FinGraph) : ℕ := P.Es.sup id + 1

theorem freshV_notMem : freshV P ∉ P.Vs := by
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  unfold freshV at this
  omega

theorem freshV_succ_notMem : freshV P + 1 ∉ P.Vs := by
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  unfold freshV at this
  omega

theorem freshE_notMem : freshE P ∉ P.Es := by
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  unfold freshE at this
  omega

theorem freshE_succ_notMem : freshE P + 1 ∉ P.Es := by
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  unfold freshE at this
  omega

/-- The second index of the second couple. -/
def other (m : Fin 3) : Fin 4 := if m = 0 then 2 else 1

theorem other_ne_zero (m : Fin 3) : other m ≠ 0 := by
  revert m
  decide

theorem other_ne_pairing_zero (m : Fin 3) : other m ≠ pairing m 0 := by
  revert m
  decide

/-- The four boundary positions are `0`, its partner, `other m`, and its partner. -/
theorem four_positions (m : Fin 3) (i : Fin 4) :
    i = 0 ∨ i = pairing m 0 ∨ i = other m ∨ i = pairing m (other m) := by
  revert m i
  decide

/-- The first couple of boundary edges. -/
noncomputable def couple₁ (m : Fin 3) : Finset ℕ := {bdEmb hP 0, bdEmb hP (pairing m 0)}

/-- The second couple of boundary edges. -/
noncomputable def couple₂ (m : Fin 3) : Finset ℕ :=
  {bdEmb hP (other m), bdEmb hP (pairing m (other m))}

/-- **The cap completion** (isochromatic side): fresh adjacent vertices attached to the outer
ends of the two couples. -/
noncomputable def cap (m : Fin 3) : FinGraph where
  Vs := insert (freshV P) (insert (freshV P + 1) P.Vs)
  Es := insert (freshE P) P.Es
  ends e i :=
    if e = freshE P then (if i = 0 then freshV P else freshV P + 1)
    else if e ∈ P.dangling ∧ P.ends e i ∉ P.Vs then
      (if e ∈ couple₁ hP m then freshV P else freshV P + 1)
    else P.ends e i

/-- **The join completion** (heterochromatic side): each couple of dangling edges is replaced by
a fresh edge between the inner ends. -/
noncomputable def join (m : Fin 3) : FinGraph where
  Vs := P.Vs
  Es := insert (freshE P) (insert (freshE P + 1) (P.Es \ P.dangling))
  ends e i :=
    if e = freshE P then
      (if i = 0 then innerEnd hP (bdEmb hP 0) else innerEnd hP (bdEmb hP (pairing m 0)))
    else if e = freshE P + 1 then
      (if i = 0 then innerEnd hP (bdEmb hP (other m))
        else innerEnd hP (bdEmb hP (pairing m (other m))))
    else P.ends e i

end Defs

section CapLemmas

variable (hP : P.IsPole4) (m : Fin 3)

theorem cap_Vs : (cap hP m).Vs = insert (freshV P) (insert (freshV P + 1) P.Vs) := rfl
theorem cap_Es : (cap hP m).Es = insert (freshE P) P.Es := rfl

theorem cap_ends_old {e : ℕ} (he : e ∈ P.Es) {i : Fin 2} (hi : P.ends e i ∈ P.Vs) :
    (cap hP m).ends e i = P.ends e i := by
  show (if e = freshE P then _ else if e ∈ P.dangling ∧ P.ends e i ∉ P.Vs then _ else _) = _
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ h.2 hi)]

theorem cap_ends_inner {e : ℕ} (he : e ∈ P.Es) {i : Fin 2} (hi : ∀ j, P.ends e j ∈ P.Vs) :
    (cap hP m).ends e i = P.ends e i := cap_ends_old hP m he (hi i)

theorem cap_ends_outer {d : ℕ} (hd : d ∈ P.dangling) :
    (cap hP m).ends d (outerIdx hP d) = if d ∈ couple₁ hP m then freshV P else freshV P + 1 := by
  show (if d = freshE P then _ else if d ∈ P.dangling ∧ _ then _ else _) = _
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ (mem_dangling.mp hd).1)),
    if_pos ⟨hd, ends_outerIdx_notMem hP hd⟩]

theorem cap_ends_new (i : Fin 2) :
    (cap hP m).ends (freshE P) i = if i = 0 then freshV P else freshV P + 1 := by
  show (if freshE P = freshE P then _ else _) = _
  rw [if_pos rfl]

theorem cap_isClosed : (cap hP m).IsClosed := by
  intro e he i
  rw [cap_Es, Finset.mem_insert] at he
  rw [cap_Vs]
  rcases he with rfl | he
  · rw [cap_ends_new]
    split_ifs <;> simp
  · by_cases hi : P.ends e i ∈ P.Vs
    · rw [cap_ends_old hP m he hi]
      simp [hi]
    · have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
      have hio : i = outerIdx hP e := by
        rcases idx_eq_inner_or_outer hP hd i with h | h
        · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
        · exact h
      rw [hio, cap_ends_outer hP m hd]
      split_ifs <;> simp

/-- The edges of the cap inside an old vertex set are the old edges inside it. -/
theorem cap_edgesIn {Y : Finset ℕ} (hY : Y ⊆ P.Vs) : (cap hP m).edgesIn Y = P.edgesIn Y := by
  ext e
  rw [mem_edgesIn, mem_edgesIn, cap_Es, Finset.mem_insert]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | he
    · exfalso
      have := hY (hend 0)
      rw [cap_ends_new] at this
      simp only [if_true] at this
      exact freshV_notMem this
    · refine ⟨he, fun i ↦ ?_⟩
      by_cases hi : P.ends e i ∈ P.Vs
      · have := hend i
        rw [cap_ends_old hP m he hi] at this
        exact this
      · exfalso
        have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        have := hY (hend i)
        rw [hio, cap_ends_outer hP m hd] at this
        split_ifs at this
        · exact freshV_notMem this
        · exact freshV_succ_notMem this
  · rintro ⟨he, hend⟩
    exact ⟨Or.inr he, fun i ↦ by rw [cap_ends_old hP m he (hY (hend i))]; exact hend i⟩

/-- Degrees inside old edge sets agree. -/
theorem cap_degIn {Y F : Finset ℕ} (hY : Y ⊆ P.Vs) (hF : F ⊆ P.edgesIn Y) (v : ℕ) :
    (cap hP m).degIn F v = P.degIn F v := by
  unfold degIn halfEdgesIn
  congr 1
  apply Finset.filter_congr
  intro h hh
  rw [Finset.mem_product] at hh
  have := mem_edgesIn.mp (hF hh.1)
  rw [cap_ends_inner hP m this.1 (fun j ↦ hY (this.2 j))]

theorem cap_hasCycle {Y : Finset ℕ} (hY : Y ⊆ P.Vs) : (cap hP m).HasCycle Y ↔ P.HasCycle Y := by
  unfold HasCycle
  rw [cap_edgesIn hP m hY]
  have hYc : Y ⊆ (cap hP m).Vs := by
    rw [cap_Vs]
    exact hY.trans (Finset.subset_insert _ _ |>.trans (Finset.subset_insert _ _))
  constructor
  · rintro ⟨F, hF, hne, hev⟩
    refine ⟨F, hF, hne, ?_⟩
    rw [isEven_iff_of_subset hY hF]
    rw [isEven_iff_of_subset (Γ := cap hP m) hYc (by rw [cap_edgesIn hP m hY]; exact hF)] at hev
    intro v hv
    rw [← cap_degIn hP m hY hF]
    exact hev v hv
  · rintro ⟨F, hF, hne, hev⟩
    refine ⟨F, hF, hne, ?_⟩
    rw [isEven_iff_of_subset (Γ := cap hP m) hYc (by rw [cap_edgesIn hP m hY]; exact hF)]
    rw [isEven_iff_of_subset hY hF] at hev
    intro v hv
    rw [cap_degIn hP m hY hF]
    exact hev v hv

end CapLemmas

section JoinLemmas

variable (hP : P.IsPole4) (m : Fin 3)

theorem join_Vs : (join hP m).Vs = P.Vs := rfl
theorem join_Es : (join hP m).Es = insert (freshE P) (insert (freshE P + 1) (P.Es \ P.dangling)) :=
  rfl

theorem join_ends_old {e : ℕ} (he : e ∈ P.Es) (i : Fin 2) : (join hP m).ends e i = P.ends e i := by
  show (if e = freshE P then _ else if e = freshE P + 1 then _ else _) = _
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ freshE_succ_notMem (h ▸ he))]

theorem join_ends_new₁ (i : Fin 2) : (join hP m).ends (freshE P) i =
    if i = 0 then innerEnd hP (bdEmb hP 0) else innerEnd hP (bdEmb hP (pairing m 0)) := by
  show (if freshE P = freshE P then _ else _) = _
  rw [if_pos rfl]

theorem join_ends_new₂ (i : Fin 2) : (join hP m).ends (freshE P + 1) i =
    if i = 0 then innerEnd hP (bdEmb hP (other m))
      else innerEnd hP (bdEmb hP (pairing m (other m))) := by
  show (if freshE P + 1 = freshE P then _ else if freshE P + 1 = freshE P + 1 then _ else _) = _
  rw [if_neg (by omega), if_pos rfl]

theorem join_isClosed : (join hP m).IsClosed := by
  intro e he i
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff] at he
  rw [join_Vs]
  rcases he with rfl | rfl | ⟨he, hd⟩
  · rw [join_ends_new₁]
    split_ifs <;> exact innerEnd_mem hP (bdEmb_mem hP _)
  · rw [join_ends_new₂]
    split_ifs <;> exact innerEnd_mem hP (bdEmb_mem hP _)
  · rw [join_ends_old hP m he]
    by_contra h
    exact hd (mem_dangling.mpr ⟨he, i, h⟩)

/-- The edges of the join inside a vertex set avoiding both ends of the new edges are the old
edges inside it. -/
theorem join_edgesIn {Y : Finset ℕ} (hY : Y ⊆ P.Vs)
    (h₁ : ¬ (innerEnd hP (bdEmb hP 0) ∈ Y ∧ innerEnd hP (bdEmb hP (pairing m 0)) ∈ Y))
    (h₂ : ¬ (innerEnd hP (bdEmb hP (other m)) ∈ Y ∧
      innerEnd hP (bdEmb hP (pairing m (other m))) ∈ Y)) :
    (join hP m).edgesIn Y = P.edgesIn Y := by
  ext e
  rw [mem_edgesIn, mem_edgesIn, join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | rfl | ⟨he, hd⟩
    · exfalso
      have h0 := hend 0
      have h1 := hend 1
      rw [join_ends_new₁] at h0 h1
      simp only [if_true, one_ne_zero, if_false] at h0 h1
      exact h₁ ⟨h0, h1⟩
    · exfalso
      have h0 := hend 0
      have h1 := hend 1
      rw [join_ends_new₂] at h0 h1
      simp only [if_true, one_ne_zero, if_false] at h0 h1
      exact h₂ ⟨h0, h1⟩
    · refine ⟨he, fun i ↦ ?_⟩
      have := hend i
      rw [join_ends_old hP m he] at this
      exact this
  · rintro ⟨he, hend⟩
    have hd : e ∉ P.dangling := by
      rw [mem_dangling]
      rintro ⟨-, i, hi⟩
      exact hi (hY (hend i))
    exact ⟨Or.inr (Or.inr ⟨he, hd⟩), fun i ↦ by rw [join_ends_old hP m he]; exact hend i⟩

end JoinLemmas

end FinGraph
end GraphPuzzles
