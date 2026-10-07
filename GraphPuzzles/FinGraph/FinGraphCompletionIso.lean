import GraphPuzzles.FinGraph.FinGraphCompletionCubic

/-!
# Completions transport along isomorphisms of poles

An isomorphism `f` of `4`-poles permutes the boundary positions by `π = f.bdPerm`, and the
pairing `m` of the first pole corresponds to the pairing `conj π m` of the second.  The cap and
join completions of the two poles are then isomorphic: the fresh vertices and edges are matched
according to whether `π` preserves the first couple, and the fresh join edges are flipped
according to the images of their end positions.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {P Q : FinGraph} (f : Iso P Q) (hP : P.IsPole4) (hQ : Q.IsPole4) (m : Fin 3)

/-- The pairing of the second pole. -/
noncomputable abbrev conjPairing : Fin 3 := conj (f.bdPerm hP hQ) m

section Couples

/-- The image of the first couple is one of the two couples of the second pole. -/
theorem image_couple₁ : (couple₁ hP m).image f.fe = couple₁ hQ (conjPairing f hP hQ m) ∨
    (couple₁ hP m).image f.fe = couple₂ hQ (conjPairing f hP hQ m) := by
  set π := f.bdPerm hP hQ with hπ
  have h0 : f.fe (bdEmb hP 0) = bdEmb hQ (π 0) := (f.bdEmb_bdPerm hP hQ 0).symm
  have h1 : f.fe (bdEmb hP (pairing m 0)) = bdEmb hQ (pairing (conj π m) (π 0)) := by
    rw [← f.bdEmb_bdPerm hP hQ, pairing_conj]
  have himg : (couple₁ hP m).image f.fe = {bdEmb hQ (π 0), bdEmb hQ (pairing (conj π m) (π 0))} := by
    unfold couple₁
    rw [Finset.image_insert, Finset.image_singleton, h0, h1]
  rw [himg]
  rcases four_positions (conj π m) (π 0) with h | h | h | h
  · left
    unfold couple₁
    rw [h]
  · left
    unfold couple₁
    rw [h, pairing_involutive, Finset.pair_comm]
  · right
    unfold couple₂
    rw [h]
  · right
    unfold couple₂
    rw [h, pairing_involutive, Finset.pair_comm]

theorem mem_dangling_of_mem_couple₁ {d : ℕ} (hd : d ∈ couple₁ hP m) : d ∈ P.dangling :=
  couple₁_subset_dangling hP m hd

/-- Membership in the first couple of the image, in terms of the source couples. -/
theorem fe_mem_couple₁_iff {d : ℕ} (hd : d ∈ P.dangling) :
    f.fe d ∈ couple₁ hQ (conjPairing f hP hQ m) ↔
      ((couple₁ hP m).image f.fe = couple₁ hQ (conjPairing f hP hQ m) ∧ d ∈ couple₁ hP m) ∨
      ((couple₁ hP m).image f.fe = couple₂ hQ (conjPairing f hP hQ m) ∧ d ∉ couple₁ hP m) := by
  have hfd : f.fe d ∈ Q.dangling := by
    rw [f.dangling_image]
    exact Finset.mem_image_of_mem _ hd
  have hmem : d ∈ couple₁ hP m ↔ f.fe d ∈ (couple₁ hP m).image f.fe := by
    constructor
    · exact Finset.mem_image_of_mem _
    · intro h
      obtain ⟨d', hd', heq⟩ := Finset.mem_image.mp h
      rw [f.fe_inj (mem_dangling.mp (mem_dangling_of_mem_couple₁ hP m hd')).1 (mem_dangling.mp hd).1
        heq] at hd'
      exact hd'
  rcases image_couple₁ f hP hQ m with h | h
  · rw [h] at hmem
    constructor
    · intro h'
      exact Or.inl ⟨h, hmem.mpr h'⟩
    · rintro (⟨-, h'⟩ | ⟨h', -⟩)
      · exact hmem.mp h'
      · exfalso
        -- the two couples are disjoint and both equal the image
        have := h.symm.trans h'
        have h0 : bdEmb hQ 0 ∈ couple₂ hQ (conjPairing f hP hQ m) := by
          rw [← this]
          unfold couple₁
          exact Finset.mem_insert_self _ _
        have h0' := (mem_couple₂_iff hQ _ (bdEmb_mem hQ 0)).mp h0
        exact h0' (Finset.mem_insert_self _ _)
  · rw [h] at hmem
    constructor
    · intro h'
      refine Or.inr ⟨h, fun h'' ↦ ?_⟩
      have := (mem_couple₂_iff hQ _ hfd).mp (hmem.mp h'')
      exact this h'
    · rintro (⟨h', -⟩ | ⟨-, h'⟩)
      · exfalso
        have := h.symm.trans h'
        have h0 : bdEmb hQ 0 ∈ couple₂ hQ (conjPairing f hP hQ m) := by
          rw [this]
          unfold couple₁
          exact Finset.mem_insert_self _ _
        have h0' := (mem_couple₂_iff hQ _ (bdEmb_mem hQ 0)).mp h0
        exact h0' (Finset.mem_insert_self _ _)
      · by_contra hc
        have : f.fe d ∈ couple₂ hQ (conjPairing f hP hQ m) := (mem_couple₂_iff hQ _ hfd).mpr hc
        exact h' (hmem.mpr this)

end Couples

section Cap

attribute [local instance] Classical.propDecidable

/-- Whether the isomorphism preserves the first couple. -/
noncomputable def preserves : Prop :=
  (couple₁ hP m).image f.fe = couple₁ hQ (conjPairing f hP hQ m)

/-- The vertex map of the cap isomorphism. -/
noncomputable def capFv (v : ℕ) : ℕ :=
  if v = freshV P then (if preserves f hP hQ m then freshV Q else freshV Q + 1)
  else if v = freshV P + 1 then (if preserves f hP hQ m then freshV Q + 1 else freshV Q)
  else f.fv v

noncomputable def capGv (v : ℕ) : ℕ :=
  if v = freshV Q then (if preserves f hP hQ m then freshV P else freshV P + 1)
  else if v = freshV Q + 1 then (if preserves f hP hQ m then freshV P + 1 else freshV P)
  else f.gv v

noncomputable def capFe (e : ℕ) : ℕ := if e = freshE P then freshE Q else f.fe e

noncomputable def capGe (e : ℕ) : ℕ := if e = freshE Q then freshE P else f.ge e

noncomputable def capFlip (e : ℕ) : Bool :=
  if e = freshE P then decide (¬ preserves f hP hQ m) else f.flip e

theorem capFv_u : capFv f hP hQ m (freshV P) =
    if preserves f hP hQ m then freshV Q else freshV Q + 1 := by
  unfold capFv
  rw [if_pos rfl]

theorem capFv_w : capFv f hP hQ m (freshV P + 1) =
    if preserves f hP hQ m then freshV Q + 1 else freshV Q := by
  unfold capFv
  rw [if_neg (by omega), if_pos rfl]

theorem capFv_old {v : ℕ} (hv : v ∈ P.Vs) : capFv f hP hQ m v = f.fv v := by
  unfold capFv
  rw [if_neg (fun h ↦ freshV_notMem (h ▸ hv)), if_neg (fun h ↦ freshV_succ_notMem (h ▸ hv))]

theorem capGv_u : capGv f hP hQ m (freshV Q) =
    if preserves f hP hQ m then freshV P else freshV P + 1 := by
  unfold capGv
  rw [if_pos rfl]

theorem capGv_w : capGv f hP hQ m (freshV Q + 1) =
    if preserves f hP hQ m then freshV P + 1 else freshV P := by
  unfold capGv
  rw [if_neg (by omega), if_pos rfl]

theorem capGv_old {v : ℕ} (hv : v ∈ Q.Vs) : capGv f hP hQ m v = f.gv v := by
  unfold capGv
  rw [if_neg (fun h ↦ freshV_notMem (h ▸ hv)), if_neg (fun h ↦ freshV_succ_notMem (h ▸ hv))]

theorem capFe_new : capFe f (freshE P) = freshE Q := by
  unfold capFe
  rw [if_pos rfl]

theorem capFe_old {e : ℕ} (he : e ∈ P.Es) : capFe f e = f.fe e := by
  unfold capFe
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he))]

theorem capGe_new : capGe f (freshE Q) = freshE P := by
  unfold capGe
  rw [if_pos rfl]

theorem capGe_old {e : ℕ} (he : e ∈ Q.Es) : capGe f e = f.ge e := by
  unfold capGe
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he))]

theorem outerIdx_fe {d : ℕ} (hd : d ∈ P.dangling) :
    outerIdx hQ (f.fe d) = sw (f.flip d) (outerIdx hP d) := by
  have hfd : f.fe d ∈ Q.dangling := by
    rw [f.dangling_image]
    exact Finset.mem_image_of_mem _ hd
  have hdE := (mem_dangling.mp hd).1
  rcases idx_eq_inner_or_outer hQ hfd (sw (f.flip d) (outerIdx hP d)) with h | h
  · exfalso
    have : Q.ends (f.fe d) (sw (f.flip d) (outerIdx hP d)) ∈ Q.Vs := by
      rw [h]
      exact (innerIdx_spec hQ hfd).1
    exact ends_outerIdx_notMem hP hd ((f.ends_iff d hdE _).mpr this)
  · exact h.symm

theorem innerIdx_fe {d : ℕ} (hd : d ∈ P.dangling) (hfd : f.fe d ∈ Q.dangling) :
    innerIdx hQ hfd = sw (f.flip d) (innerIdx hP hd) := by
  have hdE := (mem_dangling.mp hd).1
  symm
  rw [← ends_mem_iff_inner hQ hfd, ← f.ends_iff d hdE]
  exact (innerIdx_spec hP hd).1

theorem cap_mem_Vs_cases {v : ℕ} (hv : v ∈ (cap hP m).Vs) :
    v = freshV P ∨ v = freshV P + 1 ∨ v ∈ P.Vs := by
  rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at hv
  exact hv

theorem cap_mem_Es_cases {e : ℕ} (he : e ∈ (cap hP m).Es) : e = freshE P ∨ e ∈ P.Es := by
  rw [cap_Es, Finset.mem_insert] at he
  exact he

theorem mem_cap_Vs_of_old {v : ℕ} (hv : v ∈ P.Vs) : v ∈ (cap hP m).Vs := by
  rw [cap_Vs]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)

theorem freshV_mem_cap : freshV P ∈ (cap hP m).Vs := by
  rw [cap_Vs]
  exact Finset.mem_insert_self _ _

theorem freshV_succ_mem_cap : freshV P + 1 ∈ (cap hP m).Vs := by
  rw [cap_Vs]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- **Caps of isomorphic poles are isomorphic.** -/
noncomputable def capIso : Iso (cap hP m) (cap hQ (conjPairing f hP hQ m)) where
  fv := capFv f hP hQ m
  gv := capGv f hP hQ m
  fe := capFe f
  ge := capGe f
  flip := capFlip f hP hQ m
  fv_mem := by
    intro v hv
    rcases cap_mem_Vs_cases hP m hv with rfl | rfl | hv
    · rw [capFv_u]
      split_ifs
      · exact freshV_mem_cap hQ _
      · exact freshV_succ_mem_cap hQ _
    · rw [capFv_w]
      split_ifs
      · exact freshV_succ_mem_cap hQ _
      · exact freshV_mem_cap hQ _
    · rw [capFv_old f hP hQ m hv]
      exact mem_cap_Vs_of_old hQ _ (f.fv_mem v hv)
  gv_mem := by
    intro v hv
    rcases cap_mem_Vs_cases hQ _ hv with rfl | rfl | hv
    · rw [capGv_u]
      split_ifs
      · exact freshV_mem_cap hP _
      · exact freshV_succ_mem_cap hP _
    · rw [capGv_w]
      split_ifs
      · exact freshV_succ_mem_cap hP _
      · exact freshV_mem_cap hP _
    · rw [capGv_old f hP hQ m hv]
      exact mem_cap_Vs_of_old hP _ (f.gv_mem v hv)
  gv_fv := by
    intro v hv
    rcases cap_mem_Vs_cases hP m hv with rfl | rfl | hv
    · rw [capFv_u]
      by_cases hpres : preserves f hP hQ m
      · rw [if_pos hpres, capGv_u, if_pos hpres]
      · rw [if_neg hpres, capGv_w, if_neg hpres]
    · rw [capFv_w]
      by_cases hpres : preserves f hP hQ m
      · rw [if_pos hpres, capGv_w, if_pos hpres]
      · rw [if_neg hpres, capGv_u, if_neg hpres]
    · rw [capFv_old f hP hQ m hv, capGv_old f hP hQ m (f.fv_mem v hv)]
      exact f.gv_fv v hv
  fv_gv := by
    intro v hv
    rcases cap_mem_Vs_cases hQ _ hv with rfl | rfl | hv
    · rw [capGv_u]
      by_cases hpres : preserves f hP hQ m
      · rw [if_pos hpres, capFv_u, if_pos hpres]
      · rw [if_neg hpres, capFv_w, if_neg hpres]
    · rw [capGv_w]
      by_cases hpres : preserves f hP hQ m
      · rw [if_pos hpres, capFv_w, if_pos hpres]
      · rw [if_neg hpres, capFv_u, if_neg hpres]
    · rw [capGv_old f hP hQ m hv, capFv_old f hP hQ m (f.gv_mem v hv)]
      exact f.fv_gv v hv
  fe_mem := by
    intro e he
    rw [cap_Es, Finset.mem_insert]
    rcases cap_mem_Es_cases hP m he with rfl | he
    · rw [capFe_new]
      exact Or.inl rfl
    · rw [capFe_old f he]
      exact Or.inr (f.fe_mem e he)
  ge_mem := by
    intro e he
    rw [cap_Es, Finset.mem_insert]
    rcases cap_mem_Es_cases hQ _ he with rfl | he
    · rw [capGe_new]
      exact Or.inl rfl
    · rw [capGe_old f he]
      exact Or.inr (f.ge_mem e he)
  ge_fe := by
    intro e he
    rcases cap_mem_Es_cases hP m he with rfl | he
    · rw [capFe_new, capGe_new]
    · rw [capFe_old f he, capGe_old f (f.fe_mem e he)]
      exact f.ge_fe e he
  fe_ge := by
    intro e he
    rcases cap_mem_Es_cases hQ _ he with rfl | he
    · rw [capGe_new, capFe_new]
    · rw [capGe_old f he, capFe_old f (f.ge_mem e he)]
      exact f.fe_ge e he
  ends_iff := by
    intro e he i
    have hcl := cap_isClosed hP m e he i
    have hcl' := cap_isClosed hQ (conjPairing f hP hQ m)
    constructor
    · intro _
      apply hcl'
      rw [cap_Es, Finset.mem_insert]
      rcases cap_mem_Es_cases hP m he with rfl | he
      · rw [capFe_new]
        exact Or.inl rfl
      · rw [capFe_old f he]
        exact Or.inr (f.fe_mem e he)
    · intro _
      exact hcl
  map_ends := by
    intro e he i _
    rcases cap_mem_Es_cases hP m he with rfl | he
    · rw [capFe_new, cap_ends_new, cap_ends_new]
      unfold capFlip
      rw [if_pos rfl]
      by_cases hpres : preserves f hP hQ m
      · have hd : decide (¬ preserves f hP hQ m) = false := by simp [hpres]
        rw [hd]
        simp only [sw, Bool.false_eq_true, if_false]
        by_cases hi : i = 0
        · rw [if_pos hi, if_pos hi, capFv_u, if_pos hpres]
        · rw [if_neg hi, if_neg hi, capFv_w, if_pos hpres]
      · have hd : decide (¬ preserves f hP hQ m) = true := by simp [hpres]
        rw [hd]
        simp only [sw, if_true]
        by_cases hi : i = 0
        · subst hi
          rw [if_pos rfl, Iso.rev_zero', if_neg (by decide), capFv_u, if_neg hpres]
        · have hi1 : i = 1 := by omega
          subst hi1
          rw [if_neg (by decide), Iso.rev_one', if_pos rfl, capFv_w, if_neg hpres]
    · rw [capFe_old f he]
      unfold capFlip
      rw [if_neg (fun h ↦ freshE_notMem (h ▸ he))]
      by_cases hi : P.ends e i ∈ P.Vs
      · rw [cap_ends_old hP m he hi, cap_ends_old hQ _ (f.fe_mem e he)
          ((f.ends_iff e he i).mp hi), capFv_old f hP hQ m hi]
        exact f.map_ends e he i hi
      · have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        have hfd : f.fe e ∈ Q.dangling := by
          rw [f.dangling_image]
          exact Finset.mem_image_of_mem _ hd
        rw [hio, cap_ends_outer hP m hd, ← outerIdx_fe f hP hQ hd, cap_ends_outer hQ _ hfd]
        have hiff := fe_mem_couple₁_iff f hP hQ m hd
        have hdisj : ¬ ((couple₁ hP m).image f.fe = couple₁ hQ (conjPairing f hP hQ m) ∧
            (couple₁ hP m).image f.fe = couple₂ hQ (conjPairing f hP hQ m)) := by
          rintro ⟨h1, h2⟩
          have := h1.symm.trans h2
          have h0 : bdEmb hQ 0 ∈ couple₂ hQ (conjPairing f hP hQ m) := by
            rw [← this]
            unfold couple₁
            exact Finset.mem_insert_self _ _
          exact (mem_couple₂_iff hQ _ (bdEmb_mem hQ 0)).mp h0 (Finset.mem_insert_self _ _)
        by_cases hpres : preserves f hP hQ m
        · have hpres' := hpres
          unfold preserves at hpres'
          by_cases hc : e ∈ couple₁ hP m
          · rw [if_pos hc, capFv_u, if_pos hpres, if_pos (hiff.mpr (Or.inl ⟨hpres', hc⟩))]
          · rw [if_neg hc, capFv_w, if_pos hpres, if_neg]
            intro h
            rcases hiff.mp h with ⟨-, h⟩ | ⟨h, -⟩
            · exact hc h
            · exact hdisj ⟨hpres', h⟩
        · have hpres' : (couple₁ hP m).image f.fe = couple₂ hQ (conjPairing f hP hQ m) :=
            (image_couple₁ f hP hQ m).resolve_left hpres
          by_cases hc : e ∈ couple₁ hP m
          · rw [if_pos hc, capFv_u, if_neg hpres, if_neg]
            intro h
            rcases hiff.mp h with ⟨h, -⟩ | ⟨-, h⟩
            · exact hpres h
            · exact h hc
          · rw [if_neg hc, capFv_w, if_neg hpres, if_pos (hiff.mpr (Or.inr ⟨hpres', hc⟩))]

end Cap

section Join

attribute [local instance] Classical.propDecidable

theorem fv_innerEnd {d : ℕ} (hd : d ∈ P.dangling) :
    f.fv (innerEnd hP d) = innerEnd hQ (f.fe d) := by
  have hfd : f.fe d ∈ Q.dangling := by
    rw [f.dangling_image]
    exact Finset.mem_image_of_mem _ hd
  rw [← ends_innerIdx hP hd, ← ends_innerIdx hQ hfd, innerIdx_fe f hP hQ hd hfd]
  exact f.map_ends d (mem_dangling.mp hd).1 _ (innerIdx_spec hP hd).1

theorem fe_bdEmb (k : Fin 4) : f.fe (bdEmb hP k) = bdEmb hQ (f.bdPerm hP hQ k) :=
  (f.bdEmb_bdPerm hP hQ k).symm

/-- The partner position has the same new edge and the opposite end. -/
theorem newHalf_pairing (m' : Fin 3) (j : Fin 4) :
    (newHalf (P := Q) m' (pairing m' j)).1 = (newHalf (P := Q) m' j).1 ∧
      (newHalf (P := Q) m' (pairing m' j)).2 = Fin.rev (newHalf (P := Q) m' j).2 := by
  rcases four_positions m' j with rfl | rfl | rfl | rfl
  · rw [newHalf_zero, newHalf_pairing_zero]
    exact ⟨rfl, Iso.rev_zero'.symm⟩
  · rw [pairing_involutive, newHalf_zero, newHalf_pairing_zero]
    exact ⟨rfl, Iso.rev_one'.symm⟩
  · rw [newHalf_other, newHalf_pairing_other]
    exact ⟨rfl, Iso.rev_zero'.symm⟩
  · rw [pairing_involutive, newHalf_other, newHalf_pairing_other]
    exact ⟨rfl, Iso.rev_one'.symm⟩

theorem newHalf_snd_cases (m' : Fin 3) (j : Fin 4) :
    (newHalf (P := Q) m' j).2 = 0 ∨ (newHalf (P := Q) m' j).2 = 1 := by
  rcases four_positions m' j with rfl | rfl | rfl | rfl
  · rw [newHalf_zero]; exact Or.inl rfl
  · rw [newHalf_pairing_zero]; exact Or.inr rfl
  · rw [newHalf_other]; exact Or.inl rfl
  · rw [newHalf_pairing_other]; exact Or.inr rfl

theorem newHalf_fst_mem_join (m' : Fin 3) (j : Fin 4) :
    (newHalf (P := Q) m' j).1 ∈ (join hQ m').Es := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert]
  rcases newHalf_fst_mem (P := Q) m' j with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The edge map of the join isomorphism. -/
noncomputable def joinFe (e : ℕ) : ℕ :=
  if e = freshE P then (newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ 0)).1
  else if e = freshE P + 1 then
    (newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ (other m))).1
  else f.fe e

/-- The inverse edge map. -/
noncomputable def joinGe (e : ℕ) : ℕ :=
  if e = freshE Q then (newHalf (P := P) m ((f.bdPerm hP hQ).symm 0)).1
  else if e = freshE Q + 1 then
    (newHalf (P := P) m ((f.bdPerm hP hQ).symm (other (conjPairing f hP hQ m)))).1
  else f.ge e

noncomputable def joinFlip (e : ℕ) : Bool :=
  if e = freshE P then
    decide ((newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ 0)).2 = 1)
  else if e = freshE P + 1 then
    decide ((newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ (other m))).2 = 1)
  else f.flip e

/-- The new half-edge at a position, as an element of the join. -/
theorem joinFe_newHalf (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    joinFe f hP hQ m (newHalf (P := P) m k).1 =
      (newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ k)).1 := by
  unfold joinFe
  rcases hk with rfl | rfl
  · rw [newHalf_zero]
    simp only [if_true]
  · rw [newHalf_other]
    rw [if_neg (by omega), if_pos rfl]

theorem sw_joinFlip (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    sw (joinFlip f hP hQ m (newHalf (P := P) m k).1) 0 =
      (newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ k)).2 := by
  unfold joinFlip
  rcases hk with rfl | rfl
  · rw [newHalf_zero]
    simp only [if_true]
    rcases newHalf_snd_cases (Q := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ 0) with h | h
    · rw [h]
      simp [sw]
    · rw [h]
      simp [sw]
  · rw [newHalf_other]
    rw [if_neg (by omega), if_pos rfl]
    rcases newHalf_snd_cases (Q := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ (other m)) with h | h
    · rw [h]
      simp [sw]
    · rw [h]
      simp [sw]

theorem sw_joinFlip_one (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    sw (joinFlip f hP hQ m (newHalf (P := P) m k).1) 1 =
      (newHalf (P := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ (pairing m k))).2 := by
  have h1 := sw_joinFlip f hP hQ m k hk
  have h2 := (newHalf_pairing (Q := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ k)).2
  have hpc : pairing (conjPairing f hP hQ m) (f.bdPerm hP hQ k) = f.bdPerm hP hQ (pairing m k) :=
    pairing_conj _ _ _
  rw [hpc] at h2
  rw [h2, ← h1]
  cases joinFlip f hP hQ m (newHalf (P := P) m k).1 <;> simp [sw]

/-- The new edges of the join of `P` correspond to the new edges of the join of `Q`. -/
theorem join_ends_transport (k : Fin 4) (hk : k = 0 ∨ k = other m) (i : Fin 2) :
    f.fv ((join hP m).ends (newHalf (P := P) m k).1 i) =
      (join hQ (conjPairing f hP hQ m)).ends (joinFe f hP hQ m (newHalf (P := P) m k).1)
        (sw (joinFlip f hP hQ m (newHalf (P := P) m k).1) i) := by
  rw [joinFe_newHalf f hP hQ m k hk]
  by_cases hi : i = 0
  · subst hi
    rw [sw_joinFlip f hP hQ m k hk, join_ends_newHalf hQ, ← fe_bdEmb, ← fv_innerEnd f hP hQ
      (bdEmb_mem hP k)]
    congr 1
    have := join_ends_newHalf hP m k
    have hk0 : (newHalf (P := P) m k).2 = 0 := by
      rcases hk with rfl | rfl
      · rw [newHalf_zero]
      · rw [newHalf_other]
    rw [hk0] at this
    exact this
  · have hi1 : i = 1 := by omega
    subst hi1
    have hpc : pairing (conjPairing f hP hQ m) (f.bdPerm hP hQ k) =
        f.bdPerm hP hQ (pairing m k) := pairing_conj _ _ _
    have e1 := (newHalf_pairing (Q := Q) (conjPairing f hP hQ m) (f.bdPerm hP hQ k)).1
    rw [hpc] at e1
    rw [sw_joinFlip_one f hP hQ m k hk, ← e1, join_ends_newHalf hQ, ← fe_bdEmb f hP hQ,
      ← fv_innerEnd f hP hQ (bdEmb_mem hP _)]
    congr 1
    have := join_ends_newHalf hP m (pairing m k)
    have hk1 : (newHalf (P := P) m (pairing m k)).1 = (newHalf (P := P) m k).1 :=
      (newHalf_pairing (Q := P) m k).1
    have hk2 : (newHalf (P := P) m (pairing m k)).2 = 1 := by
      rw [(newHalf_pairing (Q := P) m k).2]
      rcases hk with rfl | rfl
      · rw [newHalf_zero]; exact Iso.rev_zero'
      · rw [newHalf_other]; exact Iso.rev_zero'
    rw [hk1, hk2] at this
    exact this

theorem join_mem_Es_cases {e : ℕ} (he : e ∈ (join hP m).Es) :
    e = freshE P ∨ e = freshE P + 1 ∨ (e ∈ P.Es ∧ e ∉ P.dangling) := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff] at he
  exact he

theorem joinFe_old {e : ℕ} (he : e ∈ P.Es) : joinFe f hP hQ m e = f.fe e := by
  unfold joinFe
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ freshE_succ_notMem (h ▸ he))]

theorem joinGe_old {e : ℕ} (he : e ∈ Q.Es) : joinGe f hP hQ m e = f.ge e := by
  unfold joinGe
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ freshE_succ_notMem (h ▸ he))]

theorem joinFlip_old {e : ℕ} (he : e ∈ P.Es) : joinFlip f hP hQ m e = f.flip e := by
  unfold joinFlip
  rw [if_neg (fun h ↦ freshE_notMem (h ▸ he)), if_neg (fun h ↦ freshE_succ_notMem (h ▸ he))]

theorem fe_notMem_dangling {e : ℕ} (he : e ∈ P.Es) (hd : e ∉ P.dangling) :
    f.fe e ∉ Q.dangling := by
  rw [f.dangling_image]
  intro h
  obtain ⟨e', he', heq⟩ := Finset.mem_image.mp h
  rw [f.fe_inj (mem_dangling.mp he').1 he heq] at he'
  exact hd he'

theorem ge_notMem_dangling {e : ℕ} (he : e ∈ Q.Es) (hd : e ∉ Q.dangling) :
    f.ge e ∉ P.dangling := by
  intro h
  apply hd
  rw [f.dangling_image]
  rw [← f.fe_ge e he]
  exact Finset.mem_image_of_mem _ h

theorem joinGe_new (j : Fin 4) (hj : j = 0 ∨ j = other (conjPairing f hP hQ m)) :
    joinGe f hP hQ m (newHalf (P := Q) (conjPairing f hP hQ m) j).1 =
      (newHalf (P := P) m ((f.bdPerm hP hQ).symm j)).1 := by
  unfold joinGe
  rcases hj with rfl | rfl
  · rw [newHalf_zero]
    simp only [if_true]
  · rw [newHalf_other]
    rw [if_neg (by omega), if_pos rfl]

/-- Every position lies in the couple of `0` or in the couple of `other m`. -/
theorem exists_rep (m : Fin 3) (k₀ : Fin 4) :
    ∃ k, (k = 0 ∨ k = other m) ∧ (k₀ = k ∨ k₀ = pairing m k) := by
  rcases four_positions m k₀ with h | h | h | h
  · exact ⟨0, Or.inl rfl, Or.inl h⟩
  · exact ⟨0, Or.inl rfl, Or.inr h⟩
  · exact ⟨other m, Or.inr rfl, Or.inl h⟩
  · exact ⟨other m, Or.inr rfl, Or.inr h⟩

theorem newHalf_fst_rep {P' : FinGraph} (m : Fin 3) {k₀ k : Fin 4} (h : k₀ = k ∨ k₀ = pairing m k) :
    (newHalf (P := P') m k₀).1 = (newHalf (P := P') m k).1 := by
  rcases h with rfl | rfl
  · rfl
  · exact (newHalf_pairing (Q := P') m k).1

theorem joinGe_joinFe_new (k : Fin 4) (hk : k = 0 ∨ k = other m) :
    joinGe f hP hQ m (joinFe f hP hQ m (newHalf (P := P) m k).1) = (newHalf (P := P) m k).1 := by
  rw [joinFe_newHalf f hP hQ m k hk]
  obtain ⟨j, hj, hj₀⟩ := exists_rep (conjPairing f hP hQ m) (f.bdPerm hP hQ k)
  rw [newHalf_fst_rep _ hj₀, joinGe_new f hP hQ m j hj]
  rcases hj₀ with h | h
  · rw [← h, Equiv.symm_apply_apply]
  · have h' : (f.bdPerm hP hQ).symm j = pairing m k := by
      have := congrArg (pairing (conjPairing f hP hQ m)) h
      rw [pairing_involutive, pairing_conj] at this
      rw [← this, Equiv.symm_apply_apply]
    rw [h']
    exact (newHalf_pairing (Q := P) m k).1

theorem joinFe_joinGe_new (j : Fin 4) (hj : j = 0 ∨ j = other (conjPairing f hP hQ m)) :
    joinFe f hP hQ m (joinGe f hP hQ m (newHalf (P := Q) (conjPairing f hP hQ m) j).1) =
      (newHalf (P := Q) (conjPairing f hP hQ m) j).1 := by
  rw [joinGe_new f hP hQ m j hj]
  obtain ⟨k, hk, hk₀⟩ := exists_rep m ((f.bdPerm hP hQ).symm j)
  rw [newHalf_fst_rep _ hk₀, joinFe_newHalf f hP hQ m k hk]
  rcases hk₀ with h | h
  · rw [← h, Equiv.apply_symm_apply]
  · have h' : f.bdPerm hP hQ k = pairing (conjPairing f hP hQ m) j := by
      have := congrArg (f.bdPerm hP hQ) h
      rw [Equiv.apply_symm_apply, ← pairing_conj] at this
      have := congrArg (pairing (conjPairing f hP hQ m)) this
      rw [pairing_involutive] at this
      exact this.symm
    rw [h']
    exact (newHalf_pairing (Q := Q) (conjPairing f hP hQ m) j).1

theorem newHalf_zero_fst {P' : FinGraph} (m : Fin 3) : (newHalf (P := P') m 0).1 = freshE P' := by
  rw [newHalf_zero]

theorem newHalf_other_fst {P' : FinGraph} (m : Fin 3) :
    (newHalf (P := P') m (other m)).1 = freshE P' + 1 := by
  rw [newHalf_other]

theorem mem_join_Es_of_old {e : ℕ} (he : e ∈ P.Es) (hd : e ∉ P.dangling) : e ∈ (join hP m).Es := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
  exact Or.inr (Or.inr ⟨he, hd⟩)

/-- **Joins of isomorphic poles are isomorphic.** -/
noncomputable def joinIso : Iso (join hP m) (join hQ (conjPairing f hP hQ m)) where
  fv := f.fv
  gv := f.gv
  fe := joinFe f hP hQ m
  ge := joinGe f hP hQ m
  flip := joinFlip f hP hQ m
  fv_mem := f.fv_mem
  gv_mem := f.gv_mem
  gv_fv := f.gv_fv
  fv_gv := f.fv_gv
  fe_mem := by
    intro e he
    rcases join_mem_Es_cases hP m he with rfl | rfl | ⟨he, hd⟩
    · rw [← newHalf_zero_fst m, joinFe_newHalf f hP hQ m 0 (Or.inl rfl)]
      exact newHalf_fst_mem_join hQ _ _
    · rw [← newHalf_other_fst m, joinFe_newHalf f hP hQ m (other m) (Or.inr rfl)]
      exact newHalf_fst_mem_join hQ _ _
    · rw [joinFe_old f hP hQ m he]
      exact mem_join_Es_of_old hQ _ (f.fe_mem e he) (fe_notMem_dangling f he hd)
  ge_mem := by
    intro e he
    rcases join_mem_Es_cases hQ _ he with rfl | rfl | ⟨he, hd⟩
    · rw [← newHalf_zero_fst (conjPairing f hP hQ m), joinGe_new f hP hQ m 0 (Or.inl rfl)]
      exact newHalf_fst_mem_join hP _ _
    · rw [← newHalf_other_fst (conjPairing f hP hQ m),
        joinGe_new f hP hQ m (other _) (Or.inr rfl)]
      exact newHalf_fst_mem_join hP _ _
    · rw [joinGe_old f hP hQ m he]
      exact mem_join_Es_of_old hP _ (f.ge_mem e he) (ge_notMem_dangling f he hd)
  ge_fe := by
    intro e he
    rcases join_mem_Es_cases hP m he with rfl | rfl | ⟨he, hd⟩
    · rw [← newHalf_zero_fst m]
      exact joinGe_joinFe_new f hP hQ m 0 (Or.inl rfl)
    · rw [← newHalf_other_fst m]
      exact joinGe_joinFe_new f hP hQ m (other m) (Or.inr rfl)
    · rw [joinFe_old f hP hQ m he, joinGe_old f hP hQ m (f.fe_mem e he)]
      exact f.ge_fe e he
  fe_ge := by
    intro e he
    rcases join_mem_Es_cases hQ _ he with rfl | rfl | ⟨he, hd⟩
    · rw [← newHalf_zero_fst (conjPairing f hP hQ m)]
      exact joinFe_joinGe_new f hP hQ m 0 (Or.inl rfl)
    · rw [← newHalf_other_fst (conjPairing f hP hQ m)]
      exact joinFe_joinGe_new f hP hQ m (other _) (Or.inr rfl)
    · rw [joinGe_old f hP hQ m he, joinFe_old f hP hQ m (f.ge_mem e he)]
      exact f.fe_ge e he
  ends_iff := by
    intro e he i
    have hcl := join_isClosed hP m e he i
    have hcl' := join_isClosed hQ (conjPairing f hP hQ m)
    constructor
    · intro _
      apply hcl'
      rcases join_mem_Es_cases hP m he with rfl | rfl | ⟨he, hd⟩
      · rw [← newHalf_zero_fst m, joinFe_newHalf f hP hQ m 0 (Or.inl rfl)]
        exact newHalf_fst_mem_join hQ _ _
      · rw [← newHalf_other_fst m, joinFe_newHalf f hP hQ m (other m) (Or.inr rfl)]
        exact newHalf_fst_mem_join hQ _ _
      · rw [joinFe_old f hP hQ m he]
        exact mem_join_Es_of_old hQ _ (f.fe_mem e he) (fe_notMem_dangling f he hd)
    · intro _
      exact hcl
  map_ends := by
    intro e he i _
    rcases join_mem_Es_cases hP m he with rfl | rfl | ⟨he, hd⟩
    · rw [← newHalf_zero_fst m]
      exact join_ends_transport f hP hQ m 0 (Or.inl rfl) i
    · rw [← newHalf_other_fst m]
      exact join_ends_transport f hP hQ m (other m) (Or.inr rfl) i
    · rw [joinFe_old f hP hQ m he, joinFlip_old f hP hQ m he, join_ends_old hP m he,
        join_ends_old hQ _ (f.fe_mem e he)]
      apply f.map_ends e he i
      by_contra h
      exact hd (mem_dangling.mpr ⟨he, i, h⟩)

end Join

end FinGraph
end GraphPuzzles
