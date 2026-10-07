import GraphPuzzles.FinGraph.FinGraphCompletion

/-!
# Completions of cubic `4`-poles are cubic

The old vertices keep their three half-edges in both completions.  In the cap the two fresh
vertices each see the two outer ends of a couple and the fresh edge.  In the join the inner
half-edges of the four dangling edges are replaced by the four ends of the two fresh edges.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

section Couples

theorem couple₁_subset_dangling : couple₁ hP m ⊆ P.dangling := by
  intro d hd
  unfold couple₁ at hd
  rw [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> exact bdEmb_mem hP _

theorem couple₂_subset_dangling : couple₂ hP m ⊆ P.dangling := by
  intro d hd
  unfold couple₂ at hd
  rw [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> exact bdEmb_mem hP _

theorem card_couple₁ : (couple₁ hP m).card = 2 := by
  unfold couple₁
  rw [Finset.card_pair]
  intro h
  exact pairing_ne m 0 (bdEmb_injective hP h).symm

theorem card_couple₂ : (couple₂ hP m).card = 2 := by
  unfold couple₂
  rw [Finset.card_pair]
  intro h
  exact pairing_ne m (other m) (bdEmb_injective hP h).symm

theorem mem_couple₂_iff {d : ℕ} (hd : d ∈ P.dangling) : d ∈ couple₂ hP m ↔ d ∉ couple₁ hP m := by
  obtain ⟨i, rfl⟩ := exists_bdEmb_eq hP hd
  unfold couple₁ couple₂
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hinj := bdEmb_injective hP
  constructor
  · rintro (h | h) h'
    · rcases h' with h' | h'
      · exact other_ne_zero m (hinj (h.symm.trans h'))
      · exact other_ne_pairing_zero m (hinj (h.symm.trans h'))
    · rcases h' with h' | h'
      · have := hinj (h.symm.trans h')
        have h2 := congrArg (pairing m) this
        rw [pairing_involutive] at h2
        exact other_ne_pairing_zero m h2
      · have := hinj (h.symm.trans h')
        have h2 := congrArg (pairing m) this
        rw [pairing_involutive, pairing_involutive] at h2
        exact other_ne_zero m h2
  · intro h
    rw [not_or] at h
    rcases four_positions m i with rfl | rfl | rfl | rfl
    · exact absurd rfl h.1
    · exact absurd rfl h.2
    · exact Or.inl rfl
    · exact Or.inr rfl

end Couples

section Cap

theorem cap_halfEdges_old {v : ℕ} (hv : v ∈ P.Vs) :
    (cap hP m).halfEdgesIn (cap hP m).Es v = P.halfEdgesIn P.Es v := by
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, mem_halfEdgesIn, cap_Es, Finset.mem_insert]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | he
    · exfalso
      rw [cap_ends_new] at hend
      split_ifs at hend
      · exact freshV_notMem (hend ▸ hv)
      · exact freshV_succ_notMem (hend ▸ hv)
    · refine ⟨he, ?_⟩
      by_cases hi : P.ends e i ∈ P.Vs
      · rw [cap_ends_old hP m he hi] at hend
        exact hend
      · exfalso
        have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        rw [hio, cap_ends_outer hP m hd] at hend
        split_ifs at hend
        · exact freshV_notMem (hend ▸ hv)
        · exact freshV_succ_notMem (hend ▸ hv)
  · rintro ⟨he, hend⟩
    exact ⟨Or.inr he, by rw [cap_ends_old hP m he (hend ▸ hv)]; exact hend⟩

theorem cap_deg_old {v : ℕ} (hv : v ∈ P.Vs) : (cap hP m).deg v = P.deg v := by
  unfold deg degIn
  rw [cap_halfEdges_old hP m hv]

theorem cap_halfEdges_u :
    (cap hP m).halfEdgesIn (cap hP m).Es (freshV P) =
      insert (freshE P, 0) ((couple₁ hP m).image fun d ↦ (d, outerIdx hP d)) := by
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, cap_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | he
    · rw [cap_ends_new] at hend
      split_ifs at hend with hi
      · exact Or.inl (Prod.ext rfl hi)
      · omega
    · by_cases hi : P.ends e i ∈ P.Vs
      · rw [cap_ends_old hP m he hi] at hend
        exact absurd (hend ▸ hi) freshV_notMem
      · have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        rw [hio, cap_ends_outer hP m hd] at hend
        split_ifs at hend with hc
        · exact Or.inr ⟨e, hc, by rw [hio]⟩
        · omega
  · rintro (h | ⟨d, hd, h⟩)
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Or.inl rfl, by rw [cap_ends_new]; simp⟩
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hdd := couple₁_subset_dangling hP m hd
      exact ⟨Or.inr (mem_dangling.mp hdd).1, by rw [cap_ends_outer hP m hdd, if_pos hd]⟩

theorem cap_halfEdges_w :
    (cap hP m).halfEdgesIn (cap hP m).Es (freshV P + 1) =
      insert (freshE P, 1) ((couple₂ hP m).image fun d ↦ (d, outerIdx hP d)) := by
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, cap_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | he
    · rw [cap_ends_new] at hend
      split_ifs at hend with hi
      · omega
      · have hi' : i ≠ 0 := hi
        have hi1 : i = 1 := by omega
        exact Or.inl (Prod.ext rfl hi1)
    · by_cases hi : P.ends e i ∈ P.Vs
      · rw [cap_ends_old hP m he hi] at hend
        exact absurd (hend ▸ hi) freshV_succ_notMem
      · have hd : e ∈ P.dangling := mem_dangling.mpr ⟨he, i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        rw [hio, cap_ends_outer hP m hd] at hend
        split_ifs at hend with hc
        · omega
        · exact Or.inr ⟨e, (mem_couple₂_iff hP m hd).mpr hc, by rw [hio]⟩
  · rintro (h | ⟨d, hd, h⟩)
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Or.inl rfl, by rw [cap_ends_new]; simp⟩
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hdd := couple₂_subset_dangling hP m hd
      have hc : d ∉ couple₁ hP m := (mem_couple₂_iff hP m hdd).mp hd
      exact ⟨Or.inr (mem_dangling.mp hdd).1, by rw [cap_ends_outer hP m hdd, if_neg hc]⟩

theorem card_couple_image (C : Finset ℕ) :
    (C.image fun d ↦ (d, outerIdx hP d)).card = C.card :=
  Finset.card_image_of_injective _ fun _ _ h ↦ congrArg Prod.fst h

theorem cap_deg_u : (cap hP m).deg (freshV P) = 3 := by
  unfold deg degIn
  rw [cap_halfEdges_u, Finset.card_insert_of_notMem, card_couple_image, card_couple₁]
  rw [Finset.mem_image]
  rintro ⟨d, hd, h⟩
  have h1 : d = freshE P := congrArg Prod.fst h
  exact freshE_notMem (h1 ▸ (mem_dangling.mp (couple₁_subset_dangling hP m hd)).1)

theorem cap_deg_w : (cap hP m).deg (freshV P + 1) = 3 := by
  unfold deg degIn
  rw [cap_halfEdges_w, Finset.card_insert_of_notMem, card_couple_image, card_couple₂]
  rw [Finset.mem_image]
  rintro ⟨d, hd, h⟩
  have h1 : d = freshE P := congrArg Prod.fst h
  exact freshE_notMem (h1 ▸ (mem_dangling.mp (couple₂_subset_dangling hP m hd)).1)

theorem cap_isCubic : (cap hP m).IsCubic := by
  intro v hv
  rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at hv
  rcases hv with rfl | rfl | hv
  · exact cap_deg_u hP m
  · exact cap_deg_w hP m
  · rw [cap_deg_old hP m hv]
    exact hP.cubic v hv

end Cap

section Join

/-- The half-edge of a new join edge attached to boundary position `k`. -/
def newHalf (k : Fin 4) : ℕ × Fin 2 :=
  if k = 0 then (freshE P, 0) else if k = pairing m 0 then (freshE P, 1)
  else if k = other m then (freshE P + 1, 0) else (freshE P + 1, 1)

theorem pairing_other_ne_zero : pairing m (other m) ≠ 0 := by
  intro h
  have := congrArg (pairing m) h
  rw [pairing_involutive] at this
  exact other_ne_pairing_zero m this

theorem pairing_other_ne_pairing_zero : pairing m (other m) ≠ pairing m 0 := by
  intro h
  have := congrArg (pairing m) h
  rw [pairing_involutive, pairing_involutive] at this
  exact other_ne_zero m this

theorem newHalf_zero : newHalf (P := P) m 0 = (freshE P, 0) := by simp [newHalf]

theorem newHalf_pairing_zero : newHalf (P := P) m (pairing m 0) = (freshE P, 1) := by
  unfold newHalf
  rw [if_neg (pairing_ne m 0), if_pos rfl]

theorem newHalf_other : newHalf (P := P) m (other m) = (freshE P + 1, 0) := by
  unfold newHalf
  rw [if_neg (other_ne_zero m), if_neg (other_ne_pairing_zero m), if_pos rfl]

theorem newHalf_pairing_other : newHalf (P := P) m (pairing m (other m)) = (freshE P + 1, 1) := by
  unfold newHalf
  rw [if_neg (pairing_other_ne_zero m), if_neg (pairing_other_ne_pairing_zero m),
    if_neg (pairing_ne m _)]

theorem newHalf_injective : Function.Injective (newHalf (P := P) m) := by
  intro k k' h
  rcases four_positions m k with rfl | rfl | rfl | rfl <;>
    rcases four_positions m k' with rfl | rfl | rfl | rfl <;>
    simp only [newHalf_zero, newHalf_pairing_zero, newHalf_other, newHalf_pairing_other,
      Prod.mk.injEq] at h <;>
    first
    | rfl
    | (exfalso; omega)

theorem join_ends_newHalf (k : Fin 4) :
    (join hP m).ends (newHalf (P := P) m k).1 (newHalf (P := P) m k).2 =
      innerEnd hP (bdEmb hP k) := by
  rcases four_positions m k with rfl | rfl | rfl | rfl
  · rw [newHalf_zero]
    simp [join_ends_new₁]
  · rw [newHalf_pairing_zero]
    simp [join_ends_new₁]
  · rw [newHalf_other]
    simp [join_ends_new₂]
  · rw [newHalf_pairing_other]
    simp [join_ends_new₂]

theorem newHalf_fst_mem (k : Fin 4) : (newHalf (P := P) m k).1 = freshE P ∨
    (newHalf (P := P) m k).1 = freshE P + 1 := by
  unfold newHalf
  split_ifs <;> simp

/-- The half-edges of the join at an old vertex coming from the new edges. -/
theorem join_halfEdges_new (v : ℕ) :
    (join hP m).halfEdgesIn {freshE P, freshE P + 1} v =
      (Finset.univ.filter fun k : Fin 4 ↦ innerEnd hP (bdEmb hP k) = v).image
        (newHalf (P := P) m) := by
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨he, hend⟩
    rcases he with rfl | rfl
    · rw [join_ends_new₁] at hend
      by_cases hi : i = 0
      · subst hi
        refine ⟨0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa using hend
        · rw [newHalf_zero]
      · rw [if_neg hi] at hend
        refine ⟨pairing m 0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hend
        · rw [newHalf_pairing_zero]
          have hi' : i ≠ 0 := hi
          have hi1 : i = 1 := by omega
          rw [hi1]
    · rw [join_ends_new₂] at hend
      by_cases hi : i = 0
      · subst hi
        refine ⟨other m, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa using hend
        · rw [newHalf_other]
      · rw [if_neg hi] at hend
        refine ⟨pairing m (other m), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hend
        · rw [newHalf_pairing_other]
          have hi' : i ≠ 0 := hi
          have hi1 : i = 1 := by omega
          rw [hi1]
  · rintro ⟨k, hk, hke⟩
    rw [Finset.mem_filter] at hk
    rw [← hke]
    refine ⟨newHalf_fst_mem m k, ?_⟩
    rw [join_ends_newHalf hP m k]
    exact hk.2

/-- The inner half-edges of the dangling edges at a vertex. -/
theorem halfEdges_dangling (v : ℕ) (hv : v ∈ P.Vs) :
    P.halfEdgesIn P.dangling v =
      (Finset.univ.filter fun k : Fin 4 ↦ innerEnd hP (bdEmb hP k) = v).image
        fun k ↦ (bdEmb hP k, innerIdx hP (bdEmb_mem hP k)) := by
  ext ⟨e, i⟩
  rw [mem_halfEdgesIn, Finset.mem_image]
  constructor
  · rintro ⟨he, hend⟩
    obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP he
    have hi : i = innerIdx hP he := (ends_mem_iff_inner hP he i).mp (hend ▸ hv)
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ends_innerIdx hP he, ← hi]
      exact hend
    · rw [hi]
  · rintro ⟨k, hk, h⟩
    rw [Finset.mem_filter] at hk
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨bdEmb_mem hP k, by rw [ends_innerIdx]; exact hk.2⟩

theorem join_deg (v : ℕ) (hv : v ∈ P.Vs) : (join hP m).deg v = P.deg v := by
  unfold deg
  have hsplit : (join hP m).Es = {freshE P, freshE P + 1} ∪ (P.Es \ P.dangling) := by
    rw [join_Es]
    ext e
    simp [Finset.mem_insert]
  have hdisj : Disjoint ({freshE P, freshE P + 1} : Finset ℕ) (P.Es \ P.dangling) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_sdiff] at he'
    rcases he with rfl | rfl
    · exact freshE_notMem he'.1
    · exact freshE_succ_notMem he'.1
  rw [hsplit, degIn_union_of_disjoint hdisj]
  have hsplit' : P.Es = P.dangling ∪ (P.Es \ P.dangling) :=
    (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
  conv_rhs => rw [hsplit']
  rw [degIn_union_of_disjoint Finset.disjoint_sdiff]
  congr 1
  · unfold degIn
    rw [join_halfEdges_new, halfEdges_dangling hP v hv,
      Finset.card_image_of_injective _ (newHalf_injective (P := P) m),
      Finset.card_image_of_injective]
    intro k k' h
    exact bdEmb_injective hP (congrArg Prod.fst h)
  · unfold degIn halfEdgesIn
    congr 1
    apply Finset.filter_congr
    intro h hh
    rw [Finset.mem_product, Finset.mem_sdiff] at hh
    rw [join_ends_old hP m hh.1.1]

theorem join_isCubic : (join hP m).IsCubic := by
  intro v hv
  rw [join_Vs] at hv
  rw [join_deg hP m v hv]
  exact hP.cubic v hv

end Join

end FinGraph
end GraphPuzzles
