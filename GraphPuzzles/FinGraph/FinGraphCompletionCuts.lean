import GraphPuzzles.Factorization.FactorCuts

/-!
# Cuts and cycles inside completions

For a pole `pole Γ Y` of a closed graph and its cap or join completion, this file computes the
boundaries of old vertex sets and of old vertex sets extended by a fresh cap vertex, and shows
that cycles of `Γ` inside `Y` persist in the completions.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} {Y : Finset ℕ} (hP : (Γ.pole Y).IsPole4) (m : Fin 3)

section Cap

/-- Old edges of the cap at an old vertex set are the edges of `Γ` there. -/
theorem cap_bd_old (_hcl : Γ.IsClosed) (_hY : Y ⊆ Γ.Vs) {Z : Finset ℕ} (hZ : Z ⊆ Y) :
    (cap hP m).bd Z = Γ.bd Z := by
  ext e
  rw [mem_bd, mem_bd, cap_Es, Finset.mem_insert]
  constructor
  · rintro ⟨he, hiff⟩
    rcases he with rfl | he
    · exfalso
      apply hiff
      have h0 : (cap hP m).ends (freshE (Γ.pole Y)) 0 = freshV (Γ.pole Y) := by
        rw [cap_ends_new]; simp
      have h1 : (cap hP m).ends (freshE (Γ.pole Y)) 1 = freshV (Γ.pole Y) + 1 := by
        rw [cap_ends_new]; simp
      rw [h0, h1]
      constructor
      · intro h; exact absurd (hZ h) freshV_notMem
      · intro h; exact absurd (hZ h) freshV_succ_notMem
    · have heΓ : e ∈ Γ.Es := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.elim (fun h ↦ edgesIn_subset Y h) (fun h ↦ bd_subset Y h)
      refine ⟨heΓ, fun h ↦ hiff ?_⟩
      -- the ends of `e` in `Z` are inner ends of the pole, so unchanged
      have key : ∀ i, (cap hP m).ends e i ∈ Z ↔ Γ.ends e i ∈ Z := by
        intro i
        by_cases hi : Γ.ends e i ∈ Y
        · rw [cap_ends_old hP m he hi, pole_ends]
        · have hd : e ∈ (Γ.pole Y).dangling := mem_dangling.mpr ⟨he, i, hi⟩
          have hio : i = outerIdx hP e := by
            rcases idx_eq_inner_or_outer hP hd i with h | h
            · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
            · exact h
          rw [hio, cap_ends_outer hP m hd]
          constructor
          · intro h'
            split_ifs at h'
            · exact absurd (hZ h') freshV_notMem
            · exact absurd (hZ h') freshV_succ_notMem
          · intro h'
            exact absurd (hZ h') (hio ▸ hi)
      rw [key 0, key 1]
      exact h
  · rintro ⟨he, hiff⟩
    have he' : e ∈ (Γ.pole Y).Es := by
      rw [pole_Es, Finset.mem_union]
      obtain ⟨i, hi, _⟩ := bd_side (mem_bd.mpr ⟨he, hiff⟩)
      exact mem_edgesIn_or_bd he (hZ hi)
    refine ⟨Or.inr he', fun h ↦ hiff ?_⟩
    have key : ∀ i, (cap hP m).ends e i ∈ Z ↔ Γ.ends e i ∈ Z := by
      intro i
      by_cases hi : Γ.ends e i ∈ Y
      · rw [cap_ends_old hP m he' hi, pole_ends]
      · have hd : e ∈ (Γ.pole Y).dangling := mem_dangling.mpr ⟨he', i, hi⟩
        have hio : i = outerIdx hP e := by
          rcases idx_eq_inner_or_outer hP hd i with h | h
          · exact absurd (h ▸ (innerIdx_spec hP hd).1) hi
          · exact h
        rw [hio, cap_ends_outer hP m hd]
        constructor
        · intro h'
          split_ifs at h'
          · exact absurd (hZ h') freshV_notMem
          · exact absurd (hZ h') freshV_succ_notMem
        · intro h'
          exact absurd (hZ h') (hio ▸ hi)
    rw [← key 0, ← key 1]
    exact h

/-- The inner and outer indices of a dangling edge are `0, 1` in some order. -/
theorem dangling_idx_cases {e : ℕ} (hd : e ∈ (Γ.pole Y).dangling) :
    (innerIdx hP hd = 0 ∧ outerIdx hP e = 1) ∨ (innerIdx hP hd = 1 ∧ outerIdx hP e = 0) := by
  have h : outerIdx hP e = Fin.rev (innerIdx hP hd) := by
    unfold outerIdx
    rw [dif_pos hd]
  have hi : innerIdx hP hd = 0 ∨ innerIdx hP hd = 1 := by omega
  rcases hi with hi | hi
  · left
    rw [h, hi]
    exact ⟨rfl, Iso.rev_zero'⟩
  · right
    rw [h, hi]
    exact ⟨rfl, Iso.rev_one'⟩

/-- The two ends of a dangling edge in the cap. -/
theorem cap_ends_dangling {e : ℕ} (hd : e ∈ (Γ.pole Y).dangling) :
    (cap hP m).ends e (innerIdx hP hd) = Γ.ends e (innerIdx hP hd) ∧
      (cap hP m).ends e (Fin.rev (innerIdx hP hd)) =
        (if e ∈ couple₁ hP m then freshV (Γ.pole Y) else freshV (Γ.pole Y) + 1) ∧
      Γ.ends e (innerIdx hP hd) ∈ Y ∧ Γ.ends e (Fin.rev (innerIdx hP hd)) ∉ Y := by
  have he := (mem_dangling.mp hd).1
  refine ⟨cap_ends_old hP m he (innerIdx_spec hP hd).1, ?_, (innerIdx_spec hP hd).1,
    (innerIdx_spec hP hd).2⟩
  have hout : outerIdx hP e = Fin.rev (innerIdx hP hd) := by
    unfold outerIdx
    rw [dif_pos hd]
  rw [← hout]
  exact cap_ends_outer hP m hd

/-- Membership of a dangling edge of the pole in the boundary of a subset of `Y`. -/
theorem mem_bd_of_dangling {Z : Finset ℕ} (hZ : Z ⊆ Y) {e : ℕ} (hd : e ∈ (Γ.pole Y).dangling) :
    e ∈ Γ.bd Z ↔ Γ.ends e (innerIdx hP hd) ∈ Z := by
  have heΓ := bd_subset Y (dangling_pole Y ▸ hd)
  have hout' : Γ.ends e (Fin.rev (innerIdx hP hd)) ∉ Z := fun h ↦ (innerIdx_spec hP hd).2 (hZ h)
  rw [mem_bd]
  rcases dangling_idx_cases hP hd with ⟨hi, -⟩ | ⟨hi, -⟩
  · rw [hi] at hout' ⊢
    rw [Iso.rev_zero'] at hout'
    constructor
    · rintro ⟨-, h⟩
      by_contra hc
      exact h ⟨fun h ↦ (hc h).elim, fun h ↦ (hout' h).elim⟩
    · intro hc
      exact ⟨heΓ, fun h ↦ hout' (h.mp hc)⟩
  · rw [hi] at hout' ⊢
    rw [Iso.rev_one'] at hout'
    constructor
    · rintro ⟨-, h⟩
      by_contra hc
      exact h ⟨fun h ↦ (hout' h).elim, fun h ↦ (hc h).elim⟩
    · intro hc
      exact ⟨heΓ, fun h ↦ hout' (h.mpr hc)⟩

/-- The boundary of an old vertex set together with the first fresh vertex: the first couple's
edges attached inside become internal, those attached outside become boundary, and the fresh
edge is a boundary edge. -/
theorem cap_bd_insert_u (_hcl : Γ.IsClosed) (_hY : Y ⊆ Γ.Vs) {Z : Finset ℕ} (hZ : Z ⊆ Y) :
    (cap hP m).bd (insert (freshV (Γ.pole Y)) Z) =
      insert (freshE (Γ.pole Y))
        ((Γ.bd Z \ couple₁ hP m) ∪ (couple₁ hP m \ Γ.bd Z)) := by
  ext e
  rw [mem_bd]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, cap_Es]
  have hu : freshV (Γ.pole Y) ∉ Z := fun h ↦ freshV_notMem (hZ h)
  have hw : freshV (Γ.pole Y) + 1 ∉ Z := fun h ↦ freshV_succ_notMem (hZ h)
  have hwu : freshV (Γ.pole Y) + 1 ≠ freshV (Γ.pole Y) := by omega
  -- the two kinds of old edges
  have key_d : ∀ (hd : e ∈ (Γ.pole Y).dangling),
      (¬ (((cap hP m).ends e 0 = freshV (Γ.pole Y) ∨ (cap hP m).ends e 0 ∈ Z) ↔
        ((cap hP m).ends e 1 = freshV (Γ.pole Y) ∨ (cap hP m).ends e 1 ∈ Z))) ↔
      (e ∈ couple₁ hP m ↔ Γ.ends e (innerIdx hP hd) ∉ Z) := by
    intro hd
    obtain ⟨h1, h2, hi, -⟩ := cap_ends_dangling hP m hd
    have hZu : Γ.ends e (innerIdx hP hd) ≠ freshV (Γ.pole Y) := fun h ↦ freshV_notMem (h ▸ hi)
    rcases dangling_idx_cases hP hd with ⟨hii, -⟩ | ⟨hii, -⟩
    · rw [hii] at h1 h2 hZu ⊢
      rw [Iso.rev_zero'] at h2
      rw [h1, h2]
      by_cases hc : e ∈ couple₁ hP m
      · rw [if_pos hc]
        simp only [hc, hZu, true_iff, true_or, false_or]
        tauto
      · rw [if_neg hc]
        simp only [hc, hZu, false_or, false_iff, hw, hwu]
        tauto
    · rw [hii] at h1 h2 hZu ⊢
      rw [Iso.rev_one'] at h2
      rw [h1, h2]
      by_cases hc : e ∈ couple₁ hP m
      · rw [if_pos hc]
        simp only [hc, hZu, true_iff, true_or, false_or]
      · rw [if_neg hc]
        simp only [hc, hZu, false_or, false_iff, hw, hwu]
  have key_i : ∀ (he : e ∈ (Γ.pole Y).Es), e ∉ (Γ.pole Y).dangling →
      ((¬ (((cap hP m).ends e 0 = freshV (Γ.pole Y) ∨ (cap hP m).ends e 0 ∈ Z) ↔
        ((cap hP m).ends e 1 = freshV (Γ.pole Y) ∨ (cap hP m).ends e 1 ∈ Z))) ↔
      ¬ (Γ.ends e 0 ∈ Z ↔ Γ.ends e 1 ∈ Z)) := by
    intro he hd
    have hin : ∀ i, Γ.ends e i ∈ Y := by
      intro i
      by_contra h
      exact hd (mem_dangling.mpr ⟨he, i, h⟩)
    rw [cap_ends_inner hP m he hin, cap_ends_inner hP m he hin]
    have h0 : (Γ.pole Y).ends e 0 ≠ freshV (Γ.pole Y) := fun h' ↦ freshV_notMem (h' ▸ hin 0)
    have h1 : (Γ.pole Y).ends e 1 ≠ freshV (Γ.pole Y) := fun h' ↦ freshV_notMem (h' ▸ hin 1)
    simp only [h0, h1, false_or]
    rfl
  constructor
  · rintro ⟨he, hiff⟩
    rcases he with rfl | he
    · exact Or.inl rfl
    · right
      by_cases hd : e ∈ (Γ.pole Y).dangling
      · have h := (key_d hd).mp hiff
        by_cases hc : e ∈ couple₁ hP m
        · exact Or.inr ⟨hc, fun hb ↦ (h.mp hc) ((mem_bd_of_dangling hP hZ hd).mp hb)⟩
        · exact Or.inl ⟨(mem_bd_of_dangling hP hZ hd).mpr (by by_contra hz; exact hc (h.mpr hz)),
            hc⟩
      · have h := (key_i he hd).mp hiff
        have heΓ : e ∈ Γ.Es := by
          rw [pole_Es, Finset.mem_union] at he
          exact he.elim (fun h ↦ edgesIn_subset Y h) (fun h ↦ bd_subset Y h)
        exact Or.inl ⟨mem_bd.mpr ⟨heΓ, h⟩, fun hc ↦ hd (couple₁_subset_dangling hP m hc)⟩
  · rintro (rfl | ⟨hb, hc⟩ | ⟨hc, hb⟩)
    · refine ⟨Or.inl rfl, ?_⟩
      have h0 : (cap hP m).ends (freshE (Γ.pole Y)) 0 = freshV (Γ.pole Y) := by
        rw [cap_ends_new]; simp
      have h1 : (cap hP m).ends (freshE (Γ.pole Y)) 1 = freshV (Γ.pole Y) + 1 := by
        rw [cap_ends_new]; simp
      rw [h0, h1]
      simp [hw]
    · have he : e ∈ (Γ.pole Y).Es := by
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side hb
        exact mem_edgesIn_or_bd (bd_subset Z hb) (hZ hi)
      refine ⟨Or.inr he, ?_⟩
      by_cases hd : e ∈ (Γ.pole Y).dangling
      · rw [key_d hd]
        exact ⟨fun h ↦ absurd h hc, fun h ↦ absurd ((mem_bd_of_dangling hP hZ hd).mp hb) h⟩
      · rw [key_i he hd]
        exact (mem_bd.mp hb).2
    · have hd := couple₁_subset_dangling hP m hc
      have he := (mem_dangling.mp hd).1
      refine ⟨Or.inr he, ?_⟩
      rw [key_d hd]
      exact ⟨fun _ ↦ fun hz ↦ hb ((mem_bd_of_dangling hP hZ hd).mpr hz), fun _ ↦ hc⟩

end Cap

section Join

/-- Cycles of `Γ` inside `Y` persist in the join. -/
theorem join_hasCycle_of {Z : Finset ℕ} (hZ : Z ⊆ Y) (hY : Y ⊆ Γ.Vs) (h : Γ.HasCycle Z) :
    (join hP m).HasCycle Z := by
  obtain ⟨F, hF, hne, hev⟩ := h
  refine ⟨F, ?_, hne, ?_⟩
  · intro e he
    have h := mem_edgesIn.mp (hF he)
    rw [mem_edgesIn, join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff]
    have hd : e ∉ (Γ.pole Y).dangling := by
      rw [mem_dangling]
      rintro ⟨-, i, hi⟩
      exact hi (hZ (h.2 i))
    have he' : e ∈ (Γ.pole Y).Es := by
      rw [pole_Es, Finset.mem_union]
      exact Or.inl (edgesIn_mono hZ (hF he))
    exact ⟨Or.inr (Or.inr ⟨he', hd⟩), fun i ↦ by rw [join_ends_old hP m he']; exact h.2 i⟩
  · intro v hv
    have : (join hP m).degIn F v = Γ.degIn F v := by
      unfold degIn halfEdgesIn
      congr 1
      apply Finset.filter_congr
      intro h hh
      rw [Finset.mem_product] at hh
      have he := mem_edgesIn.mp (hF hh.1)
      have he' : h.1 ∈ (Γ.pole Y).Es := by
        rw [pole_Es, Finset.mem_union]
        exact Or.inl (edgesIn_mono hZ (hF hh.1))
      rw [join_ends_old hP m he', pole_ends]
    rw [this]
    exact hev v (hY hv)

/-- Cycles of `Γ` inside `Y` persist in the cap. -/
theorem cap_hasCycle_of {Z : Finset ℕ} (hZ : Z ⊆ Y) (hY : Y ⊆ Γ.Vs) (h : Γ.HasCycle Z) :
    (cap hP m).HasCycle Z := by
  have hZ' : Z ⊆ (Γ.pole Y).Vs := hZ
  rw [cap_hasCycle hP m hZ']
  rw [pole_hasCycle hY hZ]
  exact h

/-- The membership of a new join edge's ends in an old vertex set. -/
theorem join_bd_old {Z : Finset ℕ} (hZ : Z ⊆ Y) (_hY : Y ⊆ Γ.Vs) :
    (join hP m).bd Z =
      ((Γ.bd Z).filter fun e ↦ e ∉ Γ.bd Y) ∪
        (({freshE (Γ.pole Y), freshE (Γ.pole Y) + 1} : Finset ℕ).filter fun f ↦
          ¬ ((join hP m).ends f 0 ∈ Z ↔ (join hP m).ends f 1 ∈ Z)) := by
  ext e
  rw [mem_bd, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, mem_bd, join_Es,
    Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hiff⟩
    rcases he with rfl | rfl | ⟨he, hd⟩
    · exact Or.inr ⟨Or.inl rfl, hiff⟩
    · exact Or.inr ⟨Or.inr rfl, hiff⟩
    · left
      have heΓ : e ∈ Γ.Es := by
        rw [pole_Es, Finset.mem_union] at he
        exact he.elim (fun h ↦ edgesIn_subset Y h) (fun h ↦ bd_subset Y h)
      rw [join_ends_old hP m he, join_ends_old hP m he] at hiff
      refine ⟨⟨heΓ, hiff⟩, ?_⟩
      rw [dangling_pole] at hd
      exact hd
  · rintro (⟨⟨he, hiff⟩, hnb⟩ | ⟨hf, hiff⟩)
    · have he' : e ∈ (Γ.pole Y).Es := by
        rw [pole_Es, Finset.mem_union]
        obtain ⟨i, hi, _⟩ := bd_side (mem_bd.mpr ⟨he, hiff⟩)
        exact mem_edgesIn_or_bd he (hZ hi)
      have hd : e ∉ (Γ.pole Y).dangling := by
        rw [dangling_pole]
        exact hnb
      refine ⟨Or.inr (Or.inr ⟨he', hd⟩), ?_⟩
      rw [join_ends_old hP m he', join_ends_old hP m he']
      exact hiff
    · rcases hf with rfl | rfl
      · exact ⟨Or.inl rfl, hiff⟩
      · exact ⟨Or.inr (Or.inl rfl), hiff⟩

end Join

end FinGraph
end GraphPuzzles
