import GraphPuzzles.Factorization.FactorQuasiStructure

/-!
# Helpers for the quasiatomic case
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Helpers

variable {Γ : FinGraph} {W : Finset ℕ} (hP : (Γ.pole W).IsPole4) (m : Fin 3)

/-- The inner end of a boundary edge is its end in the shore. -/
theorem innerEnd_eq_of_end {d : ℕ} (hd : d ∈ Γ.bd W) {i : Fin 2} (hi : Γ.ends d i ∈ W) :
    innerEnd hP d = Γ.ends d i := by
  have hd' : d ∈ (Γ.pole W).dangling := dangling_pole W ▸ hd
  rw [← ends_innerIdx hP hd', pole_ends]
  have hin : Γ.ends d (innerIdx hP hd') ∈ W := (innerIdx_spec hP hd').1
  have hout : Γ.ends d (Fin.rev (innerIdx hP hd')) ∉ W := (innerIdx_spec hP hd').2
  by_cases h : i = innerIdx hP hd'
  · rw [h]
  · exfalso
    have : i = Fin.rev (innerIdx hP hd') := by
      have h1 : i = 0 ∨ i = 1 := by omega
      have h2 : innerIdx hP hd' = 0 ∨ innerIdx hP hd' = 1 := by omega
      rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> rw [h2] at h ⊢
      · exact absurd rfl h
      · rw [Iso.rev_one']
      · rw [Iso.rev_zero']
      · exact absurd rfl h
    rw [this] at hi
    exact hout hi

/-- The other end of a boundary edge lies outside the shore. -/
theorem other_end_notMem {d : ℕ} (hd : d ∈ Γ.bd W) {i : Fin 2} (hi : Γ.ends d i ∈ W) :
    Γ.ends d (Fin.rev i) ∉ W := by
  rw [mem_bd] at hd
  have h1 : i = 0 ∨ i = 1 := by omega
  rcases h1 with rfl | rfl
  · rw [Iso.rev_zero']; exact fun h ↦ hd.2 ⟨fun _ ↦ h, fun _ ↦ hi⟩
  · rw [Iso.rev_one']; exact fun h ↦ hd.2 ⟨fun _ ↦ hi, fun _ ↦ h⟩

/-- The four dangling edges are two couples. -/
theorem dangling_eq_four {e e' : ℕ} (he : e ∈ (Γ.pole W).dangling) (he' : e' ∈ (Γ.pole W).dangling)
    (h1 : e' ≠ e) (h2 : e' ≠ partner hP m e) :
    (Γ.pole W).dangling = {e, partner hP m e, e', partner hP m e'} := by
  have hpe := partner_mem hP m he
  have hpe' := partner_mem hP m he'
  have hne := partner_ne hP m he
  have hne' := partner_ne hP m he'
  have h3 : partner hP m e' ≠ e := by
    intro h
    rw [← h, partner_partner hP m he'] at h2
    exact h2 rfl
  have h4 : partner hP m e' ≠ partner hP m e := fun h ↦ h1 (partner_inj hP m he' he h)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · rw [hP.card_dangling]
    rw [Finset.card_insert_of_notMem (by simp [hne.symm, h1.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [h2.symm, h4.symm]),
      Finset.card_pair hne'.symm]

/-- The new edge of the couple of a dangling edge joins the inner ends of the couple. -/
theorem join_new_joins {e : ℕ} (he : e ∈ (Γ.pole W).dangling) :
    (join hP m).Joins (if e ∈ couple₁ hP m then freshE (Γ.pole W) else freshE (Γ.pole W) + 1)
      (innerEnd hP e) (innerEnd hP (partner hP m e)) := by
  by_cases h : e ∈ couple₁ hP m
  · rw [if_pos h]
    rw [mem_couple₁_iff'] at h
    have e0 : (join hP m).ends (freshE (Γ.pole W)) 0 = innerEnd hP (bdEmb hP 0) := by
      rw [join_ends_new₁]; simp
    have e1 : (join hP m).ends (freshE (Γ.pole W)) 1 = innerEnd hP (partner hP m (bdEmb hP 0)) := by
      rw [join_ends_new₁, partner_bdEmb]; simp
    rcases h with h | h
    · left; rw [e0, e1, h]; exact ⟨rfl, rfl⟩
    · right; rw [e0, e1, ← h, partner_partner hP m he]; exact ⟨rfl, rfl⟩
  · rw [if_neg h]
    rw [← mem_couple₂_iff hP m he, mem_couple₂_iff'] at h
    have e0 : (join hP m).ends (freshE (Γ.pole W) + 1) 0 = innerEnd hP (bdEmb hP (other m)) := by
      rw [join_ends_new₂]; simp
    have e1 : (join hP m).ends (freshE (Γ.pole W) + 1) 1 =
        innerEnd hP (partner hP m (bdEmb hP (other m))) := by
      rw [join_ends_new₂, partner_bdEmb]; simp
    rcases h with h | h
    · left; rw [e0, e1, h]; exact ⟨rfl, rfl⟩
    · right; rw [e0, e1, ← h, partner_partner hP m he]; exact ⟨rfl, rfl⟩

theorem join_new_mem {e : ℕ} :
    (if e ∈ couple₁ hP m then freshE (Γ.pole W) else freshE (Γ.pole W) + 1) ∈ (join hP m).Es := by
  rw [join_Es]
  split_ifs
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The two new edges of a join. -/
theorem join_mem_Es_cases' {e : ℕ} (he : e ∈ (join hP m).Es) :
    e = freshE (Γ.pole W) ∨ e = freshE (Γ.pole W) + 1 ∨
      (e ∈ (Γ.pole W).Es ∧ e ∉ (Γ.pole W).dangling) := by
  rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff] at he
  exact he

/-- The ends of the new edges of a join are inner ends of the couples. -/
theorem join_new_ends_cases (n : ℕ) (hn : n = freshE (Γ.pole W) ∨ n = freshE (Γ.pole W) + 1) :
    ∃ e ∈ (Γ.pole W).dangling,
      n = (if e ∈ couple₁ hP m then freshE (Γ.pole W) else freshE (Γ.pole W) + 1) ∧
      (join hP m).Joins n (innerEnd hP e) (innerEnd hP (partner hP m e)) := by
  rcases hn with rfl | rfl
  · refine ⟨bdEmb hP 0, bdEmb_mem hP 0, ?_, ?_⟩
    · rw [if_pos (by rw [mem_couple₁_iff']; exact Or.inl rfl)]
    · have := join_new_joins hP m (bdEmb_mem hP 0)
      rw [if_pos (by rw [mem_couple₁_iff']; exact Or.inl rfl)] at this
      exact this
  · have hn : bdEmb hP (other m) ∉ couple₁ hP m := by
      rw [← mem_couple₂_iff hP m (bdEmb_mem hP (other m)), mem_couple₂_iff']; exact Or.inl rfl
    refine ⟨bdEmb hP (other m), bdEmb_mem hP (other m), ?_, ?_⟩
    · rw [if_neg hn]
    · have := join_new_joins hP m (bdEmb_mem hP (other m))
      rw [if_neg hn] at this
      exact this

end Helpers

end FinGraph
end GraphPuzzles
