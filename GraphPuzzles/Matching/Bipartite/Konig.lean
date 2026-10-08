import GraphPuzzles.Cuts.SeparatingCut
import Mathlib.Combinatorics.Hall.Basic

/-!
# König's theorem for cubic bipartite multigraphs

A regular bipartite multigraph has a perfect matching (Hall's theorem, from Mathlib), so a cubic
bipartite multigraph is the union of three perfect matchings and hence `3`-edge-colourable.  This
is the step "a bipartite cubic graph is `3`-edge-colourable" of the note's Lemma (brick).
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : j = Fin.rev i := by
  revert i j
  decide

/-- Bipartite: a two-colouring of the vertices with every edge joining the two colours. -/
def IsBipartite (H : LoopMultigraph V E) : Prop :=
  ∃ c : V → Bool, ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)

section Regular

variable {H : LoopMultigraph V E} {c : V → Bool}

open Classical in
/-- The neighbours of a vertex of one side through the edges of `F`. -/
noncomputable def nbr (H : LoopMultigraph V E) (c : V → Bool) (F : Finset E)
    (x : {v // c v = true}) : Finset {v // c v = false} :=
  Finset.univ.filter fun y ↦ ∃ e ∈ F, H.Joins e x.1 y.1

open Classical in
omit [DecidableEq V] [DecidableEq E] in
theorem mem_nbr {F : Finset E} {x : {v // c v = true}} {y : {v // c v = false}} :
    y ∈ nbr H c F x ↔ ∃ e ∈ F, H.Joins e x.1 y.1 := by
  simp [nbr]

variable (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1))

include hc in
omit [DecidableEq E] in
/-- An edge has at most one end in a set of vertices of one colour. -/
theorem endsIn_le_one {S : Finset V} (hS : ∀ v ∈ S, c v = true) (e : E) :
    H.endsIn S e = if ∃ i, H.endAt e i ∈ S then 1 else 0 := by
  unfold endsIn
  rw [Finset.card_filter, Fin.sum_univ_two]
  have hnot : ¬ (H.endAt e 0 ∈ S ∧ H.endAt e 1 ∈ S) := fun ⟨h0, h1⟩ ↦
    hc e ((hS _ h0).trans (hS _ h1).symm)
  by_cases h0 : H.endAt e 0 ∈ S <;> by_cases h1 : H.endAt e 1 ∈ S
  · exact absurd ⟨h0, h1⟩ hnot
  · rw [if_pos h0, if_neg h1, if_pos ⟨0, h0⟩]
  · rw [if_neg h0, if_pos h1, if_pos ⟨1, h1⟩]
  · rw [if_neg h0, if_neg h1, if_neg (fun ⟨i, hi⟩ ↦ by
      rcases fin2_cases i with rfl | rfl
      · exact h0 hi
      · exact h1 hi)]

include hc in
omit [DecidableEq E] in
/-- An edge has exactly one end of each colour. -/
theorem endsIn_side (b : Bool) (e : E) :
    H.endsIn (Finset.univ.filter fun v ↦ c v = b) e = 1 := by
  unfold endsIn
  rw [Finset.card_filter, Fin.sum_univ_two]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := hc e
  cases hb0 : c (H.endAt e 0) <;> cases hb1 : c (H.endAt e 1) <;> rw [hb0, hb1] at h <;>
    cases b <;> simp_all

variable {F : Finset E} {k : ℕ} (hF : ∀ v, H.degreeIn F v = k)

include hc hF in
omit [DecidableEq E] in
/-- Hall's condition for a regular bipartite multigraph. -/
theorem hall_condition (hk : 0 < k) (S : Finset {v // c v = true}) :
    S.card ≤ (S.biUnion (nbr H c F)).card := by
  let S' : Finset V := S.map (Function.Embedding.subtype _)
  let N' : Finset V := (S.biUnion (nbr H c F)).map (Function.Embedding.subtype _)
  have hS' : ∀ v ∈ S', c v = true := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hv
    exact x.2
  have hN' : ∀ v ∈ N', c v = false := by
    intro v hv
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hv
    exact y.2
  -- the edges of `F` with an end in `S'`
  have hcount : k * S'.card = (F.filter fun e ↦ ∃ i, H.endAt e i ∈ S').card := by
    have h := sum_degreeIn_eq (K := H) S' F
    rw [Finset.sum_congr rfl (fun v _ ↦ hF v), Finset.sum_const, smul_eq_mul, mul_comm] at h
    rw [h, Finset.sum_congr rfl (fun e _ ↦ endsIn_le_one hc hS' e), Finset.sum_boole, Nat.cast_id]
  have hcount' : k * N'.card = ∑ e ∈ F, H.endsIn N' e := by
    have h := sum_degreeIn_eq (K := H) N' F
    rw [Finset.sum_congr rfl (fun v _ ↦ hF v), Finset.sum_const, smul_eq_mul, mul_comm] at h
    exact h
  have hle : (F.filter fun e ↦ ∃ i, H.endAt e i ∈ S').card ≤ ∑ e ∈ F, H.endsIn N' e := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro e he
    split_ifs with hi
    · obtain ⟨i, hi⟩ := hi
      obtain ⟨x, hxS, hxe⟩ := Finset.mem_map.mp hi
      -- the other end lies in `N'`
      simp only [Function.Embedding.coe_subtype] at hxe
      have hother : H.endAt e (Fin.rev i) ∈ N' := by
        have hcol : c (H.endAt e (Fin.rev i)) = false := by
          have h := hc e
          rcases fin2_cases i with rfl | rfl
          · rw [show Fin.rev (0 : Fin 2) = 1 from rfl]
            rw [← hxe, x.2] at h
            cases h' : c (H.endAt e 1)
            · rfl
            · exact absurd h'.symm h
          · rw [show Fin.rev (1 : Fin 2) = 0 from rfl]
            rw [← hxe, x.2] at h
            cases h' : c (H.endAt e 0)
            · rfl
            · exact absurd h' h
        refine Finset.mem_map.mpr ⟨⟨_, hcol⟩, ?_, rfl⟩
        refine Finset.mem_biUnion.mpr ⟨x, hxS, ?_⟩
        refine mem_nbr.mpr ⟨e, he, ?_⟩
        rcases fin2_cases i with rfl | rfl
        · exact Or.inl ⟨hxe.symm, rfl⟩
        · exact Or.inr ⟨rfl, hxe.symm⟩
      unfold endsIn
      exact Finset.card_pos.mpr ⟨Fin.rev i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩⟩
    · exact Nat.zero_le _
  have hSc : S'.card = S.card := Finset.card_map _
  have hNc : N'.card = (S.biUnion (nbr H c F)).card := Finset.card_map _
  have : k * S.card ≤ k * (S.biUnion (nbr H c F)).card := by
    rw [← hSc, ← hNc, hcount, hcount']
    exact hle
  exact Nat.le_of_mul_le_mul_left this hk

include hc hF in
omit [DecidableEq E] in
/-- Both sides of a regular bipartite multigraph have the same size. -/
theorem card_sides_eq (hk : 0 < k) :
    (Finset.univ.filter fun v ↦ c v = true).card = (Finset.univ.filter fun v ↦ c v = false).card := by
  have h : ∀ b : Bool, k * (Finset.univ.filter fun v ↦ c v = b).card = F.card := by
    intro b
    have h := sum_degreeIn_eq (K := H) (Finset.univ.filter fun v ↦ c v = b) F
    rw [Finset.sum_congr rfl (fun v _ ↦ hF v), Finset.sum_const, smul_eq_mul, mul_comm,
      Finset.sum_congr rfl (fun e _ ↦ endsIn_side hc b e), Finset.sum_const, smul_eq_mul,
      mul_one] at h
    exact h
  have := (h true).trans (h false).symm
  exact Nat.eq_of_mul_eq_mul_left hk this

include hc hF in
/-- **Hall**: a regular bipartite multigraph has a perfect matching inside `F`. -/
theorem exists_perfectMatching_subset_of_regular (hk : 0 < k) :
    ∃ M ⊆ F, H.IsPerfectMatching M := by
  classical
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective (nbr H c F)).mp
    (hall_condition hc hF hk)
  have hcard : Fintype.card {v // c v = true} = Fintype.card {v // c v = false} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact card_sides_eq hc hF hk
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  have hjoin : ∀ x, ∃ e, e ∈ F ∧ H.Joins e x.1 (f x).1 := fun x ↦ by
    obtain ⟨e, he, hj⟩ := mem_nbr.mp (hf x)
    exact ⟨e, he, hj⟩
  choose pickF hpickF using hjoin
  have hne : ∀ x, x.1 ≠ (f x).1 := fun x h ↦ by
    have h1 := x.2
    have h2 := (f x).2
    rw [h] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  refine ⟨Finset.univ.image pickF, fun e he ↦ ?_, ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
    exact (hpickF x).1
  · intro v
    -- the unique matching edge at `v`
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, (v = x₀.1 ∨ v = (f x₀).1) ∧
        ∀ x, (v = x.1 ∨ v = (f x).1) → x = x₀ := by
      cases hv : c v
      · obtain ⟨x₀, hx₀⟩ := hfbij.2 ⟨v, hv⟩
        refine ⟨x₀, Or.inr (by rw [hx₀]), fun x hx ↦ ?_⟩
        rcases hx with hx | hx
        · have := x.2
          rw [← hx, hv] at this
          exact absurd this Bool.noConfusion
        · apply hfinj
          rw [hx₀]
          exact Subtype.ext hx.symm
      · refine ⟨⟨v, hv⟩, Or.inl rfl, fun x hx ↦ ?_⟩
        rcases hx with hx | hx
        · exact Subtype.ext hx.symm
        · have := (f x).2
          rw [← hx, hv] at this
          exact absurd this Bool.noConfusion
    obtain ⟨kv, hkv⟩ : ∃ kv, H.endAt (pickF x₀) kv = v := by
      rcases hx₀.1 with h | h
      · rw [h]
        exact (hpickF x₀).2.exists_end
      · rw [h]
        exact (H.joins_comm.mp (hpickF x₀).2).exists_end
    unfold degreeIn
    rw [Finset.card_eq_one]
    refine ⟨(pickF x₀, kv), ?_⟩
    ext ⟨e, i⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_singleton, Prod.mk.injEq, Finset.mem_image, true_and]
    constructor
    · rintro ⟨⟨x, rfl⟩, hi⟩
      have hx : x = x₀ := by
        apply hx₀.2
        rcases (hpickF x).2.endAt_mem i with h | h
        · exact Or.inl (hi.symm.trans h)
        · exact Or.inr (hi.symm.trans h)
      subst hx
      refine ⟨rfl, ?_⟩
      rcases hx₀.1 with h | h
      · rw [h] at hi hkv
        exact (hpickF x).2.end_unique (hne x) hi hkv
      · rw [h] at hi hkv
        exact (H.joins_comm.mp (hpickF x).2).end_unique (hne x).symm hi hkv
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨x₀, rfl⟩, hkv⟩

end Regular

/-- **König**: a cubic bipartite multigraph is `3`-edge-colourable. -/
theorem exists_properOff_of_bipartite {H : LoopMultigraph V E} (hCubic : ∀ v, H.degree v = 3)
    (hbip : H.IsBipartite) : ∃ g : E → Color, H.ProperOff ∅ g := by
  obtain ⟨c, hc⟩ := hbip
  obtain ⟨M₁, -, hM₁⟩ := exists_perfectMatching_subset_of_regular hc (F := Finset.univ) (k := 3)
    (fun v ↦ by rw [degreeIn_univ']; exact hCubic v) (by decide)
  have h2 : ∀ v, H.degreeIn (Finset.univ \ M₁) v = 2 := fun v ↦ by
    have := degreeIn_add_compl (H := H) M₁ v
    rw [hM₁ v, hCubic v] at this
    omega
  obtain ⟨M₂, hM₂sub, hM₂⟩ := exists_perfectMatching_subset_of_regular hc h2 (by decide)
  have h1 : ∀ v, H.degreeIn ((Finset.univ \ M₁) \ M₂) v = 1 := fun v ↦ by
    have := degreeIn_union_of_disjoint (H := H) (Finset.sdiff_disjoint (s := M₂)
      (t := Finset.univ \ M₁)) v
    rw [Finset.sdiff_union_of_subset hM₂sub, h2 v, hM₂ v] at this
    omega
  let g : E → Color := fun e ↦ if e ∈ M₁ then (1, 0) else if e ∈ M₂ then (0, 1) else (1, 1)
  refine ⟨g, fun e _ ↦ ?_, ?_⟩
  · simp only [g]
    split_ifs <;> decide
  · intro v _ h₁ h₂ _ _ heq
    by_contra hne
    -- both edges lie in the same perfect matching
    have key : ∀ M, H.IsPerfectMatching M → h₁.1.1 ∈ M → h₂.1.1 ∈ M → False := by
      intro M hM hm₁ hm₂
      have := H.two_le_degreeIn_of_ne h₁ h₂ hne hm₁ hm₂
      rw [hM v] at this
      omega
    simp only [g] at heq
    by_cases ha : h₁.1.1 ∈ M₁ <;> by_cases hb : h₂.1.1 ∈ M₁
    · exact key M₁ hM₁ ha hb
    · rw [if_pos ha, if_neg hb] at heq
      split_ifs at heq <;> exact absurd heq (by decide)
    · rw [if_neg ha, if_pos hb] at heq
      split_ifs at heq <;> exact absurd heq (by decide)
    · rw [if_neg ha, if_neg hb] at heq
      by_cases ha' : h₁.1.1 ∈ M₂ <;> by_cases hb' : h₂.1.1 ∈ M₂
      · exact key M₂ hM₂ ha' hb'
      · rw [if_pos ha', if_neg hb'] at heq
        exact absurd heq (by decide)
      · rw [if_neg ha', if_pos hb'] at heq
        exact absurd heq (by decide)
      · exact key _ h1 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩, ha'⟩)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩, hb'⟩)

end LoopMultigraph
end GraphPuzzles
