import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoCapCycle
import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoJoinCycle

/-!
# The Hamilton-cycle descent lemma

For a cycle-separating `4`-cut `Y` of `Δ` with cap factor `B` (on `Y`) and join factor `A` (on
the complement): a Hamilton cycle of `Δ - v` yields a Hamilton cycle of `A - v` for `v` outside
`Y` (when `B` is not Hamiltonian), of `B - z` for `z ∈ Y` (when `A` is not Hamiltonian), and of
`B - u`, `B - w` from Hamilton cycles of `Δ` minus the outer ends of suitable cut edges (when `B`
is not Hamiltonian).  (Hypohamiltonian snark note, Section 3.)
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {Y : Finset ℕ} (hcl : Δ.IsClosed) (hY : Y ⊆ Δ.Vs)
  (hind : Δ.IsIndependentCut Y) (hPY : (Δ.pole Y).IsPole4) (hPYc : (Δ.pole (Δ.Vs \ Y)).IsPole4)
  (m : Fin 3) (hbd4 : (Δ.bd Y).card = 4)

section Cuts

include hcl in
theorem couple₁_eq_compl : couple₁ hPY m = couple₁ hPYc m := by
  unfold couple₁
  rw [bdEmb_eq_compl hcl hPY hPYc, bdEmb_eq_compl hcl hPY hPYc]

include hcl in
theorem couple₂_eq_compl : couple₂ hPY m = couple₂ hPYc m := by
  unfold couple₂
  rw [bdEmb_eq_compl hcl hPY hPYc, bdEmb_eq_compl hcl hPY hPYc]

theorem couple₁_subset_bd : couple₁ hPY m ⊆ Δ.bd Y := by
  intro d hd
  rw [← dangling_pole]; exact couple₁_subset_dangling hPY m hd

theorem couple₂_subset_bd : couple₂ hPY m ⊆ Δ.bd Y := by
  intro d hd
  rw [← dangling_pole]; exact couple₂_subset_dangling hPY m hd

theorem mem_couple_or {d : ℕ} (hd : d ∈ Δ.bd Y) : d ∈ couple₁ hPY m ∨ d ∈ couple₂ hPY m := by
  by_cases h : d ∈ couple₁ hPY m
  · exact Or.inl h
  · exact Or.inr ((mem_couple₂_iff hPY m (mem_dangling_Y hd)).mpr h)

theorem disjoint_couples : Disjoint (couple₁ hPY m) (couple₂ hPY m) := by
  rw [Finset.disjoint_left]
  intro d h1 h2
  exact (mem_couple₂_iff hPY m (couple₂_subset_dangling hPY m h2)).mp h2 h1

theorem notMem_couple₁_of_mem_couple₂ {d : ℕ} (h : d ∈ couple₂ hPY m) : d ∉ couple₁ hPY m :=
  fun h' ↦ Finset.disjoint_left.mp (disjoint_couples hPY m) h' h

variable {S C : Finset ℕ} (hC : Δ.IsHamCycle S C)
include hC

/-- The number of cut edges of a Hamilton cycle is even. -/
theorem K_even (hS : ∀ y ∈ Y, y ∈ S ∨ Δ.degIn C y = 0) : Even (C ∩ Δ.bd Y).card :=
  even_card_inter_bd (hC.subset.trans (edgesIn_subset S)) (fun v hv ↦ by
    rcases hS v hv with h | h
    · rw [hC.deg v h]; exact ⟨1, rfl⟩
    · rw [h]; exact ⟨0, rfl⟩)

/-- A Hamilton cycle through vertices on both sides has a cut edge. -/
theorem K_nonempty {y x : ℕ} (hyY : y ∈ Y) (hyS : y ∈ S) (hx : x ∈ Δ.Vs \ Y) (hxS : x ∈ S) :
    (C ∩ Δ.bd Y).Nonempty := by
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset S)
  obtain ⟨⟨e, i⟩, he⟩ : (Δ.halfEdgesIn C y).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hC.deg y hyS]; omega
  obtain ⟨⟨f, j⟩, hf⟩ : (Δ.halfEdgesIn C x).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hC.deg x hxS]; omega
  rw [mem_halfEdgesIn] at he hf
  dsimp only at he hf
  by_cases hfb : f ∈ Δ.bd Y
  · exact ⟨f, Finset.mem_inter.mpr ⟨hf.1, hfb⟩⟩
  · have hfS : f ∉ Δ.sidePart C Y := by
      rw [mem_sidePart_iff]
      rintro ⟨-, h | h⟩
      · exact (Finset.mem_sdiff.mp hx).2 (hf.2 ▸ (mem_edgesIn.mp h).2 j)
      · exact hfb h
    have heS : e ∈ Δ.sidePart C Y := mem_sidePart_of_ends hCE he.1 (he.2 ▸ hyY)
    have key : ∀ z, Relation.ReflTransGen (Δ.AdjIn C) e z →
        z ∈ Δ.sidePart C Y ∨ (C ∩ Δ.bd Y).Nonempty := by
      intro z hz
      induction hz with
      | refl => exact Or.inl heS
      | @tail b c _ hlast ih =>
        rcases ih with hb | hne
        · by_cases hc : c ∈ Δ.sidePart C Y
          · exact Or.inl hc
          · exact Or.inr ⟨b, Finset.mem_inter.mpr ⟨sidePart_subset hb,
              mem_bd_of_adj_outside hCE hb hc hlast⟩⟩
        · exact Or.inr hne
    rcases key f (hC.connected e he.1 f hf.1) with h | h
    · exact absurd h hfS
    · exact h

omit hC in
include hbd4 in
theorem K_card_le : (C ∩ Δ.bd Y).card ≤ 4 :=
  (Finset.card_le_card Finset.inter_subset_right).trans hbd4.le

omit hC in
include hbd4 in
theorem K_eq_bd_of_four (h4 : (C ∩ Δ.bd Y).card = 4) : C ∩ Δ.bd Y = Δ.bd Y :=
  Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hbd4, h4])

omit hC in
/-- Two cut edges of the same couple form that couple. -/
theorem K_eq_couple_of_two (h2 : (C ∩ Δ.bd Y).card = 2)
    (hsame : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y, (a ∈ couple₁ hPY m ↔ b ∈ couple₁ hPY m)) :
    C ∩ Δ.bd Y = couple₁ hPY m ∨ C ∩ Δ.bd Y = couple₂ hPY m := by
  obtain ⟨a, b, hab, hK⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ C ∩ Δ.bd Y := by rw [hK]; exact Finset.mem_insert_self _ _
  have hb : b ∈ C ∩ Δ.bd Y := by rw [hK]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases mem_couple_or hPY m (Finset.mem_inter.mp ha).2 with h₁ | h₂
  · left
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h₁
      · exact (hsame a ha x hb).mp h₁
    · rw [h2, card_couple₁]
  · right
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      have ha₁ : a ∉ couple₁ hPY m := notMem_couple₁_of_mem_couple₂ hPY m h₂
      rcases hx with rfl | rfl
      · exact h₂
      · exact (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hb).2)).mpr
          (fun h ↦ ha₁ ((hsame a ha x hb).mpr h))
    · rw [h2, card_couple₂]

end Cuts

section Descent

include hcl hY hind hbd4

/-- **Descent to the join factor.** -/
theorem descent_join {v : ℕ} (hv : v ∈ Δ.Vs \ Y) {C : Finset ℕ}
    (hC : Δ.IsHamCycle (Δ.Vs.erase v) C) (hV3 : 3 ≤ Δ.Vs.card) (hYne : Y.Nonempty)
    (hYc2 : 2 ≤ (Δ.Vs \ Y).card) (hB : ¬ (cap hPY m).IsHamiltonian) :
    ∃ C', (join hPYc m).IsHamCycle ((Δ.Vs \ Y).erase v) C' := by
  classical
  have hSV : Δ.Vs.erase v ⊆ Δ.Vs := Finset.erase_subset v Δ.Vs
  have h2 : 2 ≤ (Δ.Vs.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hv).1]; omega
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset _)
  have hyS : ∀ y ∈ Y, y ∈ Δ.Vs.erase v :=
    fun y hy ↦ Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp hv).2 (h ▸ hy), hY hy⟩
  obtain ⟨y, hyY⟩ := hYne
  obtain ⟨x, hx, hxv⟩ := Finset.exists_mem_ne (by omega : 1 < (Δ.Vs \ Y).card) v
  have hK : (C ∩ Δ.bd Y).Nonempty := K_nonempty hC hyY (hyS y hyY) hx
    (Finset.mem_erase.mpr ⟨hxv, (Finset.mem_sdiff.mp hx).1⟩)
  have hKeven : Even (C ∩ Δ.bd Y).card := K_even hC (fun y hy ↦ Or.inl (hyS y hy))
  have hKle : (C ∩ Δ.bd Y).card ≤ 4 := K_card_le hbd4 (C := C)
  have hKcase : (C ∩ Δ.bd Y).card = 2 ∨ (C ∩ Δ.bd Y).card = 4 := by
    obtain ⟨t, ht⟩ := hKeven
    have := Finset.card_pos.mpr hK
    omega
  have hc₁ := couple₁_eq_compl hcl hPY hPYc m
  have hc₂ := couple₂_eq_compl hcl hPY hPYc m
  -- the cap must not be Hamiltonian: general contradiction from `cap_hamCycle`
  have hcapT : ∀ (uw : Bool), (freshV (Δ.pole Y) ∈ (cap hPY m).Vs ↔ (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty) →
      (freshV (Δ.pole Y) + 1 ∈ (cap hPY m).Vs ↔ (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty) →
      ((C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty →
        (C ∩ Δ.bd Y ∩ couple₁ hPY m).card + (if uw then 1 else 0) = 2) →
      ((C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty →
        (C ∩ Δ.bd Y ∩ couple₂ hPY m).card + (if uw then 1 else 0) = 2) →
      (uw = true → (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty ∧ (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty) →
      (uw = false → (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty → (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty →
        ∃ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∃ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
          Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) a b) → False := by
    intro uw hu hw hdu hdw huw hcross
    apply hB
    refine ⟨_, cap_hamCycle hind hPY m hC uw (T := (cap hPY m).Vs) ?_ ?_ hu hw hdu hdw
      huw hK hcross⟩
    · intro y hy
      rw [cap_Vs]
      exact ⟨fun _ ↦ hyS y hy, fun _ ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩
    · exact fun x hx ↦ hx
  have huV : freshV (Δ.pole Y) ∈ (cap hPY m).Vs := by rw [cap_Vs]; exact Finset.mem_insert_self _ _
  have hwV : freshV (Δ.pole Y) + 1 ∈ (cap hPY m).Vs := by
    rw [cap_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- (R2): with two cut edges they lie in the same couple
  have hsame : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y, (C ∩ Δ.bd Y).card = 2 →
      (a ∈ couple₁ hPY m ↔ b ∈ couple₁ hPY m) := by
    intro a ha b hb h2'
    by_contra hne
    -- one in each couple
    have key : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y, a ∈ couple₁ hPY m → b ∉ couple₁ hPY m → False := by
      intro a ha b hb ha₁ hb₁
      have hb₂ : b ∈ couple₂ hPY m :=
        (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hb).2)).mpr hb₁
      have hab : a ≠ b := fun h ↦ hb₁ (h ▸ ha₁)
      have hK1 : C ∩ Δ.bd Y ∩ couple₁ hPY m = {a} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rw [Finset.mem_inter] at hx
          rw [Finset.mem_singleton]
          -- `x` is `a` or `b`; `b` is not in the first couple
          obtain ⟨a', b', -, hK⟩ := Finset.card_eq_two.mp h2'
          have hxK := hx.1
          have haK := ha
          have hbK := hb
          rw [hK, Finset.mem_insert, Finset.mem_singleton] at hxK haK hbK
          rcases hxK with rfl | rfl <;> rcases haK with rfl | rfl <;> rcases hbK with rfl | rfl
          all_goals
            first
            | rfl
            | exact absurd rfl hab
            | exact absurd hx.2 hb₁
        · rw [Finset.card_singleton]
          exact Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, ha₁⟩⟩
      have hK2 : C ∩ Δ.bd Y ∩ couple₂ hPY m = {b} := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rw [Finset.mem_inter] at hx
          rw [Finset.mem_singleton]
          obtain ⟨a', b', -, hK⟩ := Finset.card_eq_two.mp h2'
          have hxK := hx.1
          have haK := ha
          have hbK := hb
          rw [hK, Finset.mem_insert, Finset.mem_singleton] at hxK haK hbK
          rcases hxK with rfl | rfl <;> rcases haK with rfl | rfl <;> rcases hbK with rfl | rfl
          all_goals
            first
            | rfl
            | exact absurd rfl hab
            | exact absurd ha₁ (notMem_couple₁_of_mem_couple₂ hPY m hx.2)
        · rw [Finset.card_singleton]
          exact Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨hb, hb₂⟩⟩
      exact hcapT true (by rw [hK1]; exact ⟨fun _ ↦ ⟨a, Finset.mem_singleton_self _⟩, fun _ ↦ huV⟩)
        (by rw [hK2]; exact ⟨fun _ ↦ ⟨b, Finset.mem_singleton_self _⟩, fun _ ↦ hwV⟩)
        (fun _ ↦ by simp [hK1]) (fun _ ↦ by simp [hK2])
        (fun _ ↦ ⟨⟨a, by rw [hK1]; exact Finset.mem_singleton_self _⟩,
          ⟨b, by rw [hK2]; exact Finset.mem_singleton_self _⟩⟩)
        (fun h ↦ absurd h (by decide))
    by_cases ha₁ : a ∈ couple₁ hPY m
    · exact key a ha b hb ha₁ (fun hb₁ ↦ hne ⟨fun _ ↦ hb₁, fun _ ↦ ha₁⟩)
    · have hb₁ : b ∈ couple₁ hPY m := by
        by_contra hb₁; exact hne ⟨fun h ↦ absurd h ha₁, fun h ↦ absurd h hb₁⟩
      exact key b hb a ha hb₁ ha₁
  -- (R4): with four cut edges, `Y`-links stay within couples
  have hH : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y,
      Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) a b →
      (a ∈ couple₁ hPY m ↔ b ∈ couple₁ hPY m) := by
    intro a ha b hb hab
    rcases hKcase with h2' | h4
    · exact hsame a ha b hb h2'
    · have hKbd := K_eq_bd_of_four hbd4 (C := C) h4
      have hK1 : C ∩ Δ.bd Y ∩ couple₁ hPY m = couple₁ hPY m := by
        rw [hKbd]; exact Finset.inter_eq_right.mpr (couple₁_subset_bd hPY m)
      have hK2 : C ∩ Δ.bd Y ∩ couple₂ hPY m = couple₂ hPY m := by
        rw [hKbd]; exact Finset.inter_eq_right.mpr (couple₂_subset_bd hPY m)
      have key : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y,
          Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) a b →
          a ∈ couple₁ hPY m → b ∉ couple₁ hPY m → False := by
        intro a ha b hb hab ha₁ hb₁
        have hb₂ : b ∈ couple₂ hPY m :=
          (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hb).2)).mpr hb₁
        exact hcapT false (by rw [hK1]; exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ huV⟩)
          (by rw [hK2]; exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ hwV⟩)
          (fun _ ↦ by simp [hK1, card_couple₁]) (fun _ ↦ by simp [hK2, card_couple₂])
          (fun h ↦ absurd h (by decide))
          (fun _ _ _ ↦ ⟨a, Finset.mem_inter.mpr ⟨ha, ha₁⟩, b, Finset.mem_inter.mpr ⟨hb, hb₂⟩, hab⟩)
      by_cases ha₁ : a ∈ couple₁ hPY m
      · exact ⟨fun _ ↦ by by_contra hb₁; exact key a ha b hb hab ha₁ hb₁, fun _ ↦ ha₁⟩
      · refine ⟨fun h ↦ absurd h ha₁, fun hb₁ ↦ ?_⟩
        exact absurd ha₁ (fun ha₁' ↦ key b hb a ha (reflTransGen_adjIn_symm hab) hb₁ ha₁')
  -- the cut edges of `C` form whole couples
  have hcouples : (C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty → couple₁ hPY m ⊆ C := by
    intro hne
    rcases hKcase with h2' | h4
    · rcases K_eq_couple_of_two hPY m (C := C) h2' (fun a ha b hb ↦ hsame a ha b hb h2') with h | h
      · rw [← h]; exact Finset.inter_subset_left
      · exfalso
        obtain ⟨a, ha⟩ := hne
        rw [Finset.mem_inter, h] at ha
        exact notMem_couple₁_of_mem_couple₂ hPY m ha.1 ha.2
    · exact (couple₁_subset_bd hPY m).trans
        (by rw [← K_eq_bd_of_four hbd4 (C := C) h4]; exact Finset.inter_subset_left)
  have hcouples' : (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty → couple₂ hPY m ⊆ C := by
    intro hne
    rcases hKcase with h2' | h4
    · rcases K_eq_couple_of_two hPY m (C := C) h2' (fun a ha b hb ↦ hsame a ha b hb h2') with h | h
      · exfalso
        obtain ⟨a, ha⟩ := hne
        rw [Finset.mem_inter, h] at ha
        exact notMem_couple₁_of_mem_couple₂ hPY m ha.2 ha.1
      · rw [← h]; exact Finset.inter_subset_left
    · exact (couple₂_subset_bd hPY m).trans
        (by rw [← K_eq_bd_of_four hbd4 (C := C) h4]; exact Finset.inter_subset_left)
  -- a cross link on the complementary side, from the alternating chain
  have hlink : (C ∩ Δ.bd Y ∩ couple₁ hPYc m).Nonempty → (C ∩ Δ.bd Y ∩ couple₂ hPYc m).Nonempty →
      ∃ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPYc m, ∃ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPYc m,
        Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) a b := by
    rw [← hc₁, ← hc₂]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have haK := Finset.mem_inter.mp ha
    have hbK := Finset.mem_inter.mp hb
    have hchain := alternating_chain hcl hCE hC.connected haK.1 hbK.1
    have key : ∀ k, Relation.ReflTransGen (Δ.SideLink C Y) a k →
        k ∈ couple₁ hPY m ∨ ∃ a' ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∃ b' ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
          Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) a' b' := by
      intro k hk
      induction hk with
      | refl => exact Or.inl haK.2
      | @tail k k' _ hkk' ih =>
        rcases ih with hk₁ | hex
        · obtain ⟨hkK, hk'K, hlk | hlk⟩ := hkk'
          · exact Or.inl ((hH k hkK k' hk'K hlk).mp hk₁)
          · by_cases hk'₁ : k' ∈ couple₁ hPY m
            · exact Or.inl hk'₁
            · exact Or.inr ⟨k, Finset.mem_inter.mpr ⟨hkK, hk₁⟩, k', Finset.mem_inter.mpr ⟨hk'K,
                (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hk'K).2)).mpr hk'₁⟩, hlk⟩
        · exact Or.inr hex
    rcases key b hchain with hb₁ | hex
    · exact absurd hb₁ (notMem_couple₁_of_mem_couple₂ hPY m hbK.2)
    · exact hex
  refine ⟨_, join_hamCycle hcl hind hPYc m hC h2 (T := (Δ.Vs \ Y).erase v) ?_
    (Finset.erase_subset v _) ?_ ?_ hK hlink⟩
  · intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h ↦ ⟨h.1, (Finset.mem_sdiff.mp hx).1⟩, fun h ↦ ⟨h.1, hx⟩⟩
  · rw [← hc₁]; exact hcouples
  · rw [← hc₂]; exact hcouples'

/-- **Descent to the cap factor, old vertex.** -/
theorem descent_cap_old {z : ℕ} (hz : z ∈ Y) {C : Finset ℕ} (hC : Δ.IsHamCycle (Δ.Vs.erase z) C)
    (hV3 : 3 ≤ Δ.Vs.card) (hY2 : 2 ≤ Y.card) (hYc : (Δ.Vs \ Y).Nonempty)
    (hA : ¬ (join hPYc m).IsHamiltonian) :
    ∃ C', (cap hPY m).IsHamCycle ((cap hPY m).Vs.erase z) C' := by
  classical
  have hzV : z ∈ Δ.Vs := hY hz
  have hSV : Δ.Vs.erase z ⊆ Δ.Vs := Finset.erase_subset z Δ.Vs
  have h2 : 2 ≤ (Δ.Vs.erase z).card := by rw [Finset.card_erase_of_mem hzV]; omega
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset _)
  obtain ⟨y, hyY, hyz⟩ := Finset.exists_mem_ne (by omega : 1 < Y.card) z
  obtain ⟨x, hx⟩ := hYc
  have hK : (C ∩ Δ.bd Y).Nonempty := K_nonempty hC hyY (Finset.mem_erase.mpr ⟨hyz, hY hyY⟩) hx
    (Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp hx).2 (h ▸ hz), (Finset.mem_sdiff.mp hx).1⟩)
  have hKeven : Even (C ∩ Δ.bd Y).card := K_even hC (fun y hy ↦ by
    by_cases h : y = z
    · right; subst h
      rw [degIn_eq_zero_iff]
      intro e he i hi
      exact (Finset.mem_erase.mp ((mem_edgesIn.mp (hC.subset he)).2 i)).1 hi
    · left; exact Finset.mem_erase.mpr ⟨h, hY hy⟩)
  have hKle : (C ∩ Δ.bd Y).card ≤ 4 := K_card_le hbd4 (C := C)
  have hKcase : (C ∩ Δ.bd Y).card = 2 ∨ (C ∩ Δ.bd Y).card = 4 := by
    obtain ⟨t, ht⟩ := hKeven
    have := Finset.card_pos.mpr hK
    omega
  have hc₁ := couple₁_eq_compl hcl hPY hPYc m
  have hc₂ := couple₂_eq_compl hcl hPY hPYc m
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  -- the join must not be Hamiltonian: general contradiction from `join_hamCycle`
  have hjoinT : ((C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty → couple₁ hPY m ⊆ C) →
      ((C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty → couple₂ hPY m ⊆ C) →
      ((C ∩ Δ.bd Y ∩ couple₁ hPY m).Nonempty → (C ∩ Δ.bd Y ∩ couple₂ hPY m).Nonempty →
        ∃ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∃ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
          Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) a b) → False := by
    intro hK₁ hK₂ hlink
    apply hA
    rw [hc₁] at hK₁ hlink
    rw [hc₂] at hK₂ hlink
    refine ⟨_, join_hamCycle hcl hind hPYc m hC h2 (T := Δ.Vs \ Y) ?_ subset_rfl hK₁ hK₂
      hK hlink⟩
    intro x hx
    exact ⟨fun _ ↦ Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp hx).2 (h ▸ hz),
      (Finset.mem_sdiff.mp hx).1⟩, fun _ ↦ hx⟩
  -- (L2): two cut edges lie in different couples
  have hdiff : (C ∩ Δ.bd Y).card = 2 → ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y, a ≠ b →
      ¬ (a ∈ couple₁ hPY m ↔ b ∈ couple₁ hPY m) := by
    intro h2' a ha b hb hab hiff
    -- then the cut edges form one couple
    have hsame : ∀ a' ∈ C ∩ Δ.bd Y, ∀ b' ∈ C ∩ Δ.bd Y, (a' ∈ couple₁ hPY m ↔ b' ∈ couple₁ hPY m) := by
      intro a' ha' b' hb'
      obtain ⟨p, q, hpq, hK'⟩ := Finset.card_eq_two.mp h2'
      have hmem : ∀ x ∈ C ∩ Δ.bd Y, x = a ∨ x = b := by
        intro x hx
        rw [hK', Finset.mem_insert, Finset.mem_singleton] at hx ha hb
        rcases hx with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hab
      rcases hmem a' ha' with rfl | rfl <;> rcases hmem b' hb' with rfl | rfl
      · exact Iff.rfl
      · exact hiff
      · exact hiff.symm
      · exact Iff.rfl
    rcases K_eq_couple_of_two hPY m (C := C) h2' hsame with h | h
    · exact hjoinT (fun _ ↦ by rw [← h]; exact Finset.inter_subset_left)
        (fun hne ↦ by
          exfalso
          obtain ⟨x, hx⟩ := hne
          rw [Finset.mem_inter, h] at hx
          exact notMem_couple₁_of_mem_couple₂ hPY m hx.2 hx.1)
        (fun _ hne ↦ by
          exfalso
          obtain ⟨x, hx⟩ := hne
          rw [Finset.mem_inter, h] at hx
          exact notMem_couple₁_of_mem_couple₂ hPY m hx.2 hx.1)
    · exact hjoinT (fun hne ↦ by
          exfalso
          obtain ⟨x, hx⟩ := hne
          rw [Finset.mem_inter, h] at hx
          exact notMem_couple₁_of_mem_couple₂ hPY m hx.1 hx.2)
        (fun _ ↦ by rw [← h]; exact Finset.inter_subset_left)
        (fun hne _ ↦ by
          exfalso
          obtain ⟨x, hx⟩ := hne
          rw [Finset.mem_inter, h] at hx
          exact notMem_couple₁_of_mem_couple₂ hPY m hx.1 hx.2)
  -- (L4): with four cut edges, no cross link on the complementary side
  have hnocross : (C ∩ Δ.bd Y).card = 4 → ∀ a ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m,
      ∀ b ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
      ¬ Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C (Δ.Vs \ Y))) a b := by
    intro h4 a ha b hb hab
    have hKbd := K_eq_bd_of_four hbd4 (C := C) h4
    exact hjoinT
      (fun _ ↦ (couple₁_subset_bd hPY m).trans (by rw [← hKbd]; exact Finset.inter_subset_left))
      (fun _ ↦ (couple₂_subset_bd hPY m).trans (by rw [← hKbd]; exact Finset.inter_subset_left))
      (fun _ _ ↦ ⟨a, ha, b, hb, hab⟩)
  -- the cap cycle
  rcases hKcase with h2' | h4
  · -- two cut edges, in different couples: add the new edge `uw`
    obtain ⟨p, q, hpq, hK'⟩ := Finset.card_eq_two.mp h2'
    have hp : p ∈ C ∩ Δ.bd Y := by rw [hK']; exact Finset.mem_insert_self _ _
    have hq : q ∈ C ∩ Δ.bd Y := by rw [hK']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hpq' := hdiff h2' p hp q hq hpq
    -- one of them is in the first couple, the other in the second
    have hsplit : ∃ a ∈ C ∩ Δ.bd Y, ∃ b ∈ C ∩ Δ.bd Y, a ∈ couple₁ hPY m ∧ b ∈ couple₂ hPY m ∧
        C ∩ Δ.bd Y ∩ couple₁ hPY m = {a} ∧ C ∩ Δ.bd Y ∩ couple₂ hPY m = {b} := by
      have key : ∀ a ∈ C ∩ Δ.bd Y, ∀ b ∈ C ∩ Δ.bd Y, a ≠ b → a ∈ couple₁ hPY m → b ∉ couple₁ hPY m →
          C ∩ Δ.bd Y ∩ couple₁ hPY m = {a} ∧ C ∩ Δ.bd Y ∩ couple₂ hPY m = {b} := by
        intro a ha b hb hab ha₁ hb₁
        have hb₂ : b ∈ couple₂ hPY m :=
          (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hb).2)).mpr hb₁
        have hmem : ∀ x ∈ C ∩ Δ.bd Y, x = a ∨ x = b := by
          intro x hx
          rw [hK', Finset.mem_insert, Finset.mem_singleton] at hx ha hb
          rcases hx with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hab
        constructor
        · ext x
          rw [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hx₁⟩
            rcases hmem x hx with rfl | rfl
            · rfl
            · exact absurd hx₁ hb₁
          · rintro rfl; exact ⟨ha, ha₁⟩
        · ext x
          rw [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hx₂⟩
            rcases hmem x hx with rfl | rfl
            · exact absurd ha₁ (notMem_couple₁_of_mem_couple₂ hPY m hx₂)
            · rfl
          · rintro rfl; exact ⟨hb, hb₂⟩
      by_cases hp₁ : p ∈ couple₁ hPY m
      · have hq₁ : q ∉ couple₁ hPY m := fun hq₁ ↦ hpq' ⟨fun _ ↦ hq₁, fun _ ↦ hp₁⟩
        obtain ⟨h1, h2⟩ := key p hp q hq hpq hp₁ hq₁
        exact ⟨p, hp, q, hq, hp₁,
          (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hq).2)).mpr hq₁, h1, h2⟩
      · have hq₁ : q ∈ couple₁ hPY m := by
          by_contra hq₁; exact hpq' ⟨fun h ↦ absurd h hp₁, fun h ↦ absurd h hq₁⟩
        obtain ⟨h1, h2⟩ := key q hq p hp hpq.symm hq₁ hp₁
        exact ⟨q, hq, p, hp, hq₁,
          (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hp).2)).mpr hp₁, h1, h2⟩
    obtain ⟨a, ha, b, hb, ha₁, hb₂, hK1, hK2⟩ := hsplit
    refine ⟨_, cap_hamCycle hind hPY m hC true (T := (cap hPY m).Vs.erase z) ?_
      (Finset.erase_subset _ _) ?_ ?_ ?_ ?_ ?_ hK ?_⟩
    · intro y hy
      rw [Finset.mem_erase, Finset.mem_erase, cap_Vs]
      exact ⟨fun h ↦ ⟨h.1, hY hy⟩, fun h ↦ ⟨h.1, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩⟩
    · rw [hK1, Finset.mem_erase, cap_Vs]
      exact ⟨fun _ ↦ ⟨a, Finset.mem_singleton_self _⟩,
        fun _ ↦ ⟨fun h ↦ huY (h ▸ hz), Finset.mem_insert_self _ _⟩⟩
    · rw [hK2, Finset.mem_erase, cap_Vs]
      exact ⟨fun _ ↦ ⟨b, Finset.mem_singleton_self _⟩,
        fun _ ↦ ⟨fun h ↦ hwY (h ▸ hz), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩⟩
    · intro _; simp [hK1]
    · intro _; simp [hK2]
    · intro _
      exact ⟨⟨a, by rw [hK1]; exact Finset.mem_singleton_self _⟩,
        ⟨b, by rw [hK2]; exact Finset.mem_singleton_self _⟩⟩
    · intro h; exact absurd h (by decide)
  · -- four cut edges: the cross link on the `Y` side from the alternating chain
    have hKbd := K_eq_bd_of_four hbd4 (C := C) h4
    have hK1 : C ∩ Δ.bd Y ∩ couple₁ hPY m = couple₁ hPY m := by
      rw [hKbd]; exact Finset.inter_eq_right.mpr (couple₁_subset_bd hPY m)
    have hK2 : C ∩ Δ.bd Y ∩ couple₂ hPY m = couple₂ hPY m := by
      rw [hKbd]; exact Finset.inter_eq_right.mpr (couple₂_subset_bd hPY m)
    refine ⟨_, cap_hamCycle hind hPY m hC false (T := (cap hPY m).Vs.erase z) ?_
      (Finset.erase_subset _ _) ?_ ?_ ?_ ?_ ?_ hK ?_⟩
    · intro y hy
      rw [Finset.mem_erase, Finset.mem_erase, cap_Vs]
      exact ⟨fun h ↦ ⟨h.1, hY hy⟩, fun h ↦ ⟨h.1, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩⟩
    · rw [hK1, Finset.mem_erase, cap_Vs]
      exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩,
        fun _ ↦ ⟨fun h ↦ huY (h ▸ hz), Finset.mem_insert_self _ _⟩⟩
    · rw [hK2, Finset.mem_erase, cap_Vs]
      exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩,
        fun _ ↦ ⟨fun h ↦ hwY (h ▸ hz), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩⟩
    · intro _; simp [hK1, card_couple₁]
    · intro _; simp [hK2, card_couple₂]
    · intro h; exact absurd h (by decide)
    · intro _ h₁ h₂
      obtain ⟨a, ha⟩ := h₁
      obtain ⟨b, hb⟩ := h₂
      have haK := Finset.mem_inter.mp ha
      have hbK := Finset.mem_inter.mp hb
      have hchain := alternating_chain hcl hCE hC.connected haK.1 hbK.1
      have key : ∀ k, Relation.ReflTransGen (Δ.SideLink C Y) a k →
          k ∈ couple₁ hPY m ∨ ∃ a' ∈ C ∩ Δ.bd Y ∩ couple₁ hPY m, ∃ b' ∈ C ∩ Δ.bd Y ∩ couple₂ hPY m,
            Relation.ReflTransGen (Δ.AdjIn (Δ.sidePart C Y)) a' b' := by
        intro k hk
        induction hk with
        | refl => exact Or.inl haK.2
        | @tail k k' _ hkk' ih =>
          rcases ih with hk₁ | hex
          · obtain ⟨hkK, hk'K, hlk | hlk⟩ := hkk'
            · by_cases hk'₁ : k' ∈ couple₁ hPY m
              · exact Or.inl hk'₁
              · exact Or.inr ⟨k, Finset.mem_inter.mpr ⟨hkK, hk₁⟩, k', Finset.mem_inter.mpr ⟨hk'K,
                  (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hk'K).2)).mpr hk'₁⟩,
                  hlk⟩
            · by_cases hk'₁ : k' ∈ couple₁ hPY m
              · exact Or.inl hk'₁
              · exfalso
                exact hnocross h4 k (Finset.mem_inter.mpr ⟨hkK, hk₁⟩) k' (Finset.mem_inter.mpr ⟨hk'K,
                  (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hk'K).2)).mpr hk'₁⟩)
                  hlk
          · exact Or.inr hex
      rcases key b hchain with hb₁ | hex
      · exact absurd hb₁ (notMem_couple₁_of_mem_couple₂ hPY m hbK.2)
      · exact hex

/-- **Descent to the cap factor, new vertex `u`.**  From a Hamilton cycle of `Δ` minus the
outer end of the first cut edge. -/
theorem descent_cap_u {C : Finset ℕ}
    (hC : Δ.IsHamCycle (Δ.Vs.erase (innerEnd hPYc (bdEmb hPY 0))) C) (hV3 : 3 ≤ Δ.Vs.card)
    (hYne : Y.Nonempty) (hYc2 : 2 ≤ (Δ.Vs \ Y).card) (hB : ¬ (cap hPY m).IsHamiltonian) :
    ∃ C', (cap hPY m).IsHamCycle ((cap hPY m).Vs.erase (freshV (Δ.pole Y))) C' := by
  classical
  set d := bdEmb hPY 0 with hddef
  set a := innerEnd hPYc d with hadef
  have hdbd : d ∈ Δ.bd Y := by rw [hddef, ← dangling_pole]; exact bdEmb_mem hPY 0
  have hd₁ : d ∈ couple₁ hPY m := Finset.mem_insert_self _ _
  have haV : a ∈ Δ.Vs \ Y := innerEnd_compl_mem hcl hPYc hdbd
  have hSV : Δ.Vs.erase a ⊆ Δ.Vs := Finset.erase_subset a Δ.Vs
  have h2 : 2 ≤ (Δ.Vs.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp haV).1]; omega
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset _)
  have hyS : ∀ y ∈ Y, y ∈ Δ.Vs.erase a :=
    fun y hy ↦ Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp haV).2 (h ▸ hy), hY hy⟩
  obtain ⟨y, hyY⟩ := hYne
  obtain ⟨x, hx, hxa⟩ := Finset.exists_mem_ne (by omega : 1 < (Δ.Vs \ Y).card) a
  have hK : (C ∩ Δ.bd Y).Nonempty := K_nonempty hC hyY (hyS y hyY) hx
    (Finset.mem_erase.mpr ⟨hxa, (Finset.mem_sdiff.mp hx).1⟩)
  have hKeven : Even (C ∩ Δ.bd Y).card := K_even hC (fun y hy ↦ Or.inl (hyS y hy))
  -- `d` is not an edge of `C`
  have hdC : d ∉ C := by
    intro h
    obtain ⟨i, hi⟩ := ends_innerEnd_compl hcl hPYc hdbd
    have := (mem_edgesIn.mp (hC.subset h)).2 i
    rw [hi] at this
    exact (Finset.mem_erase.mp this).1 rfl
  have hKle : (C ∩ Δ.bd Y).card ≤ 3 := by
    have hsub : C ∩ Δ.bd Y ⊆ (Δ.bd Y).erase d := by
      intro x hx
      rw [Finset.mem_inter] at hx
      exact Finset.mem_erase.mpr ⟨fun h ↦ hdC (h ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hdbd, hbd4] at this
    exact this
  have h2' : (C ∩ Δ.bd Y).card = 2 := by
    obtain ⟨t, ht⟩ := hKeven
    have := Finset.card_pos.mpr hK
    omega
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have huV : freshV (Δ.pole Y) ∈ (cap hPY m).Vs := by rw [cap_Vs]; exact Finset.mem_insert_self _ _
  have hwV : freshV (Δ.pole Y) + 1 ∈ (cap hPY m).Vs := by
    rw [cap_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- the two cut edges lie in the same couple, else the cap is Hamiltonian
  have hsame : ∀ p ∈ C ∩ Δ.bd Y, ∀ q ∈ C ∩ Δ.bd Y, (p ∈ couple₁ hPY m ↔ q ∈ couple₁ hPY m) := by
    intro p hp q hq
    by_contra hne
    have key : ∀ p ∈ C ∩ Δ.bd Y, ∀ q ∈ C ∩ Δ.bd Y, p ∈ couple₁ hPY m → q ∉ couple₁ hPY m → False := by
      intro p hp q hq hp₁ hq₁
      have hq₂ : q ∈ couple₂ hPY m :=
        (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hq).2)).mpr hq₁
      have hpq : p ≠ q := fun h ↦ hq₁ (h ▸ hp₁)
      obtain ⟨p', q', -, hK'⟩ := Finset.card_eq_two.mp h2'
      have hmem : ∀ x ∈ C ∩ Δ.bd Y, x = p ∨ x = q := by
        intro x hx
        rw [hK', Finset.mem_insert, Finset.mem_singleton] at hx hp hq
        rcases hx with rfl | rfl <;> rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hpq
      have hK1 : C ∩ Δ.bd Y ∩ couple₁ hPY m = {p} := by
        ext x
        rw [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hx₁⟩
          rcases hmem x hx with rfl | rfl
          · rfl
          · exact absurd hx₁ hq₁
        · rintro rfl; exact ⟨hp, hp₁⟩
      have hK2 : C ∩ Δ.bd Y ∩ couple₂ hPY m = {q} := by
        ext x
        rw [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hx₂⟩
          rcases hmem x hx with rfl | rfl
          · exact absurd hp₁ (notMem_couple₁_of_mem_couple₂ hPY m hx₂)
          · rfl
        · rintro rfl; exact ⟨hq, hq₂⟩
      apply hB
      refine ⟨_, cap_hamCycle hind hPY m hC true (T := (cap hPY m).Vs) ?_ (fun x hx ↦ hx)
        ?_ ?_ ?_ ?_ ?_ hK ?_⟩
      · intro y hy
        rw [cap_Vs]
        exact ⟨fun _ ↦ hyS y hy, fun _ ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩
      · rw [hK1]; exact ⟨fun _ ↦ ⟨p, Finset.mem_singleton_self _⟩, fun _ ↦ huV⟩
      · rw [hK2]; exact ⟨fun _ ↦ ⟨q, Finset.mem_singleton_self _⟩, fun _ ↦ hwV⟩
      · intro _; simp [hK1]
      · intro _; simp [hK2]
      · intro _
        exact ⟨⟨p, by rw [hK1]; exact Finset.mem_singleton_self _⟩,
          ⟨q, by rw [hK2]; exact Finset.mem_singleton_self _⟩⟩
      · intro h; exact absurd h (by decide)
    by_cases hp₁ : p ∈ couple₁ hPY m
    · exact key p hp q hq hp₁ (fun hq₁ ↦ hne ⟨fun _ ↦ hq₁, fun _ ↦ hp₁⟩)
    · have hq₁ : q ∈ couple₁ hPY m := by
        by_contra hq₁; exact hne ⟨fun h ↦ absurd h hp₁, fun h ↦ absurd h hq₁⟩
      exact key q hq p hp hq₁ hp₁
  -- hence the cut edges of `C` form the second couple
  have hK2 : C ∩ Δ.bd Y = couple₂ hPY m := by
    rcases K_eq_couple_of_two hPY m (C := C) h2' hsame with h | h
    · exfalso
      exact hdC (Finset.mem_inter.mp (h ▸ hd₁ : d ∈ C ∩ Δ.bd Y)).1
    · exact h
  have hK1' : C ∩ Δ.bd Y ∩ couple₁ hPY m = ∅ := by
    rw [hK2, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter] at hx
    exact notMem_couple₁_of_mem_couple₂ hPY m hx.1 hx.2
  have hK2' : C ∩ Δ.bd Y ∩ couple₂ hPY m = couple₂ hPY m := by
    rw [hK2, Finset.inter_self]
  refine ⟨_, cap_hamCycle hind hPY m hC false
    (T := (cap hPY m).Vs.erase (freshV (Δ.pole Y))) ?_ (Finset.erase_subset _ _) ?_ ?_ ?_ ?_ ?_ hK ?_⟩
  · intro y hy
    rw [Finset.mem_erase, cap_Vs]
    exact ⟨fun _ ↦ hyS y hy, fun _ ↦ ⟨fun h ↦ huY (h ▸ hy),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩⟩
  · rw [hK1', Finset.mem_erase]
    exact ⟨fun h ↦ absurd rfl h.1, fun h ↦ absurd h Finset.not_nonempty_empty⟩
  · rw [hK2', Finset.mem_erase]
    exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ ⟨by omega, hwV⟩⟩
  · intro h; rw [hK1'] at h; exact absurd h Finset.not_nonempty_empty
  · intro _; simp [hK2', card_couple₂]
  · intro h; exact absurd h (by decide)
  · intro _ h; rw [hK1'] at h; exact absurd h Finset.not_nonempty_empty

/-- **Descent to the cap factor, new vertex `w`.**  From a Hamilton cycle of `Δ` minus the
outer end of the first cut edge of the second couple. -/
theorem descent_cap_w {C : Finset ℕ}
    (hC : Δ.IsHamCycle (Δ.Vs.erase (innerEnd hPYc (bdEmb hPY (other m)))) C) (hV3 : 3 ≤ Δ.Vs.card)
    (hYne : Y.Nonempty) (hYc2 : 2 ≤ (Δ.Vs \ Y).card) (hB : ¬ (cap hPY m).IsHamiltonian) :
    ∃ C', (cap hPY m).IsHamCycle ((cap hPY m).Vs.erase (freshV (Δ.pole Y) + 1)) C' := by
  classical
  set d := bdEmb hPY (other m) with hddef
  set a := innerEnd hPYc d with hadef
  have hdbd : d ∈ Δ.bd Y := by rw [hddef, ← dangling_pole]; exact bdEmb_mem hPY _
  have hd₂ : d ∈ couple₂ hPY m := Finset.mem_insert_self _ _
  have hd₁ : d ∉ couple₁ hPY m := notMem_couple₁_of_mem_couple₂ hPY m hd₂
  have haV : a ∈ Δ.Vs \ Y := innerEnd_compl_mem hcl hPYc hdbd
  have hSV : Δ.Vs.erase a ⊆ Δ.Vs := Finset.erase_subset a Δ.Vs
  have h2 : 2 ≤ (Δ.Vs.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp haV).1]; omega
  have hCE : C ⊆ Δ.Es := hC.subset.trans (edgesIn_subset _)
  have hyS : ∀ y ∈ Y, y ∈ Δ.Vs.erase a :=
    fun y hy ↦ Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp haV).2 (h ▸ hy), hY hy⟩
  obtain ⟨y, hyY⟩ := hYne
  obtain ⟨x, hx, hxa⟩ := Finset.exists_mem_ne (by omega : 1 < (Δ.Vs \ Y).card) a
  have hK : (C ∩ Δ.bd Y).Nonempty := K_nonempty hC hyY (hyS y hyY) hx
    (Finset.mem_erase.mpr ⟨hxa, (Finset.mem_sdiff.mp hx).1⟩)
  have hKeven : Even (C ∩ Δ.bd Y).card := K_even hC (fun y hy ↦ Or.inl (hyS y hy))
  have hdC : d ∉ C := by
    intro h
    obtain ⟨i, hi⟩ := ends_innerEnd_compl hcl hPYc hdbd
    have := (mem_edgesIn.mp (hC.subset h)).2 i
    rw [hi] at this
    exact (Finset.mem_erase.mp this).1 rfl
  have hKle : (C ∩ Δ.bd Y).card ≤ 3 := by
    have hsub : C ∩ Δ.bd Y ⊆ (Δ.bd Y).erase d := by
      intro x hx
      rw [Finset.mem_inter] at hx
      exact Finset.mem_erase.mpr ⟨fun h ↦ hdC (h ▸ hx.1), hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hdbd, hbd4] at this
    exact this
  have h2' : (C ∩ Δ.bd Y).card = 2 := by
    obtain ⟨t, ht⟩ := hKeven
    have := Finset.card_pos.mpr hK
    omega
  have huY : freshV (Δ.pole Y) ∉ Y := freshV_notMem (P := Δ.pole Y)
  have hwY : freshV (Δ.pole Y) + 1 ∉ Y := freshV_succ_notMem (P := Δ.pole Y)
  have huV : freshV (Δ.pole Y) ∈ (cap hPY m).Vs := by rw [cap_Vs]; exact Finset.mem_insert_self _ _
  have hwV : freshV (Δ.pole Y) + 1 ∈ (cap hPY m).Vs := by
    rw [cap_Vs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hsame : ∀ p ∈ C ∩ Δ.bd Y, ∀ q ∈ C ∩ Δ.bd Y, (p ∈ couple₁ hPY m ↔ q ∈ couple₁ hPY m) := by
    intro p hp q hq
    by_contra hne
    have key : ∀ p ∈ C ∩ Δ.bd Y, ∀ q ∈ C ∩ Δ.bd Y, p ∈ couple₁ hPY m → q ∉ couple₁ hPY m → False := by
      intro p hp q hq hp₁ hq₁
      have hq₂ : q ∈ couple₂ hPY m :=
        (mem_couple₂_iff hPY m (mem_dangling_Y (Finset.mem_inter.mp hq).2)).mpr hq₁
      have hpq : p ≠ q := fun h ↦ hq₁ (h ▸ hp₁)
      obtain ⟨p', q', -, hK'⟩ := Finset.card_eq_two.mp h2'
      have hmem : ∀ x ∈ C ∩ Δ.bd Y, x = p ∨ x = q := by
        intro x hx
        rw [hK', Finset.mem_insert, Finset.mem_singleton] at hx hp hq
        rcases hx with rfl | rfl <;> rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hpq
      have hK1 : C ∩ Δ.bd Y ∩ couple₁ hPY m = {p} := by
        ext x
        rw [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hx₁⟩
          rcases hmem x hx with rfl | rfl
          · rfl
          · exact absurd hx₁ hq₁
        · rintro rfl; exact ⟨hp, hp₁⟩
      have hK2 : C ∩ Δ.bd Y ∩ couple₂ hPY m = {q} := by
        ext x
        rw [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hx₂⟩
          rcases hmem x hx with rfl | rfl
          · exact absurd hp₁ (notMem_couple₁_of_mem_couple₂ hPY m hx₂)
          · rfl
        · rintro rfl; exact ⟨hq, hq₂⟩
      apply hB
      refine ⟨_, cap_hamCycle hind hPY m hC true (T := (cap hPY m).Vs) ?_ (fun x hx ↦ hx)
        ?_ ?_ ?_ ?_ ?_ hK ?_⟩
      · intro y hy
        rw [cap_Vs]
        exact ⟨fun _ ↦ hyS y hy, fun _ ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩
      · rw [hK1]; exact ⟨fun _ ↦ ⟨p, Finset.mem_singleton_self _⟩, fun _ ↦ huV⟩
      · rw [hK2]; exact ⟨fun _ ↦ ⟨q, Finset.mem_singleton_self _⟩, fun _ ↦ hwV⟩
      · intro _; simp [hK1]
      · intro _; simp [hK2]
      · intro _
        exact ⟨⟨p, by rw [hK1]; exact Finset.mem_singleton_self _⟩,
          ⟨q, by rw [hK2]; exact Finset.mem_singleton_self _⟩⟩
      · intro h; exact absurd h (by decide)
    by_cases hp₁ : p ∈ couple₁ hPY m
    · exact key p hp q hq hp₁ (fun hq₁ ↦ hne ⟨fun _ ↦ hq₁, fun _ ↦ hp₁⟩)
    · have hq₁ : q ∈ couple₁ hPY m := by
        by_contra hq₁; exact hne ⟨fun h ↦ absurd h hp₁, fun h ↦ absurd h hq₁⟩
      exact key q hq p hp hq₁ hp₁
  -- hence the cut edges of `C` form the first couple
  have hK1 : C ∩ Δ.bd Y = couple₁ hPY m := by
    rcases K_eq_couple_of_two hPY m (C := C) h2' hsame with h | h
    · exact h
    · exfalso
      exact hdC (Finset.mem_inter.mp (h ▸ hd₂ : d ∈ C ∩ Δ.bd Y)).1
  have hK2' : C ∩ Δ.bd Y ∩ couple₂ hPY m = ∅ := by
    rw [hK1, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter] at hx
    exact notMem_couple₁_of_mem_couple₂ hPY m hx.2 hx.1
  have hK1' : C ∩ Δ.bd Y ∩ couple₁ hPY m = couple₁ hPY m := by
    rw [hK1, Finset.inter_self]
  refine ⟨_, cap_hamCycle hind hPY m hC false
    (T := (cap hPY m).Vs.erase (freshV (Δ.pole Y) + 1)) ?_ (Finset.erase_subset _ _) ?_ ?_ ?_ ?_ ?_
    hK ?_⟩
  · intro y hy
    rw [Finset.mem_erase, cap_Vs]
    exact ⟨fun _ ↦ hyS y hy, fun _ ↦ ⟨fun h ↦ hwY (h ▸ hy),
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)⟩⟩
  · rw [hK1', Finset.mem_erase]
    exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ ⟨by omega, huV⟩⟩
  · rw [hK2', Finset.mem_erase]
    exact ⟨fun h ↦ absurd rfl h.1, fun h ↦ absurd h Finset.not_nonempty_empty⟩
  · intro _; simp [hK1', card_couple₁]
  · intro h; rw [hK2'] at h; exact absurd h Finset.not_nonempty_empty
  · intro h; exact absurd h (by decide)
  · intro _ _ h; rw [hK2'] at h; exact absurd h Finset.not_nonempty_empty

end Descent

end FinGraph
end GraphPuzzles
