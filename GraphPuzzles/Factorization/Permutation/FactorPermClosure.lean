import GraphPuzzles.Factorization.Permutation.FactorPermPairing
import GraphPuzzles.Factorization.Hypohamiltonian.FactorHypoClass
import GraphPuzzles.Factorization.FactorMain

/-!
# Permutation snarks form a good class

The cap and join factors of a permutation snark along a cycle-separating `4`-cut are again
permutation graphs: the rim segments inside the shore, closed through the new vertices (cap) or
by the new edges (join), are the rims of the factor, and the spokes inside the shore together
with the new edge `uw` (cap) are its spokes.  Hence Theorem C applies to permutation snarks
(Máčajová–Škoviera's closure assertion, proved here).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Δ : FinGraph} {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Δ.IsPermGraph V₁ V₂ R₁ R₂)
  (hcl : Δ.IsClosed) (hcub : Δ.IsCubic) (hnc : ¬ Δ.Colourable) {X : Finset ℕ} (hX : Δ.CycSep X)
include hP hcl hcub hnc hX

section Couples

/-- The couples of the pairing of a cycle-separating `4`-cut are the pairs of cut edges of the
two rims; when the first cut edge lies on `R₁`, the first couple is the `R₁`-pair. -/
theorem IsPermGraph.couples_rims (hPX : (Δ.pole X).IsPole4) (m : Fin 3)
    (hm : IsoWith hPX m ∨ HetWith hPX m) (h0 : bdEmb hPX 0 ∈ R₁) :
    couple₁ hPX m ⊆ R₁ ∧ couple₂ hPX m ⊆ R₂ := by
  classical
  obtain ⟨h1, h2, hs⟩ := hP.cycSep_structure hcl hcub hnc hX
  have hbd : ∀ k, bdEmb hPX k ∈ Δ.bd X := fun k ↦ by rw [← dangling_pole]; exact bdEmb_mem hPX k
  have hrim : ∀ d ∈ Δ.bd X, d ∈ R₁ ∨ d ∈ R₂ := by
    intro d hd
    have hE := bd_subset _ hd
    have := hcl d hE 0
    rw [← hP.union, Finset.mem_union] at this
    rcases this with h | h
    · rcases hP.edge_at_V₁ hE h with h' | h'
      · exact Or.inl h'
      · exact absurd (Finset.mem_inter.mpr ⟨hd, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
    · rcases hP.edge_at_V₂ hcl hE h with h' | h'
      · exact Or.inr h'
      · exact absurd (Finset.mem_inter.mpr ⟨hd, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
  have hc₁ : couple₁ hPX m ⊆ R₁ := by
    rw [couple₁_eq]
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact h0
    · exact hP.partner_mem_rim hcl hcub hnc hX hPX m hm (Finset.mem_inter.mpr ⟨h0, hbd 0⟩)
  refine ⟨hc₁, ?_⟩
  -- the second couple lies on `R₂`: otherwise `R₁` would contain all four cut edges
  have hother : bdEmb hPX (other m) ∈ R₂ := by
    rcases hrim _ (hbd (other m)) with h | h
    · exfalso
      have hc₂ : couple₂ hPX m ⊆ R₁ := by
        rw [couple₂_eq]
        intro d hd
        rw [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact h
        · exact hP.partner_mem_rim hcl hcub hnc hX hPX m hm (Finset.mem_inter.mpr ⟨h, hbd _⟩)
      have hall : Δ.bd X ⊆ R₁ ∩ Δ.bd X := by
        intro d hd
        rcases mem_couple_or hPX m hd with h' | h'
        · exact Finset.mem_inter.mpr ⟨hc₁ h', hd⟩
        · exact Finset.mem_inter.mpr ⟨hc₂ h', hd⟩
      have := Finset.card_le_card hall
      rw [hX.2.1, h1] at this
      omega
    · exact h
  rw [couple₂_eq]
  intro d hd
  rw [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact hother
  · exact (hP.swap hcl).partner_mem_rim hcl hcub hnc hX hPX m hm (Finset.mem_inter.mpr ⟨hother, hbd _⟩)

end Couples

section Cap

variable (hPX : (Δ.pole X).IsPole4) (m : Fin 3) (hiso : IsoWith hPX m)
  (hR₁ : couple₁ hPX m ⊆ R₁) (hR₂ : couple₂ hPX m ⊆ R₂)
include hiso hR₁ hR₂

/-- **The cap factor is a permutation graph** (first couple on `R₁`). -/
theorem IsPermGraph.cap_isPermGraph :
    (cap hPX m).IsPermGraph (insert (freshV (Δ.pole X)) (X ∩ V₁))
      (insert (freshV (Δ.pole X) + 1) (X ∩ V₂)) (Δ.sidePart R₁ X) (Δ.sidePart R₂ X) := by
  classical
  have hg5 := hP.girth5 hcl hcub hnc
  have hc4 := hP.cyc4Conn hcl hcub hnc
  have hind := hX.independent hcl hcub hg5 hc4
  have hXV := hX.1
  obtain ⟨h1, h2, hs⟩ := hP.cycSep_structure hcl hcub hnc hX
  have huX : freshV (Δ.pole X) ∉ X := freshV_notMem (P := Δ.pole X)
  have hwX : freshV (Δ.pole X) + 1 ∉ X := freshV_succ_notMem (P := Δ.pole X)
  have hV₁V := hP.V₁_subset
  have hV₂V := hP.V₂_subset
  have h12 : ∀ e ∈ R₁, e ∉ R₂ := fun e he h ↦ Finset.disjoint_left.mp hP.disjoint_rims he h
  have hK₁ : R₁ ∩ Δ.bd X ∩ couple₁ hPX m = couple₁ hPX m :=
    Finset.inter_eq_right.mpr (fun d hd ↦ Finset.mem_inter.mpr ⟨hR₁ hd, couple₁_subset_bd hPX m hd⟩)
  have hK₁' : R₁ ∩ Δ.bd X ∩ couple₂ hPX m = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    rw [Finset.mem_inter, Finset.mem_inter] at hd
    exact h12 d hd.1.1 (hR₂ hd.2)
  have hK₂ : R₂ ∩ Δ.bd X ∩ couple₂ hPX m = couple₂ hPX m :=
    Finset.inter_eq_right.mpr (fun d hd ↦ Finset.mem_inter.mpr ⟨hR₂ hd, couple₂_subset_bd hPX m hd⟩)
  have hK₂' : R₂ ∩ Δ.bd X ∩ couple₁ hPX m = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    rw [Finset.mem_inter, Finset.mem_inter] at hd
    exact h12 d (hR₁ hd.2) hd.1.1
  have hK₁ne : (R₁ ∩ Δ.bd X).Nonempty := by rw [← Finset.card_pos, h1]; omega
  have hK₂ne : (R₂ ∩ Δ.bd X).Nonempty := by rw [← Finset.card_pos, h2]; omega
  -- the two rims of the cap
  have hham₁ := cap_hamCycle hind hPX m hP.ham₁ false
    (T := insert (freshV (Δ.pole X)) (X ∩ V₁))
    (fun y hy ↦ by
      rw [Finset.mem_insert, Finset.mem_inter]
      exact ⟨fun h ↦ (h.resolve_left (fun h' ↦ huX (h' ▸ hy))).2, fun h ↦ Or.inr ⟨hy, h⟩⟩)
    (by intro x hx; rw [Finset.mem_insert, Finset.mem_inter] at hx; rw [Finset.mem_insert, Finset.mem_insert]
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hx.1))
    (by rw [hK₁]; exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ Finset.mem_insert_self _ _⟩)
    (by rw [hK₁', Finset.mem_insert, Finset.mem_inter]
        exact ⟨fun h ↦ absurd h (by rintro (h | h); omega; exact hwX h.1),
          fun h ↦ absurd h Finset.not_nonempty_empty⟩)
    (fun _ ↦ by simp [hK₁, card_couple₁])
    (fun h ↦ by rw [hK₁'] at h; exact absurd h Finset.not_nonempty_empty)
    (fun h ↦ absurd h (by decide)) hK₁ne
    (fun _ _ h ↦ by rw [hK₁'] at h; exact absurd h Finset.not_nonempty_empty)
  have hham₂ := cap_hamCycle hind hPX m hP.ham₂ false
    (T := insert (freshV (Δ.pole X) + 1) (X ∩ V₂))
    (fun y hy ↦ by
      rw [Finset.mem_insert, Finset.mem_inter]
      exact ⟨fun h ↦ (h.resolve_left (fun h' ↦ hwX (h' ▸ hy))).2, fun h ↦ Or.inr ⟨hy, h⟩⟩)
    (by intro x hx; rw [Finset.mem_insert, Finset.mem_inter] at hx; rw [Finset.mem_insert, Finset.mem_insert]
        rcases hx with rfl | hx
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hx.1))
    (by rw [hK₂', Finset.mem_insert, Finset.mem_inter]
        exact ⟨fun h ↦ absurd h (by rintro (h | h); omega; exact huX h.1),
          fun h ↦ absurd h Finset.not_nonempty_empty⟩)
    (by rw [hK₂]; exact ⟨fun _ ↦ ⟨_, Finset.mem_insert_self _ _⟩, fun _ ↦ Finset.mem_insert_self _ _⟩)
    (fun h ↦ by rw [hK₂'] at h; exact absurd h Finset.not_nonempty_empty)
    (fun _ ↦ by simp [hK₂, card_couple₂])
    (fun h ↦ absurd h (by decide)) hK₂ne
    (fun _ h ↦ by rw [hK₂'] at h; exact absurd h Finset.not_nonempty_empty)
  simp only [Bool.false_eq_true, if_false, Finset.union_empty] at hham₁ hham₂
  -- the parity of the segments
  have hs_even : Even (X ∩ V₁).card := (hP.segment_parity hcl hcub hnc hX hPX m).1 hiso
  have hs_eq : (X ∩ V₁).card = (X ∩ V₂).card := hP.card_inter_eq hcl hcub hnc hX
  have hs_pos : 0 < (X ∩ V₁).card := by
    obtain ⟨d, hd⟩ := hK₁ne
    obtain ⟨i, hi, -⟩ := bd_side (Finset.mem_inter.mp hd).2
    exact Finset.card_pos.mpr ⟨_, Finset.mem_inter.mpr ⟨hi,
      (mem_edgesIn.mp (hP.ham₁.subset (Finset.mem_inter.mp hd).1)).2 i⟩⟩
  have huV₁ : freshV (Δ.pole X) ∉ X ∩ V₁ := fun h ↦ huX (Finset.mem_inter.mp h).1
  have hwV₂ : freshV (Δ.pole X) + 1 ∉ X ∩ V₂ := fun h ↦ hwX (Finset.mem_inter.mp h).1
  -- the spokes of the cap
  have hspokes : (cap hPX m).bd (insert (freshV (Δ.pole X)) (X ∩ V₁)) =
      (Δ.bd V₁ ∩ Δ.edgesIn X) ∪ {freshE (Δ.pole X)} := by
    ext e
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_inter]
    constructor
    · intro he
      have heE := bd_subset _ he
      rw [cap_Es, Finset.mem_insert] at heE
      rcases heE with rfl | heP
      · exact Or.inr rfl
      · left
        -- `e` is old: a rim edge lies inside a rim, so `e` is a spoke inside `X`
        have heΔ : e ∈ Δ.Es := by
          rw [pole_Es, Finset.mem_union] at heP
          exact heP.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h)
        have hnot₁ : e ∉ R₁ := by
          intro h
          have hin : e ∈ (cap hPX m).edgesIn (insert (freshV (Δ.pole X)) (X ∩ V₁)) :=
            hham₁.subset (mem_sidePart_iff.mpr ⟨h, by
              rw [pole_Es, Finset.mem_union] at heP; exact heP⟩)
          exact Finset.disjoint_left.mp (disjoint_edgesIn_bd _) hin he
        have hnot₂ : e ∉ R₂ := by
          intro h
          have hin : e ∈ (cap hPX m).edgesIn (insert (freshV (Δ.pole X) + 1) (X ∩ V₂)) :=
            hham₂.subset (mem_sidePart_iff.mpr ⟨h, by
              rw [pole_Es, Finset.mem_union] at heP; exact heP⟩)
          rw [mem_edgesIn] at hin
          obtain ⟨i, hi, -⟩ := bd_side he
          have := hin.2 i
          rw [Finset.mem_insert, Finset.mem_inter] at hi this
          rcases hi with hi | hi <;> rcases this with h' | h'
          · omega
          · exact huX (hi ▸ h'.1)
          · exact hwX (h' ▸ hi.1)
          · exact Finset.disjoint_left.mp hP.disj hi.2 h'.2
        have hsp : e ∈ Δ.bd V₁ := by
          have h0 := hcl e heΔ 0
          rw [← hP.union, Finset.mem_union] at h0
          rcases h0 with h | h
          · exact (hP.edge_at_V₁ heΔ h).resolve_left hnot₁
          · exact (hP.edge_at_V₂ hcl heΔ h).resolve_left hnot₂
        refine ⟨hsp, ?_⟩
        rw [pole_Es, Finset.mem_union] at heP
        rcases heP with h | h
        · exact h
        · exact absurd (Finset.mem_inter.mpr ⟨h, hsp⟩) (fun h' ↦ Finset.notMem_empty _ (hs ▸ h'))
    · rintro (⟨hsp, hin⟩ | rfl)
      · have heP : e ∈ (Δ.pole X).Es := by rw [pole_Es, Finset.mem_union]; exact Or.inl hin
        rw [mem_bd]
        refine ⟨by rw [cap_Es]; exact Finset.mem_insert_of_mem heP, ?_⟩
        rw [cap_ends_eq hPX m heP, cap_ends_eq hPX m heP]
        have hin0 : (Δ.pole X).ends e 0 ∈ (Δ.pole X).Vs := (mem_edgesIn.mp hin).2 0
        have hin1 : (Δ.pole X).ends e 1 ∈ (Δ.pole X).Vs := (mem_edgesIn.mp hin).2 1
        rw [if_pos hin0, if_pos hin1]
        rw [mem_bd] at hsp
        simp only [pole_ends, Finset.mem_insert, Finset.mem_inter]
        have h0 : Δ.ends e 0 ≠ freshV (Δ.pole X) := fun h ↦ huX (h ▸ hin0)
        have h1 : Δ.ends e 1 ≠ freshV (Δ.pole X) := fun h ↦ huX (h ▸ hin1)
        intro hiff
        apply hsp.2
        constructor
        · intro h; exact ((hiff.mp (Or.inr ⟨hin0, h⟩)).resolve_left h1).2
        · intro h; exact ((hiff.mpr (Or.inr ⟨hin1, h⟩)).resolve_left h0).2
      · rw [mem_bd]
        refine ⟨by rw [cap_Es]; exact Finset.mem_insert_self _ _, ?_⟩
        rw [cap_ends_new, cap_ends_new, if_pos rfl, if_neg (by decide)]
        simp only [Finset.mem_insert, Finset.mem_inter]
        intro h
        have := h.mp (by simp)
        rcases this with h' | h'
        · omega
        · exact hwX h'.1
  refine ⟨?_, ?_, hham₁, hham₂, ?_, ?_, ?_, ?_⟩
  · -- disjoint
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_insert, Finset.mem_inter] at hx hx'
    rcases hx with rfl | hx <;> rcases hx' with h | h
    · omega
    · exact huX h.1
    · exact hwX (h ▸ hx.1)
    · exact Finset.disjoint_left.mp hP.disj hx.2 h.2
  · -- union
    rw [cap_Vs]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_inter]
    constructor
    · rintro ((h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h.1)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h.1)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · have := hXV h
        rw [← hP.union, Finset.mem_union] at this
        rcases this with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr (Or.inr ⟨h, h'⟩)
  · -- induced first rim
    apply Finset.Subset.antisymm
    · intro e he
      have heE := (mem_edgesIn.mp he).1
      rw [cap_Es, Finset.mem_insert] at heE
      rcases heE with rfl | heP
      · exfalso
        have := (mem_edgesIn.mp he).2 1
        rw [cap_ends_new, if_neg (by decide), Finset.mem_insert, Finset.mem_inter] at this
        rcases this with h | h
        · omega
        · exact hwX h.1
      · rw [mem_sidePart_iff]
        by_cases hin : ∀ i, Δ.ends e i ∈ X
        · have heX : e ∈ Δ.edgesIn X := mem_edgesIn.mpr ⟨by
            rw [pole_Es, Finset.mem_union] at heP
            exact heP.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h), hin⟩
          have heV : e ∈ Δ.edgesIn V₁ := by
            rw [mem_edgesIn]
            refine ⟨(mem_edgesIn.mp heX).1, fun i ↦ ?_⟩
            have := (mem_edgesIn.mp he).2 i
            rw [cap_ends_eq hPX m heP,
              if_pos (show (Δ.pole X).ends e i ∈ (Δ.pole X).Vs from hin i), Finset.mem_insert,
              Finset.mem_inter] at this
            rcases this with h | h
            · exact absurd (h ▸ hin i) huX
            · exact h.2
          rw [hP.induced₁] at heV
          exact ⟨heV, Or.inl heX⟩
        · push Not at hin
          obtain ⟨i, hi⟩ := hin
          have := (mem_edgesIn.mp he).2 i
          rw [cap_ends_eq hPX m heP,
            if_neg (show (Δ.pole X).ends e i ∉ (Δ.pole X).Vs from hi)] at this
          split_ifs at this with hc₁
          · exact ⟨hR₁ hc₁, Or.inr (couple₁_subset_bd hPX m hc₁)⟩
          · exfalso
            rw [Finset.mem_insert, Finset.mem_inter] at this
            rcases this with h | h
            · omega
            · exact hwX h.1
    · exact hham₁.subset
  · -- induced second rim
    apply Finset.Subset.antisymm
    · intro e he
      have heE := (mem_edgesIn.mp he).1
      rw [cap_Es, Finset.mem_insert] at heE
      rcases heE with rfl | heP
      · exfalso
        have := (mem_edgesIn.mp he).2 0
        rw [cap_ends_new, if_pos rfl, Finset.mem_insert, Finset.mem_inter] at this
        rcases this with h | h
        · omega
        · exact huX h.1
      · rw [mem_sidePart_iff]
        by_cases hin : ∀ i, Δ.ends e i ∈ X
        · have heX : e ∈ Δ.edgesIn X := mem_edgesIn.mpr ⟨by
            rw [pole_Es, Finset.mem_union] at heP
            exact heP.elim (fun h ↦ edgesIn_subset _ h) (fun h ↦ bd_subset _ h), hin⟩
          have heV : e ∈ Δ.edgesIn V₂ := by
            rw [mem_edgesIn]
            refine ⟨(mem_edgesIn.mp heX).1, fun i ↦ ?_⟩
            have := (mem_edgesIn.mp he).2 i
            rw [cap_ends_eq hPX m heP,
              if_pos (show (Δ.pole X).ends e i ∈ (Δ.pole X).Vs from hin i), Finset.mem_insert,
              Finset.mem_inter] at this
            rcases this with h | h
            · exact absurd (h ▸ hin i) hwX
            · exact h.2
          rw [hP.induced₂] at heV
          exact ⟨heV, Or.inl heX⟩
        · push Not at hin
          obtain ⟨i, hi⟩ := hin
          have := (mem_edgesIn.mp he).2 i
          rw [cap_ends_eq hPX m heP,
            if_neg (show (Δ.pole X).ends e i ∉ (Δ.pole X).Vs from hi)] at this
          split_ifs at this with hc₁
          · exfalso
            rw [Finset.mem_insert, Finset.mem_inter] at this
            rcases this with h | h
            · omega
            · exact huX h.1
          · have hd : e ∈ (Δ.pole X).dangling := mem_dangling.mpr ⟨heP, i, hi⟩
            have hc₂ := (mem_couple₂_iff hPX m hd).mpr hc₁
            exact ⟨hR₂ hc₂, Or.inr (couple₂_subset_bd hPX m hc₂)⟩
    · exact hham₂.subset
  · -- spokes
    intro v hv
    rw [hspokes]
    have hF : (Δ.bd V₁ ∩ Δ.edgesIn X) ∪ {freshE (Δ.pole X)} ⊆ (cap hPX m).Es := by
      intro e he
      rw [Finset.mem_union, Finset.mem_singleton] at he
      rw [cap_Es, Finset.mem_insert]
      rcases he with he | rfl
      · right; rw [pole_Es, Finset.mem_union]; exact Or.inl (Finset.mem_inter.mp he).2
      · exact Or.inl rfl
    rw [cap_Vs, Finset.mem_insert, Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · rw [cap_degIn_u hPX m hF, if_pos (Finset.mem_union_right _ (Finset.mem_singleton_self _))]
      have : ((Δ.bd V₁ ∩ Δ.edgesIn X) ∪ {freshE (Δ.pole X)}) ∩ couple₁ hPX m = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton] at he
        rcases he.1 with h | h
        · exact hP.rim_not_spoke₁ (hR₁ he.2) (Finset.mem_inter.mp h).1
        · exact freshE_notMem ((mem_dangling.mp (couple₁_subset_dangling hPX m (h ▸ he.2))).1)
      rw [this, Finset.card_empty]
    · rw [cap_degIn_w hPX m hF, if_pos (Finset.mem_union_right _ (Finset.mem_singleton_self _))]
      have : ((Δ.bd V₁ ∩ Δ.edgesIn X) ∪ {freshE (Δ.pole X)}) ∩ couple₂ hPX m = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton] at he
        rcases he.1 with h | h
        · exact hP.rim_not_spoke₂ hcl (hR₂ he.2) (Finset.mem_inter.mp h).1
        · exact freshE_notMem ((mem_dangling.mp (couple₂_subset_dangling hPX m (h ▸ he.2))).1)
      rw [this, Finset.card_empty]
    · rw [degIn_eq_card, cap_halfEdgesIn_old hPX m hF hv, ← degIn_eq_card]
      have herase : ((Δ.bd V₁ ∩ Δ.edgesIn X) ∪ {freshE (Δ.pole X)}).erase (freshE (Δ.pole X)) =
          Δ.bd V₁ ∩ Δ.edgesIn X := by
        rw [Finset.union_singleton, Finset.erase_insert]
        intro h
        exact freshE_notMem (by rw [pole_Es, Finset.mem_union]; exact Or.inl (Finset.mem_inter.mp h).2)
      rw [herase]
      -- every spoke at a vertex of `X` lies inside `X`
      have : Δ.halfEdgesIn (Δ.bd V₁ ∩ Δ.edgesIn X) v = Δ.halfEdgesIn (Δ.bd V₁) v := by
        ext ⟨e, i⟩
        rw [mem_halfEdgesIn, mem_halfEdgesIn, Finset.mem_inter]
        constructor
        · rintro ⟨⟨he, -⟩, hi⟩; exact ⟨he, hi⟩
        · rintro ⟨he, hi⟩
          exact ⟨⟨he, hP.spoke_mem_edgesIn hcl hcub hnc hX he hi hv⟩, hi⟩
      rw [degIn_eq_card, this, ← degIn_eq_card]
      exact hP.spoke v (hXV hv)
  · -- at least three
    rw [Finset.card_insert_of_notMem huV₁]
    obtain ⟨k, hk⟩ := hs_even
    omega

end Cap

section Join

variable (hP' : (Δ.pole (Δ.Vs \ X)).IsPole4) (hPX : (Δ.pole X).IsPole4) (m : Fin 3)
  (hiso : IsoWith hPX m) (hR₁ : couple₁ hP' m ⊆ R₁) (hR₂ : couple₂ hP' m ⊆ R₂)
include hiso hR₁ hR₂

/-- **The join factor is a permutation graph** (first couple on `R₁`). -/
theorem IsPermGraph.join_isPermGraph :
    (join hP' m).IsPermGraph ((Δ.Vs \ X) ∩ V₁) ((Δ.Vs \ X) ∩ V₂)
      ((R₁ ∩ Δ.edgesIn (Δ.Vs \ X)) ∪ {freshE (Δ.pole (Δ.Vs \ X))})
      ((R₂ ∩ Δ.edgesIn (Δ.Vs \ X)) ∪ {freshE (Δ.pole (Δ.Vs \ X)) + 1}) := by
  classical
  have hg5 := hP.girth5 hcl hcub hnc
  have hc4 := hP.cyc4Conn hcl hcub hnc
  have hind := hX.independent hcl hcub hg5 hc4
  have hXV := hX.1
  obtain ⟨h1, h2, hs⟩ := hP.cycSep_structure hcl hcub hnc hX
  have hV₁V := hP.V₁_subset
  have hV₂V := hP.V₂_subset
  have h12 : ∀ e ∈ R₁, e ∉ R₂ := fun e he h ↦ Finset.disjoint_left.mp hP.disjoint_rims he h
  have h2V : 2 ≤ V₁.card := by have := hP.three; omega
  have h2V' : 2 ≤ V₂.card := by rw [hP.card_V₂ hcl]; exact h2V
  have hbd : ∀ k, bdEmb hP' k ∈ Δ.bd X := fun k ↦ by
    rw [← bd_compl hcl, ← dangling_pole]; exact bdEmb_mem hP' k
  have hK₁ : R₁ ∩ Δ.bd X ∩ couple₁ hP' m = couple₁ hP' m :=
    Finset.inter_eq_right.mpr (fun d hd ↦ Finset.mem_inter.mpr ⟨hR₁ hd, by
      have := couple₁_subset_dangling hP' m hd; rwa [dangling_pole, bd_compl hcl] at this⟩)
  have hK₁' : R₁ ∩ Δ.bd X ∩ couple₂ hP' m = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    rw [Finset.mem_inter, Finset.mem_inter] at hd
    exact h12 d hd.1.1 (hR₂ hd.2)
  have hK₂ : R₂ ∩ Δ.bd X ∩ couple₂ hP' m = couple₂ hP' m :=
    Finset.inter_eq_right.mpr (fun d hd ↦ Finset.mem_inter.mpr ⟨hR₂ hd, by
      have := couple₂_subset_dangling hP' m hd; rwa [dangling_pole, bd_compl hcl] at this⟩)
  have hK₂' : R₂ ∩ Δ.bd X ∩ couple₁ hP' m = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    rw [Finset.mem_inter, Finset.mem_inter] at hd
    exact h12 d (hR₁ hd.2) hd.1.1
  have hK₁ne : (R₁ ∩ Δ.bd X).Nonempty := by rw [← Finset.card_pos, h1]; omega
  have hK₂ne : (R₂ ∩ Δ.bd X).Nonempty := by rw [← Finset.card_pos, h2]; omega
  have hc₁ne : (R₁ ∩ Δ.bd X ∩ couple₁ hP' m).Nonempty := by
    rw [hK₁]; exact ⟨_, Finset.mem_insert_self _ _⟩
  have hc₂ne : (R₂ ∩ Δ.bd X ∩ couple₂ hP' m).Nonempty := by
    rw [hK₂]; exact ⟨_, Finset.mem_insert_self _ _⟩
  -- the two rims of the join
  have hham₁ := join_hamCycle hcl hind hP' m hP.ham₁ h2V (T := (Δ.Vs \ X) ∩ V₁)
    (fun x hx ↦ by rw [Finset.mem_inter]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩)
    Finset.inter_subset_left (fun _ ↦ hR₁)
    (fun h ↦ by rw [hK₁'] at h; exact absurd h Finset.not_nonempty_empty) hK₁ne
    (fun _ h ↦ by rw [hK₁'] at h; exact absurd h Finset.not_nonempty_empty)
  have hham₂ := join_hamCycle hcl hind hP' m hP.ham₂ h2V' (T := (Δ.Vs \ X) ∩ V₂)
    (fun x hx ↦ by rw [Finset.mem_inter]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩)
    Finset.inter_subset_left
    (fun h ↦ by rw [hK₂'] at h; exact absurd h Finset.not_nonempty_empty) (fun _ ↦ hR₂) hK₂ne
    (fun h ↦ by rw [hK₂'] at h; exact absurd h Finset.not_nonempty_empty)
  rw [if_pos hc₁ne, if_neg (by rw [hK₁']; exact Finset.not_nonempty_empty), Finset.union_empty]
    at hham₁
  rw [if_neg (by rw [hK₂']; exact Finset.not_nonempty_empty), if_pos hc₂ne, Finset.empty_union]
    at hham₂
  -- the ends of the new edges
  have hnew₁ : ∀ i, (join hP' m).ends (freshE (Δ.pole (Δ.Vs \ X))) i ∈ (Δ.Vs \ X) ∩ V₁ :=
    fun i ↦ (mem_edgesIn.mp (hham₁.subset (Finset.mem_union_right _ (Finset.mem_singleton_self _)))).2 i
  have hnew₂ : ∀ i, (join hP' m).ends (freshE (Δ.pole (Δ.Vs \ X)) + 1) i ∈ (Δ.Vs \ X) ∩ V₂ :=
    fun i ↦ (mem_edgesIn.mp (hham₂.subset (Finset.mem_union_right _ (Finset.mem_singleton_self _)))).2 i
  have hold : ∀ e ∈ (join hP' m).Es, e ≠ freshE (Δ.pole (Δ.Vs \ X)) →
      e ≠ freshE (Δ.pole (Δ.Vs \ X)) + 1 → e ∈ Δ.edgesIn (Δ.Vs \ X) ∧ e ∈ Δ.Es := by
    intro e he h1' h2'
    rw [join_Es, Finset.mem_insert, Finset.mem_insert, Finset.mem_sdiff, pole_Es, Finset.mem_union,
      dangling_pole] at he
    rcases he with h | h | ⟨h | h, hd⟩
    · exact absurd h h1'
    · exact absurd h h2'
    · exact ⟨h, edgesIn_subset _ h⟩
    · exact absurd h hd
  -- the spokes of the join
  have hspokes : (join hP' m).bd ((Δ.Vs \ X) ∩ V₁) = Δ.bd V₁ ∩ Δ.edgesIn (Δ.Vs \ X) := by
    ext e
    rw [Finset.mem_inter]
    constructor
    · intro he
      have heE := bd_subset _ he
      by_cases h1' : e = freshE (Δ.pole (Δ.Vs \ X))
      · exfalso
        subst h1'
        rw [mem_bd] at he
        exact he.2 ⟨fun _ ↦ hnew₁ 1, fun _ ↦ hnew₁ 0⟩
      by_cases h2' : e = freshE (Δ.pole (Δ.Vs \ X)) + 1
      · exfalso
        subst h2'
        rw [mem_bd] at he
        have h0 := hnew₂ 0
        have h1'' := hnew₂ 1
        rw [Finset.mem_inter] at h0 h1''
        exact he.2 ⟨fun h ↦ absurd (Finset.mem_inter.mp h).2
          (fun h' ↦ Finset.disjoint_left.mp hP.disj h' h0.2),
          fun h ↦ absurd (Finset.mem_inter.mp h).2 (fun h' ↦ Finset.disjoint_left.mp hP.disj h' h1''.2)⟩
      obtain ⟨hin, heΔ⟩ := hold e heE h1' h2'
      refine ⟨?_, hin⟩
      rw [mem_bd] at he ⊢
      refine ⟨heΔ, ?_⟩
      rw [join_ends_old hP' m (by rw [pole_Es, Finset.mem_union]; exact Or.inl hin),
        join_ends_old hP' m (by rw [pole_Es, Finset.mem_union]; exact Or.inl hin)] at he
      simp only [pole_ends, Finset.mem_inter] at he
      have h0 := (mem_edgesIn.mp hin).2 0
      have h1'' := (mem_edgesIn.mp hin).2 1
      intro hiff
      exact he.2 ⟨fun h ↦ ⟨h1'', hiff.mp h.2⟩, fun h ↦ ⟨h0, hiff.mpr h.2⟩⟩
    · rintro ⟨hsp, hin⟩
      have heP : e ∈ (Δ.pole (Δ.Vs \ X)).Es := by rw [pole_Es, Finset.mem_union]; exact Or.inl hin
      have heJ : e ∈ (join hP' m).Es := by
        rw [join_Es]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨heP, by
          rw [dangling_pole, bd_compl hcl]
          exact fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd _) hin (by rw [bd_compl hcl]; exact h)⟩))
      rw [mem_bd]
      refine ⟨heJ, ?_⟩
      rw [join_ends_old hP' m heP, join_ends_old hP' m heP]
      simp only [pole_ends, Finset.mem_inter]
      rw [mem_bd] at hsp
      have h0 := (mem_edgesIn.mp hin).2 0
      have h1'' := (mem_edgesIn.mp hin).2 1
      intro hiff
      exact hsp.2 ⟨fun h ↦ (hiff.mp ⟨h0, h⟩).2, fun h ↦ (hiff.mpr ⟨h1'', h⟩).2⟩
  -- the outer ends of the two `R₁`-cut edges are distinct vertices of the complement
  have hcard₁ : 2 ≤ ((Δ.Vs \ X) ∩ V₁).card := by
    obtain ⟨d, d', hdd', hK⟩ := Finset.card_eq_two.mp h1
    have hd : d ∈ R₁ ∩ Δ.bd X := by rw [hK]; exact Finset.mem_insert_self _ _
    have hd' : d' ∈ R₁ ∩ Δ.bd X := by rw [hK]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hmem : ∀ e ∈ R₁ ∩ Δ.bd X, innerEnd hP' e ∈ (Δ.Vs \ X) ∩ V₁ := by
      intro e he
      obtain ⟨i, hi⟩ := ends_innerEnd_compl hcl hP' (Finset.mem_inter.mp he).2
      refine Finset.mem_inter.mpr ⟨innerEnd_compl_mem hcl hP' (Finset.mem_inter.mp he).2, ?_⟩
      rw [← hi]
      exact (mem_edgesIn.mp (hP.ham₁.subset (Finset.mem_inter.mp he).1)).2 i
    apply Finset.one_lt_card.mpr
    refine ⟨_, hmem d hd, _, hmem d' hd', ?_⟩
    intro h
    exact hdd' (innerEnd_compl_inj hcl hP' hind (Finset.mem_inter.mp hd).2
      (Finset.mem_inter.mp hd').2 h)
  have hs_even : Even (X ∩ V₁).card := (hP.segment_parity hcl hcub hnc hX hPX m).1 hiso
  have hsplit : V₁.card = (X ∩ V₁).card + ((Δ.Vs \ X) ∩ V₁).card := by
    rw [← Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx').1).2 (Finset.mem_inter.mp hx).1)]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro h
      by_cases hx : x ∈ X
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨⟨hV₁V h, hx⟩, h⟩
    · rintro (h | h)
      · exact h.2
      · exact h.2
  refine ⟨?_, ?_, hham₁, hham₂, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp hP.disj (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
  · rw [join_Vs, pole_Vs]
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      have := h.1
      rw [← hP.union, Finset.mem_union] at this
      rcases this with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  · apply Finset.Subset.antisymm
    · intro e he
      have heE := (mem_edgesIn.mp he).1
      by_cases h1' : e = freshE (Δ.pole (Δ.Vs \ X))
      · rw [h1']; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      by_cases h2' : e = freshE (Δ.pole (Δ.Vs \ X)) + 1
      · exfalso
        subst h2'
        have := (mem_edgesIn.mp he).2 0
        exact Finset.disjoint_left.mp hP.disj (Finset.mem_inter.mp this).2 (Finset.mem_inter.mp (hnew₂ 0)).2
      obtain ⟨hin, heΔ⟩ := hold e heE h1' h2'
      have heP : e ∈ (Δ.pole (Δ.Vs \ X)).Es := by rw [pole_Es, Finset.mem_union]; exact Or.inl hin
      apply Finset.mem_union_left
      refine Finset.mem_inter.mpr ⟨?_, hin⟩
      rw [← hP.induced₁, mem_edgesIn]
      refine ⟨heΔ, fun i ↦ ?_⟩
      have := (mem_edgesIn.mp he).2 i
      rw [join_ends_old hP' m heP] at this
      exact (Finset.mem_inter.mp this).2
    · exact hham₁.subset
  · apply Finset.Subset.antisymm
    · intro e he
      have heE := (mem_edgesIn.mp he).1
      by_cases h1' : e = freshE (Δ.pole (Δ.Vs \ X))
      · exfalso
        subst h1'
        have := (mem_edgesIn.mp he).2 0
        exact Finset.disjoint_left.mp hP.disj (Finset.mem_inter.mp (hnew₁ 0)).2 (Finset.mem_inter.mp this).2
      by_cases h2' : e = freshE (Δ.pole (Δ.Vs \ X)) + 1
      · rw [h2']; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      obtain ⟨hin, heΔ⟩ := hold e heE h1' h2'
      have heP : e ∈ (Δ.pole (Δ.Vs \ X)).Es := by rw [pole_Es, Finset.mem_union]; exact Or.inl hin
      apply Finset.mem_union_left
      refine Finset.mem_inter.mpr ⟨?_, hin⟩
      rw [← hP.induced₂, mem_edgesIn]
      refine ⟨heΔ, fun i ↦ ?_⟩
      have := (mem_edgesIn.mp he).2 i
      rw [join_ends_old hP' m heP] at this
      exact (Finset.mem_inter.mp this).2
    · exact hham₂.subset
  · intro v hv
    rw [hspokes]
    rw [join_Vs, pole_Vs] at hv
    have hF : Δ.bd V₁ ∩ Δ.edgesIn (Δ.Vs \ X) ⊆ (Δ.pole (Δ.Vs \ X)).Es := by
      intro e he
      rw [pole_Es, Finset.mem_union]; exact Or.inl (Finset.mem_inter.mp he).2
    have hhalf : (join hP' m).halfEdgesIn (Δ.bd V₁ ∩ Δ.edgesIn (Δ.Vs \ X)) v =
        Δ.halfEdgesIn (Δ.bd V₁) v := by
      ext ⟨e, i⟩
      rw [mem_halfEdgesIn, mem_halfEdgesIn]
      constructor
      · rintro ⟨he, hend⟩
        rw [join_ends_old hP' m (hF he)] at hend
        exact ⟨(Finset.mem_inter.mp he).1, hend⟩
      · rintro ⟨he, hend⟩
        have hin : e ∈ Δ.edgesIn (Δ.Vs \ X) := by
          rcases mem_edgesIn_or_bd (bd_subset _ he) (i := i) (hend ▸ hv) with h | h
          · exact h
          · exfalso
            rw [bd_compl hcl] at h
            exact Finset.notMem_empty e (hs ▸ Finset.mem_inter.mpr ⟨h, he⟩)
        refine ⟨Finset.mem_inter.mpr ⟨he, hin⟩, ?_⟩
        rw [join_ends_old hP' m (hF (Finset.mem_inter.mpr ⟨he, hin⟩))]
        exact hend
    rw [degIn_eq_card, hhalf, ← degIn_eq_card]
    exact hP.spoke v (Finset.mem_sdiff.mp hv).1
  · have hodd := hP.odd hcl hnc
    rw [hsplit] at hodd
    obtain ⟨k, hk⟩ := hs_even
    obtain ⟨t, ht⟩ := hodd
    omega

end Join

section Class

omit hX in
/-- The cap factor of a permutation snark is a permutation graph. -/
theorem IsPermGraph.cap_mem {m : Fin 3} (hPX : (Δ.pole X).IsPole4) (hv : Δ.ValidDatum X m) :
    ∃ V₁' V₂' R₁' R₂', (cap hPX m).IsPermGraph V₁' V₂' R₁' R₂' := by
  obtain ⟨_, hiso⟩ := hv.iso
  have hX := hv.cycSep
  obtain ⟨-, -, hs⟩ := hP.cycSep_structure hcl hcub hnc hX
  have hb0 : bdEmb hPX 0 ∈ Δ.bd X := by rw [← dangling_pole]; exact bdEmb_mem hPX 0
  have hrim : bdEmb hPX 0 ∈ R₁ ∨ bdEmb hPX 0 ∈ R₂ := by
    have hE := bd_subset _ hb0
    have := hcl _ hE 0
    rw [← hP.union, Finset.mem_union] at this
    rcases this with h | h
    · rcases hP.edge_at_V₁ hE h with h' | h'
      · exact Or.inl h'
      · exact absurd (Finset.mem_inter.mpr ⟨hb0, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
    · rcases hP.edge_at_V₂ hcl hE h with h' | h'
      · exact Or.inr h'
      · exact absurd (Finset.mem_inter.mpr ⟨hb0, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
  rcases hrim with h | h
  · obtain ⟨hR₁, hR₂⟩ := hP.couples_rims hcl hcub hnc hX hPX m (Or.inl hiso) h
    exact ⟨_, _, _, _, hP.cap_isPermGraph hcl hcub hnc hX hPX m hiso hR₁ hR₂⟩
  · obtain ⟨hR₁, hR₂⟩ := (hP.swap hcl).couples_rims hcl hcub hnc hX hPX m (Or.inl hiso) h
    exact ⟨_, _, _, _, (hP.swap hcl).cap_isPermGraph hcl hcub hnc hX hPX m hiso hR₁ hR₂⟩

omit hX in
/-- The join factor of a permutation snark is a permutation graph. -/
theorem IsPermGraph.join_mem {m : Fin 3} (hP' : (Δ.pole (Δ.Vs \ X)).IsPole4)
    (hv : Δ.ValidDatum X m) :
    ∃ V₁' V₂' R₁' R₂', (join hP' m).IsPermGraph V₁' V₂' R₁' R₂' := by
  obtain ⟨hPX, hiso⟩ := hv.iso
  have hX := hv.cycSep
  obtain ⟨-, -, hs⟩ := hP.cycSep_structure hcl hcub hnc hX
  have hb0 : bdEmb hPX 0 ∈ Δ.bd X := by rw [← dangling_pole]; exact bdEmb_mem hPX 0
  have hrim : bdEmb hPX 0 ∈ R₁ ∨ bdEmb hPX 0 ∈ R₂ := by
    have hE := bd_subset _ hb0
    have := hcl _ hE 0
    rw [← hP.union, Finset.mem_union] at this
    rcases this with h | h
    · rcases hP.edge_at_V₁ hE h with h' | h'
      · exact Or.inl h'
      · exact absurd (Finset.mem_inter.mpr ⟨hb0, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
    · rcases hP.edge_at_V₂ hcl hE h with h' | h'
      · exact Or.inr h'
      · exact absurd (Finset.mem_inter.mpr ⟨hb0, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (hs ▸ h''))
  have hc₁ := couple₁_eq_compl hcl hPX hP' m
  have hc₂ := couple₂_eq_compl hcl hPX hP' m
  rcases hrim with h | h
  · obtain ⟨hR₁, hR₂⟩ := hP.couples_rims hcl hcub hnc hX hPX m (Or.inl hiso) h
    rw [hc₁] at hR₁; rw [hc₂] at hR₂
    exact ⟨_, _, _, _, hP.join_isPermGraph hcl hcub hnc hX hP' hPX m hiso hR₁ hR₂⟩
  · obtain ⟨hR₁, hR₂⟩ := (hP.swap hcl).couples_rims hcl hcub hnc hX hPX m (Or.inl hiso) h
    rw [hc₁] at hR₁; rw [hc₂] at hR₂
    exact ⟨_, _, _, _, (hP.swap hcl).join_isPermGraph hcl hcub hnc hX hP' hPX m hiso hR₁ hR₂⟩

end Class

section Main

omit hP hcl hcub hnc hX

/-- **Permutation snarks form a good class** (closure under the factors of decompositions
along cycle-separating `4`-cuts, girth at least five and cyclic `4`-edge-connectivity). -/
theorem goodClass_permutation : GoodClass IsPermutationSnark where
  closed := fun _ h ↦ h.1
  cubic := fun _ h ↦ h.2.1
  girth := fun Γ h ↦ by
    obtain ⟨hcl, hcub, hnc, V₁, V₂, R₁, R₂, hP⟩ := h
    exact hP.girth5 hcl hcub hnc
  cyc4 := fun Γ h ↦ by
    obtain ⟨hcl, hcub, hnc, V₁, V₂, R₁, R₂, hP⟩ := h
    exact hP.cyc4Conn hcl hcub hnc
  snark := fun _ h ↦ h.2.2.1
  pole_colourable := fun Γ h X hX ↦ by
    obtain ⟨hcl, hcub, hnc, V₁, V₂, R₁, R₂, hP⟩ := h
    obtain ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩ := hP.rims_cut hcl hcub hnc hX.1 hX.2.1.le hX.2.2.1 hX.2.2.2
    exact hP.pole_colourable_of_cut hcl (Finset.mem_inter.mp he₁).1 (Finset.mem_inter.mp he₁).2
      (Finset.mem_inter.mp he₂).1 (Finset.mem_inter.mp he₂).2
  cap_mem := fun Γ h X m hPX hv ↦ by
    obtain ⟨hcl, hcub, hnc, V₁, V₂, R₁, R₂, hP⟩ := h
    obtain ⟨_, hiso⟩ := hv.iso
    exact ⟨cap_isClosed hPX m, cap_isCubic hPX m, not_colourable_cap_of_isoWith hPX m hiso,
      hP.cap_mem hcl hcub hnc hPX hv⟩
  join_mem := fun Γ h X m hP' hv ↦ by
    obtain ⟨hcl, hcub, hnc, V₁, V₂, R₁, R₂, hP⟩ := h
    obtain ⟨_, hhet⟩ := hv.het
    exact ⟨join_isClosed hP' m, join_isCubic hP' m, not_colourable_join_of_hetWith hP' m hhet,
      hP.join_mem hcl hcub hnc hP' hv⟩

/-- **Unique factorisation of permutation snarks.**  Any two complete decompositions of a
permutation snark along cycle-separating `4`-cuts give the same multiset of terminal factors up
to isomorphism. -/
theorem permutation_unique_factorisation {Δ : FinGraph} (hΔ : IsPermutationSnark Δ)
    {M M' : Multiset FinGraph} (hM : (factorSystem goodClass_permutation).Chain Δ M)
    (hM' : (factorSystem goodClass_permutation).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  unique_factorisation goodClass_permutation hΔ hM hM'

theorem permutation_exists_factorisation (Δ : FinGraph) :
    ∃ M, (factorSystem goodClass_permutation).Chain Δ M :=
  exists_factorisation goodClass_permutation Δ

/-- **Every factor is a cyclically `5`-edge-connected permutation snark.** -/
theorem permutation_factors {Δ : FinGraph} (hΔ : IsPermutationSnark Δ) {M : Multiset FinGraph}
    (hM : (factorSystem goodClass_permutation).Chain Δ M) :
    ∀ H ∈ M, IsPermutationSnark H ∧ ∀ X, ¬ H.CycSep X := by
  intro H hH
  obtain ⟨hP, hT⟩ := hM.mem_P hΔ H hH
  exact ⟨hP, fun X hX ↦ hT ⟨_, _, exists_step_of_cycSep goodClass_permutation hP hX⟩⟩

/-- The terminal members of the class are exactly those without cycle-separating `4`-cuts, i.e.
the cyclically `5`-edge-connected permutation snarks. -/
theorem permutation_terminal_iff {Γ : FinGraph} (h : IsPermutationSnark Γ) :
    (factorSystem goodClass_permutation).Terminal Γ ↔ ∀ X, ¬ Γ.CycSep X := by
  constructor
  · intro ht X hX
    exact ht ⟨_, _, exists_step_of_cycSep goodClass_permutation h hX⟩
  · rintro hno ⟨A, B, Z, m, -, -, -, -, -, hv, -⟩
    exact hno Z hv.cycSep

/-- The factors of a decomposition of a permutation snark are permutation snarks. -/
theorem IsPermutationSnark.step {Δ C D : FinGraph} (hΔ : IsPermutationSnark Δ)
    (h : Step Δ C D) : IsPermutationSnark C ∧ IsPermutationSnark D :=
  Step.class_mem goodClass_permutation hΔ h

/-- The intersection of two good classes is a good class. -/
theorem GoodClass.inter {P Q : FinGraph → Prop} (hP : GoodClass P) (hQ : GoodClass Q) :
    GoodClass (fun Γ ↦ P Γ ∧ Q Γ) where
  closed := fun Γ h ↦ hP.closed Γ h.1
  cubic := fun Γ h ↦ hP.cubic Γ h.1
  girth := fun Γ h ↦ hP.girth Γ h.1
  cyc4 := fun Γ h ↦ hP.cyc4 Γ h.1
  snark := fun Γ h ↦ hP.snark Γ h.1
  pole_colourable := fun Γ h X hX ↦ hP.pole_colourable Γ h.1 X hX
  cap_mem := fun Γ h X m hPX hv ↦ ⟨hP.cap_mem Γ h.1 X m hPX hv, hQ.cap_mem Γ h.2 X m hPX hv⟩
  join_mem := fun Γ h X m hP' hv ↦ ⟨hP.join_mem Γ h.1 X m hP' hv, hQ.join_mem Γ h.2 X m hP' hv⟩

/-- **HP snarks**: hypohamiltonian permutation snarks. -/
def IsHPSnark (Γ : FinGraph) : Prop := IsHypohamiltonianSnark Γ ∧ IsPermutationSnark Γ

/-- HP snarks form a good class. -/
theorem goodClass_hp : GoodClass IsHPSnark :=
  goodClass_hypohamiltonian.inter goodClass_permutation

/-- **Unique factorisation of HP snarks.** -/
theorem hp_unique_factorisation {Δ : FinGraph} (hΔ : IsHPSnark Δ)
    {M M' : Multiset FinGraph} (hM : (factorSystem goodClass_hp).Chain Δ M)
    (hM' : (factorSystem goodClass_hp).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  unique_factorisation goodClass_hp hΔ hM hM'

theorem hp_exists_factorisation (Δ : FinGraph) : ∃ M, (factorSystem goodClass_hp).Chain Δ M :=
  exists_factorisation goodClass_hp Δ

/-- **Every factor is a cyclically `5`-edge-connected HP snark.** -/
theorem hp_factors {Δ : FinGraph} (hΔ : IsHPSnark Δ) {M : Multiset FinGraph}
    (hM : (factorSystem goodClass_hp).Chain Δ M) :
    ∀ H ∈ M, IsHPSnark H ∧ ∀ X, ¬ H.CycSep X := by
  intro H hH
  obtain ⟨hP, hT⟩ := hM.mem_P hΔ H hH
  exact ⟨hP, fun X hX ↦ hT ⟨_, _, exists_step_of_cycSep goodClass_hp hP hX⟩⟩

/-- The factors of a decomposition of an HP snark are HP snarks. -/
theorem IsHPSnark.step {Δ C D : FinGraph} (hΔ : IsHPSnark Δ) (h : Step Δ C D) :
    IsHPSnark C ∧ IsHPSnark D :=
  Step.class_mem goodClass_hp hΔ h

end Main

end FinGraph
end GraphPuzzles
