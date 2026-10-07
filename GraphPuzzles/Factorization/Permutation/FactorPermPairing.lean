import GraphPuzzles.Factorization.Permutation.FactorPermSegment
import GraphPuzzles.Factorization.Bicritical.FactorCapBicriticalA

/-!
# Rim segments, couples and parity

For a cycle-separating `4`-cut `Y` of a permutation snark: each rim meets `Y` in a path (the
segment) between the inner ends of its two cut edges; the couples of the pairing of the cut are
the pairs of cut edges of the same rim; and the segment of a rim inside `Y` has an even number of
vertices when the pole at `Y` is isochromatic, an odd number when it is heterochromatic.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section PathLike

variable {Γ : FinGraph}

/-- A subset of a Hamilton cycle with exactly two vertices of degree one and all other degrees
zero or two, missing some edge of the cycle, is connected. -/
theorem isConnected_of_path_like {S C P : Finset ℕ} (hC : Γ.IsHamCycle S C) (hPC : P ⊆ C)
    {p q : ℕ} (_hpS : p ∈ S) (hqS : q ∈ S) (_hpq : p ≠ q) (hp : Γ.degIn P p = 1)
    (hq : Γ.degIn P q = 1) (hother : ∀ v ∈ S, v ≠ p → v ≠ q → Γ.degIn P v = 0 ∨ Γ.degIn P v = 2)
    (hne : ∃ e ∈ C, e ∉ P) : Γ.IsConnected P := by
  classical
  -- the edge of `P` at `p`
  obtain ⟨⟨ep, ip⟩, hep⟩ : (Γ.halfEdgesIn P p).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hp]; omega
  rw [mem_halfEdgesIn] at hep
  dsimp only at hep
  -- every edge of `P` is linked to `ep`
  have key : ∀ f ∈ P, Relation.ReflTransGen (Γ.AdjIn P) f ep := by
    intro f hf
    set D := P.filter (fun g ↦ Relation.ReflTransGen (Γ.AdjIn P) f g) with hDdef
    have hDP : D ⊆ P := Finset.filter_subset _ _
    have hfD : f ∈ D := Finset.mem_filter.mpr ⟨hf, Relation.ReflTransGen.refl⟩
    have hDclosed : ∀ g ∈ D, ∀ g' ∈ P, (∃ k l, Γ.ends g k = Γ.ends g' l) → g' ∈ D := by
      intro g hg g' hg' hkl
      rw [Finset.mem_filter] at hg ⊢
      obtain ⟨k, l, hkl⟩ := hkl
      exact ⟨hg', hg.2.tail ⟨hg.1, hg', k, l, hkl⟩⟩
    -- the degree of `D` at a touched vertex is the degree of `P`
    have hdegD : ∀ v, 0 < Γ.degIn D v → Γ.degIn D v = Γ.degIn P v := by
      intro v hpos
      rw [degIn_eq_card, Finset.card_pos] at hpos
      obtain ⟨⟨g, k⟩, hgk⟩ := hpos
      rw [mem_halfEdgesIn] at hgk
      dsimp only at hgk
      rw [degIn_eq_card, degIn_eq_card]
      congr 1
      apply Finset.Subset.antisymm (halfEdgesIn_mono hDP v)
      intro ⟨g', l⟩ hg'
      rw [mem_halfEdgesIn] at hg' ⊢
      exact ⟨hDclosed g hgk.1 g' hg'.1 ⟨k, l, by rw [hgk.2, hg'.2]⟩, hg'.2⟩
    -- handshake for `D` on `S`
    have hsum : ∑ v ∈ S, Γ.degIn D v = 2 * D.card := by
      rw [sum_degIn_eq, Finset.sum_congr rfl (fun g hg ↦ endsIn_of_mem_edgesIn (hC.subset (hPC (hDP hg)))),
        Finset.sum_const, smul_eq_mul, mul_comm]
    by_cases hpD : 0 < Γ.degIn D p
    · -- `D` touches `p`, hence contains `ep`
      have : (ep, ip) ∈ Γ.halfEdgesIn D p := by
        have h := hdegD p hpD
        rw [degIn_eq_card, degIn_eq_card] at h
        have hsub := halfEdgesIn_mono (Γ := Γ) hDP p
        have heq := Finset.eq_of_subset_of_card_le hsub h.ge
        rw [heq, mem_halfEdgesIn]; exact hep
      rw [mem_halfEdgesIn] at this
      exact (Finset.mem_filter.mp this.1).2
    · exfalso
      -- `D` does not touch `p`; by parity it does not touch `q` either, so `D` is even
      have hp0 : Γ.degIn D p = 0 := by omega
      have hq0 : Γ.degIn D q = 0 := by
        by_contra hq0
        have hqpos : 0 < Γ.degIn D q := Nat.pos_of_ne_zero hq0
        have hq1 : Γ.degIn D q = 1 := by rw [hdegD q hqpos]; exact hq
        -- the sum over `S` is odd
        have heven : Even (∑ v ∈ S, Γ.degIn D v) := ⟨D.card, by rw [hsum]; ring⟩
        have hS' : S = insert q (S.erase q) := (Finset.insert_erase hqS).symm
        rw [hS', Finset.sum_insert (Finset.notMem_erase q S), hq1] at heven
        have hev' : Even (∑ v ∈ S.erase q, Γ.degIn D v) := by
          apply Finset.even_sum
          intro v hv
          rw [Finset.mem_erase] at hv
          by_cases hvp : v = p
          · rw [hvp, hp0]; exact ⟨0, rfl⟩
          · by_cases hpos : 0 < Γ.degIn D v
            · rw [hdegD v hpos]
              rcases hother v hv.2 hvp hv.1 with h | h
              · rw [h]; exact ⟨0, rfl⟩
              · rw [h]; exact ⟨1, rfl⟩
            · have : Γ.degIn D v = 0 := by omega
              rw [this]; exact ⟨0, rfl⟩
        obtain ⟨t, ht⟩ := heven
        obtain ⟨t', ht'⟩ := hev'
        omega
      have hDeven : ∀ v ∈ S, Γ.degIn D v = 0 ∨ Γ.degIn D v = 2 := by
        intro v hv
        by_cases hvp : v = p
        · rw [hvp, hp0]; exact Or.inl rfl
        by_cases hvq : v = q
        · rw [hvq, hq0]; exact Or.inl rfl
        by_cases hpos : 0 < Γ.degIn D v
        · rw [hdegD v hpos]; exact hother v hv hvp hvq
        · left; omega
      have hDC : D = C := hC.eq_of_subset (hDP.trans hPC) ⟨f, hfD⟩ hDeven
      obtain ⟨e, heC, heP⟩ := hne
      exact heP (hDP (hDC ▸ heC))
  intro f hf g hg
  exact (key f hf).trans (reflTransGen_adjIn_symm (key g hg))

end PathLike

section Segment

variable {Γ : FinGraph} {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂)
  (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable) {Y : Finset ℕ} (hY : Γ.CycSep Y)
include hP hcl hcub hnc hY

/-- **The rim segment.** -/
theorem IsPermGraph.rim_segment : ∃ d d' p q : ℕ, d ∈ R₁ ∩ Γ.bd Y ∧ d' ∈ R₁ ∩ Γ.bd Y ∧ d ≠ d' ∧
    R₁ ∩ Γ.bd Y = {d, d'} ∧ p ∈ Y ∩ V₁ ∧ q ∈ Y ∩ V₁ ∧ p ≠ q ∧ (∃ i, Γ.ends d i = p) ∧
    (∃ i, Γ.ends d' i = q) ∧ (∀ i, Γ.ends d i ∈ Y → Γ.ends d i = p) ∧
    (∀ i, Γ.ends d' i ∈ Y → Γ.ends d' i = q) ∧
    Γ.IsConnected (R₁ ∩ Γ.edgesIn Y) ∧ R₁ ∩ Γ.edgesIn Y ⊆ Γ.edgesIn (Y ∩ V₁) ∧
    (∀ v ∈ Y ∩ V₁, Γ.degIn (R₁ ∩ Γ.edgesIn Y) v ≤ 2) ∧ Γ.degIn (R₁ ∩ Γ.edgesIn Y) p = 1 ∧
    Γ.degIn (R₁ ∩ Γ.edgesIn Y) q = 1 ∧
    (∀ v ∈ Y ∩ V₁, v ≠ p → v ≠ q → Γ.degIn (R₁ ∩ Γ.edgesIn Y) v = 2) ∧
    (R₁ ∩ Γ.edgesIn Y).card + 1 = (Y ∩ V₁).card := by
  classical
  have hg5 := hP.girth5 hcl hcub hnc
  have hc4 := hP.cyc4Conn hcl hcub hnc
  have hind := hY.independent hcl hcub hg5 hc4
  have hloop := hP.no_loop hcl
  obtain ⟨h1, -, -⟩ := hP.cycSep_structure hcl hcub hnc hY
  obtain ⟨d, d', hdd', hK⟩ := Finset.card_eq_two.mp h1
  have hd : d ∈ R₁ ∩ Γ.bd Y := by rw [hK]; exact Finset.mem_insert_self _ _
  have hd' : d' ∈ R₁ ∩ Γ.bd Y := by rw [hK]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨id, hid, hid'⟩ := bd_side (Finset.mem_inter.mp hd).2
  obtain ⟨id', hid'', hid'''⟩ := bd_side (Finset.mem_inter.mp hd').2
  set p := Γ.ends d id with hpdef
  set q := Γ.ends d' id' with hqdef
  have hpV₁ : p ∈ V₁ := (mem_edgesIn.mp (hP.ham₁.subset (Finset.mem_inter.mp hd).1)).2 _
  have hqV₁ : q ∈ V₁ := (mem_edgesIn.mp (hP.ham₁.subset (Finset.mem_inter.mp hd').1)).2 _
  have hpq : p ≠ q := fun h ↦ hdd' (hind.eq_of_ends (Finset.mem_inter.mp hd).2
    (Finset.mem_inter.mp hd').2 h)
  -- the unique `Y`-end
  have huniq : ∀ (e : ℕ) (i j : Fin 2), e ∈ Γ.bd Y → Γ.ends e i ∈ Y → Γ.ends e (Fin.rev i) ∉ Y →
      Γ.ends e j ∈ Y → Γ.ends e j = Γ.ends e i := by
    intro e i j _ hi hi' hj
    by_cases hij : j = i
    · rw [hij]
    · rw [fin2_eq_rev_of_ne hij] at hj; exact absurd hj hi'
  set P := R₁ ∩ Γ.edgesIn Y with hPdef
  have hPR : P ⊆ R₁ := Finset.inter_subset_left
  -- the half-edges of `P` at a vertex of `Y ∩ V₁`
  have hdegP : ∀ v ∈ Y ∩ V₁, Γ.degIn P v + ((Γ.halfEdgesIn R₁ v).filter fun x ↦ x.1 ∈ Γ.bd Y).card = 2 := by
    intro v hv
    have hsplit := Finset.card_filter_add_card_filter_not (s := Γ.halfEdgesIn R₁ v) (fun x ↦ x.1 ∈ Γ.bd Y)
    rw [← degIn_eq_card, hP.ham₁.deg v (Finset.mem_inter.mp hv).2] at hsplit
    have hPeq : Γ.halfEdgesIn P v = (Γ.halfEdgesIn R₁ v).filter fun x ↦ x.1 ∉ Γ.bd Y := by
      ext ⟨e, i⟩
      rw [mem_halfEdgesIn, Finset.mem_filter, mem_halfEdgesIn, hPdef, Finset.mem_inter]
      constructor
      · rintro ⟨⟨he, heY⟩, hi⟩
        exact ⟨⟨he, hi⟩, fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) heY h⟩
      · rintro ⟨⟨he, hi⟩, hb⟩
        refine ⟨⟨he, ?_⟩, hi⟩
        rcases mem_edgesIn_or_bd (hP.R₁_subset he) (i := i) (hi ▸ (Finset.mem_inter.mp hv).1) with h | h
        · exact h
        · exact absurd h hb
    rw [degIn_eq_card, hPeq]
    omega
  have hcut_le : ∀ v, ((Γ.halfEdgesIn R₁ v).filter fun x ↦ x.1 ∈ Γ.bd Y).card ≤ 1 := by
    intro v
    rw [Finset.card_le_one]
    rintro ⟨e, i⟩ he ⟨f, j⟩ hf
    rw [Finset.mem_filter, mem_halfEdgesIn] at he hf
    dsimp only at he hf
    have hef : e = f := hind.eq_of_ends he.2 hf.2 (he.1.2.trans hf.1.2.symm)
    subst hef
    rw [idx_eq_of_ends_eq_single (hloop e (hP.R₁_subset he.1.1)) (he.1.2.trans hf.1.2.symm)]
  have hcut_p : ((Γ.halfEdgesIn R₁ p).filter fun x ↦ x.1 ∈ Γ.bd Y).card = 1 := by
    apply le_antisymm (hcut_le p)
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    exact ⟨(d, id), Finset.mem_filter.mpr ⟨mem_halfEdgesIn.mpr ⟨(Finset.mem_inter.mp hd).1, rfl⟩,
      (Finset.mem_inter.mp hd).2⟩⟩
  have hcut_q : ((Γ.halfEdgesIn R₁ q).filter fun x ↦ x.1 ∈ Γ.bd Y).card = 1 := by
    apply le_antisymm (hcut_le q)
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    exact ⟨(d', id'), Finset.mem_filter.mpr ⟨mem_halfEdgesIn.mpr ⟨(Finset.mem_inter.mp hd').1, rfl⟩,
      (Finset.mem_inter.mp hd').2⟩⟩
  have hcut_other : ∀ v ∈ Y ∩ V₁, v ≠ p → v ≠ q →
      ((Γ.halfEdgesIn R₁ v).filter fun x ↦ x.1 ∈ Γ.bd Y).card = 0 := by
    intro v hv hvp hvq
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨e, i⟩ he
    rw [Finset.mem_filter, mem_halfEdgesIn] at he
    dsimp only at he
    have heK : e ∈ R₁ ∩ Γ.bd Y := Finset.mem_inter.mpr ⟨he.1.1, he.2⟩
    rw [hK, Finset.mem_insert, Finset.mem_singleton] at heK
    rcases heK with rfl | rfl
    · exact hvp (he.1.2.symm.trans (huniq e id i he.2 hid hid' (he.1.2 ▸ (Finset.mem_inter.mp hv).1)))
    · exact hvq (he.1.2.symm.trans (huniq e id' i he.2 hid'' hid''' (he.1.2 ▸ (Finset.mem_inter.mp hv).1)))
  have hpY : p ∈ Y ∩ V₁ := Finset.mem_inter.mpr ⟨hid, hpV₁⟩
  have hqY : q ∈ Y ∩ V₁ := Finset.mem_inter.mpr ⟨hid'', hqV₁⟩
  have hdp : Γ.degIn P p = 1 := by have := hdegP p hpY; omega
  have hdq : Γ.degIn P q = 1 := by have := hdegP q hqY; omega
  have hdo : ∀ v ∈ Y ∩ V₁, v ≠ p → v ≠ q → Γ.degIn P v = 2 := by
    intro v hv hvp hvq
    have := hdegP v hv
    rw [hcut_other v hv hvp hvq] at this
    omega
  have hPsub : P ⊆ Γ.edgesIn (Y ∩ V₁) := by
    intro e he
    rw [hPdef, Finset.mem_inter] at he
    rw [mem_edgesIn]
    refine ⟨(mem_edgesIn.mp he.2).1, fun i ↦ Finset.mem_inter.mpr ⟨(mem_edgesIn.mp he.2).2 i,
      (mem_edgesIn.mp (hP.ham₁.subset he.1)).2 i⟩⟩
  have hdegle : ∀ v ∈ Y ∩ V₁, Γ.degIn P v ≤ 2 := fun v hv ↦ by have := hdegP v hv; omega
  -- connectivity
  have hconn : Γ.IsConnected P := by
    refine isConnected_of_path_like hP.ham₁ hPR hpV₁ hqV₁ hpq hdp hdq ?_ ⟨d, (Finset.mem_inter.mp hd).1, ?_⟩
    · intro v hv hvp hvq
      by_cases hvY : v ∈ Y
      · exact Or.inr (hdo v (Finset.mem_inter.mpr ⟨hvY, hv⟩) hvp hvq)
      · left
        rw [degIn_eq_zero_iff]
        intro e he i hi
        exact hvY (hi ▸ (mem_edgesIn.mp (Finset.mem_inter.mp he).2).2 i)
    · intro h
      exact Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) (Finset.mem_inter.mp h).2
        (Finset.mem_inter.mp hd).2
  -- the number of edges
  have hcard : P.card + 1 = (Y ∩ V₁).card := by
    have hsum := sum_degIn_eq (Γ := Γ) P (Y ∩ V₁)
    rw [Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_edgesIn (hPsub he)), Finset.sum_const,
      smul_eq_mul] at hsum
    have hS : Y ∩ V₁ = insert p (insert q ((Y ∩ V₁).erase p |>.erase q)) := by
      rw [Finset.insert_erase, Finset.insert_erase hpY]
      exact Finset.mem_erase.mpr ⟨hpq.symm, hqY⟩
    have hrest : ∑ v ∈ ((Y ∩ V₁).erase p).erase q, Γ.degIn P v =
        ∑ v ∈ ((Y ∩ V₁).erase p).erase q, 2 :=
      Finset.sum_congr rfl (fun v hv ↦ by
        rw [Finset.mem_erase, Finset.mem_erase] at hv
        exact hdo v hv.2.2 hv.2.1 hv.1)
    rw [hS, Finset.sum_insert (by
        rw [Finset.mem_insert, Finset.mem_erase, Finset.mem_erase]
        rintro (h | ⟨-, h, -⟩)
        · exact hpq h
        · exact h rfl),
      Finset.sum_insert (by
        rw [Finset.mem_erase, Finset.mem_erase]
        rintro ⟨h, -⟩
        exact h rfl), hdp, hdq, hrest, Finset.sum_const, smul_eq_mul] at hsum
    have hcardS : (Y ∩ V₁).card = ((Y ∩ V₁).erase p |>.erase q).card + 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm, hqY⟩),
        Finset.card_erase_of_mem hpY]
      have := Finset.card_pos.mpr ⟨p, hpY⟩
      have : 2 ≤ (Y ∩ V₁).card := Finset.one_lt_card.mpr ⟨p, hpY, q, hqY, hpq⟩
      omega
    omega
  refine ⟨d, d', p, q, hd, hd', hdd', hK, hpY, hqY, hpq, ⟨id, rfl⟩, ⟨id', rfl⟩,
    fun i hi ↦ huniq d id i (Finset.mem_inter.mp hd).2 hid hid' hi,
    fun i hi ↦ huniq d' id' i (Finset.mem_inter.mp hd').2 hid'' hid''' hi,
    hconn, hPsub, hdegle, hdp, hdq, hdo, hcard⟩

/-- The partner of a cut edge of `R₁` under the pairing of the cut lies in `R₁`. -/
theorem IsPermGraph.partner_mem_rim (hPY : (Γ.pole Y).IsPole4) (m : Fin 3)
    (hm : IsoWith hPY m ∨ HetWith hPY m) {d : ℕ} (hd : d ∈ R₁ ∩ Γ.bd Y) :
    partner hPY m d ∈ R₁ := by
  classical
  have hdd : d ∈ (Γ.pole Y).dangling := mem_dangling_Y (Finset.mem_inter.mp hd).2
  have hpd : partner hPY m d ∈ Γ.bd Y := by
    have := partner_mem hPY m hdd; rwa [dangling_pole] at this
  have hpne : partner hPY m d ≠ d := partner_ne hPY m hdd
  obtain ⟨h1, h2, h0⟩ := hP.cycSep_structure hcl hcub hnc hY
  -- the partner is a rim edge; suppose it lies on `R₂`
  by_contra hnot
  have hf₂ : partner hPY m d ∈ R₂ := by
    have hE := bd_subset _ hpd
    have := hcl _ hE 0
    rw [← hP.union, Finset.mem_union] at this
    rcases this with h | h
    · rcases hP.edge_at_V₁ hE h with h' | h'
      · exact absurd h' hnot
      · exact absurd (Finset.mem_inter.mpr ⟨hpd, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (h0 ▸ h''))
    · rcases hP.edge_at_V₂ hcl hE h with h' | h'
      · exact h'
      · exact absurd (Finset.mem_inter.mpr ⟨hpd, h'⟩) (fun h'' ↦ Finset.notMem_empty _ (h0 ▸ h''))
  set f := partner hPY m d with hfdef
  -- colourings of the pole from two-colourings of the rims, and the `R₂`-swapped one
  have h3 : 2 ≤ V₁.card := by have := hP.three; omega
  have h3' : 2 ≤ V₂.card := by rw [hP.card_V₂ hcl]; exact h3
  obtain ⟨c₁, hc₁⟩ := exists_two_colouring_cut hP.ham₁ h3 (Finset.mem_inter.mp hd).1
    (Finset.mem_inter.mp hd).2
  obtain ⟨c₂, hc₂⟩ := exists_two_colouring_cut hP.ham₂ h3' hf₂ hpd
  have hc₂' : ∀ f ∈ Γ.sidePart R₂ Y, ∀ g ∈ Γ.sidePart R₂ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → (1 - c₂ f) ≠ (1 - c₂ g) := by
    intro f hf g hg hfg v hv i j hi hj h
    apply hc₂ f hf g hg hfg v hv i j hi hj
    have hf0 : c₂ f = 0 ∨ c₂ f = 1 := by omega
    have hg0 : c₂ g = 0 ∨ c₂ g = 1 := by omega
    rcases hf0 with hf0 | hf0 <;> rcases hg0 with hg0 | hg0 <;> rw [hf0, hg0] at h ⊢ <;>
      first | rfl | exact absurd h (by decide)
  have hcol := hP.isColouring_of_rims hcl hc₁ hc₂
  have hcol' := hP.isColouring_of_rims hcl hc₁ hc₂'
  have hdR₂ : d ∉ R₂ := fun h ↦ Finset.disjoint_left.mp hP.disjoint_rims (Finset.mem_inter.mp hd).1 h
  have hfR₁ : f ∉ R₁ := hnot
  -- the colours of `d` and `f`
  have hcd : (if d ∈ R₁ then twoColor (c₁ d) else if d ∈ R₂ then twoColor (c₂ d) else (1, 1))
      = twoColor (c₁ d) := by rw [if_pos (Finset.mem_inter.mp hd).1]
  have hcf : (if f ∈ R₁ then twoColor (c₁ f) else if f ∈ R₂ then twoColor (c₂ f) else (1, 1))
      = twoColor (c₂ f) := by rw [if_neg hfR₁, if_pos hf₂]
  have hcd' : (if d ∈ R₁ then twoColor (c₁ d) else if d ∈ R₂ then twoColor (1 - c₂ d) else (1, 1))
      = twoColor (c₁ d) := by rw [if_pos (Finset.mem_inter.mp hd).1]
  have hcf' : (if f ∈ R₁ then twoColor (c₁ f) else if f ∈ R₂ then twoColor (1 - c₂ f) else (1, 1))
      = twoColor (1 - c₂ f) := by rw [if_neg hfR₁, if_pos hf₂]
  obtain ⟨k, hk⟩ := exists_bdEmb_eq hPY hdd
  have hpk : bdEmb hPY (pairing m k) = f := by rw [hfdef, ← hk, partner_bdEmb]
  rcases hm with hiso | hhet
  · have h1' := hiso _ ⟨_, hcol, rfl⟩ k
    have h2' := hiso _ ⟨_, hcol', rfl⟩ k
    simp only [tvec, hk, hpk] at h1' h2'
    rw [hcd, hcf] at h1'
    rw [hcd', hcf'] at h2'
    have := twoColor_inj (h1'.symm.trans h2')
    exact (fin2_sub_eq_iff _ _).mp this.symm rfl
  · have h1' := hhet _ ⟨_, hcol, rfl⟩ k
    have h2' := hhet _ ⟨_, hcol', rfl⟩ k
    simp only [tvec, hk, hpk] at h1' h2'
    rw [hcd, hcf] at h1'
    rw [hcd', hcf'] at h2'
    apply h2'
    congr 1
    exact ((fin2_sub_eq_iff _ _).mpr (fun h ↦ h1' (by rw [h]))).symm

/-- **Parity of the segment**: the rim segment inside an isochromatic shore has an even number
of vertices, inside a heterochromatic shore an odd number. -/
theorem IsPermGraph.segment_parity (hPY : (Γ.pole Y).IsPole4) (m : Fin 3) :
    (IsoWith hPY m → Even (Y ∩ V₁).card) ∧ (HetWith hPY m → Odd (Y ∩ V₁).card) := by
  classical
  have hloop := hP.no_loop hcl
  obtain ⟨d, d', p, q, hd, hd', hdd', hK, hpY, hqY, hpq, ⟨id, hid⟩, ⟨id', hid'⟩, hdY, hd'Y,
    hconn, hPsub, hdegle, hdp, hdq, hdo, hcard⟩ := hP.rim_segment hcl hcub hnc hY
  set P := R₁ ∩ Γ.edgesIn Y with hPdef
  have h3 : 2 ≤ V₁.card := by have := hP.three; omega
  have h3' : 2 ≤ V₂.card := by rw [hP.card_V₂ hcl]; exact h3
  -- a two-colouring of the segment with controlled end colours
  obtain ⟨c₀, hc₀prop, hc₀end⟩ := exists_two_colouring P.card P rfl hPsub
    (fun v hv ↦ hdegle v hv) hconn (fun e he ↦ hloop e (hP.R₁_subset (Finset.mem_inter.mp he).1))
    p q hpY hqY hpq hdp hdq
  obtain ⟨⟨ep, ip⟩, hep⟩ : (Γ.halfEdgesIn P p).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdp]; omega
  obtain ⟨⟨eq', iq⟩, heq'⟩ : (Γ.halfEdgesIn P q).Nonempty := by
    rw [← Finset.card_pos, ← degIn_eq_card, hdq]; omega
  rw [mem_halfEdgesIn] at hep heq'
  dsimp only at hep heq'
  have hend := hc₀end ep hep.1 eq' heq'.1 ⟨ip, hep.2⟩ ⟨iq, heq'.2⟩
  -- the extended colouring of the side part of `R₁`
  let c₁ : ℕ → Fin 2 := fun e ↦ if e = d then 1 - c₀ ep else if e = d' then 1 - c₀ eq' else c₀ e
  have hside : ∀ e ∈ Γ.sidePart R₁ Y, e = d ∨ e = d' ∨ e ∈ P := by
    intro e he
    rw [mem_sidePart_iff] at he
    rcases he.2 with h | h
    · exact Or.inr (Or.inr (Finset.mem_inter.mpr ⟨he.1, h⟩))
    · have : e ∈ R₁ ∩ Γ.bd Y := Finset.mem_inter.mpr ⟨he.1, h⟩
      rw [hK, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  have hdP : d ∉ P := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y)
    (Finset.mem_inter.mp h).2 (Finset.mem_inter.mp hd).2
  have hd'P : d' ∉ P := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y)
    (Finset.mem_inter.mp h).2 (Finset.mem_inter.mp hd').2
  -- the unique edge of `P` at `p` is `ep`, at `q` is `eq'`
  have hatp : ∀ g ∈ P, ∀ j, Γ.ends g j = p → g = ep :=
    fun g hg j hj ↦ (eq_of_degIn_eq_one hdp hg hep.1 hj hep.2).1
  have hatq : ∀ g ∈ P, ∀ j, Γ.ends g j = q → g = eq' :=
    fun g hg j hj ↦ (eq_of_degIn_eq_one hdq hg heq'.1 hj heq'.2).1
  have hPd : ∀ g ∈ P, g ≠ d := fun g hg h ↦ hdP (h ▸ hg)
  have hPd' : ∀ g ∈ P, g ≠ d' := fun g hg h ↦ hd'P (h ▸ hg)
  have hc₁P : ∀ g ∈ P, c₁ g = c₀ g := by
    intro g hg
    show (if g = d then 1 - c₀ ep else if g = d' then 1 - c₀ eq' else c₀ g) = c₀ g
    rw [if_neg (hPd g hg), if_neg (hPd' g hg)]
  have hc₁d : c₁ d = 1 - c₀ ep := by
    show (if d = d then 1 - c₀ ep else if d = d' then 1 - c₀ eq' else c₀ d) = _
    rw [if_pos rfl]
  have hc₁d' : c₁ d' = 1 - c₀ eq' := by
    show (if d' = d then 1 - c₀ ep else if d' = d' then 1 - c₀ eq' else c₀ d') = _
    rw [if_neg hdd'.symm, if_pos rfl]
  have hvp_of : ∀ (i : Fin 2) (v : ℕ), Γ.ends d i = v → v ∈ Y → v = p := by
    intro i v hi hv
    rw [← hi]; exact hdY i (by rw [hi]; exact hv)
  have hvq_of : ∀ (i : Fin 2) (v : ℕ), Γ.ends d' i = v → v ∈ Y → v = q := by
    intro i v hi hv
    rw [← hi]; exact hd'Y i (by rw [hi]; exact hv)
  have hc₁ : ∀ f ∈ Γ.sidePart R₁ Y, ∀ g ∈ Γ.sidePart R₁ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c₁ f ≠ c₁ g := by
    intro f hf g hg hfg v hv i j hi hj
    rcases hside f hf with hfd | hfd' | hfP <;> rcases hside g hg with hgd | hgd' | hgP
    · subst f; subst g; exact absurd rfl hfg
    · subst f; subst g
      exact absurd ((hvp_of i v hi hv).symm.trans (hvq_of j v hj hv)) hpq
    · subst f
      have hvp := hvp_of i v hi hv
      have hgp : g = ep := hatp g hgP j (hj.trans hvp)
      rw [hc₁d, hc₁P g hgP, hgp]
      intro h; exact (fin2_sub_eq_iff _ _).mp h rfl
    · subst f; subst g
      exact absurd ((hvp_of j v hj hv).symm.trans (hvq_of i v hi hv)) hpq
    · subst f; subst g; exact absurd rfl hfg
    · subst f
      have hvq := hvq_of i v hi hv
      have hgq : g = eq' := hatq g hgP j (hj.trans hvq)
      rw [hc₁d', hc₁P g hgP, hgq]
      intro h; exact (fin2_sub_eq_iff _ _).mp h rfl
    · subst g
      have hvp := hvp_of j v hj hv
      have hfp : f = ep := hatp f hfP i (hi.trans hvp)
      rw [hc₁d, hc₁P f hfP, hfp]
      intro h; exact (fin2_sub_eq_iff _ _).mp h.symm rfl
    · subst g
      have hvq := hvq_of j v hj hv
      have hfq : f = eq' := hatq f hfP i (hi.trans hvq)
      rw [hc₁d', hc₁P f hfP, hfq]
      intro h; exact (fin2_sub_eq_iff _ _).mp h.symm rfl
    · rw [hc₁P f hfP, hc₁P g hgP]
      exact hc₀prop f hfP g hgP hfg ⟨hfP, hgP, i, j, hi.trans hj.symm⟩
  -- the second rim
  obtain ⟨-, h2, -⟩ := hP.cycSep_structure hcl hcub hnc hY
  obtain ⟨f₂, hf₂⟩ : (R₂ ∩ Γ.bd Y).Nonempty := by rw [← Finset.card_pos, h2]; omega
  obtain ⟨c₂, hc₂⟩ := exists_two_colouring_cut hP.ham₂ h3' (Finset.mem_inter.mp hf₂).1
    (Finset.mem_inter.mp hf₂).2
  have hcol := hP.isColouring_of_rims hcl hc₁ hc₂
  -- the partner of `d` is `d'`
  have hpart : ∀ m', (IsoWith hPY m' ∨ HetWith hPY m') → partner hPY m' d = d' := by
    intro m' hm'
    have hmem := hP.partner_mem_rim hcl hcub hnc hY hPY m' hm' hd
    have hdd : d ∈ (Γ.pole Y).dangling := mem_dangling_Y (Finset.mem_inter.mp hd).2
    have hpd : partner hPY m' d ∈ Γ.bd Y := by
      have := partner_mem hPY m' hdd; rwa [dangling_pole] at this
    have : partner hPY m' d ∈ R₁ ∩ Γ.bd Y := Finset.mem_inter.mpr ⟨hmem, hpd⟩
    rw [hK, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h (partner_ne hPY m' hdd)
    · exact h
  -- colours of `d` and `d'` in the combined colouring
  have hcd : (if d ∈ R₁ then twoColor (c₁ d) else if d ∈ R₂ then twoColor (c₂ d) else (1, 1))
      = twoColor (1 - c₀ ep) := by rw [if_pos (Finset.mem_inter.mp hd).1, hc₁d]
  have hcd' : (if d' ∈ R₁ then twoColor (c₁ d') else if d' ∈ R₂ then twoColor (c₂ d') else (1, 1))
      = twoColor (1 - c₀ eq') := by rw [if_pos (Finset.mem_inter.mp hd').1, hc₁d']
  have hdd : d ∈ (Γ.pole Y).dangling := mem_dangling_Y (Finset.mem_inter.mp hd).2
  obtain ⟨k, hk⟩ := exists_bdEmb_eq hPY hdd
  -- the segment has `P.card + 1` vertices
  have hodd_iff : Odd P.card ↔ Even (Y ∩ V₁).card := by
    rw [← hcard, Nat.even_add_one, Nat.not_even_iff_odd]
  constructor
  · intro hiso
    have hpk : bdEmb hPY (pairing m k) = d' := by rw [← hpart m (Or.inl hiso), ← hk, partner_bdEmb]
    have h1' := hiso _ ⟨_, hcol, rfl⟩ k
    simp only [tvec, hk, hpk] at h1'
    rw [hcd, hcd'] at h1'
    have := twoColor_inj h1'
    have hce : c₀ ep = c₀ eq' := by
      have h0 : c₀ ep = 0 ∨ c₀ ep = 1 := by omega
      have h0' : c₀ eq' = 0 ∨ c₀ eq' = 1 := by omega
      rcases h0 with h0 | h0 <;> rcases h0' with h0' | h0' <;> rw [h0, h0'] at this ⊢ <;>
        first | rfl | exact absurd this (by decide)
    exact hodd_iff.mp (hend.mp hce)
  · intro hhet
    have hpk : bdEmb hPY (pairing m k) = d' := by rw [← hpart m (Or.inr hhet), ← hk, partner_bdEmb]
    have h1' := hhet _ ⟨_, hcol, rfl⟩ k
    simp only [tvec, hk, hpk] at h1'
    rw [hcd, hcd'] at h1'
    have hne : c₀ ep ≠ c₀ eq' := fun h ↦ h1' (by rw [h])
    have : ¬ Even (Y ∩ V₁).card := fun h ↦ hne (hend.mpr (hodd_iff.mpr h))
    exact Nat.not_even_iff_odd.mp this

end Segment

end FinGraph
end GraphPuzzles
