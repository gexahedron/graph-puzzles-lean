import GraphPuzzles.CycleCovers.TJoin
import GraphPuzzles.Graph.Boundary
import GraphPuzzles.Circuits.OrdinaryCircuit

/-!
# Hamilton cycles and dot products

This file proves the Hamilton-cycle descent lemma for the dot product of two cubic graphs: if the
product is hypohamiltonian and both factors are non-Hamiltonian, then both factors are
hypohamiltonian.  This is the elementary ingredient of the unique-factorisation results for
hypohamiltonian and hypohamiltonian permutation snarks. The uniqueness of the factor multiset
is Chladný–Škoviera's Theorem C, formalized in the FinGraph model (`FactorMain`,
`FactorHypoUnique`, `FactorHypoClass`).

Both factors and the product are subgraphs of one ambient endpoint multigraph: the left factor
adds two edges joining the left terminals, and the right factor adds two cap vertices joined to
the right terminals and to each other.  A Hamilton cycle of a subgraph is a minimal nonempty
binary-even edge set inside the allowed edges whose support is the required vertex set, so all
the cycle surgery of the informal proof becomes finite-set algebra on binary boundaries.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

section MinimalEven

/-- Minimal nonempty binary-even edge sets: the circuits of the bounded-cover convention. -/
def IsMinimalEven (D : Finset E) : Prop :=
  D.Nonempty ∧ G.IsEvenEdgeSet D ∧
    ∀ D₀, D₀.Nonempty → D₀ ⊆ D → G.IsEvenEdgeSet D₀ → D₀ = D

variable {G}

omit [DecidableEq E] in
theorem IsMinimalEven.eq_of_subset {D D₀ : Finset E} (hD : G.IsMinimalEven D)
    (hne : D₀.Nonempty) (hsub : D₀ ⊆ D) (heven : G.IsEvenEdgeSet D₀) : D₀ = D :=
  hD.2.2 D₀ hne hsub heven

/-- **Replacement lemma.**  Replacing a nonempty part `P` of a minimal even set by a nonempty
set `Q` with the same binary boundary gives a minimal even set, provided every even subset of
the result contains all or none of `Q`. -/
theorem IsMinimalEven.replace {D P Q : Finset E} (hD : G.IsMinimalEven D) (hP : P ⊆ D)
    (hPne : P.Nonempty) (hQne : Q.Nonempty) (hQ : Disjoint Q (D \ P))
    (hbd : ∀ w, G.boundary P w = G.boundary Q w)
    (hall : ∀ D₀, D₀ ⊆ (D \ P) ∪ Q → G.IsEvenEdgeSet D₀ → Disjoint D₀ Q ∨ Q ⊆ D₀) :
    G.IsMinimalEven ((D \ P) ∪ Q) := by
  have heven : G.IsEvenEdgeSet ((D \ P) ∪ Q) := by
    intro w
    change G.boundary ((D \ P) ∪ Q) w = 0
    have hD0 : G.boundary D w = 0 := hD.2.1 w
    rw [G.boundary_union _ _ hQ.symm, G.boundary_sdiff hP, hD0, zero_add, hbd, F₂_add_self]
  refine ⟨?_, heven, ?_⟩
  · obtain ⟨q, hq⟩ := hQne
    exact ⟨q, Finset.mem_union_right _ hq⟩
  · intro D₀ hne hsub heven₀
    rcases hall D₀ hsub heven₀ with hdisj | hQsub
    · have hsub' : D₀ ⊆ D \ P := by
        intro e he
        rcases Finset.mem_union.mp (hsub he) with h | h
        · exact h
        · exact absurd h (Finset.disjoint_left.mp hdisj he)
      have hD₀ : D₀ = D := hD.eq_of_subset hne (hsub'.trans Finset.sdiff_subset) heven₀
      exfalso
      obtain ⟨p, hp⟩ := hPne
      have hmem : p ∈ D \ P := hsub' (hD₀ ▸ hP hp)
      exact (Finset.mem_sdiff.mp hmem).2 hp
    · have hD'sub : (D₀ \ Q) ∪ P ⊆ D := by
        apply Finset.union_subset _ hP
        intro e he
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hsub hm.1) with h | h
        · exact (Finset.mem_sdiff.mp h).1
        · exact absurd h hm.2
      have hdisj' : Disjoint (D₀ \ Q) P := by
        rw [Finset.disjoint_left]
        intro e he hp
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hsub hm.1) with h | h
        · exact (Finset.mem_sdiff.mp h).2 hp
        · exact hm.2 h
      have heven' : G.IsEvenEdgeSet ((D₀ \ Q) ∪ P) := by
        intro w
        change G.boundary ((D₀ \ Q) ∪ P) w = 0
        have h0 : G.boundary D₀ w = 0 := heven₀ w
        rw [G.boundary_union _ _ hdisj', G.boundary_sdiff hQsub, h0, zero_add, ← hbd,
          F₂_add_self]
      have hne' : ((D₀ \ Q) ∪ P).Nonempty := by
        obtain ⟨p, hp⟩ := hPne
        exact ⟨p, Finset.mem_union_right _ hp⟩
      have hD' : (D₀ \ Q) ∪ P = D := hD.eq_of_subset hne' hD'sub heven'
      apply Finset.Subset.antisymm hsub
      intro e he
      rcases Finset.mem_union.mp he with h | h
      · have hmem : e ∈ (D₀ \ Q) ∪ P := hD' ▸ (Finset.mem_sdiff.mp h).1
        rcases Finset.mem_union.mp hmem with h' | h'
        · exact (Finset.mem_sdiff.mp h').1
        · exact absurd h' (Finset.mem_sdiff.mp h).2
      · exact hQsub h

/-- A single-edge replacement always satisfies the all-or-nothing condition. -/
theorem IsMinimalEven.replace_singleton {D P : Finset E} {q : E} (hD : G.IsMinimalEven D)
    (hP : P ⊆ D) (hPne : P.Nonempty) (hq : q ∉ D \ P)
    (hbd : ∀ w, G.boundary P w = G.boundary {q} w) :
    G.IsMinimalEven ((D \ P) ∪ {q}) := by
  apply hD.replace hP hPne ⟨q, Finset.mem_singleton_self q⟩ (Finset.disjoint_singleton_left.mpr hq) hbd
  intro D₀ _ _
  by_cases h : q ∈ D₀
  · right
    exact Finset.singleton_subset_iff.mpr h
  · left
    exact Finset.disjoint_singleton_right.mpr h

end MinimalEven

section Hamilton

/-- A Hamilton cycle of the subgraph with allowed edges `A` and vertex set `S`: a minimal even
set of allowed edges whose support is exactly `S`. -/
def IsHamiltonCycleIn (A : Finset E) (S : Finset V) (D : Finset E) : Prop :=
  D ⊆ A ∧ G.IsMinimalEven D ∧ G.edgeSupport D = S

/-- The subgraph `(A, S)` is hypohamiltonian: it has no Hamilton cycle, but every vertex
deletion has one. -/
def IsHypohamiltonianIn (A : Finset E) (S : Finset V) : Prop :=
  (¬ ∃ D, G.IsHamiltonCycleIn A S D) ∧ ∀ v ∈ S, ∃ D, G.IsHamiltonCycleIn A (S.erase v) D

end Hamilton


private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

section Helpers

theorem boundary_insert_singleton {e : E} {S : Finset E} (he : e ∉ S) (w : V) :
    G.boundary (insert e S) w = G.boundary {e} w + G.boundary S w := by
  rw [Finset.insert_eq, G.boundary_union _ _ (Finset.disjoint_singleton_left.mpr he)]

omit [DecidableEq E] in
theorem boundary_eq_sum_of {D : Finset E} {w : V} (f : E → F₂)
    (hf : ∀ e ∈ D, G.edgeIncidence w e = f e) : G.boundary D w = ∑ e ∈ D, f e :=
  Finset.sum_congr rfl hf

theorem boundary_sdiff_part (C T : Finset E) (w : V) :
    G.boundary (C \ T) w = G.boundary C w + G.boundary (C ∩ T) w := by
  have h : C \ T = C \ (C ∩ T) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [h]
  exact G.boundary_sdiff Finset.inter_subset_left w

end Helpers

omit [Fintype E] in
/-- Summing two membership indicators over a set. -/
theorem sum_two_indicators (D : Finset E) (g₁ g₂ : E) :
    (∑ e ∈ D, ((if e = g₁ then (1 : F₂) else 0) + (if e = g₂ then 1 else 0))) =
      (if g₁ ∈ D then 1 else 0) + (if g₂ ∈ D then 1 else 0) := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

private theorem F₂_eq_of_add_eq_zero {a b : F₂} (h : a + b = 0) : a = b := by
  revert a b
  decide

omit [Fintype E] in
theorem mem_iff_of_indicator_add {D : Finset E} {g₁ g₂ : E}
    (h : (if g₁ ∈ D then (1 : F₂) else 0) + (if g₂ ∈ D then 1 else 0) = 0) :
    g₁ ∈ D ↔ g₂ ∈ D := by
  have h' := F₂_eq_of_add_eq_zero h
  by_cases h₁ : g₁ ∈ D <;> by_cases h₂ : g₂ ∈ D <;> simp_all

private theorem F₂_cancel_pair (u v α β : F₂) : (u + α) + ((u + v) + (v + β)) = α + β := by
  revert u v α β
  decide

private theorem F₂_cancel_single (u α β : F₂) : (u + α) + (u + β) = α + β := by
  revert u α β
  decide

omit [Fintype E] in
theorem sdiff_sdiff_eq_inter (C T : Finset E) : C \ (C \ T) = C ∩ T := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- The data of a dot product `A · B` inside an ambient endpoint multigraph `G`.

The left factor `A` has vertex set `L` and edges `EL ∪ {eab, ecd}`; the right factor `B` has
vertex set `R ∪ {x, y}` and edges `ER ∪ {exa, exb, exy, eyc, eyd}`; the product has vertex
set `L ∪ R` and edges `EL ∪ ER ∪ {faa, fbb, fcc, fdd}`.  All three live in `G`. -/
structure DotProduct (G : LoopMultigraph V E) where
  (L R : Finset V)
  (x y a b c d a' b' c' d' : V)
  (EL ER : Finset E)
  (faa fbb fcc fdd eab ecd exa exb exy eyc eyd : E)
  disjLR : Disjoint L R
  x_notin_L : x ∉ L
  x_notin_R : x ∉ R
  y_notin_L : y ∉ L
  y_notin_R : y ∉ R
  x_ne_y : x ≠ y
  a_mem : a ∈ L
  b_mem : b ∈ L
  c_mem : c ∈ L
  d_mem : d ∈ L
  a'_mem : a' ∈ R
  b'_mem : b' ∈ R
  c'_mem : c' ∈ R
  d'_mem : d' ∈ R
  ab_ne : a ≠ b
  ac_ne : a ≠ c
  ad_ne : a ≠ d
  bc_ne : b ≠ c
  bd_ne : b ≠ d
  cd_ne : c ≠ d
  a'b'_ne : a' ≠ b'
  a'c'_ne : a' ≠ c'
  a'd'_ne : a' ≠ d'
  b'c'_ne : b' ≠ c'
  b'd'_ne : b' ≠ d'
  c'd'_ne : c' ≠ d'
  EL_ends : ∀ e ∈ EL, ∀ i, G.endAt e i ∈ L
  ER_ends : ∀ e ∈ ER, ∀ i, G.endAt e i ∈ R
  faa_ends : G.endAt faa 0 = a ∧ G.endAt faa 1 = a'
  fbb_ends : G.endAt fbb 0 = b ∧ G.endAt fbb 1 = b'
  fcc_ends : G.endAt fcc 0 = c ∧ G.endAt fcc 1 = c'
  fdd_ends : G.endAt fdd 0 = d ∧ G.endAt fdd 1 = d'
  eab_ends : G.endAt eab 0 = a ∧ G.endAt eab 1 = b
  ecd_ends : G.endAt ecd 0 = c ∧ G.endAt ecd 1 = d
  exa_ends : G.endAt exa 0 = x ∧ G.endAt exa 1 = a'
  exb_ends : G.endAt exb 0 = x ∧ G.endAt exb 1 = b'
  exy_ends : G.endAt exy 0 = x ∧ G.endAt exy 1 = y
  eyc_ends : G.endAt eyc 0 = y ∧ G.endAt eyc 1 = c'
  eyd_ends : G.endAt eyd 0 = y ∧ G.endAt eyd 1 = d'
  eab_notin : eab ∉ EL
  ecd_notin : ecd ∉ EL

namespace DotProduct

variable {G} (P : G.DotProduct)

/-- The four bond edges. -/
def bond : Finset E := {P.faa, P.fbb, P.fcc, P.fdd}

/-- The edges of the product. -/
def EG : Finset E := P.EL ∪ P.ER ∪ P.bond

/-- The edges of the left factor. -/
def EA : Finset E := P.EL ∪ {P.eab, P.ecd}

/-- The edges of the right factor. -/
def EB : Finset E := P.ER ∪ {P.exa, P.exb, P.exy, P.eyc, P.eyd}

/-- The vertices of the product. -/
def VG : Finset V := P.L ∪ P.R

/-- The vertices of the right factor. -/
def VB : Finset V := insert P.x (insert P.y P.R)

omit [DecidableEq V] [DecidableEq E] in
theorem notin_EL_of_end {e : E} {i : Fin 2} (h : G.endAt e i ∉ P.L) : e ∉ P.EL :=
  fun he ↦ h (P.EL_ends e he i)

omit [DecidableEq V] [DecidableEq E] in
theorem notin_ER_of_end {e : E} {i : Fin 2} (h : G.endAt e i ∉ P.R) : e ∉ P.ER :=
  fun he ↦ h (P.ER_ends e he i)

omit [DecidableEq V] [DecidableEq E] in
theorem notin_R_of_mem_L {v : V} (h : v ∈ P.L) : v ∉ P.R :=
  Finset.disjoint_left.mp P.disjLR h

omit [DecidableEq V] [DecidableEq E] in
theorem notin_L_of_mem_R {v : V} (h : v ∈ P.R) : v ∉ P.L :=
  Finset.disjoint_right.mp P.disjLR h

omit [DecidableEq V] [DecidableEq E] in
theorem faa_notin_EL : P.faa ∉ P.EL := P.notin_EL_of_end (i := 1) (P.faa_ends.2 ▸ P.notin_L_of_mem_R P.a'_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fbb_notin_EL : P.fbb ∉ P.EL := P.notin_EL_of_end (i := 1) (P.fbb_ends.2 ▸ P.notin_L_of_mem_R P.b'_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fcc_notin_EL : P.fcc ∉ P.EL := P.notin_EL_of_end (i := 1) (P.fcc_ends.2 ▸ P.notin_L_of_mem_R P.c'_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fdd_notin_EL : P.fdd ∉ P.EL := P.notin_EL_of_end (i := 1) (P.fdd_ends.2 ▸ P.notin_L_of_mem_R P.d'_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem faa_notin_ER : P.faa ∉ P.ER := P.notin_ER_of_end (i := 0) (P.faa_ends.1 ▸ P.notin_R_of_mem_L P.a_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fbb_notin_ER : P.fbb ∉ P.ER := P.notin_ER_of_end (i := 0) (P.fbb_ends.1 ▸ P.notin_R_of_mem_L P.b_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fcc_notin_ER : P.fcc ∉ P.ER := P.notin_ER_of_end (i := 0) (P.fcc_ends.1 ▸ P.notin_R_of_mem_L P.c_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem fdd_notin_ER : P.fdd ∉ P.ER := P.notin_ER_of_end (i := 0) (P.fdd_ends.1 ▸ P.notin_R_of_mem_L P.d_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem eab_notin_ER : P.eab ∉ P.ER := P.notin_ER_of_end (i := 0) (P.eab_ends.1 ▸ P.notin_R_of_mem_L P.a_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem ecd_notin_ER : P.ecd ∉ P.ER := P.notin_ER_of_end (i := 0) (P.ecd_ends.1 ▸ P.notin_R_of_mem_L P.c_mem)
omit [DecidableEq V] [DecidableEq E] in
theorem exa_notin_EL : P.exa ∉ P.EL := P.notin_EL_of_end (i := 0) (P.exa_ends.1 ▸ P.x_notin_L)
omit [DecidableEq V] [DecidableEq E] in
theorem exa_notin_ER : P.exa ∉ P.ER := P.notin_ER_of_end (i := 0) (P.exa_ends.1 ▸ P.x_notin_R)
omit [DecidableEq V] [DecidableEq E] in
theorem exb_notin_EL : P.exb ∉ P.EL := P.notin_EL_of_end (i := 0) (P.exb_ends.1 ▸ P.x_notin_L)
omit [DecidableEq V] [DecidableEq E] in
theorem exb_notin_ER : P.exb ∉ P.ER := P.notin_ER_of_end (i := 0) (P.exb_ends.1 ▸ P.x_notin_R)
omit [DecidableEq V] [DecidableEq E] in
theorem exy_notin_EL : P.exy ∉ P.EL := P.notin_EL_of_end (i := 0) (P.exy_ends.1 ▸ P.x_notin_L)
omit [DecidableEq V] [DecidableEq E] in
theorem exy_notin_ER : P.exy ∉ P.ER := P.notin_ER_of_end (i := 0) (P.exy_ends.1 ▸ P.x_notin_R)
omit [DecidableEq V] [DecidableEq E] in
theorem eyc_notin_EL : P.eyc ∉ P.EL := P.notin_EL_of_end (i := 0) (P.eyc_ends.1 ▸ P.y_notin_L)
omit [DecidableEq V] [DecidableEq E] in
theorem eyc_notin_ER : P.eyc ∉ P.ER := P.notin_ER_of_end (i := 0) (P.eyc_ends.1 ▸ P.y_notin_R)
omit [DecidableEq V] [DecidableEq E] in
theorem eyd_notin_EL : P.eyd ∉ P.EL := P.notin_EL_of_end (i := 0) (P.eyd_ends.1 ▸ P.y_notin_L)
omit [DecidableEq V] [DecidableEq E] in
theorem eyd_notin_ER : P.eyd ∉ P.ER := P.notin_ER_of_end (i := 0) (P.eyd_ends.1 ▸ P.y_notin_R)

omit [DecidableEq V] [DecidableEq E] in
/-- Two edges with different ends at side `0` are different. -/
theorem ne_of_end0 {e f : E} (h : G.endAt e 0 ≠ G.endAt f 0) : e ≠ f := fun hef ↦ h (hef ▸ rfl)

omit [DecidableEq V] [DecidableEq E] in
/-- Two edges with different ends at side `1` are different. -/
theorem ne_of_end1 {e f : E} (h : G.endAt e 1 ≠ G.endAt f 1) : e ≠ f := fun hef ↦ h (hef ▸ rfl)

omit [DecidableEq V] [DecidableEq E] in
theorem faa_ne_fbb : P.faa ≠ P.fbb := ne_of_end0 (by rw [P.faa_ends.1, P.fbb_ends.1]; exact P.ab_ne)
omit [DecidableEq V] [DecidableEq E] in
theorem faa_ne_fcc : P.faa ≠ P.fcc := ne_of_end0 (by rw [P.faa_ends.1, P.fcc_ends.1]; exact P.ac_ne)
omit [DecidableEq V] [DecidableEq E] in
theorem faa_ne_fdd : P.faa ≠ P.fdd := ne_of_end0 (by rw [P.faa_ends.1, P.fdd_ends.1]; exact P.ad_ne)
omit [DecidableEq V] [DecidableEq E] in
theorem fbb_ne_fcc : P.fbb ≠ P.fcc := ne_of_end0 (by rw [P.fbb_ends.1, P.fcc_ends.1]; exact P.bc_ne)
omit [DecidableEq V] [DecidableEq E] in
theorem fbb_ne_fdd : P.fbb ≠ P.fdd := ne_of_end0 (by rw [P.fbb_ends.1, P.fdd_ends.1]; exact P.bd_ne)
omit [DecidableEq V] [DecidableEq E] in
theorem fcc_ne_fdd : P.fcc ≠ P.fdd := ne_of_end0 (by rw [P.fcc_ends.1, P.fdd_ends.1]; exact P.cd_ne)

omit [DecidableEq V] in
theorem mem_bond {e : E} : e ∈ P.bond ↔ e = P.faa ∨ e = P.fbb ∨ e = P.fcc ∨ e = P.fdd := by
  simp [bond]

omit [DecidableEq V] in
theorem bond_ends (e : E) (he : e ∈ P.bond) : G.endAt e 0 ∈ P.L ∧ G.endAt e 1 ∈ P.R := by
  rcases P.mem_bond.mp he with rfl | rfl | rfl | rfl
  · exact ⟨P.faa_ends.1 ▸ P.a_mem, P.faa_ends.2 ▸ P.a'_mem⟩
  · exact ⟨P.fbb_ends.1 ▸ P.b_mem, P.fbb_ends.2 ▸ P.b'_mem⟩
  · exact ⟨P.fcc_ends.1 ▸ P.c_mem, P.fcc_ends.2 ▸ P.c'_mem⟩
  · exact ⟨P.fdd_ends.1 ▸ P.d_mem, P.fdd_ends.2 ▸ P.d'_mem⟩

omit [DecidableEq V] in
theorem bond_disjoint_EL : Disjoint P.bond P.EL := by
  rw [Finset.disjoint_left]
  intro e he hEL
  exact P.notin_L_of_mem_R (P.bond_ends e he).2 (P.EL_ends e hEL 1)

omit [DecidableEq V] in
theorem bond_disjoint_ER : Disjoint P.bond P.ER := by
  rw [Finset.disjoint_left]
  intro e he hER
  exact P.notin_R_of_mem_L (P.bond_ends e he).1 (P.ER_ends e hER 0)

omit [DecidableEq V] [DecidableEq E] in
theorem EL_disjoint_ER : Disjoint P.EL P.ER := by
  rw [Finset.disjoint_left]
  intro e hEL hER
  exact P.notin_R_of_mem_L (P.EL_ends e hEL 0) (P.ER_ends e hER 0)

omit [DecidableEq V] in
theorem eab_notin_bond : P.eab ∉ P.bond := fun h ↦
  P.notin_R_of_mem_L (P.eab_ends.2 ▸ P.b_mem) (P.bond_ends _ h).2

omit [DecidableEq V] in
theorem ecd_notin_bond : P.ecd ∉ P.bond := fun h ↦
  P.notin_R_of_mem_L (P.ecd_ends.2 ▸ P.d_mem) (P.bond_ends _ h).2

omit [DecidableEq V] in
theorem eab_notin_EG : P.eab ∉ P.EG := by
  simp only [EG, Finset.mem_union, not_or]
  exact ⟨⟨P.eab_notin, P.eab_notin_ER⟩, P.eab_notin_bond⟩

omit [DecidableEq V] in
theorem ecd_notin_EG : P.ecd ∉ P.EG := by
  simp only [EG, Finset.mem_union, not_or]
  exact ⟨⟨P.ecd_notin, P.ecd_notin_ER⟩, P.ecd_notin_bond⟩

omit [DecidableEq V] in
/-- The three-part decomposition of a set of product edges. -/
theorem eq_union_of_subset_EG {C : Finset E} (hC : C ⊆ P.EG) :
    C = (C ∩ P.EL) ∪ (C ∩ P.ER) ∪ (C ∩ P.bond) := by
  ext e
  constructor
  · intro he
    have := hC he
    simp only [EG, Finset.mem_union] at this
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro he
    simp only [Finset.mem_union, Finset.mem_inter] at he
    tauto

/-- Boundary of a set of product edges, split into its three parts. -/
theorem boundary_split {C : Finset E} (hC : C ⊆ P.EG) (w : V) :
    G.boundary C w =
      G.boundary (C ∩ P.EL) w + G.boundary (C ∩ P.ER) w + G.boundary (C ∩ P.bond) w := by
  have h1 : Disjoint (C ∩ P.EL) (C ∩ P.ER) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.EL_disjoint_ER)
  have h2 : Disjoint ((C ∩ P.EL) ∪ (C ∩ P.ER)) (C ∩ P.bond) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right P.bond_disjoint_EL.symm),
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right P.bond_disjoint_ER.symm)⟩
  conv_lhs => rw [P.eq_union_of_subset_EG hC]
  rw [G.boundary_union _ _ h2, G.boundary_union _ _ h1]

theorem boundary_inter_EL_eq_zero {C : Finset E} {w : V} (hw : w ∉ P.L) :
    G.boundary (C ∩ P.EL) w = 0 :=
  G.boundary_eq_zero_of_ends (fun e he i ↦ P.EL_ends e (Finset.mem_inter.mp he).2 i) hw

theorem boundary_inter_ER_eq_zero {C : Finset E} {w : V} (hw : w ∉ P.R) :
    G.boundary (C ∩ P.ER) w = 0 :=
  G.boundary_eq_zero_of_ends (fun e he i ↦ P.ER_ends e (Finset.mem_inter.mp he).2 i) hw

/-- On the left, the boundary of the left part of an even set of product edges is the boundary
of its bond part. -/
theorem boundary_inter_EL_of_mem_L {C : Finset E} (hC : C ⊆ P.EG) (heven : G.IsEvenEdgeSet C)
    {w : V} (hw : w ∈ P.L) : G.boundary (C ∩ P.EL) w = G.boundary (C ∩ P.bond) w := by
  have h := P.boundary_split hC w
  have h0 : G.boundary C w = 0 := heven w
  rw [h0, P.boundary_inter_ER_eq_zero (P.notin_R_of_mem_L hw), add_zero] at h
  calc
    G.boundary (C ∩ P.EL) w
        = G.boundary (C ∩ P.EL) w + (G.boundary (C ∩ P.EL) w + G.boundary (C ∩ P.bond) w) := by
          rw [← h, add_zero]
    _ = G.boundary (C ∩ P.bond) w := by
          rw [← add_assoc, F₂_add_self, zero_add]

/-- On the right, the boundary of the right part of an even set of product edges is the boundary
of its bond part. -/
theorem boundary_inter_ER_of_mem_R {C : Finset E} (hC : C ⊆ P.EG) (heven : G.IsEvenEdgeSet C)
    {w : V} (hw : w ∈ P.R) : G.boundary (C ∩ P.ER) w = G.boundary (C ∩ P.bond) w := by
  have h := P.boundary_split hC w
  have h0 : G.boundary C w = 0 := heven w
  rw [h0, P.boundary_inter_EL_eq_zero (P.notin_L_of_mem_R hw), zero_add] at h
  calc
    G.boundary (C ∩ P.ER) w
        = G.boundary (C ∩ P.ER) w + (G.boundary (C ∩ P.ER) w + G.boundary (C ∩ P.bond) w) := by
          rw [← h, add_zero]
    _ = G.boundary (C ∩ P.bond) w := by
          rw [← add_assoc, F₂_add_self, zero_add]


omit [DecidableEq V] in
theorem exa_mem_EB : P.exa ∈ P.EB := by simp [EB]
omit [DecidableEq V] in
theorem exb_mem_EB : P.exb ∈ P.EB := by simp [EB]
omit [DecidableEq V] in
theorem eyc_mem_EB : P.eyc ∈ P.EB := by simp [EB]
omit [DecidableEq V] in
theorem eyd_mem_EB : P.eyd ∈ P.EB := by simp [EB]
omit [DecidableEq V] in
theorem eab_mem_EA : P.eab ∈ P.EA := by simp [EA]
omit [DecidableEq V] in
theorem ecd_mem_EA : P.ecd ∈ P.EA := by simp [EA]
omit [DecidableEq V] in
theorem exy_mem_EB : P.exy ∈ P.EB := by simp [EB]

section BondFacts

omit [DecidableEq V] in
theorem inter_bond_eq_pair {C : Finset E} {f₁ f₂ : E} (h₁ : f₁ ∈ C) (h₂ : f₂ ∈ C)
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond)
    (hother : ∀ f ∈ P.bond, f ∈ C → f = f₁ ∨ f = f₂) : C ∩ P.bond = {f₁, f₂} := by
  ext e
  constructor
  · intro he
    have hm := Finset.mem_inter.mp he
    rcases hother e hm.2 hm.1 with rfl | rfl <;> simp
  · intro he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_inter.mpr ⟨h₁, hf₁⟩
    · rw [Finset.mem_singleton] at he
      subst he
      exact Finset.mem_inter.mpr ⟨h₂, hf₂⟩

omit [DecidableEq V] in
theorem mem_of_mem_inter_bond {C : Finset E} {f : E} {T : Finset E} (hpat : C ∩ P.bond = T)
    (hf : f ∈ T) : f ∈ C :=
  (Finset.mem_inter.mp (hpat ▸ hf)).1

omit [DecidableEq V] in
theorem notin_of_subset_EG {C : Finset E} (hC : C ⊆ P.EG) {e : E} (hEL : e ∉ P.EL)
    (hER : e ∉ P.ER) (hb : e ∉ P.bond) : e ∉ C := by
  intro he
  have := hC he
  simp only [EG, Finset.mem_union] at this
  tauto

end BondFacts

private theorem F₂_cancel_four (u v α β γ δ : F₂) :
    (u + α) + ((u + β) + ((v + γ) + (v + δ))) = α + (β + (γ + δ)) := by
  revert u v α β γ δ
  decide

private theorem F₂_sum_pairs (α β α' β' : F₂) :
    (α + β) + (((α + α') + (β + β')) + (α' + β')) = 0 := by
  revert α β α' β'
  decide

section Replacements

variable {C : Finset E} (hC : C ⊆ P.EG) (hmin : G.IsMinimalEven C)
include hC hmin

omit hmin in
/-- Support of the left part extended by virtual edges, in terms of the support of `C`. -/
theorem support_left_general (Q : Finset E)
    (hQ : ∀ g ∈ Q, ∀ i, ∃ f ∈ C ∩ P.bond, G.endAt g i = G.endAt f 0)
    (hcov : ∀ f ∈ C ∩ P.bond, ∃ g ∈ Q, ∃ i, G.endAt g i = G.endAt f 0) :
    G.edgeSupport ((C ∩ P.EL) ∪ Q) = G.edgeSupport C ∩ P.L := by
  ext w
  simp only [Finset.mem_inter, mem_edgeSupport_iff, Finset.mem_union]
  constructor
  · rintro ⟨e, he, i, hi⟩
    rcases he with he | he
    · exact ⟨⟨e, he.1, i, hi⟩, hi ▸ P.EL_ends e he.2 i⟩
    · obtain ⟨f, hf, hfi⟩ := hQ e he i
      have hfm := Finset.mem_inter.mp hf
      exact ⟨⟨f, hfm.1, 0, hfi.symm.trans hi⟩, hi ▸ hfi ▸ (P.bond_ends f hfm.2).1⟩
  · rintro ⟨⟨e, he, i, hi⟩, hwL⟩
    have hEG := hC he
    simp only [EG, Finset.mem_union] at hEG
    rcases hEG with (hEL | hER) | hb
    · exact ⟨e, Or.inl ⟨he, hEL⟩, i, hi⟩
    · exact absurd (hi ▸ P.ER_ends e hER i) (P.notin_R_of_mem_L hwL)
    · rcases fin2_cases i with rfl | rfl
      · obtain ⟨g, hg, j, hj⟩ := hcov e (Finset.mem_inter.mpr ⟨he, hb⟩)
        exact ⟨g, Or.inr hg, j, hj.trans hi⟩
      · exact absurd (hi ▸ (P.bond_ends e hb).2) (P.notin_R_of_mem_L hwL)

omit hmin in
/-- Support of the right part extended by cap edges, in terms of the support of `C`. -/
theorem support_right_general (Q : Finset E) (Z : Finset V)
    (hQ : ∀ g ∈ Q, ∀ i, G.endAt g i ∈ Z ∨ ∃ f ∈ C ∩ P.bond, G.endAt g i = G.endAt f 1)
    (hZ : ∀ z ∈ Z, ∃ g ∈ Q, ∃ i, G.endAt g i = z)
    (hcov : ∀ f ∈ C ∩ P.bond, ∃ g ∈ Q, ∃ i, G.endAt g i = G.endAt f 1) :
    G.edgeSupport ((C ∩ P.ER) ∪ Q) = (G.edgeSupport C ∩ P.R) ∪ Z := by
  ext w
  simp only [Finset.mem_inter, mem_edgeSupport_iff, Finset.mem_union]
  constructor
  · rintro ⟨e, he, i, hi⟩
    rcases he with he | he
    · exact Or.inl ⟨⟨e, he.1, i, hi⟩, hi ▸ P.ER_ends e he.2 i⟩
    · rcases hQ e he i with hZ' | ⟨f, hf, hfi⟩
      · exact Or.inr (hi ▸ hZ')
      · have hfm := Finset.mem_inter.mp hf
        exact Or.inl ⟨⟨f, hfm.1, 1, hfi.symm.trans hi⟩, hi ▸ hfi ▸ (P.bond_ends f hfm.2).2⟩
  · rintro (⟨⟨e, he, i, hi⟩, hwR⟩ | hwZ)
    · have hEG := hC he
      simp only [EG, Finset.mem_union] at hEG
      rcases hEG with (hEL | hER) | hb
      · exact absurd (hi ▸ P.EL_ends e hEL i) (P.notin_L_of_mem_R hwR)
      · exact ⟨e, Or.inl ⟨he, hER⟩, i, hi⟩
      · rcases fin2_cases i with rfl | rfl
        · exact absurd (hi ▸ (P.bond_ends e hb).1) (P.notin_L_of_mem_R hwR)
        · obtain ⟨g, hg, j, hj⟩ := hcov e (Finset.mem_inter.mpr ⟨he, hb⟩)
          exact ⟨g, Or.inr hg, j, hj.trans hi⟩
    · obtain ⟨g, hg, j, hj⟩ := hZ w hwZ
      exact ⟨g, Or.inr hg, j, hj⟩

/-- The right part of an even set of product edges with bond pair `{f₁, f₂}` has boundary
exactly at the right ends of the pair. -/
theorem boundary_inter_ER_of_pair {f₁ f₂ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hpat : C ∩ P.bond = {f₁, f₂}) (w : V) :
    G.boundary (C ∩ P.ER) w = (if p' = w then 1 else 0) + (if q' = w then 1 else 0) := by
  have hp : p ∈ P.L := h₁.1 ▸ (P.bond_ends f₁ hf₁).1
  have hq : q ∈ P.L := h₂.1 ▸ (P.bond_ends f₂ hf₂).1
  have hp' : p' ∈ P.R := h₁.2 ▸ (P.bond_ends f₁ hf₁).2
  have hq' : q' ∈ P.R := h₂.2 ▸ (P.bond_ends f₂ hf₂).2
  by_cases hw : w ∈ P.R
  · have hpw : ¬ p = w := fun h ↦ P.notin_R_of_mem_L hp (h ▸ hw)
    have hqw : ¬ q = w := fun h ↦ P.notin_R_of_mem_L hq (h ▸ hw)
    rw [P.boundary_inter_ER_of_mem_R hC hmin.2.1 hw, hpat, G.boundary_pair hne, h₁.1, h₁.2, h₂.1,
      h₂.2, if_neg hpw, if_neg hqw, zero_add, zero_add]
  · have hp'w : ¬ p' = w := fun h ↦ hw (h ▸ hp')
    have hq'w : ¬ q' = w := fun h ↦ hw (h ▸ hq')
    rw [P.boundary_inter_ER_eq_zero hw, if_neg hp'w, if_neg hq'w, add_zero]

/-- The left part of an even set of product edges with bond pair `{f₁, f₂}` has boundary
exactly at the left ends of the pair. -/
theorem boundary_inter_EL_of_pair {f₁ f₂ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hpat : C ∩ P.bond = {f₁, f₂}) (w : V) :
    G.boundary (C ∩ P.EL) w = (if p = w then 1 else 0) + (if q = w then 1 else 0) := by
  have hp : p ∈ P.L := h₁.1 ▸ (P.bond_ends f₁ hf₁).1
  have hq : q ∈ P.L := h₂.1 ▸ (P.bond_ends f₂ hf₂).1
  have hp' : p' ∈ P.R := h₁.2 ▸ (P.bond_ends f₁ hf₁).2
  have hq' : q' ∈ P.R := h₂.2 ▸ (P.bond_ends f₂ hf₂).2
  by_cases hw : w ∈ P.L
  · have hp'w : ¬ p' = w := fun h ↦ P.notin_L_of_mem_R hp' (h ▸ hw)
    have hq'w : ¬ q' = w := fun h ↦ P.notin_L_of_mem_R hq' (h ▸ hw)
    rw [P.boundary_inter_EL_of_mem_L hC hmin.2.1 hw, hpat, G.boundary_pair hne, h₁.1, h₁.2,
      h₂.1, h₂.2, if_neg hp'w, if_neg hq'w, add_zero, add_zero]
  · have hpw : ¬ p = w := fun h ↦ hw (h ▸ hp)
    have hqw : ¬ q = w := fun h ↦ hw (h ▸ hq)
    rw [P.boundary_inter_EL_eq_zero hw, if_neg hpw, if_neg hqw, add_zero]

/-- Replacing a bond pair by the corresponding left virtual edge. -/
theorem left_replace {f₁ f₂ e₀ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (he₀ : G.endAt e₀ 0 = p ∧ G.endAt e₀ 1 = q) (he₀EL : e₀ ∉ P.EL)
    (hpat : C ∩ P.bond = {f₁, f₂}) :
    G.IsMinimalEven ((C ∩ P.EL) ∪ {e₀}) ∧
      G.edgeSupport ((C ∩ P.EL) ∪ {e₀}) = G.edgeSupport C ∩ P.L := by
  have hf₁C : f₁ ∈ C := P.mem_of_mem_inter_bond hpat (by simp)
  have hf₂C : f₂ ∈ C := P.mem_of_mem_inter_bond hpat (by simp)
  have hmin' : G.IsMinimalEven ((C \ (C \ P.EL)) ∪ {e₀}) := by
    apply hmin.replace_singleton Finset.sdiff_subset
    · exact ⟨f₁, Finset.mem_sdiff.mpr ⟨hf₁C, Finset.disjoint_left.mp P.bond_disjoint_EL hf₁⟩⟩
    · rw [sdiff_sdiff_eq_inter]
      exact fun h ↦ he₀EL (Finset.mem_inter.mp h).2
    · intro w
      have h0 : G.boundary C w = 0 := hmin.2.1 w
      rw [G.boundary_sdiff_part, h0, zero_add,
        P.boundary_inter_EL_of_pair hC hmin hf₁ hf₂ hne h₁ h₂ hpat, G.boundary_singleton, he₀.1,
        he₀.2]
  rw [sdiff_sdiff_eq_inter] at hmin'
  refine ⟨hmin', ?_⟩
  apply P.support_left_general hC
  · intro g hg i
    rw [Finset.mem_singleton] at hg
    subst hg
    rcases fin2_cases i with rfl | rfl
    · exact ⟨f₁, hpat ▸ (by simp), he₀.1.trans h₁.1.symm⟩
    · exact ⟨f₂, hpat ▸ (by simp), he₀.2.trans h₂.1.symm⟩
  · intro f hf
    rw [hpat] at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact ⟨e₀, by simp, 0, he₀.1.trans h₁.1.symm⟩
    · rw [Finset.mem_singleton] at hf
      subst hf
      exact ⟨e₀, by simp, 1, he₀.2.trans h₂.1.symm⟩

/-- Replacing a bond pair from different couples by the path through both cap vertices. -/
theorem right_replace_two {f₁ f₂ g₁ g₂ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hg₁ : G.endAt g₁ 0 = P.x ∧ G.endAt g₁ 1 = p') (hg₂ : G.endAt g₂ 0 = P.y ∧ G.endAt g₂ 1 = q')
    (hpat : C ∩ P.bond = {f₁, f₂}) :
    G.IsMinimalEven ((C ∩ P.ER) ∪ {g₁, P.exy, g₂}) ∧
      G.edgeSupport ((C ∩ P.ER) ∪ {g₁, P.exy, g₂}) =
        (G.edgeSupport C ∩ P.R) ∪ {P.x, P.y} := by
  have hp' : p' ∈ P.R := h₁.2 ▸ (P.bond_ends f₁ hf₁).2
  have hq' : q' ∈ P.R := h₂.2 ▸ (P.bond_ends f₂ hf₂).2
  have hf₁C : f₁ ∈ C := P.mem_of_mem_inter_bond hpat (by simp)
  have hg₁ER : g₁ ∉ P.ER := P.notin_ER_of_end (i := 0) (hg₁.1 ▸ P.x_notin_R)
  have hg₂ER : g₂ ∉ P.ER := P.notin_ER_of_end (i := 0) (hg₂.1 ▸ P.y_notin_R)
  have hg₁xy : g₁ ≠ P.exy :=
    ne_of_end1 (by rw [hg₁.2, P.exy_ends.2]; exact fun h ↦ P.y_notin_R (h ▸ hp'))
  have hg₂xy : g₂ ≠ P.exy := ne_of_end0 (by rw [hg₂.1, P.exy_ends.1]; exact P.x_ne_y.symm)
  have hg₁g₂ : g₁ ≠ g₂ := ne_of_end0 (by rw [hg₁.1, hg₂.1]; exact P.x_ne_y)
  have hxp' : P.x ≠ p' := fun h ↦ P.x_notin_R (h ▸ hp')
  have hyq' : P.y ≠ q' := fun h ↦ P.y_notin_R (h ▸ hq')
  have hxq' : P.x ≠ q' := fun h ↦ P.x_notin_R (h ▸ hq')
  have hyp' : P.y ≠ p' := fun h ↦ P.y_notin_R (h ▸ hp')
  have hbdQ : ∀ w, G.boundary {g₁, P.exy, g₂} w =
      (if p' = w then 1 else 0) + (if q' = w then 1 else 0) := by
    intro w
    have hnot1 : g₁ ∉ ({P.exy, g₂} : Finset E) := by simp [hg₁xy, hg₁g₂]
    rw [G.boundary_insert_singleton hnot1, G.boundary_pair hg₂xy.symm, G.boundary_singleton, hg₁.1,
      hg₁.2, P.exy_ends.1, P.exy_ends.2, hg₂.1, hg₂.2]
    exact F₂_cancel_pair _ _ _ _
  have hmin' : G.IsMinimalEven ((C \ (C \ P.ER)) ∪ {g₁, P.exy, g₂}) := by
    apply hmin.replace Finset.sdiff_subset
    · exact ⟨f₁, Finset.mem_sdiff.mpr ⟨hf₁C, Finset.disjoint_left.mp P.bond_disjoint_ER hf₁⟩⟩
    · exact ⟨g₁, by simp⟩
    · rw [sdiff_sdiff_eq_inter, Finset.disjoint_left]
      intro e he hmem
      have hER := (Finset.mem_inter.mp hmem).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hg₁ER hER
      · exact P.exy_notin_ER hER
      · exact hg₂ER hER
    · intro w
      have h0 : G.boundary C w = 0 := hmin.2.1 w
      rw [G.boundary_sdiff_part, h0, zero_add,
        P.boundary_inter_ER_of_pair hC hmin hf₁ hf₂ hne h₁ h₂ hpat, hbdQ]
    · intro D₀ hsub heven
      rw [sdiff_sdiff_eq_inter] at hsub
      have hincx : ∀ e ∈ D₀, G.edgeIncidence P.x e =
          (if e = g₁ then 1 else 0) + (if e = P.exy then 1 else 0) := by
        intro e he
        rw [G.edgeIncidence_eq]
        rcases Finset.mem_union.mp (hsub he) with hER | hQ'
        · have hends := P.ER_ends e (Finset.mem_inter.mp hER).2
          have hne1 : e ≠ g₁ := fun h ↦ hg₁ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hne2 : e ≠ P.exy := fun h ↦ P.exy_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hx0 : ¬ G.endAt e 0 = P.x := fun h ↦ P.x_notin_R (h ▸ hends 0)
          have hx1 : ¬ G.endAt e 1 = P.x := fun h ↦ P.x_notin_R (h ▸ hends 1)
          rw [if_neg hx0, if_neg hx1, if_neg hne1, if_neg hne2]
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
          rcases hQ' with rfl | rfl | rfl
          · rw [hg₁.1, hg₁.2, if_pos rfl, if_neg hxp'.symm, if_pos rfl, if_neg hg₁xy]
          · rw [P.exy_ends.1, P.exy_ends.2, if_pos rfl, if_neg P.x_ne_y.symm,
              if_neg hg₁xy.symm, if_pos rfl]
            decide
          · rw [hg₂.1, hg₂.2, if_neg P.x_ne_y.symm, if_neg hxq'.symm, if_neg hg₁g₂.symm,
              if_neg hg₂xy]
      have hincy : ∀ e ∈ D₀, G.edgeIncidence P.y e =
          (if e = P.exy then 1 else 0) + (if e = g₂ then 1 else 0) := by
        intro e he
        rw [G.edgeIncidence_eq]
        rcases Finset.mem_union.mp (hsub he) with hER | hQ'
        · have hends := P.ER_ends e (Finset.mem_inter.mp hER).2
          have hne1 : e ≠ P.exy := fun h ↦ P.exy_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hne2 : e ≠ g₂ := fun h ↦ hg₂ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hy0 : ¬ G.endAt e 0 = P.y := fun h ↦ P.y_notin_R (h ▸ hends 0)
          have hy1 : ¬ G.endAt e 1 = P.y := fun h ↦ P.y_notin_R (h ▸ hends 1)
          rw [if_neg hy0, if_neg hy1, if_neg hne1, if_neg hne2]
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
          rcases hQ' with rfl | rfl | rfl
          · rw [hg₁.1, hg₁.2, if_neg P.x_ne_y, if_neg hyp'.symm, if_neg hg₁xy,
              if_neg hg₁g₂]
          · rw [P.exy_ends.1, P.exy_ends.2, if_neg P.x_ne_y, if_pos rfl, if_pos rfl,
              if_neg hg₂xy.symm]
            decide
          · rw [hg₂.1, hg₂.2, if_pos rfl, if_neg hyq'.symm, if_neg hg₂xy, if_pos rfl]
            decide
      have hx : G.boundary D₀ P.x = 0 := heven P.x
      have hy : G.boundary D₀ P.y = 0 := heven P.y
      rw [G.boundary_eq_sum_of _ hincx, sum_two_indicators] at hx
      rw [G.boundary_eq_sum_of _ hincy, sum_two_indicators] at hy
      have hiff1 := mem_iff_of_indicator_add hx
      have hiff2 := mem_iff_of_indicator_add hy
      by_cases hg : g₁ ∈ D₀
      · right
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hg
        · exact hiff1.mp hg
        · exact hiff2.mp (hiff1.mp hg)
      · left
        rw [Finset.disjoint_left]
        intro e he hQ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
        rcases hQ' with rfl | rfl | rfl
        · exact hg he
        · exact hg (hiff1.mpr he)
        · exact hg (hiff1.mpr (hiff2.mpr he))
  rw [sdiff_sdiff_eq_inter] at hmin'
  refine ⟨hmin', ?_⟩
  apply P.support_right_general hC
  · intro g hg i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [hg₁.1]; simp)
      · exact Or.inr ⟨f₁, hpat ▸ (by simp), hg₁.2.trans h₁.2.symm⟩
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [P.exy_ends.1]; simp)
      · exact Or.inl (by rw [P.exy_ends.2]; simp)
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [hg₂.1]; simp)
      · exact Or.inr ⟨f₂, hpat ▸ (by simp), hg₂.2.trans h₂.2.symm⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨P.exy, by simp, 0, P.exy_ends.1⟩
    · exact ⟨P.exy, by simp, 1, P.exy_ends.2⟩
  · intro f hf
    rw [hpat] at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact ⟨g₁, by simp, 1, hg₁.2.trans h₁.2.symm⟩
    · rw [Finset.mem_singleton] at hf
      subst hf
      exact ⟨g₂, by simp, 1, hg₂.2.trans h₂.2.symm⟩

/-- Replacing a bond pair from one couple by the two cap edges at its cap vertex. -/
theorem right_replace_pair {f₁ f₂ g₁ g₂ : E} {p q p' q' z : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hz : z ∉ P.R) (hp'q' : p' ≠ q')
    (hg₁ : G.endAt g₁ 0 = z ∧ G.endAt g₁ 1 = p') (hg₂ : G.endAt g₂ 0 = z ∧ G.endAt g₂ 1 = q')
    (hpat : C ∩ P.bond = {f₁, f₂}) :
    G.IsMinimalEven ((C ∩ P.ER) ∪ {g₁, g₂}) ∧
      G.edgeSupport ((C ∩ P.ER) ∪ {g₁, g₂}) = (G.edgeSupport C ∩ P.R) ∪ {z} := by
  have hp' : p' ∈ P.R := h₁.2 ▸ (P.bond_ends f₁ hf₁).2
  have hq' : q' ∈ P.R := h₂.2 ▸ (P.bond_ends f₂ hf₂).2
  have hf₁C : f₁ ∈ C := P.mem_of_mem_inter_bond hpat (by simp)
  have hg₁ER : g₁ ∉ P.ER := P.notin_ER_of_end (i := 0) (hg₁.1 ▸ hz)
  have hg₂ER : g₂ ∉ P.ER := P.notin_ER_of_end (i := 0) (hg₂.1 ▸ hz)
  have hg₁g₂ : g₁ ≠ g₂ := ne_of_end1 (by rw [hg₁.2, hg₂.2]; exact hp'q')
  have hzp' : z ≠ p' := fun h ↦ hz (h ▸ hp')
  have hzq' : z ≠ q' := fun h ↦ hz (h ▸ hq')
  have hbdQ : ∀ w, G.boundary {g₁, g₂} w =
      (if p' = w then 1 else 0) + (if q' = w then 1 else 0) := by
    intro w
    rw [G.boundary_pair hg₁g₂, hg₁.1, hg₁.2, hg₂.1, hg₂.2]
    exact F₂_cancel_single _ _ _
  have hmin' : G.IsMinimalEven ((C \ (C \ P.ER)) ∪ {g₁, g₂}) := by
    apply hmin.replace Finset.sdiff_subset
    · exact ⟨f₁, Finset.mem_sdiff.mpr ⟨hf₁C, Finset.disjoint_left.mp P.bond_disjoint_ER hf₁⟩⟩
    · exact ⟨g₁, by simp⟩
    · rw [sdiff_sdiff_eq_inter, Finset.disjoint_left]
      intro e he hmem
      have hER := (Finset.mem_inter.mp hmem).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hg₁ER hER
      · exact hg₂ER hER
    · intro w
      have h0 : G.boundary C w = 0 := hmin.2.1 w
      rw [G.boundary_sdiff_part, h0, zero_add,
        P.boundary_inter_ER_of_pair hC hmin hf₁ hf₂ hne h₁ h₂ hpat, hbdQ]
    · intro D₀ hsub heven
      rw [sdiff_sdiff_eq_inter] at hsub
      have hincz : ∀ e ∈ D₀, G.edgeIncidence z e =
          (if e = g₁ then 1 else 0) + (if e = g₂ then 1 else 0) := by
        intro e he
        rw [G.edgeIncidence_eq]
        rcases Finset.mem_union.mp (hsub he) with hER | hQ'
        · have hends := P.ER_ends e (Finset.mem_inter.mp hER).2
          have hne1 : e ≠ g₁ := fun h ↦ hg₁ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hne2 : e ≠ g₂ := fun h ↦ hg₂ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hz0 : ¬ G.endAt e 0 = z := fun h ↦ hz (h ▸ hends 0)
          have hz1 : ¬ G.endAt e 1 = z := fun h ↦ hz (h ▸ hends 1)
          rw [if_neg hz0, if_neg hz1, if_neg hne1, if_neg hne2]
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
          rcases hQ' with rfl | rfl
          · rw [hg₁.1, hg₁.2, if_pos rfl, if_neg hzp'.symm, if_pos rfl, if_neg hg₁g₂]
          · rw [hg₂.1, hg₂.2, if_pos rfl, if_neg hzq'.symm, if_neg hg₁g₂.symm, if_pos rfl]
            decide
      have hzz : G.boundary D₀ z = 0 := heven z
      rw [G.boundary_eq_sum_of _ hincz, sum_two_indicators] at hzz
      have hiff := mem_iff_of_indicator_add hzz
      by_cases hg : g₁ ∈ D₀
      · right
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hg
        · exact hiff.mp hg
      · left
        rw [Finset.disjoint_left]
        intro e he hQ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
        rcases hQ' with rfl | rfl
        · exact hg he
        · exact hg (hiff.mpr he)
  rw [sdiff_sdiff_eq_inter] at hmin'
  refine ⟨hmin', ?_⟩
  apply P.support_right_general hC
  · intro g hg i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [hg₁.1]; simp)
      · exact Or.inr ⟨f₁, hpat ▸ (by simp), hg₁.2.trans h₁.2.symm⟩
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [hg₂.1]; simp)
      · exact Or.inr ⟨f₂, hpat ▸ (by simp), hg₂.2.trans h₂.2.symm⟩
  · intro z' hz'
    rw [Finset.mem_singleton] at hz'
    subst hz'
    exact ⟨g₁, by simp, 0, hg₁.1⟩
  · intro f hf
    rw [hpat] at hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact ⟨g₁, by simp, 1, hg₁.2.trans h₁.2.symm⟩
    · rw [Finset.mem_singleton] at hf
      subst hf
      exact ⟨g₂, by simp, 1, hg₂.2.trans h₂.2.symm⟩

omit hC hmin [DecidableEq V] in
theorem bond_eq_insert : P.bond = insert P.faa (insert P.fbb {P.fcc, P.fdd}) := rfl

/-- The boundary of the left part when all four bond edges are present. -/
theorem boundary_inter_EL_of_all (hpat : C ∩ P.bond = P.bond) (w : V) :
    G.boundary (C ∩ P.EL) w =
      (if P.a = w then 1 else 0) + ((if P.b = w then 1 else 0) +
        ((if P.c = w then 1 else 0) + (if P.d = w then 1 else 0))) := by
  by_cases hw : w ∈ P.L
  · have ha' : ¬ P.a' = w := fun h ↦ P.notin_L_of_mem_R P.a'_mem (h ▸ hw)
    have hb' : ¬ P.b' = w := fun h ↦ P.notin_L_of_mem_R P.b'_mem (h ▸ hw)
    have hc' : ¬ P.c' = w := fun h ↦ P.notin_L_of_mem_R P.c'_mem (h ▸ hw)
    have hd' : ¬ P.d' = w := fun h ↦ P.notin_L_of_mem_R P.d'_mem (h ▸ hw)
    rw [P.boundary_inter_EL_of_mem_L hC hmin.2.1 hw, hpat, P.bond_eq_insert,
      G.boundary_insert_singleton (by simp [P.faa_ne_fbb, P.faa_ne_fcc, P.faa_ne_fdd]),
      G.boundary_insert_singleton (by simp [P.fbb_ne_fcc, P.fbb_ne_fdd]),
      G.boundary_pair P.fcc_ne_fdd, G.boundary_singleton, G.boundary_singleton,
      P.faa_ends.1, P.faa_ends.2, P.fbb_ends.1, P.fbb_ends.2, P.fcc_ends.1, P.fcc_ends.2,
      P.fdd_ends.1, P.fdd_ends.2, if_neg ha', if_neg hb', if_neg hc', if_neg hd', add_zero,
      add_zero, add_zero, add_zero]
  · have ha : ¬ P.a = w := fun h ↦ hw (h ▸ P.a_mem)
    have hb : ¬ P.b = w := fun h ↦ hw (h ▸ P.b_mem)
    have hc : ¬ P.c = w := fun h ↦ hw (h ▸ P.c_mem)
    have hd : ¬ P.d = w := fun h ↦ hw (h ▸ P.d_mem)
    rw [P.boundary_inter_EL_eq_zero hw, if_neg ha, if_neg hb, if_neg hc, if_neg hd, add_zero,
      add_zero, add_zero]

/-- The boundary of the right part when all four bond edges are present. -/
theorem boundary_inter_ER_of_all (hpat : C ∩ P.bond = P.bond) (w : V) :
    G.boundary (C ∩ P.ER) w =
      (if P.a' = w then 1 else 0) + ((if P.b' = w then 1 else 0) +
        ((if P.c' = w then 1 else 0) + (if P.d' = w then 1 else 0))) := by
  by_cases hw : w ∈ P.R
  · have ha : ¬ P.a = w := fun h ↦ P.notin_R_of_mem_L P.a_mem (h ▸ hw)
    have hb : ¬ P.b = w := fun h ↦ P.notin_R_of_mem_L P.b_mem (h ▸ hw)
    have hc : ¬ P.c = w := fun h ↦ P.notin_R_of_mem_L P.c_mem (h ▸ hw)
    have hd : ¬ P.d = w := fun h ↦ P.notin_R_of_mem_L P.d_mem (h ▸ hw)
    rw [P.boundary_inter_ER_of_mem_R hC hmin.2.1 hw, hpat, P.bond_eq_insert,
      G.boundary_insert_singleton (by simp [P.faa_ne_fbb, P.faa_ne_fcc, P.faa_ne_fdd]),
      G.boundary_insert_singleton (by simp [P.fbb_ne_fcc, P.fbb_ne_fdd]),
      G.boundary_pair P.fcc_ne_fdd, G.boundary_singleton, G.boundary_singleton,
      P.faa_ends.1, P.faa_ends.2, P.fbb_ends.1, P.fbb_ends.2, P.fcc_ends.1, P.fcc_ends.2,
      P.fdd_ends.1, P.fdd_ends.2, if_neg ha, if_neg hb, if_neg hc, if_neg hd, zero_add,
      zero_add, zero_add, zero_add]
  · have ha' : ¬ P.a' = w := fun h ↦ hw (h ▸ P.a'_mem)
    have hb' : ¬ P.b' = w := fun h ↦ hw (h ▸ P.b'_mem)
    have hc' : ¬ P.c' = w := fun h ↦ hw (h ▸ P.c'_mem)
    have hd' : ¬ P.d' = w := fun h ↦ hw (h ▸ P.d'_mem)
    rw [P.boundary_inter_ER_eq_zero hw, if_neg ha', if_neg hb', if_neg hc', if_neg hd', add_zero,
      add_zero, add_zero]

omit hC hmin in
/-- An even subset of the left candidate containing exactly one virtual edge yields a path in
the left part between the ends of that edge. -/
theorem path_of_even_subset {X : Finset E} {e e' : E}
    (hX : X ⊆ (C ∩ P.EL) ∪ {e, e'}) (hXeven : G.IsEvenEdgeSet X) (he : e ∈ X) (he' : e' ∉ X) :
    X \ {e} ⊆ C ∩ P.EL ∧ ∀ w, G.boundary (X \ {e}) w = G.boundary {e} w := by
  constructor
  · intro f hf
    have hm := Finset.mem_sdiff.mp hf
    rcases Finset.mem_union.mp (hX hm.1) with h | h
    · exact h
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact absurd (Finset.mem_singleton_self _) hm.2
      · rw [Finset.mem_singleton] at h
        subst h
        exact absurd hm.1 he'
  · intro w
    have h0 : G.boundary X w = 0 := hXeven w
    rw [G.boundary_sdiff (Finset.singleton_subset_iff.mpr he), h0, zero_add]

omit hC in
/-- An even set containing one cap pair but not the other cannot exist when the corresponding
left path is available: the reassembled cycle would be a proper even subset of `C`. -/
theorem no_half_pair (hall : ∀ f ∈ P.bond, f ∈ C)
    {P₁ : Finset E} (hP₁ : P₁ ⊆ C ∩ P.EL) {p q p' q' z : V} {f₁ f₂ f₃ g₁ g₂ : E}
    (hbdP₁ : ∀ w, G.boundary P₁ w = (if p = w then 1 else 0) + (if q = w then 1 else 0))
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (hf₃ : f₃ ∈ P.bond) (hf₃₁ : f₃ ≠ f₁) (hf₃₂ : f₃ ≠ f₂)
    (_hz : z ∉ P.R) (hg₁ : G.endAt g₁ 0 = z ∧ G.endAt g₁ 1 = p')
    (hg₂ : G.endAt g₂ 0 = z ∧ G.endAt g₂ 1 = q') (hg₁g₂ : g₁ ≠ g₂)
    {D₂ : Finset E} (hQ' : D₂ \ {g₁, g₂} ⊆ C ∩ P.ER) (heven : G.IsEvenEdgeSet D₂)
    (hg₁D : g₁ ∈ D₂) (hg₂D : g₂ ∈ D₂) : False := by
  have hbdQ' : ∀ w, G.boundary (D₂ \ {g₁, g₂}) w =
      (if p' = w then 1 else 0) + (if q' = w then 1 else 0) := by
    intro w
    have h0 : G.boundary D₂ w = 0 := heven w
    have hsub : ({g₁, g₂} : Finset E) ⊆ D₂ := by
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hg₁D
      · rw [Finset.mem_singleton] at hg
        subst hg
        exact hg₂D
    rw [G.boundary_sdiff hsub, h0, zero_add, G.boundary_pair hg₁g₂, hg₁.1, hg₁.2, hg₂.1, hg₂.2]
    exact F₂_cancel_single _ _ _
  let Z : Finset E := P₁ ∪ ({f₁, f₂} ∪ (D₂ \ {g₁, g₂}))
  have hZsub : Z ⊆ C := by
    apply Finset.union_subset (hP₁.trans Finset.inter_subset_left)
    apply Finset.union_subset _ (hQ'.trans Finset.inter_subset_left)
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hall _ hf₁
    · rw [Finset.mem_singleton] at hf
      subst hf
      exact hall _ hf₂
  have hd1 : Disjoint ({f₁, f₂} : Finset E) (D₂ \ {g₁, g₂}) := by
    apply Finset.disjoint_of_subset_right (hQ'.trans Finset.inter_subset_right)
    apply Finset.disjoint_of_subset_left _ P.bond_disjoint_ER
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hf₁
    · rw [Finset.mem_singleton] at hf
      subst hf
      exact hf₂
  have hd2 : Disjoint P₁ ({f₁, f₂} ∪ (D₂ \ {g₁, g₂})) := by
    rw [Finset.disjoint_union_right]
    constructor
    · apply Finset.disjoint_of_subset_left (hP₁.trans Finset.inter_subset_right)
      apply Finset.disjoint_of_subset_right _ P.bond_disjoint_EL.symm
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hf₁
      · rw [Finset.mem_singleton] at hf
        subst hf
        exact hf₂
    · exact Finset.disjoint_of_subset_left (hP₁.trans Finset.inter_subset_right)
        (Finset.disjoint_of_subset_right (hQ'.trans Finset.inter_subset_right) P.EL_disjoint_ER)
  have hZeven : G.IsEvenEdgeSet Z := by
    intro w
    change G.boundary Z w = 0
    rw [G.boundary_union _ _ hd2, G.boundary_union _ _ hd1, hbdP₁, G.boundary_pair hne, hbdQ',
      h₁.1, h₁.2, h₂.1, h₂.2]
    exact F₂_sum_pairs _ _ _ _
  have hZne : Z.Nonempty := ⟨f₁, Finset.mem_union_right _ (Finset.mem_union_left _ (by simp))⟩
  have hZ : Z = C := hmin.eq_of_subset hZne hZsub hZeven
  have hf₃C : f₃ ∈ Z := hZ ▸ hall _ hf₃
  rcases Finset.mem_union.mp hf₃C with h | h
  · exact Finset.disjoint_left.mp P.bond_disjoint_EL hf₃ (Finset.mem_inter.mp (hP₁ h)).2
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hf₃₁ h
      · exact hf₃₂ (Finset.mem_singleton.mp h)
    · exact Finset.disjoint_left.mp P.bond_disjoint_ER hf₃ (Finset.mem_inter.mp (hQ' h)).2

/-- **Four bond edges.**  Either the left factor or the right factor inherits a Hamilton cycle. -/
theorem four_bond (hpat : C ∩ P.bond = P.bond) :
    (G.IsMinimalEven ((C ∩ P.EL) ∪ {P.eab, P.ecd}) ∧
        G.edgeSupport ((C ∩ P.EL) ∪ {P.eab, P.ecd}) = G.edgeSupport C ∩ P.L) ∨
    (G.IsMinimalEven ((C ∩ P.ER) ∪ {P.exa, P.exb, P.eyc, P.eyd}) ∧
        G.edgeSupport ((C ∩ P.ER) ∪ {P.exa, P.exb, P.eyc, P.eyd}) =
          (G.edgeSupport C ∩ P.R) ∪ {P.x, P.y}) := by
  have hall : ∀ f ∈ P.bond, f ∈ C := fun f hf ↦ (Finset.mem_inter.mp (hpat ▸ hf)).1
  have hfaa := hall P.faa (by simp [bond])
  have hfbb := hall P.fbb (by simp [bond])
  have hfcc := hall P.fcc (by simp [bond])
  have hfdd := hall P.fdd (by simp [bond])
  have heabecd : P.eab ≠ P.ecd := ne_of_end0 (by rw [P.eab_ends.1, P.ecd_ends.1]; exact P.ac_ne)
  -- boundaries of the two candidate replacements
  have hbdA : ∀ w, G.boundary {P.eab, P.ecd} w =
      (if P.a = w then 1 else 0) + ((if P.b = w then 1 else 0) +
        ((if P.c = w then 1 else 0) + (if P.d = w then 1 else 0))) := by
    intro w
    rw [G.boundary_pair heabecd, P.eab_ends.1, P.eab_ends.2, P.ecd_ends.1, P.ecd_ends.2, add_assoc]
  have hexaexb : P.exa ≠ P.exb :=
    ne_of_end1 (by rw [P.exa_ends.2, P.exb_ends.2]; exact P.a'b'_ne)
  have heyceyd : P.eyc ≠ P.eyd :=
    ne_of_end1 (by rw [P.eyc_ends.2, P.eyd_ends.2]; exact P.c'd'_ne)
  have hexaeyc : P.exa ≠ P.eyc := ne_of_end0 (by rw [P.exa_ends.1, P.eyc_ends.1]; exact P.x_ne_y)
  have hexaeyd : P.exa ≠ P.eyd := ne_of_end0 (by rw [P.exa_ends.1, P.eyd_ends.1]; exact P.x_ne_y)
  have hexbeyc : P.exb ≠ P.eyc := ne_of_end0 (by rw [P.exb_ends.1, P.eyc_ends.1]; exact P.x_ne_y)
  have hexbeyd : P.exb ≠ P.eyd := ne_of_end0 (by rw [P.exb_ends.1, P.eyd_ends.1]; exact P.x_ne_y)
  have hQB : ({P.exa, P.exb, P.eyc, P.eyd} : Finset E) =
      insert P.exa (insert P.exb {P.eyc, P.eyd}) := rfl
  have hbdB : ∀ w, G.boundary {P.exa, P.exb, P.eyc, P.eyd} w =
      (if P.a' = w then 1 else 0) + ((if P.b' = w then 1 else 0) +
        ((if P.c' = w then 1 else 0) + (if P.d' = w then 1 else 0))) := by
    intro w
    rw [hQB, G.boundary_insert_singleton (by simp [hexaexb, hexaeyc, hexaeyd]),
      G.boundary_insert_singleton (by simp [hexbeyc, hexbeyd]), G.boundary_pair heyceyd,
      G.boundary_singleton, G.boundary_singleton, P.exa_ends.1, P.exa_ends.2, P.exb_ends.1,
      P.exb_ends.2, P.eyc_ends.1, P.eyc_ends.2, P.eyd_ends.1, P.eyd_ends.2]
    exact F₂_cancel_four _ _ _ _ _ _
  have hQAdisj : Disjoint ({P.eab, P.ecd} : Finset E) (C ∩ P.EL) := by
    rw [Finset.disjoint_left]
    intro e he hmem
    rcases Finset.mem_insert.mp he with rfl | he
    · exact P.eab_notin (Finset.mem_inter.mp hmem).2
    · rw [Finset.mem_singleton] at he
      subst he
      exact P.ecd_notin (Finset.mem_inter.mp hmem).2
  have hevenA : G.IsEvenEdgeSet ((C ∩ P.EL) ∪ {P.eab, P.ecd}) := by
    intro w
    change G.boundary _ w = 0
    rw [G.boundary_union _ _ hQAdisj.symm, P.boundary_inter_EL_of_all hC hmin hpat, hbdA,
      F₂_add_self]
  have hsuppA : G.edgeSupport ((C ∩ P.EL) ∪ {P.eab, P.ecd}) = G.edgeSupport C ∩ P.L := by
    apply P.support_left_general hC
    · intro g hg i
      rcases Finset.mem_insert.mp hg with rfl | hg
      · rcases fin2_cases i with rfl | rfl
        · exact ⟨P.faa, Finset.mem_inter.mpr ⟨hfaa, by simp [bond]⟩, P.eab_ends.1.trans P.faa_ends.1.symm⟩
        · exact ⟨P.fbb, Finset.mem_inter.mpr ⟨hfbb, by simp [bond]⟩, P.eab_ends.2.trans P.fbb_ends.1.symm⟩
      · rw [Finset.mem_singleton] at hg
        subst hg
        rcases fin2_cases i with rfl | rfl
        · exact ⟨P.fcc, Finset.mem_inter.mpr ⟨hfcc, by simp [bond]⟩, P.ecd_ends.1.trans P.fcc_ends.1.symm⟩
        · exact ⟨P.fdd, Finset.mem_inter.mpr ⟨hfdd, by simp [bond]⟩, P.ecd_ends.2.trans P.fdd_ends.1.symm⟩
    · intro f hf
      rcases P.mem_bond.mp (Finset.mem_inter.mp hf).2 with rfl | rfl | rfl | rfl
      · exact ⟨P.eab, by simp, 0, P.eab_ends.1.trans P.faa_ends.1.symm⟩
      · exact ⟨P.eab, by simp, 1, P.eab_ends.2.trans P.fbb_ends.1.symm⟩
      · exact ⟨P.ecd, by simp, 0, P.ecd_ends.1.trans P.fcc_ends.1.symm⟩
      · exact ⟨P.ecd, by simp, 1, P.ecd_ends.2.trans P.fdd_ends.1.symm⟩
  by_cases hminA : G.IsMinimalEven ((C ∩ P.EL) ∪ {P.eab, P.ecd})
  · exact Or.inl ⟨hminA, hsuppA⟩
  right
  -- the left candidate is not minimal: extract the two left paths
  have hCAne : ((C ∩ P.EL) ∪ {P.eab, P.ecd}).Nonempty := ⟨P.eab, by simp⟩
  unfold IsMinimalEven at hminA
  push Not at hminA
  obtain ⟨D₀, hD₀ne, hD₀sub, hD₀even, hD₀ne'⟩ := hminA hCAne hevenA
  have hpaths : ∃ P₁ P₂ : Finset E, P₁ ⊆ C ∩ P.EL ∧ P₂ ⊆ C ∩ P.EL ∧
      (∀ w, G.boundary P₁ w = (if P.a = w then 1 else 0) + (if P.b = w then 1 else 0)) ∧
      (∀ w, G.boundary P₂ w = (if P.c = w then 1 else 0) + (if P.d = w then 1 else 0)) := by
    have hcomp_sub : ((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀ ⊆ (C ∩ P.EL) ∪ {P.eab, P.ecd} :=
      Finset.sdiff_subset
    have hcomp_even : G.IsEvenEdgeSet (((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀) := by
      intro w
      change G.boundary _ w = 0
      have h1 : G.boundary ((C ∩ P.EL) ∪ {P.eab, P.ecd}) w = 0 := hevenA w
      have h2 : G.boundary D₀ w = 0 := hD₀even w
      rw [G.boundary_sdiff hD₀sub, h1, h2, add_zero]
    by_cases heab : P.eab ∈ D₀ <;> by_cases hecd : P.ecd ∈ D₀
    · -- both virtual edges in D₀: D₀ is all of the candidate
      exfalso
      apply hD₀ne'
      have hQsub : ({P.eab, P.ecd} : Finset E) ⊆ D₀ := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact heab
        · rw [Finset.mem_singleton] at he
          subst he
          exact hecd
      let Dt : Finset E := (D₀ \ {P.eab, P.ecd}) ∪ (C \ P.EL)
      have hDtsub : Dt ⊆ C := by
        apply Finset.union_subset _ Finset.sdiff_subset
        intro e he
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hD₀sub hm.1) with h | h
        · exact (Finset.mem_inter.mp h).1
        · exact absurd h hm.2
      have hDtdisj : Disjoint (D₀ \ {P.eab, P.ecd}) (C \ P.EL) := by
        rw [Finset.disjoint_left]
        intro e he hmem
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hD₀sub hm.1) with h | h
        · exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp h).2
        · exact hm.2 h
      have hDteven : G.IsEvenEdgeSet Dt := by
        intro w
        change G.boundary Dt w = 0
        have h0 : G.boundary D₀ w = 0 := hD₀even w
        have hC0 : G.boundary C w = 0 := hmin.2.1 w
        rw [G.boundary_union _ _ hDtdisj, G.boundary_sdiff hQsub, h0, zero_add,
          G.boundary_sdiff_part, hC0, zero_add, P.boundary_inter_EL_of_all hC hmin hpat, hbdA,
          F₂_add_self]
      have hDtne : Dt.Nonempty :=
        ⟨P.faa, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hfaa, P.faa_notin_EL⟩)⟩
      have hDt : Dt = C := hmin.eq_of_subset hDtne hDtsub hDteven
      apply Finset.Subset.antisymm hD₀sub
      intro e he
      rcases Finset.mem_union.mp he with h | h
      · have hmem : e ∈ Dt := hDt ▸ (Finset.mem_inter.mp h).1
        rcases Finset.mem_union.mp hmem with h' | h'
        · exact (Finset.mem_sdiff.mp h').1
        · exact absurd (Finset.mem_inter.mp h).2 (Finset.mem_sdiff.mp h').2
      · exact hQsub h
    · -- eab ∈ D₀, ecd ∉ D₀
      obtain ⟨hP₁, hbd₁⟩ := P.path_of_even_subset hD₀sub hD₀even heab hecd
      have hecd' : P.ecd ∈ ((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀ :=
        Finset.mem_sdiff.mpr ⟨by simp, hecd⟩
      have heab' : P.eab ∉ ((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀ :=
        fun h ↦ (Finset.mem_sdiff.mp h).2 heab
      have hswap : ((C ∩ P.EL) ∪ {P.eab, P.ecd}) = (C ∩ P.EL) ∪ {P.ecd, P.eab} := by
        rw [Finset.pair_comm]
      obtain ⟨hP₂, hbd₂⟩ := P.path_of_even_subset (C := C) (hswap ▸ hcomp_sub) hcomp_even hecd' heab'
      refine ⟨D₀ \ {P.eab}, (((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀) \ {P.ecd}, hP₁, hP₂, ?_, ?_⟩
      · intro w
        rw [hbd₁, G.boundary_singleton, P.eab_ends.1, P.eab_ends.2]
      · intro w
        rw [hbd₂, G.boundary_singleton, P.ecd_ends.1, P.ecd_ends.2]
    · -- ecd ∈ D₀, eab ∉ D₀
      have hswap : ((C ∩ P.EL) ∪ {P.eab, P.ecd}) = (C ∩ P.EL) ∪ {P.ecd, P.eab} := by
        rw [Finset.pair_comm]
      obtain ⟨hP₂, hbd₂⟩ := P.path_of_even_subset (C := C) (hswap ▸ hD₀sub) hD₀even hecd heab
      have heab' : P.eab ∈ ((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀ :=
        Finset.mem_sdiff.mpr ⟨by simp, heab⟩
      have hecd' : P.ecd ∉ ((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀ :=
        fun h ↦ (Finset.mem_sdiff.mp h).2 hecd
      obtain ⟨hP₁, hbd₁⟩ := P.path_of_even_subset hcomp_sub hcomp_even heab' hecd'
      refine ⟨(((C ∩ P.EL) ∪ {P.eab, P.ecd}) \ D₀) \ {P.eab}, D₀ \ {P.ecd}, hP₁, hP₂, ?_, ?_⟩
      · intro w
        rw [hbd₁, G.boundary_singleton, P.eab_ends.1, P.eab_ends.2]
      · intro w
        rw [hbd₂, G.boundary_singleton, P.ecd_ends.1, P.ecd_ends.2]
    · -- neither: D₀ lies in C ∩ EL, contradicting minimality of C
      exfalso
      have hD₀C : D₀ ⊆ C := by
        intro e he
        rcases Finset.mem_union.mp (hD₀sub he) with h | h
        · exact (Finset.mem_inter.mp h).1
        · rcases Finset.mem_insert.mp h with rfl | h
          · exact absurd he heab
          · rw [Finset.mem_singleton] at h
            subst h
            exact absurd he hecd
      have hD₀eq : D₀ = C := hmin.eq_of_subset hD₀ne hD₀C hD₀even
      have hfaaD : P.faa ∈ D₀ := hD₀eq ▸ hfaa
      rcases Finset.mem_union.mp (hD₀sub hfaaD) with h | h
      · exact P.faa_notin_EL (Finset.mem_inter.mp h).2
      · have hfb : P.faa ∈ P.bond := by simp [bond]
        rcases Finset.mem_insert.mp h with h | h
        · exact P.eab_notin_bond (h ▸ hfb)
        · rw [Finset.mem_singleton] at h
          exact P.ecd_notin_bond (h ▸ hfb)
  obtain ⟨P₁, P₂, hP₁, hP₂, hbd₁, hbd₂⟩ := hpaths
  -- the right candidate is minimal
  have hminB : G.IsMinimalEven ((C \ (C \ P.ER)) ∪ {P.exa, P.exb, P.eyc, P.eyd}) := by
    apply hmin.replace Finset.sdiff_subset
    · exact ⟨P.faa, Finset.mem_sdiff.mpr ⟨hfaa, P.faa_notin_ER⟩⟩
    · exact ⟨P.exa, by simp⟩
    · rw [sdiff_sdiff_eq_inter, Finset.disjoint_left]
      intro e he hmem
      have hER := (Finset.mem_inter.mp hmem).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact P.exa_notin_ER hER
      · exact P.exb_notin_ER hER
      · exact P.eyc_notin_ER hER
      · exact P.eyd_notin_ER hER
    · intro w
      have h0 : G.boundary C w = 0 := hmin.2.1 w
      rw [G.boundary_sdiff_part, h0, zero_add, P.boundary_inter_ER_of_all hC hmin hpat, hbdB]
    · intro D₂ hsub heven
      rw [sdiff_sdiff_eq_inter] at hsub
      have hxa' : ¬ P.a' = P.x := fun h ↦ P.x_notin_R (h ▸ P.a'_mem)
      have hxb' : ¬ P.b' = P.x := fun h ↦ P.x_notin_R (h ▸ P.b'_mem)
      have hxc' : ¬ P.c' = P.x := fun h ↦ P.x_notin_R (h ▸ P.c'_mem)
      have hxd' : ¬ P.d' = P.x := fun h ↦ P.x_notin_R (h ▸ P.d'_mem)
      have hya' : ¬ P.a' = P.y := fun h ↦ P.y_notin_R (h ▸ P.a'_mem)
      have hyb' : ¬ P.b' = P.y := fun h ↦ P.y_notin_R (h ▸ P.b'_mem)
      have hyc' : ¬ P.c' = P.y := fun h ↦ P.y_notin_R (h ▸ P.c'_mem)
      have hyd' : ¬ P.d' = P.y := fun h ↦ P.y_notin_R (h ▸ P.d'_mem)
      have hincx : ∀ e ∈ D₂, G.edgeIncidence P.x e =
          (if e = P.exa then 1 else 0) + (if e = P.exb then 1 else 0) := by
        intro e he
        rw [G.edgeIncidence_eq]
        rcases Finset.mem_union.mp (hsub he) with hER | hQ'
        · have hends := P.ER_ends e (Finset.mem_inter.mp hER).2
          have hne1 : e ≠ P.exa := fun h ↦ P.exa_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hne2 : e ≠ P.exb := fun h ↦ P.exb_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hx0 : ¬ G.endAt e 0 = P.x := fun h ↦ P.x_notin_R (h ▸ hends 0)
          have hx1 : ¬ G.endAt e 1 = P.x := fun h ↦ P.x_notin_R (h ▸ hends 1)
          rw [if_neg hx0, if_neg hx1, if_neg hne1, if_neg hne2]
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
          rcases hQ' with rfl | rfl | rfl | rfl
          · rw [P.exa_ends.1, P.exa_ends.2, if_pos rfl, if_neg hxa', if_pos rfl, if_neg hexaexb]
          · rw [P.exb_ends.1, P.exb_ends.2, if_pos rfl, if_neg hxb', if_neg hexaexb.symm,
              if_pos rfl]
            decide
          · rw [P.eyc_ends.1, P.eyc_ends.2, if_neg P.x_ne_y.symm, if_neg hxc',
              if_neg hexaeyc.symm, if_neg hexbeyc.symm]
          · rw [P.eyd_ends.1, P.eyd_ends.2, if_neg P.x_ne_y.symm, if_neg hxd',
              if_neg hexaeyd.symm, if_neg hexbeyd.symm]
      have hincy : ∀ e ∈ D₂, G.edgeIncidence P.y e =
          (if e = P.eyc then 1 else 0) + (if e = P.eyd then 1 else 0) := by
        intro e he
        rw [G.edgeIncidence_eq]
        rcases Finset.mem_union.mp (hsub he) with hER | hQ'
        · have hends := P.ER_ends e (Finset.mem_inter.mp hER).2
          have hne1 : e ≠ P.eyc := fun h ↦ P.eyc_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hne2 : e ≠ P.eyd := fun h ↦ P.eyd_notin_ER (h ▸ (Finset.mem_inter.mp hER).2)
          have hy0 : ¬ G.endAt e 0 = P.y := fun h ↦ P.y_notin_R (h ▸ hends 0)
          have hy1 : ¬ G.endAt e 1 = P.y := fun h ↦ P.y_notin_R (h ▸ hends 1)
          rw [if_neg hy0, if_neg hy1, if_neg hne1, if_neg hne2]
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
          rcases hQ' with rfl | rfl | rfl | rfl
          · rw [P.exa_ends.1, P.exa_ends.2, if_neg P.x_ne_y, if_neg hya', if_neg hexaeyc,
              if_neg hexaeyd]
          · rw [P.exb_ends.1, P.exb_ends.2, if_neg P.x_ne_y, if_neg hyb', if_neg hexbeyc,
              if_neg hexbeyd]
          · rw [P.eyc_ends.1, P.eyc_ends.2, if_pos rfl, if_neg hyc', if_pos rfl, if_neg heyceyd]
          · rw [P.eyd_ends.1, P.eyd_ends.2, if_pos rfl, if_neg hyd', if_neg heyceyd.symm,
              if_pos rfl]
            decide
      have hx : G.boundary D₂ P.x = 0 := heven P.x
      have hy : G.boundary D₂ P.y = 0 := heven P.y
      rw [G.boundary_eq_sum_of _ hincx, sum_two_indicators] at hx
      rw [G.boundary_eq_sum_of _ hincy, sum_two_indicators] at hy
      have hiffx := mem_iff_of_indicator_add hx
      have hiffy := mem_iff_of_indicator_add hy
      have hsubQx : ∀ hxa : P.exa ∈ D₂, P.eyc ∉ D₂ → D₂ \ {P.exa, P.exb} ⊆ C ∩ P.ER := by
        intro hxa hyc e he
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hsub hm.1) with h | h
        · exact h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact absurd (by simp) hm.2
          · exact absurd (by simp) hm.2
          · exact absurd hm.1 hyc
          · exact absurd hm.1 (fun h ↦ hyc (hiffy.mpr h))
      have hsubQy : ∀ hyc : P.eyc ∈ D₂, P.exa ∉ D₂ → D₂ \ {P.eyc, P.eyd} ⊆ C ∩ P.ER := by
        intro hyc hxa e he
        have hm := Finset.mem_sdiff.mp he
        rcases Finset.mem_union.mp (hsub hm.1) with h | h
        · exact h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact absurd hm.1 hxa
          · exact absurd hm.1 (fun h ↦ hxa (hiffx.mpr h))
          · exact absurd (by simp) hm.2
          · exact absurd (by simp) hm.2
      by_cases hxa : P.exa ∈ D₂ <;> by_cases hyc : P.eyc ∈ D₂
      · right
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact hxa
        · exact hiffx.mp hxa
        · exact hyc
        · exact hiffy.mp hyc
      · exfalso
        exact P.no_half_pair hmin hall hP₁ hbd₁ P.faa_ends P.fbb_ends (by simp [bond])
          (by simp [bond]) P.faa_ne_fbb (by simp [bond])
          P.faa_ne_fcc.symm P.fbb_ne_fcc.symm P.x_notin_R P.exa_ends P.exb_ends hexaexb
          (hsubQx hxa hyc) heven hxa (hiffx.mp hxa)
      · exfalso
        exact P.no_half_pair hmin hall hP₂ hbd₂ P.fcc_ends P.fdd_ends (by simp [bond])
          (by simp [bond]) P.fcc_ne_fdd (by simp [bond]) P.faa_ne_fcc P.faa_ne_fdd P.y_notin_R
          P.eyc_ends P.eyd_ends heyceyd (hsubQy hyc hxa) heven hyc (hiffy.mp hyc)
      · left
        rw [Finset.disjoint_left]
        intro e he hQ'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hQ'
        rcases hQ' with rfl | rfl | rfl | rfl
        · exact hxa he
        · exact hxa (hiffx.mpr he)
        · exact hyc he
        · exact hyc (hiffy.mpr he)
  rw [sdiff_sdiff_eq_inter] at hminB
  refine ⟨hminB, ?_⟩
  apply P.support_right_general hC
  · intro g hg i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [P.exa_ends.1]; simp)
      · exact Or.inr ⟨P.faa, Finset.mem_inter.mpr ⟨hfaa, by simp [bond]⟩, P.exa_ends.2.trans P.faa_ends.2.symm⟩
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [P.exb_ends.1]; simp)
      · exact Or.inr ⟨P.fbb, Finset.mem_inter.mpr ⟨hfbb, by simp [bond]⟩, P.exb_ends.2.trans P.fbb_ends.2.symm⟩
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [P.eyc_ends.1]; simp)
      · exact Or.inr ⟨P.fcc, Finset.mem_inter.mpr ⟨hfcc, by simp [bond]⟩, P.eyc_ends.2.trans P.fcc_ends.2.symm⟩
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inl (by rw [P.eyd_ends.1]; simp)
      · exact Or.inr ⟨P.fdd, Finset.mem_inter.mpr ⟨hfdd, by simp [bond]⟩, P.eyd_ends.2.trans P.fdd_ends.2.symm⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨P.exa, by simp, 0, P.exa_ends.1⟩
    · exact ⟨P.eyc, by simp, 0, P.eyc_ends.1⟩
  · intro f hf
    rcases P.mem_bond.mp (Finset.mem_inter.mp hf).2 with rfl | rfl | rfl | rfl
    · exact ⟨P.exa, by simp, 1, P.exa_ends.2.trans P.faa_ends.2.symm⟩
    · exact ⟨P.exb, by simp, 1, P.exb_ends.2.trans P.fbb_ends.2.symm⟩
    · exact ⟨P.eyc, by simp, 1, P.eyc_ends.2.trans P.fcc_ends.2.symm⟩
    · exact ⟨P.eyd, by simp, 1, P.eyd_ends.2.trans P.fdd_ends.2.symm⟩

/-- Packaging: a left replacement is a Hamilton cycle of the left factor. -/
theorem hamA_of_pair {f₁ f₂ e₀ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (he₀ : G.endAt e₀ 0 = p ∧ G.endAt e₀ 1 = q) (he₀EL : e₀ ∉ P.EL) (he₀A : e₀ ∈ P.EA)
    (hpat : C ∩ P.bond = {f₁, f₂}) :
    ∃ D, G.IsHamiltonCycleIn P.EA (G.edgeSupport C ∩ P.L) D := by
  obtain ⟨hm, hs⟩ := P.left_replace hC hmin hf₁ hf₂ hne h₁ h₂ he₀ he₀EL hpat
  refine ⟨_, ?_, hm, hs⟩
  apply Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
  exact Finset.singleton_subset_iff.mpr he₀A

/-- Packaging: a mixed right replacement is a Hamilton cycle of the right factor. -/
theorem hamB_of_mixed {f₁ f₂ g₁ g₂ : E} {p q p' q' : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hg₁ : G.endAt g₁ 0 = P.x ∧ G.endAt g₁ 1 = p') (hg₂ : G.endAt g₂ 0 = P.y ∧ G.endAt g₂ 1 = q')
    (hg₁B : g₁ ∈ P.EB) (hg₂B : g₂ ∈ P.EB) (hpat : C ∩ P.bond = {f₁, f₂}) :
    ∃ D, G.IsHamiltonCycleIn P.EB ((G.edgeSupport C ∩ P.R) ∪ {P.x, P.y}) D := by
  obtain ⟨hm, hs⟩ := P.right_replace_two hC hmin hf₁ hf₂ hne h₁ h₂ hg₁ hg₂ hpat
  refine ⟨_, ?_, hm, hs⟩
  apply Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
  intro g hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl
  · exact hg₁B
  · exact P.exy_mem_EB
  · exact hg₂B

/-- Packaging: a same-couple cap replacement is a Hamilton cycle of the right factor. -/
theorem hamB_of_cap {f₁ f₂ g₁ g₂ : E} {p q p' q' z : V}
    (hf₁ : f₁ ∈ P.bond) (hf₂ : f₂ ∈ P.bond) (hne : f₁ ≠ f₂)
    (h₁ : G.endAt f₁ 0 = p ∧ G.endAt f₁ 1 = p') (h₂ : G.endAt f₂ 0 = q ∧ G.endAt f₂ 1 = q')
    (hz : z ∉ P.R) (hp'q' : p' ≠ q')
    (hg₁ : G.endAt g₁ 0 = z ∧ G.endAt g₁ 1 = p') (hg₂ : G.endAt g₂ 0 = z ∧ G.endAt g₂ 1 = q')
    (hg₁B : g₁ ∈ P.EB) (hg₂B : g₂ ∈ P.EB) (hpat : C ∩ P.bond = {f₁, f₂}) :
    ∃ D, G.IsHamiltonCycleIn P.EB ((G.edgeSupport C ∩ P.R) ∪ {z}) D := by
  obtain ⟨hm, hs⟩ := P.right_replace_pair hC hmin hf₁ hf₂ hne h₁ h₂ hz hp'q' hg₁ hg₂ hpat
  refine ⟨_, ?_, hm, hs⟩
  apply Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
  intro g hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact hg₁B
  · exact hg₂B

/-- Packaging of the four-bond dichotomy. -/
theorem ham_of_four (hpat : C ∩ P.bond = P.bond) :
    (∃ D, G.IsHamiltonCycleIn P.EA (G.edgeSupport C ∩ P.L) D) ∨
    (∃ D, G.IsHamiltonCycleIn P.EB ((G.edgeSupport C ∩ P.R) ∪ {P.x, P.y}) D) := by
  rcases P.four_bond hC hmin hpat with ⟨hm, hs⟩ | ⟨hm, hs⟩
  · left
    refine ⟨_, ?_, hm, hs⟩
    apply Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
    exact Finset.subset_union_right
  · right
    refine ⟨_, ?_, hm, hs⟩
    apply Finset.union_subset (Finset.inter_subset_right.trans Finset.subset_union_left)
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact P.exa_mem_EB
    · exact P.exb_mem_EB
    · exact P.eyc_mem_EB
    · exact P.eyd_mem_EB

end Replacements

section Patterns

/-- The number of bond edges in an even set of product edges is even. -/
theorem bond_parity {C : Finset E} (hC : C ⊆ P.EG) (heven : G.IsEvenEdgeSet C) :
    ((if P.faa ∈ C then 1 else 0) + ((if P.fbb ∈ C then 1 else 0) +
      ((if P.fcc ∈ C then 1 else 0) + (if P.fdd ∈ C then 1 else 0))) : F₂) = 0 := by
  have hR : ∑ w ∈ P.R, G.boundary C w = 0 := Finset.sum_eq_zero (fun w _ ↦ heven w)
  have hswap : ∑ w ∈ P.R, G.boundary C w = ∑ e ∈ C, ∑ w ∈ P.R, G.edgeIncidence w e := by
    unfold boundary
    exact Finset.sum_comm
  have hinc : ∀ e ∈ C, ∑ w ∈ P.R, G.edgeIncidence w e = if e ∈ P.bond then 1 else 0 := by
    intro e he
    simp only [edgeIncidence, Finset.sum_add_distrib, Finset.sum_ite_eq]
    have hEG := hC he
    simp only [EG, Finset.mem_union] at hEG
    rcases hEG with (hEL | hER) | hb
    · have hends := P.EL_ends e hEL
      rw [if_neg (P.notin_R_of_mem_L (hends 0)), if_neg (P.notin_R_of_mem_L (hends 1)),
        if_neg (Finset.disjoint_right.mp P.bond_disjoint_EL hEL)]
      decide
    · have hends := P.ER_ends e hER
      rw [if_pos (hends 0), if_pos (hends 1),
        if_neg (Finset.disjoint_right.mp P.bond_disjoint_ER hER)]
      decide
    · have hends := P.bond_ends e hb
      rw [if_neg (P.notin_R_of_mem_L hends.1), if_pos hends.2, if_pos hb]
      decide
  have hcomm : ∑ e ∈ C, (if e ∈ P.bond then (1 : F₂) else 0) =
      ∑ f ∈ P.bond, (if f ∈ C then 1 else 0) := by
    calc
      ∑ e ∈ C, (if e ∈ P.bond then (1 : F₂) else 0) =
          ∑ e ∈ C, ∑ f ∈ P.bond, (if e = f then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.sum_ite_eq]
      _ = ∑ f ∈ P.bond, ∑ e ∈ C, (if e = f then 1 else 0) := Finset.sum_comm
      _ = ∑ f ∈ P.bond, (if f ∈ C then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro f _
            rw [Finset.sum_ite_eq']
  rw [hswap, Finset.sum_congr rfl hinc, hcomm, P.bond_eq_insert,
    Finset.sum_insert (by simp [P.faa_ne_fbb, P.faa_ne_fcc, P.faa_ne_fdd]),
    Finset.sum_insert (by simp [P.fbb_ne_fcc, P.fbb_ne_fdd]), Finset.sum_pair P.fcc_ne_fdd] at hR
  exact hR

/-- A Hamilton cycle of the product avoiding one vertex uses at least one bond edge. -/
theorem exists_bond_mem {C : Finset E} (hC : C ⊆ P.EG) (hmin : G.IsMinimalEven C) {v : V}
    (hsupp : G.edgeSupport C = P.VG.erase v) : ∃ f ∈ P.bond, f ∈ C := by
  by_contra hnone
  push Not at hnone
  have hpat : C ∩ P.bond = ∅ := by
    ext f
    constructor
    · intro hf
      have hm := Finset.mem_inter.mp hf
      exact absurd hm.1 (hnone f hm.2)
    · intro hf
      simp at hf
  have hEReven : G.IsEvenEdgeSet (C ∩ P.ER) := by
    intro w
    change G.boundary (C ∩ P.ER) w = 0
    by_cases hw : w ∈ P.R
    · rw [P.boundary_inter_ER_of_mem_R hC hmin.2.1 hw, hpat]
      exact G.boundary_empty w
    · exact P.boundary_inter_ER_eq_zero hw
  obtain ⟨r, hrR, hrv⟩ : ∃ r ∈ P.R, r ≠ v := by
    by_cases h : P.a' = v
    · exact ⟨P.b', P.b'_mem, fun hb ↦ P.a'b'_ne (h.trans hb.symm)⟩
    · exact ⟨P.a', P.a'_mem, h⟩
  have hrsupp : r ∈ G.edgeSupport C := by
    rw [hsupp]
    exact Finset.mem_erase.mpr ⟨hrv, Finset.mem_union_right _ hrR⟩
  obtain ⟨e, he, i, hi⟩ := G.mem_edgeSupport_iff.mp hrsupp
  have heER : e ∈ P.ER := by
    have hEG := hC he
    simp only [EG, Finset.mem_union] at hEG
    rcases hEG with (hEL | hER) | hb
    · exact absurd (hi ▸ P.EL_ends e hEL i) (P.notin_L_of_mem_R hrR)
    · exact hER
    · exact absurd he (hnone e hb)
  have hERne : (C ∩ P.ER).Nonempty := ⟨e, Finset.mem_inter.mpr ⟨he, heER⟩⟩
  have hCER : C ∩ P.ER = C := hmin.eq_of_subset hERne Finset.inter_subset_left hEReven
  obtain ⟨l, hlL, hlv⟩ : ∃ l ∈ P.L, l ≠ v := by
    by_cases h : P.a = v
    · exact ⟨P.b, P.b_mem, fun hb ↦ P.ab_ne (h.trans hb.symm)⟩
    · exact ⟨P.a, P.a_mem, h⟩
  have hlsupp : l ∈ G.edgeSupport C := by
    rw [hsupp]
    exact Finset.mem_erase.mpr ⟨hlv, Finset.mem_union_left _ hlL⟩
  obtain ⟨e', he', j, hj⟩ := G.mem_edgeSupport_iff.mp hlsupp
  have he'ER : e' ∈ P.ER := (Finset.mem_inter.mp (hCER ▸ he')).2
  exact P.notin_R_of_mem_L hlL (hj ▸ P.ER_ends e' he'ER j)

/-- The seven possible bond patterns of a Hamilton cycle of the product avoiding one vertex. -/
theorem pattern_cases {C : Finset E} (hC : C ⊆ P.EG) (hmin : G.IsMinimalEven C) {v : V}
    (hsupp : G.edgeSupport C = P.VG.erase v) :
    C ∩ P.bond = {P.faa, P.fbb} ∨ C ∩ P.bond = {P.fcc, P.fdd} ∨
    C ∩ P.bond = {P.faa, P.fcc} ∨ C ∩ P.bond = {P.faa, P.fdd} ∨
    C ∩ P.bond = {P.fbb, P.fcc} ∨ C ∩ P.bond = {P.fbb, P.fdd} ∨ C ∩ P.bond = P.bond := by
  have hpar := P.bond_parity hC hmin.2.1
  obtain ⟨f₀, hf₀b, hf₀C⟩ := P.exists_bond_mem hC hmin hsupp
  have hfaab : P.faa ∈ P.bond := by simp [bond]
  have hfbbb : P.fbb ∈ P.bond := by simp [bond]
  have hfccb : P.fcc ∈ P.bond := by simp [bond]
  have hfddb : P.fdd ∈ P.bond := by simp [bond]
  by_cases h1 : P.faa ∈ C <;> by_cases h2 : P.fbb ∈ C <;> by_cases h3 : P.fcc ∈ C <;>
    by_cases h4 : P.fdd ∈ C
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    apply Finset.inter_eq_right.mpr
    intro f hf
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl <;> assumption
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · refine Or.inl (P.inter_bond_eq_pair h1 h2 hfaab hfbbb ?_)
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hfC h3
    · exact absurd hfC h4
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · refine Or.inr (Or.inr (Or.inl (P.inter_bond_eq_pair h1 h3 hfaab hfccb ?_)))
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hfC h2
    · exact Or.inr rfl
    · exact absurd hfC h4
  · refine Or.inr (Or.inr (Or.inr (Or.inl (P.inter_bond_eq_pair h1 h4 hfaab hfddb ?_))))
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hfC h2
    · exact absurd hfC h3
    · exact Or.inr rfl
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (P.inter_bond_eq_pair h2 h3 hfbbb hfccb ?_)))))
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact absurd hfC h1
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hfC h4
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (P.inter_bond_eq_pair h2 h4 hfbbb hfddb ?_))))))
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact absurd hfC h1
    · exact Or.inl rfl
    · exact absurd hfC h3
    · exact Or.inr rfl
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · refine Or.inr (Or.inl (P.inter_bond_eq_pair h3 h4 hfccb hfddb ?_))
    intro f hf hfC
    rcases P.mem_bond.mp hf with rfl | rfl | rfl | rfl
    · exact absurd hfC h1
    · exact absurd hfC h2
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · exfalso
    simp only [h1, h2, h3, h4, if_true, if_false] at hpar
    exact absurd hpar (by decide)
  · exfalso
    rcases P.mem_bond.mp hf₀b with rfl | rfl | rfl | rfl
    · exact h1 hf₀C
    · exact h2 hf₀C
    · exact h3 hf₀C
    · exact h4 hf₀C

end Patterns

section Descent

omit [DecidableEq E] in
theorem mem_VG_of_mem_L {v : V} (hv : v ∈ P.L) : v ∈ P.VG := Finset.mem_union_left _ hv
omit [DecidableEq E] in
theorem mem_VG_of_mem_R {v : V} (hv : v ∈ P.R) : v ∈ P.VG := Finset.mem_union_right _ hv

omit [DecidableEq E] in
theorem mem_VB_iff {u : V} : u ∈ P.VB ↔ u = P.x ∨ u = P.y ∨ u ∈ P.R := by
  simp [VB]

omit [DecidableEq E] in
theorem erase_inter_L_of_mem_L {v : V} (_hv : v ∈ P.L) :
    (P.VG.erase v) ∩ P.L = P.L.erase v := by
  ext u
  simp only [Finset.mem_inter, Finset.mem_erase, VG, Finset.mem_union]
  constructor
  · rintro ⟨⟨huv, _⟩, huL⟩
    exact ⟨huv, huL⟩
  · rintro ⟨huv, huL⟩
    exact ⟨⟨huv, Or.inl huL⟩, huL⟩

omit [DecidableEq E] in
theorem erase_inter_R_union_of_mem_L {v : V} (hv : v ∈ P.L) :
    ((P.VG.erase v) ∩ P.R) ∪ {P.x, P.y} = P.VB := by
  ext u
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase, VG, VB, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨_, huR⟩ | hu | hu)
    · exact Or.inr (Or.inr huR)
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
  · rintro (rfl | rfl | huR)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨⟨fun h ↦ P.notin_R_of_mem_L hv (h ▸ huR), Or.inr huR⟩, huR⟩

omit [DecidableEq E] in
theorem erase_inter_L_of_mem_R {w : V} (hw : w ∈ P.R) : (P.VG.erase w) ∩ P.L = P.L := by
  ext u
  simp only [Finset.mem_inter, Finset.mem_erase, VG, Finset.mem_union]
  constructor
  · rintro ⟨_, huL⟩
    exact huL
  · intro huL
    exact ⟨⟨fun h ↦ P.notin_L_of_mem_R hw (h ▸ huL), Or.inl huL⟩, huL⟩

omit [DecidableEq E] in
theorem erase_inter_R_union_of_mem_R {w : V} (hw : w ∈ P.R) :
    ((P.VG.erase w) ∩ P.R) ∪ {P.x, P.y} = P.VB.erase w := by
  ext u
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase, VG, VB, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨⟨huw, _⟩, huR⟩ | rfl | rfl)
    · exact ⟨huw, Or.inr (Or.inr huR)⟩
    · exact ⟨fun h ↦ P.x_notin_R (h ▸ hw), Or.inl rfl⟩
    · exact ⟨fun h ↦ P.y_notin_R (h ▸ hw), Or.inr (Or.inl rfl)⟩
  · rintro ⟨huw, rfl | rfl | huR⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨⟨huw, Or.inr huR⟩, huR⟩

omit [DecidableEq E] in
theorem erase_a_inter_R_union_y : ((P.VG.erase P.a) ∩ P.R) ∪ {P.y} = P.VB.erase P.x := by
  ext u
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase, VG, VB, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨⟨_, _⟩, huR⟩ | rfl)
    · exact ⟨fun h ↦ P.x_notin_R (h ▸ huR), Or.inr (Or.inr huR)⟩
    · exact ⟨P.x_ne_y.symm, Or.inr (Or.inl rfl)⟩
  · rintro ⟨hux, rfl | rfl | huR⟩
    · exact absurd rfl hux
    · exact Or.inr rfl
    · exact Or.inl ⟨⟨fun h ↦ P.notin_R_of_mem_L P.a_mem (h ▸ huR), Or.inr huR⟩, huR⟩

omit [DecidableEq E] in
theorem erase_c_inter_R_union_x : ((P.VG.erase P.c) ∩ P.R) ∪ {P.x} = P.VB.erase P.y := by
  ext u
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase, VG, VB, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨⟨_, _⟩, huR⟩ | rfl)
    · exact ⟨fun h ↦ P.y_notin_R (h ▸ huR), Or.inr (Or.inr huR)⟩
    · exact ⟨P.x_ne_y, Or.inl rfl⟩
  · rintro ⟨huy, rfl | rfl | huR⟩
    · exact Or.inr rfl
    · exact absurd rfl huy
    · exact Or.inl ⟨⟨fun h ↦ P.notin_R_of_mem_L P.c_mem (h ▸ huR), Or.inr huR⟩, huR⟩

omit [DecidableEq E] in
theorem notin_of_avoids {C : Finset E} {v : V} (hsupp : G.edgeSupport C = P.VG.erase v)
    {f : E} (hf : G.endAt f 0 = v) : f ∉ C := by
  intro hfC
  have hv : v ∈ G.edgeSupport C := G.mem_edgeSupport_iff.mpr ⟨f, hfC, 0, hf⟩
  rw [hsupp] at hv
  exact (Finset.mem_erase.mp hv).1 rfl


/-- **Hamilton-cycle descent.**  If the dot product is hypohamiltonian and both factors are
non-Hamiltonian, then both factors are hypohamiltonian. -/
theorem descent
    (hA : ¬ ∃ D, G.IsHamiltonCycleIn P.EA P.L D)
    (hB : ¬ ∃ D, G.IsHamiltonCycleIn P.EB P.VB D)
    (hG : ∀ v ∈ P.VG, ∃ D, G.IsHamiltonCycleIn P.EG (P.VG.erase v) D) :
    G.IsHypohamiltonianIn P.EA P.L ∧ G.IsHypohamiltonianIn P.EB P.VB := by
  refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
  · -- vertex deletions of the left factor
    intro v hv
    obtain ⟨C, hC, hmin, hsupp⟩ := hG v (P.mem_VG_of_mem_L hv)
    have hL := P.erase_inter_L_of_mem_L hv
    have hR := P.erase_inter_R_union_of_mem_L hv
    rw [← hL]
    rcases P.pattern_cases hC hmin hsupp with h | h | h | h | h | h | h
    · rw [← hsupp]
      exact P.hamA_of_pair hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fbb P.faa_ends
        P.fbb_ends P.eab_ends P.eab_notin P.eab_mem_EA h
    · rw [← hsupp]
      exact P.hamA_of_pair hC hmin (by simp [bond]) (by simp [bond]) P.fcc_ne_fdd P.fcc_ends
        P.fdd_ends P.ecd_ends P.ecd_notin P.ecd_mem_EA h
    · exfalso
      apply hB
      rw [← hR, ← hsupp]
      exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fcc P.faa_ends
        P.fcc_ends P.exa_ends P.eyc_ends P.exa_mem_EB P.eyc_mem_EB h
    · exfalso
      apply hB
      rw [← hR, ← hsupp]
      exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fdd P.faa_ends
        P.fdd_ends P.exa_ends P.eyd_ends P.exa_mem_EB P.eyd_mem_EB h
    · exfalso
      apply hB
      rw [← hR, ← hsupp]
      exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fcc P.fbb_ends
        P.fcc_ends P.exb_ends P.eyc_ends P.exb_mem_EB P.eyc_mem_EB h
    · exfalso
      apply hB
      rw [← hR, ← hsupp]
      exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fdd P.fbb_ends
        P.fdd_ends P.exb_ends P.eyd_ends P.exb_mem_EB P.eyd_mem_EB h
    · rcases P.ham_of_four hC hmin h with hleft | hright
      · rw [← hsupp]
        exact hleft
      · exfalso
        apply hB
        rw [← hR, ← hsupp]
        exact hright
  · -- vertex deletions of the right factor
    intro w hw
    rcases P.mem_VB_iff.mp hw with rfl | rfl | hwR
    · -- the cap vertex x: use the cycle avoiding a
      obtain ⟨C, hC, hmin, hsupp⟩ := hG P.a (P.mem_VG_of_mem_L P.a_mem)
      have hfaa : P.faa ∉ C := P.notin_of_avoids hsupp P.faa_ends.1
      have hR := P.erase_inter_R_union_of_mem_L P.a_mem
      rcases P.pattern_cases hC hmin hsupp with h | h | h | h | h | h | h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfaa
      · rw [← P.erase_a_inter_R_union_y, ← hsupp]
        exact P.hamB_of_cap hC hmin (by simp [bond]) (by simp [bond]) P.fcc_ne_fdd P.fcc_ends
          P.fdd_ends P.y_notin_R P.c'd'_ne P.eyc_ends P.eyd_ends P.eyc_mem_EB P.eyd_mem_EB h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfaa
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfaa
      · exfalso
        apply hB
        rw [← hR, ← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fcc P.fbb_ends
          P.fcc_ends P.exb_ends P.eyc_ends P.exb_mem_EB P.eyc_mem_EB h
      · exfalso
        apply hB
        rw [← hR, ← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fdd P.fbb_ends
          P.fdd_ends P.exb_ends P.eyd_ends P.exb_mem_EB P.eyd_mem_EB h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp [bond])) hfaa
    · -- the cap vertex y: use the cycle avoiding c
      obtain ⟨C, hC, hmin, hsupp⟩ := hG P.c (P.mem_VG_of_mem_L P.c_mem)
      have hfcc : P.fcc ∉ C := P.notin_of_avoids hsupp P.fcc_ends.1
      have hR := P.erase_inter_R_union_of_mem_L P.c_mem
      rcases P.pattern_cases hC hmin hsupp with h | h | h | h | h | h | h
      · rw [← P.erase_c_inter_R_union_x, ← hsupp]
        exact P.hamB_of_cap hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fbb P.faa_ends
          P.fbb_ends P.x_notin_R P.a'b'_ne P.exa_ends P.exb_ends P.exa_mem_EB P.exb_mem_EB h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfcc
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfcc
      · exfalso
        apply hB
        rw [← hR, ← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fdd P.faa_ends
          P.fdd_ends P.exa_ends P.eyd_ends P.exa_mem_EB P.eyd_mem_EB h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp)) hfcc
      · exfalso
        apply hB
        rw [← hR, ← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fdd P.fbb_ends
          P.fdd_ends P.exb_ends P.eyd_ends P.exb_mem_EB P.eyd_mem_EB h
      · exact absurd (P.mem_of_mem_inter_bond h (by simp [bond])) hfcc
    · -- an inherited right vertex
      obtain ⟨C, hC, hmin, hsupp⟩ := hG w (P.mem_VG_of_mem_R hwR)
      have hL := P.erase_inter_L_of_mem_R hwR
      have hR := P.erase_inter_R_union_of_mem_R hwR
      rw [← hR]
      rcases P.pattern_cases hC hmin hsupp with h | h | h | h | h | h | h
      · exfalso
        apply hA
        rw [← hL, ← hsupp]
        exact P.hamA_of_pair hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fbb P.faa_ends
          P.fbb_ends P.eab_ends P.eab_notin P.eab_mem_EA h
      · exfalso
        apply hA
        rw [← hL, ← hsupp]
        exact P.hamA_of_pair hC hmin (by simp [bond]) (by simp [bond]) P.fcc_ne_fdd P.fcc_ends
          P.fdd_ends P.ecd_ends P.ecd_notin P.ecd_mem_EA h
      · rw [← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fcc P.faa_ends
          P.fcc_ends P.exa_ends P.eyc_ends P.exa_mem_EB P.eyc_mem_EB h
      · rw [← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.faa_ne_fdd P.faa_ends
          P.fdd_ends P.exa_ends P.eyd_ends P.exa_mem_EB P.eyd_mem_EB h
      · rw [← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fcc P.fbb_ends
          P.fcc_ends P.exb_ends P.eyc_ends P.exb_mem_EB P.eyc_mem_EB h
      · rw [← hsupp]
        exact P.hamB_of_mixed hC hmin (by simp [bond]) (by simp [bond]) P.fbb_ne_fdd P.fbb_ends
          P.fdd_ends P.exb_ends P.eyd_ends P.exb_mem_EB P.eyd_mem_EB h
      · rcases P.ham_of_four hC hmin h with hleft | hright
        · exfalso
          apply hA
          rw [← hL, ← hsupp]
          exact hleft
        · rw [← hsupp]
          exact hright

end Descent

end DotProduct

end LoopMultigraph
end GraphPuzzles
