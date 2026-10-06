import GraphPuzzles.DefectThree.MatchingTripleStructure
import GraphPuzzles.DefectThree.HexagonPairing
import GraphPuzzles.Graph.LoopMultigraphIso

/-!
# Extracting the induced hexagon of a defect-three matching triple

This proves the structural implication in Karabáš--Máčajová--Nedela--Škoviera,
*Cubic graphs with colouring defect 3*, Theorem 3.3. The proof uses the three
pairwise intersections to label the doubled edges, and counts their uncovered incidences.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators
open Hexagon

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
/-- An equivalence of numbered ends for two edges with the same unordered endpoints. -/
theorem exists_parallel_equiv {e f : E} {i j : Fin 2}
    (h₀ : H.endAt f i = H.endAt e j)
    (h₁ : H.endAt f (Fin.rev i) = H.endAt e (Fin.rev j)) :
    ∃ p : Fin 2 ≃ Fin 2, ∀ k, H.endAt f k = H.endAt e (p k) := by
  fin_cases i <;> fin_cases j
  · exact ⟨Equiv.refl _, by intro k; fin_cases k; exact h₀; exact h₁⟩
  · exact ⟨Equiv.swap 0 1, by intro k; fin_cases k; simpa using h₀; simpa using h₁⟩
  · exact ⟨Equiv.swap 0 1, by intro k; fin_cases k; simpa using h₁; simpa using h₀⟩
  · exact ⟨Equiv.refl _, by intro k; fin_cases k; exact h₁; exact h₀⟩

namespace MatchingTriple

/-- One doubly covered edge missing each of the three matching indices. -/
structure DoubleFrame (M : H.MatchingTriple) where
  edge : Fin 3 → E
  mem_edge : ∀ a i, edge a ∈ M.matching i ↔ i ≠ a

namespace DoubleFrame

variable {M : H.MatchingTriple} (D : M.DoubleFrame)

theorem multiplicity_edge (a : Fin 3) : M.multiplicity (D.edge a) = 2 := by
  simp only [multiplicity, D.mem_edge]
  exact (show ∀ a : Fin 3, (Finset.univ.filter fun i ↦ i ≠ a).card = 2 by decide) a

omit [DecidableEq E] in
theorem edge_injective : Function.Injective D.edge := by
  intro a b h
  by_contra hn
  have hb : D.edge b ∈ M.matching a := (D.mem_edge b a).mpr hn
  rw [← h, D.mem_edge] at hb
  exact hb rfl

def side (i : Fin 6) : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩

theorem side_flip (i : Fin 6) : side (pairFlip i) = Fin.rev (side i) := by revert i; decide

theorem index_injective : Function.Injective (fun i : Fin 6 ↦ (hexWord i, side i)) := by decide

def vertex (i : Fin 6) : V := H.endAt (D.edge (hexWord i)) (side i)

def half (i : Fin 6) : H.halfEdgesAt (D.vertex i) := ⟨(D.edge (hexWord i), side i), rfl⟩

theorem vertex_injective : Function.Injective D.vertex := by
  intro i j h
  have hx := M.double_half_unique (D.half i)
    (⟨(D.edge (hexWord j), side j), h.symm⟩ : H.halfEdgesAt (D.vertex i))
    (by rw [show (D.half i).1.1 = D.edge (hexWord i) from rfl, D.multiplicity_edge])
    (by rw [D.multiplicity_edge])
  apply index_injective
  exact Prod.ext (D.edge_injective (congrArg (fun x ↦ x.1.1) hx))
    (congrArg (fun x ↦ x.1.2) hx)

variable (hc : ∀ v, H.degree v = 3)

noncomputable def zeroHalf (i : Fin 6) : H.halfEdgesAt (D.vertex i) :=
  (M.double_vertex hc (D.half i) (D.multiplicity_edge _)).choose

noncomputable def singleHalf (i : Fin 6) : H.halfEdgesAt (D.vertex i) :=
  (M.double_vertex hc (D.half i) (D.multiplicity_edge _)).choose_spec.choose

theorem zeroHalf_mult (i : Fin 6) : M.multiplicity (D.zeroHalf hc i).1.1 = 0 :=
  (M.double_vertex hc (D.half i) (D.multiplicity_edge _)).choose_spec.choose_spec.1

theorem singleHalf_mult (i : Fin 6) : M.multiplicity (D.singleHalf hc i).1.1 = 1 :=
  (M.double_vertex hc (D.half i) (D.multiplicity_edge _)).choose_spec.choose_spec.2.1

theorem half_cases (i : Fin 6) (x : H.halfEdgesAt (D.vertex i)) :
    x = D.half i ∨ x = D.zeroHalf hc i ∨ x = D.singleHalf hc i :=
  (M.double_vertex hc (D.half i) (D.multiplicity_edge _)).choose_spec.choose_spec.2.2 x

noncomputable def zeroEnd (i : Fin 6) : {e // e ∈ M.uncovered} × Fin 2 :=
  (⟨(D.zeroHalf hc i).1.1, (M.mem_uncovered _).mpr (D.zeroHalf_mult hc i)⟩,
    (D.zeroHalf hc i).1.2)

theorem zeroEnd_vertex (i : Fin 6) :
    H.endAt (D.zeroEnd hc i).1.1 (D.zeroEnd hc i).2 = D.vertex i :=
  (D.zeroHalf hc i).2

theorem zeroEnd_injective : Function.Injective (D.zeroEnd hc) := by
  intro i j h
  apply D.vertex_injective
  rw [← D.zeroEnd_vertex hc i, ← D.zeroEnd_vertex hc j, h]

variable (hu : M.uncovered.card = 3)

noncomputable def zeroEquiv : Fin 6 ≃ ({e // e ∈ M.uncovered} × Fin 2) :=
  Equiv.ofBijective (D.zeroEnd hc)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨D.zeroEnd_injective hc, by
        rw [Fintype.card_prod, Fintype.card_coe, hu]
        decide⟩)

noncomputable def mate (i : Fin 6) : Fin 6 :=
  (D.zeroEquiv hc hu).symm ((D.zeroEnd hc i).1, Fin.rev (D.zeroEnd hc i).2)

theorem zeroEnd_mate (i : Fin 6) : D.zeroEnd hc (D.mate hc hu i) =
    ((D.zeroEnd hc i).1, Fin.rev (D.zeroEnd hc i).2) :=
  (D.zeroEquiv hc hu).apply_symm_apply _

theorem mate_involutive : Function.Involutive (D.mate hc hu) := by
  intro i
  apply D.zeroEnd_injective hc
  rw [D.zeroEnd_mate hc hu, D.zeroEnd_mate hc hu]
  simp

theorem mate_ne (i : Fin 6) : D.mate hc hu i ≠ i := by
  intro h
  have h' := congrArg Prod.snd (D.zeroEnd_mate hc hu i)
  rw [h] at h'
  exact (show ∀ k : Fin 2, k ≠ Fin.rev k by decide) _ h'

theorem zero_far (i : Fin 6) :
    H.endAt (D.zeroHalf hc i).1.1 (Fin.rev (D.zeroHalf hc i).1.2) =
      D.vertex (D.mate hc hu i) := by
  rw [← D.zeroEnd_vertex hc (D.mate hc hu i), D.zeroEnd_mate hc hu]
  rfl

theorem mate_word_ne (ho : M.IsOptimal) (i : Fin 6) :
    hexWord (D.mate hc hu i) ≠ hexWord i := by
  intro hword
  have hside : side (D.mate hc hu i) = Fin.rev (side i) := by
    have hn : side (D.mate hc hu i) ≠ side i := by
      intro hh
      exact D.mate_ne hc hu i (index_injective (Prod.ext hword hh))
    exact (show ∀ a b : Fin 2, a ≠ b → a = Fin.rev b by decide) _ _ hn
  have hfar := D.zero_far hc hu i
  change H.endAt (D.zeroHalf hc i).1.1 (Fin.rev (D.zeroHalf hc i).1.2) =
    H.endAt (D.edge (hexWord (D.mate hc hu i))) (side (D.mate hc hu i)) at hfar
  rw [hword, hside] at hfar
  obtain ⟨p, hp⟩ := exists_parallel_equiv (D.zeroHalf hc i).2 hfar
  exact ho.not_parallel_uncovered (by rw [D.multiplicity_edge]) (D.zeroHalf_mult hc i) p hp

include hc hu in
theorem double_edge_eq {e : E} (he : M.multiplicity e = 2) :
    ∃ a, e = D.edge a := by
  obtain ⟨z, _, hz, _, _⟩ := M.double_vertex hc
    (⟨(e, 0), rfl⟩ : H.halfEdgesAt (H.endAt e 0)) he
  obtain ⟨i, hi⟩ := (D.zeroEquiv hc hu).surjective
    (⟨z.1.1, (M.mem_uncovered _).mpr hz⟩, z.1.2)
  change D.zeroEnd hc i = _ at hi
  have hv : D.vertex i = H.endAt e 0 := by
    rw [← D.zeroEnd_vertex hc i, hi]
    exact z.2
  have hh := M.double_half_unique (⟨(e, 0), rfl⟩ : H.halfEdgesAt (H.endAt e 0))
    ⟨(D.edge (hexWord i), side i), hv⟩ (by change 2 ≤ M.multiplicity e; omega)
    (by rw [D.multiplicity_edge])
  exact ⟨hexWord i, congrArg (fun x ↦ x.1.1) hh⟩

theorem singleHalf_mem (i : Fin 6) (a : Fin 3) :
    (D.singleHalf hc i).1.1 ∈ M.matching a ↔ a = hexWord i := by
  obtain ⟨b, hb, huniq⟩ := (M.multiplicity_eq_one_iff _).mp (D.singleHalf_mult hc i)
  have heq : b = hexWord i := by
    by_contra hn
    have hh := (M.perfect b).half_unique (D.singleHalf hc i) (D.half i)
      hb ((D.mem_edge _ _).mpr hn)
    have hmul := congrArg (fun x : H.halfEdgesAt (D.vertex i) ↦ M.multiplicity x.1.1) hh
    change M.multiplicity (D.singleHalf hc i).1.1 = M.multiplicity (D.edge (hexWord i)) at hmul
    rw [D.singleHalf_mult, D.multiplicity_edge] at hmul
    omega
  subst b
  exact ⟨huniq a, fun h ↦ h ▸ hb⟩

include hc hu in
theorem common_edge_eq (hr : M.IsRegular) (a : Fin 3) {e : E}
    (h₁ : e ∈ M.matching (a + 1)) (h₂ : e ∈ M.matching (a + 2)) : e = D.edge a := by
  have tab : ∀ (s : Finset (Fin 3)) (a : Fin 3), s.card ≤ 2 →
      a + 1 ∈ s → a + 2 ∈ s → s.card = 2 := by decide
  have he : M.multiplicity e = 2 :=
    tab (Finset.univ.filter fun i ↦ e ∈ M.matching i) a (hr e) (by simpa) (by simpa)
  obtain ⟨b, rfl⟩ := D.double_edge_eq hc hu he
  rw [D.mem_edge] at h₁ h₂
  have hab : b = a := (show ∀ a b : Fin 3, a + 1 ≠ b → a + 2 ≠ b → b = a by decide) a b h₁ h₂
  rw [hab]

include hu in
/-- A simply covered chord of the six core vertices would give two disjoint matchings. -/
theorem single_far (hr : M.IsRegular)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (i j : Fin 6) :
    H.endAt (D.singleHalf hc i).1.1 (Fin.rev (D.singleHalf hc i).1.2) ≠ D.vertex j := by
  intro hfar
  let x : H.halfEdgesAt (D.vertex j) :=
    ⟨((D.singleHalf hc i).1.1, Fin.rev (D.singleHalf hc i).1.2), hfar⟩
  have hx : x = D.singleHalf hc j := by
    rcases D.half_cases hc j x with h | h | h
    · have hm := congrArg (fun y : H.halfEdgesAt (D.vertex j) ↦ M.multiplicity y.1.1) h
      change M.multiplicity (D.singleHalf hc i).1.1 = M.multiplicity (D.edge (hexWord j)) at hm
      rw [D.singleHalf_mult, D.multiplicity_edge] at hm
      omega
    · have hm := congrArg (fun y : H.halfEdgesAt (D.vertex j) ↦ M.multiplicity y.1.1) h
      change M.multiplicity (D.singleHalf hc i).1.1 = M.multiplicity (D.zeroHalf hc j).1.1 at hm
      rw [D.singleHalf_mult, D.zeroHalf_mult] at hm
      omega
    · exact h
  have hedge : (D.singleHalf hc i).1.1 = (D.singleHalf hc j).1.1 :=
    congrArg (fun y ↦ y.1.1) hx
  have hword : hexWord j = hexWord i := by
    have hm := (D.singleHalf_mem hc i (hexWord i)).mpr rfl
    rw [hedge, D.singleHalf_mem] at hm
    exact hm.symm
  have hij : j ≠ i := by
    intro h
    subst j
    have he := hfar.trans (D.singleHalf hc i).2.symm
    change H.endAt (D.singleHalf hc i).1.1 (Fin.rev (D.singleHalf hc i).1.2) =
      H.endAt (D.singleHalf hc i).1.1 (D.singleHalf hc i).1.2 at he
    have hloop := hl (D.singleHalf hc i).1.1
    generalize hk : (D.singleHalf hc i).1.2 = k at he
    fin_cases k
    · exact hloop he.symm
    · exact hloop he
  have hside : side j = Fin.rev (side i) := by
    have hn : side j ≠ side i := fun h ↦ hij (index_injective (Prod.ext hword h))
    exact (show ∀ a b : Fin 2, a ≠ b → a = Fin.rev b by decide) _ _ hn
  change H.endAt (D.singleHalf hc i).1.1 (Fin.rev (D.singleHalf hc i).1.2) =
    H.endAt (D.edge (hexWord j)) (side j) at hfar
  rw [hword, hside] at hfar
  obtain ⟨p, hp⟩ := exists_parallel_equiv (D.singleHalf hc i).2 hfar
  let a := hexWord i
  have h1a : a + 1 ≠ a := (show ∀ a : Fin 3, a + 1 ≠ a by decide) a
  have h2a : a + 2 ≠ a := (show ∀ a : Fin 3, a + 2 ≠ a by decide) a
  have hs1 : (D.singleHalf hc i).1.1 ∉ M.matching (a + 1) := by
    rw [D.singleHalf_mem]
    exact h1a
  have hs2 : (D.singleHalf hc i).1.1 ∉ M.matching (a + 2) := by
    rw [D.singleHalf_mem]
    exact h2a
  have hP := (M.perfect (a + 1)).replace_parallel ((D.mem_edge a _).mpr h1a) hs1 p hp
  apply hn
  apply colourable_of_disjoint_matchings hc hP (M.perfect (a + 2))
  rw [Finset.disjoint_left]
  intro e he he2
  rcases Finset.mem_insert.mp he with rfl | he
  · exact hs2 he2
  · exact (Finset.mem_erase.mp he).1
      (D.common_edge_eq hc hu hr a (Finset.mem_erase.mp he).2 he2)

noncomputable def order : Fin 6 → Fin 6 := coreOrder (D.mate hc hu)

theorem order_injective (ho : M.IsOptimal) : Function.Injective (D.order hc hu) :=
  (coreOrder_spec _ (D.mate_involutive hc hu) (D.mate_word_ne hc hu ho)).1

theorem order_flip (ho : M.IsOptimal) (i : Fin 6) :
    D.order hc hu (pairFlip i) = pairFlip (D.order hc hu i) :=
  (coreOrder_spec _ (D.mate_involutive hc hu) (D.mate_word_ne hc hu ho)).2.1 i

theorem order_next (ho : M.IsOptimal) (i : Fin 6) (hi : i.val % 2 = 1) :
    D.mate hc hu (D.order hc hu i) = D.order hc hu (i + 1) :=
  (coreOrder_spec _ (D.mate_involutive hc hu) (D.mate_word_ne hc hu ho)).2.2 i hi

noncomputable def coreEdge (i : Fin 6) : E :=
  if i.val % 2 = 0 then D.edge (hexWord (D.order hc hu i))
  else (D.zeroHalf hc (D.order hc hu i)).1.1

noncomputable def departure (i : Fin 6) : Fin 2 :=
  if i.val % 2 = 0 then side (D.order hc hu i)
  else (D.zeroHalf hc (D.order hc hu i)).1.2

theorem coreEdge_start (i : Fin 6) :
    H.endAt (D.coreEdge hc hu i) (D.departure hc hu i) = D.vertex (D.order hc hu i) := by
  unfold coreEdge departure
  split_ifs
  · rfl
  · exact (D.zeroHalf hc _).2

theorem coreEdge_finish (ho : M.IsOptimal) (i : Fin 6) :
    H.endAt (D.coreEdge hc hu i) (Fin.rev (D.departure hc hu i)) =
      D.vertex (D.order hc hu (i + 1)) := by
  by_cases hi : i.val % 2 = 0
  · have hflip : pairFlip i = i + 1 :=
      (show ∀ i : Fin 6, i.val % 2 = 0 → pairFlip i = i + 1 by decide) i hi
    rw [coreEdge, departure, if_pos hi, if_pos hi, ← hflip, D.order_flip hc hu ho]
    simp only [vertex, pairFlip_word, side_flip]
  · have hi' : i.val % 2 = 1 := by omega
    rw [coreEdge, departure, if_neg hi, if_neg hi, D.zero_far hc hu,
      D.order_next hc hu ho i hi']

theorem coreEdge_mult (i : Fin 6) :
    M.multiplicity (D.coreEdge hc hu i) = if i.val % 2 = 0 then 2 else 0 := by
  unfold coreEdge
  split_ifs
  · exact D.multiplicity_edge _
  · exact D.zeroHalf_mult hc _

theorem coreEdge_injective (ho : M.IsOptimal) : Function.Injective (D.coreEdge hc hu) := by
  have hv := D.vertex_injective.comp (D.order_injective hc hu ho)
  intro i j h
  by_cases hs : D.departure hc hu i = D.departure hc hu j
  · apply hv
    change D.vertex (D.order hc hu i) = D.vertex (D.order hc hu j)
    rw [← D.coreEdge_start hc hu i, ← D.coreEdge_start hc hu j, h, hs]
  · have hs' : D.departure hc hu i = Fin.rev (D.departure hc hu j) :=
      (show ∀ a b : Fin 2, a ≠ b → a = Fin.rev b by decide) _ _ hs
    have h₁ : i = j + 1 := hv (by
      change D.vertex (D.order hc hu i) = D.vertex (D.order hc hu (j + 1))
      rw [← D.coreEdge_start hc hu i, h, hs', D.coreEdge_finish hc hu ho])
    have h₂ : i + 1 = j := hv (by
      change D.vertex (D.order hc hu (i + 1)) = D.vertex (D.order hc hu j)
      rw [← D.coreEdge_finish hc hu ho i, h, hs', Fin.rev_rev, D.coreEdge_start])
    exact False.elim ((show ∀ i j : Fin 6, i = j + 1 → i + 1 ≠ j by decide) i j h₁ h₂)

theorem single_ne_coreEdge (i j : Fin 6) :
    (D.singleHalf hc i).1.1 ≠ D.coreEdge hc hu j := by
  intro h
  have hm := D.singleHalf_mult hc i
  rw [h, D.coreEdge_mult] at hm
  split_ifs at hm
  all_goals omega

include hu in
theorem coreEdge_range (ho : M.IsOptimal) :
    Finset.univ.image (D.coreEdge hc hu) = Finset.univ.image D.edge ∪ M.uncovered := by
  have hsub : Finset.univ.image (D.coreEdge hc hu) ⊆ Finset.univ.image D.edge ∪ M.uncovered := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    unfold coreEdge
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ ((M.mem_uncovered _).mpr (D.zeroHalf_mult hc _))
  have hd : Disjoint (Finset.univ.image D.edge) M.uncovered := by
    rw [Finset.disjoint_left]
    intro e he hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    have hm := (M.mem_uncovered _).mp hz
    rw [D.multiplicity_edge] at hm
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ D.edge_injective,
    Finset.card_image_of_injective _ (D.coreEdge_injective hc hu ho), hu]
  decide

theorem mult_one_off_core (ho : M.IsOptimal) (hr : M.IsRegular) {e : E}
    (he : ∀ i, e ≠ D.coreEdge hc hu i) : M.multiplicity e = 1 := by
  have hn : e ∉ Finset.univ.image (D.coreEdge hc hu) := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using
      (fun i ↦ (he i).symm)
  rw [D.coreEdge_range hc hu ho, Finset.mem_union, not_or] at hn
  have hz : M.multiplicity e ≠ 0 := fun h ↦ hn.2 ((M.mem_uncovered _).mpr h)
  have htwo : M.multiplicity e ≠ 2 := by
    intro h
    obtain ⟨a, ha⟩ := D.double_edge_eq hc hu h
    exact hn.1 (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.symm⟩)
  have hle := hr e
  omega

noncomputable def cyclicEnds (e : E) : Fin 2 ≃ Fin 2 :=
  if he : ∃ i, D.coreEdge hc hu i = e then Equiv.swap 0 (D.departure hc hu he.choose)
  else Equiv.refl _

theorem cyclicEnds_core (ho : M.IsOptimal) (i : Fin 6) :
    D.cyclicEnds hc hu (D.coreEdge hc hu i) = Equiv.swap 0 (D.departure hc hu i) := by
  have he : ∃ j, D.coreEdge hc hu j = D.coreEdge hc hu i := ⟨i, rfl⟩
  rw [cyclicEnds, dif_pos he]
  rw [D.coreEdge_injective hc hu ho he.choose_spec]

theorem cyclicEnds_off {e : E} (he : ∀ i, e ≠ D.coreEdge hc hu i) :
    D.cyclicEnds hc hu e = Equiv.refl _ := by
  have hn : ¬ ∃ i, D.coreEdge hc hu i = e := by
    rintro ⟨i, hi⟩
    exact he i hi.symm
  rw [cyclicEnds, dif_neg hn]

/-- The alternating core, with its edges numbered in cyclic direction. -/
noncomputable def hexagon (ho : M.IsOptimal) (hr : M.IsRegular)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : (H.relabelEnds (D.cyclicEnds hc hu)).Hexagon where
  v i := D.vertex (D.order hc hu i)
  h := D.coreEdge hc hu
  spoke i := (D.singleHalf hc (D.order hc hu i)).1.1
  side i := (D.singleHalf hc (D.order hc hu i)).1.2
  v_injective := D.vertex_injective.comp (D.order_injective hc hu ho)
  h_end0 i := by
    change H.endAt _ (D.cyclicEnds hc hu _ 0) = _
    rw [D.cyclicEnds_core hc hu ho, Equiv.swap_apply_left]
    exact D.coreEdge_start hc hu i
  h_end1 i := by
    change H.endAt _ (D.cyclicEnds hc hu _ 1) = _
    rw [D.cyclicEnds_core hc hu ho,
      (show ∀ k : Fin 2, Equiv.swap 0 k 1 = Fin.rev k by decide)]
    exact D.coreEdge_finish hc hu ho i
  spoke_end i := by
    change H.endAt _ (D.cyclicEnds hc hu _ _) = _
    rw [D.cyclicEnds_off hc hu (D.single_ne_coreEdge hc hu _)]
    exact (D.singleHalf hc _).2
  spoke_far i j := by
    change H.endAt _ (D.cyclicEnds hc hu _ _) ≠ _
    rw [D.cyclicEnds_off hc hu (D.single_ne_coreEdge hc hu _)]
    exact D.single_far hc hu hr hn hl _ _

/-- The matching index of an exterior edge gives its proper colour and the word `aabbcc`. -/
noncomputable def exteriorColoring (ho : M.IsOptimal) (hr : M.IsRegular)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : (D.hexagon hc hu ho hr hn hl).ExteriorColoring where
  color := tripleColor M.matching
  r := 0
  c a := choiceColor (pairIndex (D.order hc hu) a)
  c_injective := (fun _ _ h ↦ pairIndex_injective _ (D.order_injective hc hu ho)
    (D.order_flip hc hu ho) (choiceColor_injective _ _ h))
  nonzero e he := by
    obtain ⟨a, ha, huniq⟩ := (M.multiplicity_eq_one_iff e).mp (D.mult_one_off_core hc hu ho hr he)
    rw [tripleColor_eq ha huniq]
    exact choiceColor_ne_zero a
  injective_at w x y hx hy hcol := by
    obtain ⟨a, ha, huniq⟩ := (M.multiplicity_eq_one_iff x.1.1).mp
      (D.mult_one_off_core hc hu ho hr hx)
    obtain ⟨b, hb, huniq'⟩ := (M.multiplicity_eq_one_iff y.1.1).mp
      (D.mult_one_off_core hc hu ho hr hy)
    rw [tripleColor_eq ha huniq, tripleColor_eq hb huniq'] at hcol
    have hab : a = b := choiceColor_injective _ _ hcol
    subst b
    have hxe : H.endAt x.1.1 x.1.2 = w := by
      have ht := x.2
      change H.endAt x.1.1 (D.cyclicEnds hc hu x.1.1 x.1.2) = w at ht
      rw [D.cyclicEnds_off hc hu hx] at ht
      exact ht
    have hye : H.endAt y.1.1 y.1.2 = w := by
      have ht := y.2
      change H.endAt y.1.1 (D.cyclicEnds hc hu y.1.1 y.1.2) = w at ht
      rw [D.cyclicEnds_off hc hu hy] at ht
      exact ht
    have hxy := (M.perfect a).half_unique
      (⟨x.1, hxe⟩ : H.halfEdgesAt w) (⟨y.1, hye⟩ : H.halfEdgesAt w) ha hb
    exact Subtype.ext (congrArg (fun z : H.halfEdgesAt w ↦ z.1) hxy)
  spoke_color i := by
    change tripleColor M.matching (D.singleHalf hc (D.order hc hu i)).1.1 =
      choiceColor (pairIndex (D.order hc hu) (hexWord (i + 0)))
    rw [add_zero, pairIndex_word _ (D.order_flip hc hu ho)]
    exact tripleColor_eq ((D.singleHalf_mem hc _ _).mpr rfl)
      (fun a ha ↦ (D.singleHalf_mem hc _ a).mp ha)

end DoubleFrame

/-- The structural direction of KMNS Theorem 3.3, for an optimal matching triple.
No connectivity or girth assumption is needed for this direction. -/
theorem IsOptimal.exists_hexagonalCore {M : H.MatchingTriple} (ho : M.IsOptimal)
    (hu : M.uncovered.card = 3) (hc : ∀ v, H.degree v = 3)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hn : ¬ ∃ g : E → Color, H.ProperOff ∅ g) :
    ∃ ends : E → (Fin 2 ≃ Fin 2), ∃ X : (H.relabelEnds ends).Hexagon,
      Nonempty X.ExteriorColoring := by
  have hr := ho.regular_of_uncovered_le_three hc hl hu.le
  obtain ⟨d, hd⟩ := M.exists_double_edges hc hn hr
  let D : M.DoubleFrame := ⟨d, hd⟩
  exact ⟨D.cyclicEnds hc hu, D.hexagon hc hu ho hr hn hl,
    ⟨D.exteriorColoring hc hu ho hr hn hl⟩⟩
end MatchingTriple
end LoopMultigraph
end GraphPuzzles
