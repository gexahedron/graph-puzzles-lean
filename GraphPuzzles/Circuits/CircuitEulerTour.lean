import GraphPuzzles.Circuits.OrdinaryCircuit
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Euler tours of ordinary circuits

This file supplies the traversal data implicit in the usual definition of a finite ordinary
circuit.  In the endpoint-multigraph model, the two incidences at each supported vertex determine
the next edge uniquely once an orientation of one edge has been chosen.
-/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace OrdinaryCircuit

variable {H : LoopMultigraph V E} (C : H.OrdinaryCircuit)

/-- The endpoint multigraph carried by the edges of an ordinary circuit. -/
def restricted : LoopMultigraph V {e : E // e ∈ C.edges} where
  endAt e := H.endAt e.1

private abbrev CircuitEdge := {e : E // e ∈ C.edges}
private abbrev CircuitHalfEdge := {h : E × Fin 2 // h ∈ C.edges ×ˢ (Finset.univ : Finset (Fin 2))}

private def halfEdgesAt (v : V) : Finset (CircuitHalfEdge C) :=
  (C.edges ×ˢ (Finset.univ : Finset (Fin 2))).attach.filter
    fun h ↦ H.endAt h.1.1 h.1.2 = v

omit [DecidableEq E] in
@[simp]
private theorem mem_halfEdgesAt (v : V) (h : CircuitHalfEdge C) :
    h ∈ C.halfEdgesAt v ↔ H.endAt h.1.1 h.1.2 = v := by
  simp [halfEdgesAt]

omit [DecidableEq E] in
private theorem halfEdgesAt_card {v : V} (hv : v ∈ H.edgeSupport C.edges) :
    (C.halfEdgesAt v).card = 2 := by
  rw [← C.twoRegular v hv]
  change (C.halfEdgesAt v).card =
    (((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun h ↦ H.endAt h.1 h.2 = v).card)
  refine Finset.card_bij (fun h _ ↦ h.1) ?_ ?_ ?_
  · intro h hh
    exact Finset.mem_filter.mpr ⟨h.2, (C.mem_halfEdgesAt v h).mp hh⟩
  · intro h₁ hh₁ h₂ hh₂ heq
    exact Subtype.ext heq
  · intro h hh
    refine ⟨⟨h, (Finset.mem_filter.mp hh).1⟩, ?_, rfl⟩
    exact (C.mem_halfEdgesAt v _).mpr (Finset.mem_filter.mp hh).2

omit [DecidableEq E] in
private theorem halfEdge_vertex_mem_support (h : CircuitHalfEdge C) :
    H.endAt h.1.1 h.1.2 ∈ H.edgeSupport C.edges := by
  exact H.mem_edgeSupport_iff.mpr
    ⟨h.1.1, (Finset.mem_product.mp h.2).1, h.1.2, rfl⟩

private theorem existsUnique_other (h : CircuitHalfEdge C) :
    ∃! k : CircuitHalfEdge C,
      k ∈ C.halfEdgesAt (H.endAt h.1.1 h.1.2) ∧ k ≠ h := by
  classical
  let s := C.halfEdgesAt (H.endAt h.1.1 h.1.2)
  have hh : h ∈ s := by simp [s]
  have hs : s.card = 2 := C.halfEdgesAt_card (C.halfEdge_vertex_mem_support h)
  have hserase : (s.erase h).card = 1 := by
    rw [Finset.card_erase_of_mem hh, hs]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hserase
  refine ⟨k, ?_, ?_⟩
  · have hkmem : k ∈ s.erase h := by rw [hk]; simp
    exact ⟨Finset.mem_of_mem_erase hkmem, Finset.ne_of_mem_erase hkmem⟩
  · intro y hy
    have hymem : y ∈ s.erase h := Finset.mem_erase.mpr ⟨hy.2, hy.1⟩
    rw [hk] at hymem
    simpa using hymem

/-- The other circuit incidence at the same vertex. -/
private noncomputable def other (h : CircuitHalfEdge C) : CircuitHalfEdge C :=
  (C.existsUnique_other h).exists.choose

private theorem other_spec (h : CircuitHalfEdge C) :
    C.other h ∈ C.halfEdgesAt (H.endAt h.1.1 h.1.2) ∧ C.other h ≠ h :=
  (C.existsUnique_other h).exists.choose_spec

private theorem other_endpoint (h : CircuitHalfEdge C) :
    H.endAt (C.other h).1.1 (C.other h).1.2 = H.endAt h.1.1 h.1.2 := by
  exact (C.mem_halfEdgesAt _ _).mp (C.other_spec h).1

private theorem other_ne (h : CircuitHalfEdge C) : C.other h ≠ h :=
  (C.other_spec h).2

private theorem other_unique (h k : CircuitHalfEdge C)
    (hk : k ∈ C.halfEdgesAt (H.endAt h.1.1 h.1.2) ∧ k ≠ h) :
    k = C.other h :=
  (C.existsUnique_other h).unique hk (C.other_spec h)

private theorem other_other (h : CircuitHalfEdge C) : C.other (C.other h) = h := by
  symm
  apply C.other_unique (C.other h) h
  constructor
  · rw [C.mem_halfEdgesAt, C.other_endpoint]
  · exact (C.other_ne h).symm

/-- Pair the two incidences at every circuit vertex. -/
private noncomputable def otherPerm : Equiv.Perm (CircuitHalfEdge C) where
  toFun := C.other
  invFun := C.other
  left_inv := C.other_other
  right_inv := C.other_other

@[simp]
private theorem otherPerm_apply (h : CircuitHalfEdge C) : C.otherPerm h = C.other h := rfl

/-- Reverse the chosen direction of a labelled circuit edge. -/
private def edgeFlip : Equiv.Perm (CircuitHalfEdge C) where
  toFun h := ⟨(h.1.1, Fin.rev h.1.2), by simp [(Finset.mem_product.mp h.2).1]⟩
  invFun h := ⟨(h.1.1, Fin.rev h.1.2), by simp [(Finset.mem_product.mp h.2).1]⟩
  left_inv h := by ext <;> simp
  right_inv h := by ext <;> simp

omit [DecidableEq E] in
@[simp]
private theorem edgeFlip_apply (h : CircuitHalfEdge C) :
    (C.edgeFlip h).1 = (h.1.1, Fin.rev h.1.2) := rfl

omit [DecidableEq E] in
private theorem edgeFlip_ne (h : CircuitHalfEdge C) : C.edgeFlip h ≠ h := by
  intro heq
  have heq' := congr_arg (fun k : CircuitHalfEdge C ↦ k.1.2) heq
  have hne : Fin.rev h.1.2 ≠ h.1.2 := by
    intro hbad
    have hval := congr_arg Fin.val hbad
    simp [Fin.rev] at hval
    omega
  exact hne heq'

/-- Traverse an edge and then leave its arrival vertex along the unique other incidence. -/
private noncomputable def successor : Equiv.Perm (CircuitHalfEdge C) :=
  C.otherPerm * C.edgeFlip

@[simp]
private theorem successor_apply (h : CircuitHalfEdge C) :
    C.successor h = C.other (C.edgeFlip h) := rfl

private theorem successor_continuous (h : CircuitHalfEdge C) :
    H.endAt h.1.1 (Fin.rev h.1.2) =
      H.endAt (C.successor h).1.1 (C.successor h).1.2 := by
  rw [C.successor_apply, C.other_endpoint]
  rfl

private theorem otherPerm_sq : C.otherPerm ^ 2 = 1 := by
  apply Equiv.ext
  intro h
  exact C.other_other h

omit [DecidableEq E] in
private theorem edgeFlip_sq : C.edgeFlip ^ 2 = 1 := by
  apply Equiv.ext
  intro h
  change C.edgeFlip (C.edgeFlip h) = h
  apply Subtype.ext
  change (h.1.1, Fin.rev (Fin.rev h.1.2)) = h.1
  simp

private noncomputable def halfEdgeEquiv : CircuitHalfEdge C ≃ CircuitEdge C × Fin 2 where
  toFun h := (⟨h.1.1, (Finset.mem_product.mp h.2).1⟩, h.1.2)
  invFun h := ⟨(h.1.1, h.2), Finset.mem_product.mpr ⟨h.1.2, Finset.mem_univ _⟩⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv h := by ext <;> rfl

omit [DecidableEq E] in
private theorem card_circuitHalfEdge :
    Fintype.card (CircuitHalfEdge C) = 2 * C.edges.card := by
  rw [Fintype.card_congr C.halfEdgeEquiv, Fintype.card_prod]
  simp [Nat.mul_comm]

private theorem sign_otherPerm :
    Equiv.Perm.sign C.otherPerm = (-1) ^ C.edges.card := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one C.otherPerm_sq]
  haveI : IsEmpty (Function.fixedPoints C.otherPerm) :=
    ⟨fun h ↦ C.other_ne h.1 (Function.mem_fixedPoints_iff.mp h.2)⟩
  rw [C.card_circuitHalfEdge]
  simp

private theorem sign_edgeFlip :
    Equiv.Perm.sign C.edgeFlip = (-1) ^ C.edges.card := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one C.edgeFlip_sq]
  haveI : IsEmpty (Function.fixedPoints C.edgeFlip) :=
    ⟨fun h ↦ C.edgeFlip_ne h.1 (Function.mem_fixedPoints_iff.mp h.2)⟩
  rw [C.card_circuitHalfEdge]
  simp

private theorem sign_successor : Equiv.Perm.sign C.successor = 1 := by
  rw [successor, Equiv.Perm.sign_mul, C.sign_otherPerm, C.sign_edgeFlip]
  have hself : ((-1 : ℤˣ) ^ C.edges.card)⁻¹ = (-1 : ℤˣ) ^ C.edges.card := by simp
  calc
    ((-1 : ℤˣ) ^ C.edges.card)⁻¹ * ((-1 : ℤˣ) ^ C.edges.card)⁻¹ =
        (-1 : ℤˣ) ^ C.edges.card * (-1 : ℤˣ) ^ C.edges.card :=
      congrArg₂ (fun x y : ℤˣ ↦ x * y) hself hself
    _ = ((-1 : ℤˣ) * (-1 : ℤˣ)) ^ C.edges.card :=
      (mul_pow (-1 : ℤˣ) (-1 : ℤˣ) C.edges.card).symm
    _ = 1 := by simp

omit [DecidableEq E] in
private theorem edgeFlip_inv : C.edgeFlip⁻¹ = C.edgeFlip := by
  symm
  apply eq_inv_of_mul_eq_one_left
  simpa [pow_two] using C.edgeFlip_sq

private theorem otherPerm_inv : C.otherPerm⁻¹ = C.otherPerm := by
  symm
  apply eq_inv_of_mul_eq_one_left
  simpa [pow_two] using C.otherPerm_sq

private theorem edgeFlip_semiconj_successor :
    SemiconjBy C.edgeFlip C.successor C.successor⁻¹ := by
  change C.edgeFlip * C.successor = C.successor⁻¹ * C.edgeFlip
  rw [successor, mul_inv_rev, C.edgeFlip_inv, C.otherPerm_inv, mul_assoc]

private theorem sameCycle_edgeFlip_pair {h x : CircuitHalfEdge C}
    (hx : C.successor.SameCycle h x) :
    C.successor.SameCycle (C.edgeFlip h) (C.edgeFlip x) := by
  have hc := hx.conj (g := C.edgeFlip)
  have hs := C.edgeFlip_semiconj_successor
  change C.edgeFlip * C.successor = C.successor⁻¹ * C.edgeFlip at hs
  have hconj : C.edgeFlip * C.successor * C.edgeFlip⁻¹ = C.successor⁻¹ := by
    calc
      C.edgeFlip * C.successor * C.edgeFlip⁻¹ =
          (C.successor⁻¹ * C.edgeFlip) * C.edgeFlip⁻¹ := congr_arg (· * C.edgeFlip⁻¹) hs
      _ = C.successor⁻¹ := by simp [mul_assoc]
  rw [hconj] at hc
  exact Equiv.Perm.sameCycle_inv.mp hc

private theorem sameCycle_edgeFlip {h x : CircuitHalfEdge C}
    (hflip : C.successor.SameCycle h (C.edgeFlip h))
    (hx : C.successor.SameCycle h x) :
    C.successor.SameCycle h (C.edgeFlip x) := by
  exact hflip.trans (C.sameCycle_edgeFlip_pair hx)

private theorem sameCycle_other {h x : CircuitHalfEdge C}
    (hflip : C.successor.SameCycle h (C.edgeFlip h))
    (hx : C.successor.SameCycle h x) :
    C.successor.SameCycle h (C.otherPerm x) := by
  have hfx := C.sameCycle_edgeFlip hflip hx
  have hs := hfx.apply_right
  have heq : C.successor (C.edgeFlip x) = C.otherPerm x := by
    rw [C.successor_apply, C.otherPerm_apply]
    congr 1
    exact Equiv.congr_fun C.edgeFlip_sq x
  rw [heq] at hs
  exact hs

private def incidence (e : CircuitEdge C) (i : Fin 2) : CircuitHalfEdge C :=
  ⟨(e.1, i), Finset.mem_product.mpr ⟨e.2, Finset.mem_univ i⟩⟩

omit [DecidableEq E] in
@[simp]
private theorem incidence_edge (e : CircuitEdge C) (i : Fin 2) :
    (C.incidence e i).1.1 = e.1 := rfl

omit [DecidableEq E] in
@[simp]
private theorem incidence_end (e : CircuitEdge C) (i : Fin 2) :
    (C.incidence e i).1.2 = i := rfl

omit [DecidableEq E] in
private theorem edgeFlip_incidence (e : CircuitEdge C) (i : Fin 2) :
    C.edgeFlip (C.incidence e i) = C.incidence e (Fin.rev i) := by
  apply Subtype.ext
  rfl

private theorem finTwo_eq_or_eq_rev (i j : Fin 2) : i = j ∨ i = Fin.rev j := by
  fin_cases i
  · fin_cases j <;> simp [Fin.rev]
  · fin_cases j <;> simp [Fin.rev]

omit [DecidableEq E] in
private theorem incidence_eq_self_or_flip (h : CircuitHalfEdge C) (i : Fin 2) :
    C.incidence ⟨h.1.1, (Finset.mem_product.mp h.2).1⟩ i = h ∨
      C.incidence ⟨h.1.1, (Finset.mem_product.mp h.2).1⟩ i = C.edgeFlip h := by
  have hi : i = h.1.2 ∨ i = Fin.rev h.1.2 := finTwo_eq_or_eq_rev i h.1.2
  rcases hi with rfl | hi
  · left
    apply Subtype.ext
    rfl
  · right
    apply Subtype.ext
    exact Prod.ext rfl hi

omit [DecidableEq V] [DecidableEq E] in
private theorem edgeAdjacent_symm {e f : E} : H.EdgeAdjacent e f → H.EdgeAdjacent f e := by
  rintro ⟨i, j, hij⟩
  exact ⟨j, i, hij.symm⟩

private theorem sameCycle_all_of_edgeFlip {h : CircuitHalfEdge C}
    (hflip : C.successor.SameCycle h (C.edgeFlip h)) (x : CircuitHalfEdge C) :
    C.successor.SameCycle h x := by
  let R : E → E → Prop := fun e f ↦
    e ∈ C.edges ∧ f ∈ C.edges ∧ H.EdgeAdjacent e f
  let P : E → Prop := fun e ↦
    ∀ (he : e ∈ C.edges) (i : Fin 2),
      C.successor.SameCycle h (C.incidence ⟨e, he⟩ i)
  have hstart : P h.1.1 := by
    intro he i
    have hedge : (⟨h.1.1, he⟩ : CircuitEdge C) =
        ⟨h.1.1, (Finset.mem_product.mp h.2).1⟩ := Subtype.ext rfl
    rw [hedge]
    rcases C.incidence_eq_self_or_flip h i with hi | hi
    · simpa only [hi] using (Equiv.Perm.SameCycle.rfl : C.successor.SameCycle h h)
    · simpa only [hi] using hflip
  have hstep : ∀ {e f : E}, R e f → P e → P f := by
    intro e f hef hPe hf j
    obtain ⟨he, hf', ⟨i, k, hik⟩⟩ := hef
    let ei : CircuitHalfEdge C := C.incidence ⟨e, he⟩ i
    let fk : CircuitHalfEdge C := C.incidence ⟨f, hf'⟩ k
    have hei : C.successor.SameCycle h ei := hPe he i
    have hfk : C.successor.SameCycle h fk := by
      by_cases heq : fk = ei
      · simpa [heq] using hei
      · have hfkmem : fk ∈ C.halfEdgesAt (H.endAt ei.1.1 ei.1.2) := by
          rw [C.mem_halfEdgesAt]
          exact hik.symm
        have hother : fk = C.other ei := C.other_unique ei fk ⟨hfkmem, heq⟩
        rw [hother, ← C.otherPerm_apply]
        exact C.sameCycle_other hflip hei
    have hedge : (⟨f, hf⟩ : CircuitEdge C) = ⟨f, hf'⟩ := Subtype.ext rfl
    rw [hedge]
    rcases C.incidence_eq_self_or_flip fk j with hj | hj
    · have ht : C.incidence ⟨f, hf'⟩ j = fk := by simpa [fk] using hj
      simpa only [ht] using hfk
    · have ht : C.incidence ⟨f, hf'⟩ j = C.edgeFlip fk := by simpa [fk] using hj
      simpa only [ht] using C.sameCycle_edgeFlip hflip hfk
  obtain ⟨root, hroot, hconnected⟩ := C.connected
  have hstart_mem : h.1.1 ∈ C.edges := (Finset.mem_product.mp h.2).1
  have hroot_start : Relation.ReflTransGen R root h.1.1 :=
    hconnected h.1.1 hstart_mem
  have hstart_root : Relation.ReflTransGen R h.1.1 root := by
    exact Relation.ReflTransGen.mono (r := Function.swap R) (p := R)
      (fun _ _ hba ↦ ⟨hba.2.1, hba.1, edgeAdjacent_symm (H := H) hba.2.2⟩)
      hroot_start.swap
  have hx_mem : x.1.1 ∈ C.edges := (Finset.mem_product.mp x.2).1
  have hpath : Relation.ReflTransGen R h.1.1 x.1.1 :=
    hstart_root.trans (hconnected x.1.1 hx_mem)
  have hpath_prop : ∀ (y : E), Relation.ReflTransGen R h.1.1 y → P y := by
    intro y hy
    induction hy with
    | refl => exact hstart
    | tail hab hbc ih => exact hstep hbc ih
  have hPx : P x.1.1 := hpath_prop x.1.1 hpath
  have hxinc := hPx hx_mem x.1.2
  convert hxinc using 1
  apply Subtype.ext
  rfl

private theorem not_sameCycle_edgeFlip (h : CircuitHalfEdge C) :
    ¬ C.successor.SameCycle h (C.edgeFlip h) := by
  intro hflip
  have hall : ∀ x : CircuitHalfEdge C, C.successor.SameCycle h x :=
    C.sameCycle_all_of_edgeFlip hflip
  have hmove : C.successor h ≠ h := by
    intro hfixed
    have heq : h = C.edgeFlip h := hflip.eq_of_left hfixed
    exact C.edgeFlip_ne h heq.symm
  have hcycle : C.successor.IsCycle := ⟨h, hmove, fun _ _ ↦ hall _⟩
  have hsupport : C.successor.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro hfixed
    exact hmove ((hall x).apply_eq_self_iff.mpr hfixed)
  have hsign := hcycle.sign
  rw [C.sign_successor, hsupport, Finset.card_univ, C.card_circuitHalfEdge] at hsign
  norm_num [pow_mul] at hsign

private abbrev InTwoOrbits (h x : CircuitHalfEdge C) : Prop :=
  C.successor.SameCycle h x ∨ C.successor.SameCycle (C.edgeFlip h) x

private theorem inTwoOrbits_edgeFlip {h x : CircuitHalfEdge C}
    (hx : C.InTwoOrbits h x) : C.InTwoOrbits h (C.edgeFlip x) := by
  rcases hx with hx | hx
  · exact Or.inr (C.sameCycle_edgeFlip_pair hx)
  · left
    have hpair := C.sameCycle_edgeFlip_pair hx
    have hsqh : C.edgeFlip (C.edgeFlip h) = h := Equiv.congr_fun C.edgeFlip_sq h
    simpa [hsqh] using hpair

private theorem inTwoOrbits_other {h x : CircuitHalfEdge C}
    (hx : C.InTwoOrbits h x) : C.InTwoOrbits h (C.otherPerm x) := by
  have hfx := C.inTwoOrbits_edgeFlip hx
  rcases hfx with hfx | hfx
  · left
    have hs := hfx.apply_right
    have heq : C.successor (C.edgeFlip x) = C.otherPerm x := by
      rw [C.successor_apply, C.otherPerm_apply]
      congr 1
      exact Equiv.congr_fun C.edgeFlip_sq x
    simpa only [heq] using hs
  · right
    have hs := hfx.apply_right
    have heq : C.successor (C.edgeFlip x) = C.otherPerm x := by
      rw [C.successor_apply, C.otherPerm_apply]
      congr 1
      exact Equiv.congr_fun C.edgeFlip_sq x
    simpa only [heq] using hs

private theorem inTwoOrbits_all (h x : CircuitHalfEdge C) : C.InTwoOrbits h x := by
  let R : E → E → Prop := fun e f ↦
    e ∈ C.edges ∧ f ∈ C.edges ∧ H.EdgeAdjacent e f
  let P : E → Prop := fun e ↦
    ∀ (he : e ∈ C.edges) (i : Fin 2),
      C.InTwoOrbits h (C.incidence ⟨e, he⟩ i)
  have hstart : P h.1.1 := by
    intro he i
    have hedge : (⟨h.1.1, he⟩ : CircuitEdge C) =
        ⟨h.1.1, (Finset.mem_product.mp h.2).1⟩ := Subtype.ext rfl
    rw [hedge]
    rcases C.incidence_eq_self_or_flip h i with hi | hi
    · exact Or.inl (by simpa only [hi] using
        (Equiv.Perm.SameCycle.rfl : C.successor.SameCycle h h))
    · exact Or.inr (by simpa only [hi] using
        (Equiv.Perm.SameCycle.rfl : C.successor.SameCycle (C.edgeFlip h) (C.edgeFlip h)))
  have hstep : ∀ {e f : E}, R e f → P e → P f := by
    intro e f hef hPe hf j
    obtain ⟨he, hf', ⟨i, k, hik⟩⟩ := hef
    let ei : CircuitHalfEdge C := C.incidence ⟨e, he⟩ i
    let fk : CircuitHalfEdge C := C.incidence ⟨f, hf'⟩ k
    have hei : C.InTwoOrbits h ei := hPe he i
    have hfk : C.InTwoOrbits h fk := by
      by_cases heq : fk = ei
      · simpa [heq] using hei
      · have hfkmem : fk ∈ C.halfEdgesAt (H.endAt ei.1.1 ei.1.2) := by
          rw [C.mem_halfEdgesAt]
          exact hik.symm
        have hother : fk = C.other ei := C.other_unique ei fk ⟨hfkmem, heq⟩
        rw [hother, ← C.otherPerm_apply]
        exact C.inTwoOrbits_other hei
    have hedge : (⟨f, hf⟩ : CircuitEdge C) = ⟨f, hf'⟩ := Subtype.ext rfl
    rw [hedge]
    rcases C.incidence_eq_self_or_flip fk j with hj | hj
    · have ht : C.incidence ⟨f, hf'⟩ j = fk := by simpa [fk] using hj
      simpa only [ht] using hfk
    · have ht : C.incidence ⟨f, hf'⟩ j = C.edgeFlip fk := by simpa [fk] using hj
      simpa only [ht] using C.inTwoOrbits_edgeFlip hfk
  obtain ⟨root, hroot, hconnected⟩ := C.connected
  have hstart_mem : h.1.1 ∈ C.edges := (Finset.mem_product.mp h.2).1
  have hroot_start : Relation.ReflTransGen R root h.1.1 :=
    hconnected h.1.1 hstart_mem
  have hstart_root : Relation.ReflTransGen R h.1.1 root := by
    exact Relation.ReflTransGen.mono (r := Function.swap R) (p := R)
      (fun _ _ hba ↦ ⟨hba.2.1, hba.1, edgeAdjacent_symm (H := H) hba.2.2⟩)
      hroot_start.swap
  have hx_mem : x.1.1 ∈ C.edges := (Finset.mem_product.mp x.2).1
  have hpath : Relation.ReflTransGen R h.1.1 x.1.1 :=
    hstart_root.trans (hconnected x.1.1 hx_mem)
  have hpath_prop : ∀ (y : E), Relation.ReflTransGen R h.1.1 y → P y := by
    intro y hy
    induction hy with
    | refl => exact hstart
    | tail hab hbc ih => exact hstep hbc ih
  have hPx : P x.1.1 := hpath_prop x.1.1 hpath
  have hxinc := hPx hx_mem x.1.2
  convert hxinc using 1
  apply Subtype.ext
  rfl

private theorem exists_incidence_sameCycle (h : CircuitHalfEdge C) (e : CircuitEdge C) :
    ∃ i : Fin 2, C.successor.SameCycle h (C.incidence e i) := by
  have hu := C.inTwoOrbits_all h (C.incidence e 0)
  rcases hu with hu | hu
  · exact ⟨0, hu⟩
  · have hp := C.sameCycle_edgeFlip_pair hu
    have hsq : C.edgeFlip (C.edgeFlip h) = h := Equiv.congr_fun C.edgeFlip_sq h
    refine ⟨Fin.rev 0, ?_⟩
    simpa [hsq, C.edgeFlip_incidence] using hp

private theorem incidence_sameCycle_injective (h : CircuitHalfEdge C) (e : CircuitEdge C)
    {i j : Fin 2} (hi : C.successor.SameCycle h (C.incidence e i))
    (hj : C.successor.SameCycle h (C.incidence e j)) : i = j := by
  by_contra hij
  have hrev : j = Fin.rev i := by
    fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]
  have hsame :
      C.successor.SameCycle (C.incidence e i) (C.edgeFlip (C.incidence e i)) := by
    have := hi.symm.trans hj
    simpa [hrev, C.edgeFlip_incidence] using this
  exact C.not_sameCycle_edgeFlip (C.incidence e i) hsame

private def underlyingEdge (h : CircuitHalfEdge C) : CircuitEdge C :=
  ⟨h.1.1, (Finset.mem_product.mp h.2).1⟩

omit [DecidableEq E] in
@[simp]
private theorem underlyingEdge_incidence (e : CircuitEdge C) (i : Fin 2) :
    C.underlyingEdge (C.incidence e i) = e := by
  apply Subtype.ext
  rfl

omit [DecidableEq E] in
private theorem eq_or_eq_edgeFlip_of_underlyingEdge_eq {x y : CircuitHalfEdge C}
    (hxy : C.underlyingEdge x = C.underlyingEdge y) : y = x ∨ y = C.edgeFlip x := by
  have hedge : y.1.1 = x.1.1 := by
    exact congr_arg Subtype.val hxy |>.symm
  have hside : y.1.2 = x.1.2 ∨ y.1.2 = Fin.rev x.1.2 :=
    finTwo_eq_or_eq_rev y.1.2 x.1.2
  rcases hside with hside | hside
  · left
    apply Subtype.ext
    exact Prod.ext hedge hside
  · right
    apply Subtype.ext
    exact Prod.ext hedge hside

private noncomputable def startHalfEdge : CircuitHalfEdge C :=
  C.incidence ⟨C.nonempty.choose, C.nonempty.choose_spec⟩ 0

private noncomputable def orbitList (h : CircuitHalfEdge C) : List (CircuitHalfEdge C) :=
  (List.range (Function.minimalPeriod C.successor h)).map fun n ↦ C.successor^[n] h

private theorem start_mem_periodicPts (h : CircuitHalfEdge C) :
    h ∈ Function.periodicPts C.successor := by
  refine ⟨orderOf C.successor, orderOf_pos C.successor, ?_⟩
  change (C.successor ^ orderOf C.successor) h = h
  rw [pow_orderOf_eq_one]
  rfl

private theorem mem_orbitList_iff_sameCycle (h x : CircuitHalfEdge C) :
    x ∈ C.orbitList h ↔ C.successor.SameCycle h x := by
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := List.mem_map.mp hx
    refine ⟨(n : ℤ), ?_⟩
    simpa [Equiv.Perm.iterate_eq_pow] using hnx
  · intro hx
    obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
    have horbit : x ∈ Function.periodicOrbit C.successor h := by
      rw [Function.mem_periodicOrbit_iff (C.start_mem_periodicPts h)]
      exact ⟨n, by simpa [Equiv.Perm.iterate_eq_pow] using hn⟩
    simpa [orbitList, Function.periodicOrbit] using horbit

private theorem orbitList_nodup (h : CircuitHalfEdge C) : (C.orbitList h).Nodup := by
  simpa [orbitList, Function.periodicOrbit] using
    (Function.nodup_periodicOrbit (f := C.successor) (x := h))

private theorem orbitEdges_nodup (h : CircuitHalfEdge C) :
    ((C.orbitList h).map C.underlyingEdge).Nodup := by
  rw [List.nodup_map_iff_inj_on (C.orbitList_nodup h)]
  intro x hx y hy hxy
  rcases C.eq_or_eq_edgeFlip_of_underlyingEdge_eq hxy with hyx | hyx
  · exact hyx.symm
  · exfalso
    have hsx : C.successor.SameCycle h x := (C.mem_orbitList_iff_sameCycle h x).mp hx
    have hsy : C.successor.SameCycle h y := (C.mem_orbitList_iff_sameCycle h y).mp hy
    have hbad := hsx.symm.trans hsy
    rw [hyx] at hbad
    exact C.not_sameCycle_edgeFlip x hbad

private theorem every_edge_mem_orbitEdges (h : CircuitHalfEdge C) (e : CircuitEdge C) :
    e ∈ (C.orbitList h).map C.underlyingEdge := by
  obtain ⟨i, hi⟩ := C.exists_incidence_sameCycle h e
  apply List.mem_map.mpr
  exact ⟨C.incidence e i, (C.mem_orbitList_iff_sameCycle h _).mpr hi,
    C.underlyingEdge_incidence e i⟩

@[simp]
private theorem orbitList_length (h : CircuitHalfEdge C) :
    (C.orbitList h).length = Function.minimalPeriod C.successor h := by
  simp [orbitList]

private theorem orbitList_get (h : CircuitHalfEdge C)
    (i : Fin (C.orbitList h).length) :
    (C.orbitList h).get i = C.successor^[i.1] h := by
  simp [orbitList]

private theorem successor_orbitList_get_finRotate (h : CircuitHalfEdge C)
    (i : Fin (C.orbitList h).length) :
    C.successor ((C.orbitList h).get i) =
      (C.orbitList h).get (finRotate (C.orbitList h).length i) := by
  rw [C.orbitList_get, C.orbitList_get]
  have hp : 0 < Function.minimalPeriod C.successor h :=
    Function.minimalPeriod_pos_of_mem_periodicPts (C.start_mem_periodicPts h)
  letI : NeZero (C.orbitList h).length := i.neZero
  rw [finRotate_apply]
  simp only [Fin.add_def]
  have hmod :
      (i.1 + ((1 : Fin (C.orbitList h).length) : ℕ)) % (C.orbitList h).length =
        (i.1 + 1) % (C.orbitList h).length := by
    calc
      (i.1 + ((1 : Fin (C.orbitList h).length) : ℕ)) % (C.orbitList h).length =
          (i.1 + 1 % (C.orbitList h).length) % (C.orbitList h).length := by
            rw [Fin.val_one']
      _ = (i.1 % (C.orbitList h).length + 1 % (C.orbitList h).length) %
          (C.orbitList h).length := by rw [Nat.mod_eq_of_lt i.2]
      _ = (i.1 + 1) % (C.orbitList h).length :=
        (Nat.add_mod i.1 1 (C.orbitList h).length).symm
  rw [hmod]
  have hreduce :
      C.successor^[((i.1 + 1) % (C.orbitList h).length)] h =
        C.successor^[i.1 + 1] h := by
    let n := i.1 + 1
    change C.successor^[n % (C.orbitList h).length] h = C.successor^[n] h
    rw [C.orbitList_length]
    exact Function.iterate_mod_minimalPeriod_eq
  calc
    C.successor (C.successor^[i.1] h) = C.successor^[i.1 + 1] h :=
      (Function.iterate_succ_apply' C.successor i.1 h).symm
    _ = C.successor^[((i.1 + 1) % (C.orbitList h).length)] h := hreduce.symm

/-- Every finite connected 2-regular ordinary circuit has a closed traversal using each of its
labelled edges exactly once. -/
theorem exists_eulerTour : Nonempty C.restricted.EulerTour := by
  classical
  let h : CircuitHalfEdge C := C.startHalfEdge
  have hperiod : 0 < Function.minimalPeriod C.successor h :=
    Function.minimalPeriod_pos_of_mem_periodicPts (C.start_mem_periodicPts h)
  have hLne : C.orbitList h ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa using hperiod
  obtain ⟨a, l, hL⟩ := List.exists_cons_of_ne_nil hLne
  let half : Fin (l.length + 1) → CircuitHalfEdge C := fun i ↦ (a :: l).get i
  let edgeList : List (CircuitEdge C) := (a :: l).map C.underlyingEdge
  have hedgeNodup : edgeList.Nodup := by
    have hn := C.orbitEdges_nodup h
    simpa [edgeList, hL] using hn
  have hedgeAll : ∀ e : CircuitEdge C, e ∈ edgeList := by
    intro e
    have hm := C.every_edge_mem_orbitEdges h e
    simpa [edgeList, hL] using hm
  have hedgeLength : edgeList.length = l.length + 1 := by simp [edgeList]
  let edgeEquiv : Fin (l.length + 1) ≃ CircuitEdge C :=
    (finCongr hedgeLength.symm).trans
      (hedgeNodup.getEquivOfForallMemList edgeList hedgeAll)
  have hedgeEquiv (i : Fin (l.length + 1)) :
      edgeEquiv i = C.underlyingEdge (half i) := by
    change edgeList.get (Fin.cast hedgeLength.symm i) =
      C.underlyingEdge ((a :: l).get i)
    simp only [List.get_eq_getElem]
    change ((a :: l).map C.underlyingEdge)[i.1] =
      C.underlyingEdge (a :: l)[i.1]
    exact List.getElem_map C.underlyingEdge
  have hsuccessor (i : Fin (l.length + 1)) :
      C.successor (half i) = half (finRotate (l.length + 1) i) := by
    have hs : ∀ i : Fin (C.orbitList h).length,
        C.successor ((C.orbitList h).get i) =
          (C.orbitList h).get (finRotate (C.orbitList h).length i) :=
      C.successor_orbitList_get_finRotate h
    rw [hL] at hs
    exact hs i
  refine ⟨{
    n := l.length
    edge := edgeEquiv
    depart := fun i ↦ (half i).1.2
    continuous := ?_
  }⟩
  intro i
  change H.endAt (edgeEquiv i).1 (Fin.rev (half i).1.2) =
    H.endAt (edgeEquiv (finRotate (l.length + 1) i)).1
      (half (finRotate (l.length + 1) i)).1.2
  rw [hedgeEquiv, hedgeEquiv]
  have hc := C.successor_continuous (half i)
  rw [hsuccessor i] at hc
  exact hc

/-- A noncomputably chosen Euler tour of an ordinary circuit. -/
noncomputable def eulerTour : C.restricted.EulerTour := C.exists_eulerTour.some

end OrdinaryCircuit

end LoopMultigraph
end GraphPuzzles
