import GraphPuzzles.Circuits.ParityColoring

/-!
# Arcs of a traversed circuit between marked vertices

For a traversed circuit and a set `W` of *marked* vertices met by it, the circuit splits into
arcs: maximal runs of tour edges between consecutive marked positions.  This module defines the
distance `back` from a position to the last marked position at or before it, the distance
`forward` from a marked position to the next marked position, and proves the bookkeeping used
to suppress the unmarked vertices of the circuit: the arc structure is determined by `back`,
consecutive marked positions are related by `nextM`/`prevM`, and every marked position is
reached from any other by iterating `nextM`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped Fin.NatCast

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit) (W : Finset V)

omit [DecidableEq E] in
theorem posCast_sub {m m' : ℕ} (h : m' ≤ m) :
    ((m - m' : ℕ) : C.tour.Pos) = (m : C.tour.Pos) - (m' : C.tour.Pos) := by
  have := (Nat.cast_sub h : ((m - m' : ℕ) : ZMod (C.tour.n + 1)) =
    (m : ZMod (C.tour.n + 1)) - (m' : ZMod (C.tour.n + 1)))
  exact this

omit [DecidableEq E] in
theorem posCast_add (m m' : ℕ) :
    ((m + m' : ℕ) : C.tour.Pos) = (m : C.tour.Pos) + (m' : C.tour.Pos) := by
  have := (Nat.cast_add m m' : ((m + m' : ℕ) : ZMod (C.tour.n + 1)) =
    (m : ZMod (C.tour.n + 1)) + (m' : ZMod (C.tour.n + 1)))
  exact this

omit [DecidableEq E] in
theorem posCast_one : ((1 : ℕ) : C.tour.Pos) = 1 := by
  have := (Nat.cast_one : ((1 : ℕ) : ZMod (C.tour.n + 1)) = 1)
  exact this

omit [DecidableEq E] in
theorem posCast_zero : ((0 : ℕ) : C.tour.Pos) = 0 := by
  have := (Nat.cast_zero : ((0 : ℕ) : ZMod (C.tour.n + 1)) = 0)
  exact this

/-- A position is marked when its departure vertex lies in `W`. -/
def Marked (p : C.tour.Pos) : Prop := C.tour.vertexAt p ∈ W

instance (p : C.tour.Pos) : Decidable (C.Marked W p) := by
  unfold Marked
  infer_instance

variable (hex : ∃ p, C.Marked W p)
include hex

omit [DecidableEq E] in
theorem exists_back (q : C.tour.Pos) : ∃ m : ℕ, C.Marked W (q - (m : C.tour.Pos)) := by
  obtain ⟨p, hp⟩ := hex
  refine ⟨(q - p).val, ?_⟩
  rw [Fin.cast_val_eq_self, sub_sub_cancel]
  exact hp

/-- The distance back from `q` to the last marked position at or before `q`. -/
noncomputable def back (q : C.tour.Pos) : ℕ := Nat.find (C.exists_back W hex q)

/-- The last marked position at or before `q`. -/
noncomputable def start (q : C.tour.Pos) : C.tour.Pos := q - (C.back W hex q : C.tour.Pos)

omit [DecidableEq E] in
theorem marked_start (q : C.tour.Pos) : C.Marked W (C.start W hex q) :=
  Nat.find_spec (C.exists_back W hex q)

omit [DecidableEq E] in
theorem not_marked_of_lt_back (q : C.tour.Pos) {m : ℕ} (hm : m < C.back W hex q) :
    ¬ C.Marked W (q - (m : C.tour.Pos)) :=
  Nat.find_min (C.exists_back W hex q) hm

omit [DecidableEq E] in
theorem back_le_of_marked (q : C.tour.Pos) {m : ℕ} (hm : C.Marked W (q - (m : C.tour.Pos))) :
    C.back W hex q ≤ m :=
  Nat.find_min' (C.exists_back W hex q) hm

omit [DecidableEq E] in
theorem back_eq_zero_of_marked {q : C.tour.Pos} (hq : C.Marked W q) : C.back W hex q = 0 :=
  Nat.le_zero.mp (C.back_le_of_marked W hex q (by simpa using hq))

omit [DecidableEq E] in
theorem start_of_marked {q : C.tour.Pos} (hq : C.Marked W q) : C.start W hex q = q := by
  unfold start
  rw [C.back_eq_zero_of_marked W hex hq]
  simp

omit [DecidableEq E] in
theorem back_pos_of_not_marked {q : C.tour.Pos} (hq : ¬ C.Marked W q) : 0 < C.back W hex q := by
  by_contra h
  push Not at h
  have h0 : C.back W hex q = 0 := by omega
  have := C.marked_start W hex q
  unfold start at this
  rw [h0, C.posCast_zero, sub_zero] at this
  exact hq this

omit [DecidableEq E] in
/-- The characterisation of `back` by a marked position and an unmarked run after it. -/
theorem back_eq_of_run {p : C.tour.Pos} (hp : C.Marked W p) {j : ℕ}
    (hrun : ∀ m : ℕ, 0 < m → m ≤ j → ¬ C.Marked W (p + (m : C.tour.Pos))) :
    C.back W hex (p + (j : C.tour.Pos)) = j := by
  apply le_antisymm
  · apply C.back_le_of_marked W hex
    rw [add_sub_cancel_right]
    exact hp
  · by_contra hlt
    push Not at hlt
    have hm := C.marked_start W hex (p + j)
    unfold start at hm
    have hcast : (p + (j : C.tour.Pos)) - (C.back W hex (p + (j : C.tour.Pos)) : C.tour.Pos) =
        p + ((j - C.back W hex (p + (j : C.tour.Pos)) : ℕ) : C.tour.Pos) := by
      rw [C.posCast_sub hlt.le, add_sub_assoc]
    rw [hcast] at hm
    exact hrun _ (by omega) (by omega) hm

omit [DecidableEq E] in
theorem back_sub_one_of_not_marked {q : C.tour.Pos} (hq : ¬ C.Marked W q) :
    C.back W hex (q - 1) = C.back W hex q - 1 := by
  have hpos := C.back_pos_of_not_marked W hex hq
  have hstart := C.marked_start W hex q
  set b := C.back W hex q with hb
  have hq' : q - 1 = C.start W hex q + ((b - 1 : ℕ) : C.tour.Pos) := by
    unfold start
    rw [← hb, C.posCast_sub hpos, C.posCast_one]
    abel
  rw [hq']
  apply C.back_eq_of_run W hex hstart
  intro m hm hmle
  have : C.start W hex q + (m : C.tour.Pos) = q - ((b - m : ℕ) : C.tour.Pos) := by
    unfold start
    rw [← hb, C.posCast_sub (by omega)]
    abel
  rw [this]
  exact C.not_marked_of_lt_back W hex q (by omega)

omit [DecidableEq E] in
theorem start_sub_one_of_not_marked {q : C.tour.Pos} (hq : ¬ C.Marked W q) :
    C.start W hex (q - 1) = C.start W hex q := by
  unfold start
  rw [C.back_sub_one_of_not_marked W hex hq, C.posCast_sub (C.back_pos_of_not_marked W hex hq),
    C.posCast_one]
  abel

omit [DecidableEq E] in
/-- Positions strictly inside an arc are unmarked. -/
theorem not_marked_of_pos_of_le_back (q : C.tour.Pos) {m : ℕ} (hm0 : 0 < m)
    (hm : m ≤ C.back W hex q) : ¬ C.Marked W (C.start W hex q + (m : C.tour.Pos)) := by
  have : C.start W hex q + (m : C.tour.Pos) = q - ((C.back W hex q - m : ℕ) : C.tour.Pos) := by
    unfold start
    rw [C.posCast_sub hm]
    abel
  rw [this]
  exact C.not_marked_of_lt_back W hex q (by omega)

omit [DecidableEq E] hex in
theorem exists_forward {p : C.tour.Pos} (hp : C.Marked W p) :
    ∃ m : ℕ, 0 < m ∧ C.Marked W (p + (m : C.tour.Pos)) :=
  ⟨C.tour.n + 1, Nat.succ_pos _, by
    have : ((C.tour.n + 1 : ℕ) : C.tour.Pos) = 0 := Fin.natCast_self _
    rw [this, add_zero]
    exact hp⟩

omit hex in
/-- The distance from a marked position to the next marked position. -/
noncomputable def forward {p : C.tour.Pos} (hp : C.Marked W p) : ℕ :=
  Nat.find (C.exists_forward W hp)

omit hex [DecidableEq E] in
theorem forward_pos {p : C.tour.Pos} (hp : C.Marked W p) : 0 < C.forward W hp :=
  (Nat.find_spec (C.exists_forward W hp)).1

omit hex in
/-- The next marked position after a marked position. -/
noncomputable def nextM {p : C.tour.Pos} (hp : C.Marked W p) : C.tour.Pos :=
  p + (C.forward W hp : C.tour.Pos)

omit hex [DecidableEq E] in
theorem marked_nextM {p : C.tour.Pos} (hp : C.Marked W p) : C.Marked W (C.nextM W hp) :=
  (Nat.find_spec (C.exists_forward W hp)).2

omit hex [DecidableEq E] in
theorem not_marked_of_lt_forward {p : C.tour.Pos} (hp : C.Marked W p) {m : ℕ} (hm0 : 0 < m)
    (hm : m < C.forward W hp) : ¬ C.Marked W (p + (m : C.tour.Pos)) :=
  fun h ↦ Nat.find_min (C.exists_forward W hp) hm ⟨hm0, h⟩

omit hex [DecidableEq E] in
theorem forward_le_of_marked {p : C.tour.Pos} (hp : C.Marked W p) {m : ℕ} (hm0 : 0 < m)
    (hm : C.Marked W (p + (m : C.tour.Pos))) : C.forward W hp ≤ m :=
  Nat.find_min' (C.exists_forward W hp) ⟨hm0, hm⟩

omit hex [DecidableEq E] in
theorem forward_le_n_of_two {p p' : C.tour.Pos} (hp : C.Marked W p) (hp' : C.Marked W p')
    (hne : p' ≠ p) : C.forward W hp ≤ C.tour.n := by
  have hle := C.forward_le_of_marked W hp (m := (p' - p).val) ?_ ?_
  · have : (p' - p).val ≤ C.tour.n := Nat.lt_succ_iff.mp (p' - p).2
    omega
  · rcases Nat.eq_zero_or_pos (p' - p).val with h | h
    · exfalso
      apply hne
      have : p' - p = 0 := Fin.ext h
      exact sub_eq_zero.mp this
    · exact h
  · rw [Fin.cast_val_eq_self, add_sub_cancel]
    exact hp'

omit hex [DecidableEq E] in
theorem nextM_ne_of_two {p p' : C.tour.Pos} (hp : C.Marked W p) (hp' : C.Marked W p')
    (hne : p' ≠ p) : C.nextM W hp ≠ p := by
  intro h
  have hle := C.forward_le_n_of_two W hp hp' hne
  have hpos := C.forward_pos W hp
  unfold nextM at h
  have : ((C.forward W hp : ℕ) : C.tour.Pos) = 0 := by
    have h' := congrArg (fun x ↦ x - p) h
    simp only [add_sub_cancel_left, sub_self] at h'
    exact h'
  have hval : (C.forward W hp) % (C.tour.n + 1) = 0 := by
    have := congrArg Fin.val this
    rw [Fin.val_natCast] at this
    simpa using this
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  omega

omit [DecidableEq E] in
/-- Inside an arc starting at a marked position, `start` and `back` are as expected. -/
theorem start_add_of_lt_forward {p : C.tour.Pos} (hp : C.Marked W p)
    {m : ℕ} (hm : m < C.forward W hp) :
    C.back W hex (p + (m : C.tour.Pos)) = m ∧ C.start W hex (p + (m : C.tour.Pos)) = p := by
  have hb : C.back W hex (p + (m : C.tour.Pos)) = m := by
    apply C.back_eq_of_run W hex hp
    intro m' hm'0 hm'
    exact C.not_marked_of_lt_forward W hp hm'0 (by omega)
  refine ⟨hb, ?_⟩
  unfold start
  rw [hb, add_sub_cancel_right]

/-- The previous marked position before a position. -/
noncomputable def prevM (q : C.tour.Pos) : C.tour.Pos := C.start W hex (q - 1)

omit [DecidableEq E] in
theorem marked_prevM (q : C.tour.Pos) : C.Marked W (C.prevM W hex q) :=
  C.marked_start W hex (q - 1)

omit [DecidableEq E] in
theorem back_nextM_sub_one {p : C.tour.Pos} (hp : C.Marked W p) :
    C.back W hex (C.nextM W hp - 1) = C.forward W hp - 1 ∧
      C.start W hex (C.nextM W hp - 1) = p := by
  have hpos := C.forward_pos W hp
  have heq : C.nextM W hp - 1 = p + ((C.forward W hp - 1 : ℕ) : C.tour.Pos) := by
    unfold nextM
    rw [C.posCast_sub hpos, C.posCast_one]
    abel
  rw [heq]
  exact C.start_add_of_lt_forward W hex hp (by omega)

omit [DecidableEq E] in
theorem prevM_nextM {p : C.tour.Pos} (hp : C.Marked W p) : C.prevM W hex (C.nextM W hp) = p :=
  (C.back_nextM_sub_one W hex hp).2

omit [DecidableEq E] in
theorem nextM_prevM {q : C.tour.Pos} (hq : C.Marked W q) :
    C.nextM W (C.marked_prevM W hex q) = q := by
  have hb : q - 1 = C.prevM W hex q + ((C.back W hex (q - 1) : ℕ) : C.tour.Pos) := by
    unfold prevM start
    abel
  have hq' : q = C.prevM W hex q + ((C.back W hex (q - 1) + 1 : ℕ) : C.tour.Pos) := by
    rw [C.posCast_add, C.posCast_one, ← add_assoc, ← hb]
    abel
  have hfwd : C.forward W (C.marked_prevM W hex q) = C.back W hex (q - 1) + 1 := by
    apply le_antisymm
    · apply C.forward_le_of_marked W (C.marked_prevM W hex q) (m := C.back W hex (q - 1) + 1)
        (by omega)
      rw [← hq']
      exact hq
    · by_contra hlt
      push Not at hlt
      have hm := C.marked_nextM W (C.marked_prevM W hex q)
      unfold nextM at hm
      have := C.not_marked_of_pos_of_le_back W hex (q - 1)
        (C.forward_pos W (C.marked_prevM W hex q)) (by omega)
      exact this hm
  unfold nextM
  rw [hfwd]
  exact hq'.symm

omit [DecidableEq E] in
/-- Every marked position is reached from a marked position by iterating `nextM`. -/
theorem reach_marked {p₀ : C.tour.Pos} (hp₀ : C.Marked W p₀) (P : C.tour.Pos → Prop)
    (h0 : P p₀) (hstep : ∀ p (hp : C.Marked W p), P p → P (C.nextM W hp)) :
    ∀ p, C.Marked W p → P p := by
  have key : ∀ d : ℕ, ∀ p, C.Marked W p → (p - p₀).val = d → P p := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      by_cases hd0 : d = 0
      · have : p = p₀ := by
          have h : p - p₀ = 0 := Fin.ext (by rw [hd, hd0]; rfl)
          exact sub_eq_zero.mp h
        rw [this]
        exact h0
      · have hq := C.nextM_prevM W hex hp
        have hprev := C.marked_prevM W hex p
        have hlt : (C.prevM W hex p - p₀).val < d := by
          -- `prevM p = p - 1 - back (p - 1)` and `back (p - 1) ≤ d - 1`
          have hb : C.back W hex (p - 1) ≤ d - 1 := by
            apply C.back_le_of_marked W hex
            have : (p - 1) - ((d - 1 : ℕ) : C.tour.Pos) = p₀ := by
              rw [C.posCast_sub (by omega), C.posCast_one, ← hd, Fin.cast_val_eq_self]
              abel
            rw [this]
            exact hp₀
          have hval : (C.prevM W hex p - p₀).val = d - 1 - C.back W hex (p - 1) := by
            unfold prevM start
            have : p - 1 - (C.back W hex (p - 1) : C.tour.Pos) - p₀ =
                ((d - 1 - C.back W hex (p - 1) : ℕ) : C.tour.Pos) := by
              rw [C.posCast_sub hb, C.posCast_sub (by omega), C.posCast_one, ← hd,
                Fin.cast_val_eq_self]
              abel
            rw [this, Fin.val_natCast, Nat.mod_eq_of_lt]
            have : d < C.tour.n + 1 := hd ▸ (p - p₀).2
            omega
          omega
        have := ih _ hlt _ hprev rfl
        have hstep' := hstep _ hprev this
        rwa [hq] at hstep'
  intro p hp
  exact key _ p hp rfl

end TraversedCircuit

end LoopMultigraph
end GraphPuzzles
