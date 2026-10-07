import GraphPuzzles.FinGraph.FinGraphKempe

/-!
# Colouring types of four boundary values

A colouring of a `4`-pole restricts to four boundary colours.  By the parity lemma each colour
occurs an even number of times, so the boundary values are all equal or split into two pairs of
equal colours.  The three possible pairings are indexed by `Fin 3`, and the *type* of a boundary
vector is `none` (all equal) or `some m` (the pairing `m` with two distinct colours).  This file
contains the finite combinatorics of types: the type sets of the two sides of a snark cut are
disjoint and each has at least two elements, which forces one side to be isochromatic and the
other heterochromatic for the same pairing.
-/

namespace GraphPuzzles
namespace FinGraph

set_option maxRecDepth 100000

/-- The partner of an index under the pairing `m`: `01|23`, `02|13`, `03|12`. -/
def pairing : Fin 3 → Fin 4 → Fin 4
  | 0 => ![1, 0, 3, 2]
  | 1 => ![2, 3, 0, 1]
  | 2 => ![3, 2, 1, 0]

/-- Boundary vectors: four nonzero colours. -/
def Nonzero4 (t : Fin 4 → Color) : Prop := ∀ i, t i ≠ 0

/-- Valid boundary vectors: equal along some pairing (this includes the constant vectors). -/
def Valid (t : Fin 4 → Color) : Prop := ∃ m, ∀ i, t i = t (pairing m i)

instance (t : Fin 4 → Color) : Decidable (Nonzero4 t) := inferInstanceAs (Decidable (∀ i, t i ≠ 0))

instance (t : Fin 4 → Color) : Decidable (Valid t) :=
  inferInstanceAs (Decidable (∃ m, ∀ i, t i = t (pairing m i)))

/-- The type of a boundary vector. -/
def ptype (t : Fin 4 → Color) : Option (Fin 3) :=
  if t 1 = t 0 ∧ t 2 = t 0 ∧ t 3 = t 0 then none
  else if t 0 = t 1 then some 0 else if t 0 = t 2 then some 1 else some 2

/-- The types compatible with the pairing `m` being isochromatic. -/
def isoTypes (m : Fin 3) : Finset (Option (Fin 3)) := {none, some m}

/-- The types compatible with the pairing `m` being heterochromatic. -/
def hetTypes (m : Fin 3) : Finset (Option (Fin 3)) :=
  Finset.univ.filter fun τ ↦ ∃ m', τ = some m' ∧ m' ≠ m

theorem pairing_involutive (m : Fin 3) (i : Fin 4) : pairing m (pairing m i) = i := by
  revert m i
  decide

theorem pairing_ne (m : Fin 3) (i : Fin 4) : pairing m i ≠ i := by
  revert m i
  decide

/-- Even colour counts force a valid vector. -/
theorem valid_of_even_counts (t : Fin 4 → Color) (h0 : Nonzero4 t)
    (heven : ∀ κ : Color, κ ≠ 0 → Even (Finset.univ.filter fun i ↦ t i = κ).card) : Valid t := by
  revert t
  decide

/-- For a valid vector, being equal along the pairing `m` is the same as having type in
`isoTypes m`. -/
theorem valid_iso_iff (t : Fin 4 → Color) (hv : Valid t) (m : Fin 3) :
    (∀ i, t i = t (pairing m i)) ↔ ptype t ∈ isoTypes m := by
  revert t m
  decide

/-- For a valid vector, being distinct along the pairing `m` is the same as having type in
`hetTypes m`. -/
theorem valid_het_iff (t : Fin 4 → Color) (hv : Valid t) (m : Fin 3) :
    (∀ i, t i ≠ t (pairing m i)) ↔ ptype t ∈ hetTypes m := by
  revert t m
  decide

theorem ptype_none_iff (t : Fin 4 → Color) : ptype t = none ↔ ∀ i, t i = t 0 := by
  revert t
  decide

theorem ptype_some_iff (t : Fin 4 → Color) (hv : Valid t) (m : Fin 3) :
    ptype t = some m ↔ (∀ i, t i = t (pairing m i)) ∧ ¬ ∀ i, t i = t 0 := by
  revert t m
  decide

/-- The conclusion of the type-splitting lemma. -/
def SplitOK (TM TN : Finset (Option (Fin 3))) : Prop :=
  ∃ m, ((∀ τ ∈ TM, τ ∈ isoTypes m) ∧ (∀ τ ∈ TN, τ ∈ hetTypes m)) ∨
    ((∀ τ ∈ TN, τ ∈ isoTypes m) ∧ (∀ τ ∈ TM, τ ∈ hetTypes m))

/-- The hypotheses of the type-splitting lemma. -/
def SplitHyp (TM TN : Finset (Option (Fin 3))) : Prop :=
  (∀ τ ∈ TM, τ ∉ TN) ∧ (∃ τ, τ ∈ TM) ∧ (∃ τ, τ ∈ TN) ∧ (∀ τ ∈ TM, ∃ τ' ∈ TM, τ' ≠ τ) ∧
    (∀ τ ∈ TN, ∃ τ' ∈ TN, τ' ≠ τ)

instance (TM TN : Finset (Option (Fin 3))) : Decidable (SplitOK TM TN) := by
  unfold SplitOK
  infer_instance

instance (TM TN : Finset (Option (Fin 3))) : Decidable (SplitHyp TM TN) := by
  unfold SplitHyp
  infer_instance

/-- **The type combinatorics of a snark cut.**  Two disjoint nonempty type sets, each containing
at least two types, are `{none, some m}` and the two remaining types, for a pairing `m`. -/
theorem types_split : ∀ TM TN : Finset (Option (Fin 3)), SplitHyp TM TN → SplitOK TM TN := by
  decide

end FinGraph
end GraphPuzzles
