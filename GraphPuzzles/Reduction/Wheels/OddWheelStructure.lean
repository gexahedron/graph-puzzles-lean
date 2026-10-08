import GraphPuzzles.Reduction.Wheels.OddWheelRemovability
import GraphPuzzles.Matching.Bipartite.FactorCriticalContraction
import GraphPuzzles.Bricks.BrickCharacterization

/-! Bicriticality and the brick property of labelled odd wheels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A spanning odd rim with a universal hub. Additional edges are allowed. -/
structure OddWheelFrame (H : LoopMultigraph V E) (v : V) where
  root : V
  root_ne : root ≠ v
  rim : H.OddEar {root}
  labels : List E
  walk : H.EdgeChain rim.start labels (rim.interior ++ [rim.finish])
  vertices_eq : rim.vertices = Finset.univ.erase v
  length_three : 3 ≤ labels.length
  spokes : ∀ w, w ≠ v → ∃ e, H.Joins e v w
  loopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1

/-- Forget the exclusion of additional rim edges. -/
def OddWheel.toFrame {v : V} (W : H.OddWheel v) : H.OddWheelFrame v where
  root := W.root
  root_ne := W.root_ne
  rim := W.rim
  labels := W.labels
  walk := W.walk
  vertices_eq := W.vertices_eq
  length_three := W.length_three
  spokes := W.spokes
  loopless := W.loopless

namespace OddWheelFrame

variable {v : V} (W : H.OddWheelFrame v)

include W

/-- Re-root the labelled rim at any rim vertex. -/
theorem exists_rooted_rim (w : V) (hw : w ≠ v) :
    ∃ (A : H.OddEar {w}) (es : List E),
      H.EdgeChain A.start es (A.interior ++ [A.finish]) ∧
      A.vertices = Finset.univ.erase v ∧ es.toFinset = W.labels.toFinset ∧
      es.length = W.labels.length := by
  by_cases hwr : w = W.root
  · subst w
    exact ⟨W.rim, W.labels, W.walk, W.vertices_eq, rfl, rfl⟩
  let L : H.LastOutsideOddEar ∅ W.root 1 (Finset.univ.erase v) W.labels.toFinset := {
    positive := by decide
    oldVertices := {W.root}
    oldEdges := ∅
    oldIndex := 0
    ear := W.rim
    labels := W.labels
    earlier := .start
    walk := W.walk
    fresh := by simp
    outside := by
      intro hh
      have hl : W.labels = [] := by simpa using Finset.subset_empty.mp hh
      have hlen := W.length_three
      simp [hl] at hlen
    vertices_eq := W.vertices_eq
    edges_subset := by simp
    tail_mem := by simp }
  have hwI : w ∈ L.ear.interior := by
    have hh : w ∈ W.rim.vertices := W.vertices_eq.symm ▸ (by simp [hw])
    simpa only [OddEar.vertices, Finset.mem_union, Finset.mem_singleton, hwr,
      false_or, List.mem_toFinset] using hh
  obtain ⟨L', hlabels⟩ := L.rotate_first hwI
  let A := L'.ear.rebase (L'.first_ear rfl).1
  have hwalk : H.EdgeChain A.start L'.labels (A.interior ++ [A.finish]) := L'.walk
  refine ⟨A, L'.labels, hwalk, ?_, hlabels, ?_⟩
  · exact (L'.ear.rebase_vertices (L'.first_ear rfl).1).trans L'.vertices_eq
  · have hh := congrArg Finset.card hlabels
    rw [List.toFinset_card_of_nodup (L'.ear.labels_nodup L'.walk),
      List.toFinset_card_of_nodup (W.rim.labels_nodup W.walk)] at hh
    exact hh

theorem factorCritical_rim : H.IsFactorCritical (Finset.univ.erase v) :=
  W.vertices_eq ▸ W.rim.isFactorCritical
    (HasOddEarConstruction.singleton W.root).isFactorCritical

omit [DecidableEq E] in
theorem rim_card_eq_length : (Finset.univ.erase v).card = W.labels.length := by
  have hr : W.root ∉ W.rim.interior := fun h ↦
    W.rim.avoids W.root h (Finset.mem_singleton_self _)
  have hrf : W.root ∉ W.rim.interior.toFinset := by simpa only [List.mem_toFinset] using hr
  have hh := congrArg Finset.card W.vertices_eq
  simp only [OddEar.vertices, Finset.singleton_union] at hh
  rw [Finset.card_insert_of_notMem hrf, List.toFinset_card_of_nodup W.rim.nodup] at hh
  have hl := W.walk.length
  simp only [List.length_append, List.length_singleton] at hl
  omega

/-- Replacing the root of the rim by the hub gives a factor-critical
graph after deletion of any rim vertex. -/
theorem factorCritical_erase (u : V) : H.IsFactorCritical (Finset.univ.erase u) := by
  by_cases huv : u = v
  · subst u
    exact W.factorCritical_rim
  obtain ⟨A, es, hw, hV, _, hlen⟩ := W.exists_rooted_rim u huv
  have hmem (z : V) (hz : z ∈ A.interior) : z ≠ v := by
    have hh : z ∈ A.vertices := Finset.mem_union_right _ (List.mem_toFinset.mpr hz)
    exact (Finset.mem_erase.mp (hV ▸ hh)).1
  have hne : A.interior ≠ [] := by
    intro hh
    have hl := hw.length
    have h3 := W.length_three
    simp only [hh, List.nil_append, List.length_singleton] at hl
    omega
  have hc := A.chain.tail.left_of_append
  have htail : (A.interior ++ [v]).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
    apply hc.append (.singleton v)
    intro a ha b hb
    have hb' : b = v := (show v = b from by simpa using hb).symm
    subst b
    obtain ⟨e, he⟩ := W.spokes a (hmem a (List.mem_of_mem_getLast? ha))
    exact ⟨e, H.joins_comm.mp he⟩
  have hchain : (v :: A.interior ++ [v]).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
    apply htail.cons
    intro z hz
    have hzI : z ∈ A.interior := by
      cases hi : A.interior with
      | nil => exact (hne hi).elim
      | cons a l =>
        have hz' : z = a := (show a = z from by simpa only [hi, List.cons_append, List.head?_cons,
          Option.mem_some_iff] using hz).symm
        simp [hz']
    exact W.spokes z (hmem z hzI)
  let B : H.OddEar {v} := {
    start := v
    finish := v
    interior := A.interior
    start_mem := Finset.mem_singleton_self _
    finish_mem := Finset.mem_singleton_self _
    nodup := A.nodup
    avoids := fun z hz ↦ by simpa using hmem z hz
    even := A.even
    chain := hchain }
  have hBV : B.vertices = Finset.univ.erase u := by
    ext z
    have huI : u ∉ A.interior := fun hh ↦ A.avoids u hh (Finset.mem_singleton_self _)
    have hzi : z ∈ A.interior ↔ z ≠ u ∧ z ≠ v := by
      have hzV := Finset.ext_iff.mp hV z
      simp only [OddEar.vertices, Finset.mem_union, Finset.mem_singleton,
        List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true] at hzV
      constructor
      · intro hz
        exact ⟨fun hh ↦ huI (hh ▸ hz), hmem z hz⟩
      · rintro ⟨hzu, hzv⟩
        exact (hzV.mpr hzv).resolve_left hzu
    simp only [OddEar.vertices, B, Finset.mem_union, Finset.mem_singleton,
      List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true, hzi]
    constructor
    · rintro (rfl | hz)
      · exact Ne.symm huv
      · exact hz.1
    · intro hzu
      by_cases hzv : z = v
      · exact Or.inl hzv
      · exact Or.inr ⟨hzu, hzv⟩
  exact hBV ▸ B.isFactorCritical (HasOddEarConstruction.singleton v).isFactorCritical

theorem isBicritical : H.IsBicritical := by
  intro a b hab
  exact W.factorCritical_erase a b (by simp [Ne.symm hab])

omit [DecidableEq E] in
theorem isConnected : H.IsConnected := by
  intro c hc a b
  have hconst (z : V) : c z = c v := by
    by_cases hz : z = v
    · exact congrArg c hz
    obtain ⟨e, he⟩ := W.spokes z hz
    have hh := hc e
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hh.symm
    · simpa only [h0, h1] using hh
  exact (hconst a).trans (hconst b).symm

theorem isMatchingCovered : H.IsMatchingCovered :=
  W.isBicritical.isMatchingCovered W.isConnected W.loopless

theorem notBipartite : ¬ H.IsBipartite := by
  rintro ⟨c, hc⟩
  have hcard := W.factorCritical_rim.card_le_one_of_bipartiteOn ⟨c, fun e _ _ ↦ hc e⟩
  rw [W.rim_card_eq_length] at hcard
  have h3 := W.length_three
  omega

omit W [DecidableEq V] [DecidableEq E] in
private theorem chain_constant (l : List V)
    (hl : l.IsChain (fun a b ↦ ∃ e, H.Joins e a b)) (c : V → Bool)
    (hc : ∀ a ∈ l, ∀ b ∈ l, (∃ e, H.Joins e a b) → c a = c b) :
    ∀ a ∈ l, ∀ b ∈ l, c a = c b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ht := ih hl.tail (fun a ha b hb he ↦ hc a (by simp [ha]) b (by simp [hb]) he)
    have hx (a : V) (ha : a ∈ x :: l) : c a = c x := by
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · cases l with
        | nil => simp at ha
        | cons y l =>
          exact (ht a ha y (by simp)).trans
            (hc x (by simp) y (by simp) hl.rel_head).symm
    exact fun a ha b hb ↦ (hx a ha).trans (hx b hb).symm

/-- Removing one rim vertex leaves its remaining rim path connected. -/
theorem connectedOn_rim_erase (u : V) (hu : u ≠ v) :
    H.IsConnectedOn ((Finset.univ.erase v).erase u) := by
  obtain ⟨A, _, _, hV, _, _⟩ := W.exists_rooted_rim u hu
  have hmem (z : V) : z ∈ A.interior ↔ z ∈ (Finset.univ.erase v).erase u := by
    have hh := Finset.ext_iff.mp hV z
    have hn := A.avoids z
    simp only [OddEar.vertices, Finset.mem_union, Finset.mem_singleton,
      List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true] at hh ⊢
    constructor
    · intro hz
      exact ⟨fun heq ↦ hn hz (Finset.mem_singleton.mpr heq), hh.mp (Or.inr hz)⟩
    · rintro ⟨hzu, hzv⟩
      exact (hh.mpr hzv).resolve_left hzu
  intro c hc a ha b hb
  apply chain_constant A.interior A.chain.tail.left_of_append c ?_ a
    ((hmem a).mpr ha) b ((hmem b).mpr hb)
  intro x hx y hy he
  obtain ⟨e, he⟩ := he
  have hx' := (hmem x).mp hx
  have hy' := (hmem y).mp hy
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simpa only [h0, h1] using hc e (h0.symm ▸ hx') (h1.symm ▸ hy')
  · simpa only [h0, h1] using (hc e (h0.symm ▸ hy') (h1.symm ▸ hx')).symm

theorem connectedAfterDeletingPairs : H.ConnectedAfterDeletingPairs := by
  intro a b hab c hc x hx y hy
  by_cases ha : a = v
  · subst a
    apply W.connectedOn_rim_erase b (Ne.symm hab) c ?_ x ?_ y ?_
    · intro e h0 h1
      exact hc e (by simpa [Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using h0)
        (by simpa [Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using h1)
    · simpa [Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using hx
    · simpa [Finset.mem_insert, Finset.mem_singleton, not_or, and_comm] using hy
  by_cases hb : b = v
  · subst b
    apply W.connectedOn_rim_erase a hab c ?_ x ?_ y ?_
    · intro e h0 h1
      exact hc e (by simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using h0)
        (by simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using h1)
    · simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
    · simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hy
  have hv : v ∉ ({a, b} : Finset V) := by simp [Ne.symm ha, Ne.symm hb]
  have hconst (z : V) (hz : z ∉ ({a, b} : Finset V)) : c z = c v := by
    by_cases hzv : z = v
    · exact congrArg c hzv
    obtain ⟨e, he⟩ := W.spokes z hzv
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using (hc e (h0.symm ▸ hv) (h1.symm ▸ hz)).symm
    · simpa only [h0, h1] using hc e (h0.symm ▸ hz) (h1.symm ▸ hv)
  exact (hconst x hx).trans (hconst y hy).symm

/-- Odd wheels remain bricks when arbitrary parallel spokes are allowed. -/
theorem isBrick : H.IsBrick :=
  W.isMatchingCovered.isBrick_of_bicritical W.notBipartite W.isBicritical
    W.connectedAfterDeletingPairs

end OddWheelFrame

namespace OddWheel

variable {v : V} (W : H.OddWheel v)

include W

theorem factorCritical_erase (u : V) : H.IsFactorCritical (Finset.univ.erase u) :=
  W.toFrame.factorCritical_erase u

theorem isBicritical : H.IsBicritical := W.toFrame.isBicritical

theorem isConnected : H.IsConnected := W.toFrame.isConnected

theorem isMatchingCovered : H.IsMatchingCovered := W.toFrame.isMatchingCovered

theorem notBipartite : ¬ H.IsBipartite := W.toFrame.notBipartite

theorem connectedOn_rim_erase (u : V) (hu : u ≠ v) :
    H.IsConnectedOn ((Finset.univ.erase v).erase u) := W.toFrame.connectedOn_rim_erase u hu

theorem connectedAfterDeletingPairs : H.ConnectedAfterDeletingPairs :=
  W.toFrame.connectedAfterDeletingPairs

theorem isBrick : H.IsBrick := W.toFrame.isBrick

end OddWheel

end GraphPuzzles.LoopMultigraph
