import GraphPuzzles.Matching.MatchingCovered
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# Bridge to Tutte's theorem

Tutte's theorem is available in Mathlib for simple graphs.  To apply it to the endpoint
multigraph `H − u − v`, this module builds the simple graph `H.cutGraph u v` on the same vertex
type: its edges are the pairs joined by an edge of `H` avoiding `u` and `v`, together with one extra
edge `uv`.  A perfect matching of the cut graph contains `uv` and otherwise consists of pairs
joined in `H − u − v`; choosing one joining edge per pair gives a perfect matching of `H − u − v`.

The odd components of `G − X` for a simple graph `G` are extracted as a family of vertex finsets
with the properties the counting arguments of the hub lemma use: odd cardinality, disjoint from
`X`, closed under adjacency outside `X`, and pairwise disjoint; their number has the parity of
`|V| − |X|`.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

section Joins

variable (H : LoopMultigraph V E)

/-- `e` joins `a` and `b`, in either orientation. -/
def Joins (e : E) (a b : V) : Prop :=
  (H.endAt e 0 = a ∧ H.endAt e 1 = b) ∨ (H.endAt e 0 = b ∧ H.endAt e 1 = a)

omit [DecidableEq V] [DecidableEq E] in
theorem joins_comm {e : E} {a b : V} : H.Joins e a b ↔ H.Joins e b a := or_comm

variable {H}

omit [DecidableEq V] [DecidableEq E] in
theorem Joins.endAt_mem {e : E} {a b : V} (h : H.Joins e a b) (k : Fin 2) :
    H.endAt e k = a ∨ H.endAt e k = b := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases fin2_cases k with rfl | rfl
    · exact Or.inl h0
    · exact Or.inr h1
  · rcases fin2_cases k with rfl | rfl
    · exact Or.inr h0
    · exact Or.inl h1

omit [DecidableEq V] [DecidableEq E] in
theorem Joins.exists_end {e : E} {a b : V} (h : H.Joins e a b) : ∃ k, H.endAt e k = a := by
  rcases h with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

omit [DecidableEq V] [DecidableEq E] in
/-- The end index of `a` on an edge joining `a` to a different vertex `b` is unique. -/
theorem Joins.end_unique {e : E} {a b : V} (h : H.Joins e a b) (hab : a ≠ b) {k k' : Fin 2}
    (hk : H.endAt e k = a) (hk' : H.endAt e k' = a) : k = k' := by
  by_contra hne
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rcases fin2_cases k with rfl | rfl <;>
    rcases fin2_cases k' with rfl | rfl
  · exact hne rfl
  · exact hab (hk'.symm.trans h1)
  · exact hab (hk.symm.trans h1)
  · exact hne rfl
  · exact hne rfl
  · exact hab (hk.symm.trans h0)
  · exact hab (hk'.symm.trans h0)
  · exact hne rfl

variable (H)

omit [DecidableEq V] [DecidableEq E] in
private theorem choose_congr {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ x, p x)
    (hq : ∃ x, q x) : Classical.choose hp = Classical.choose hq := by
  subst hpq
  rfl

/-- A chosen edge joining `a` and `b`. -/
noncomputable def pick {a b : V} (h : ∃ e, H.Joins e a b) : E := Classical.choose h

omit [DecidableEq V] [DecidableEq E] in
theorem pick_spec {a b : V} (h : ∃ e, H.Joins e a b) : H.Joins (H.pick h) a b :=
  Classical.choose_spec h

omit [DecidableEq V] [DecidableEq E] in
/-- The chosen edge does not depend on the order of the two ends. -/
theorem pick_symm {a b : V} (h : ∃ e, H.Joins e a b) (h' : ∃ e, H.Joins e b a) :
    H.pick h = H.pick h' :=
  choose_congr (funext fun e ↦ propext (H.joins_comm (e := e) (a := a) (b := b))) h h'

end Joins

section CutGraph

variable (H : LoopMultigraph V E) (u v : V)

/-- The simple graph underlying `H − u − v`, with one extra edge `uv`.  Its perfect matchings
correspond to the perfect matchings of `H − u − v`. -/
def cutGraph (huv : u ≠ v) : SimpleGraph V where
  Adj a b := (a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ ∃ e, H.Joins e a b) ∨
    (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  symm := ⟨fun a b h ↦ by
    rcases h with ⟨hab, hau, hav, hbu, hbv, e, he⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hab.symm, hbu, hbv, hau, hav, e, H.joins_comm.mp he⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun a h ↦ by
    rcases h with ⟨hab, -⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact hab rfl
    · exact huv h
    · exact huv h.symm⟩

variable {H u v}

omit [DecidableEq V] [DecidableEq E] in
theorem cutGraph_adj {huv : u ≠ v} {a b : V} :
    (H.cutGraph u v huv).Adj a b ↔
      (a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ ∃ e, H.Joins e a b) ∨
        (a = u ∧ b = v) ∨ (a = v ∧ b = u) := Iff.rfl

omit [DecidableEq V] [DecidableEq E] in
/-- An edge of the cut graph at a vertex other than `u`, `v` is an edge of `H − u − v`. -/
theorem cutGraph_adj_of_ne {huv : u ≠ v} {a b : V} (hau : a ≠ u) (hav : a ≠ v)
    (h : (H.cutGraph u v huv).Adj a b) : a ≠ b ∧ b ≠ u ∧ b ≠ v ∧ ∃ e, H.Joins e a b := by
  rcases h with ⟨hab, -, -, hbu, hbv, he⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨hab, hbu, hbv, he⟩
  · exact absurd h hau
  · exact absurd h hav

omit [DecidableEq E] in
/-- A perfect matching of the cut graph yields a perfect matching of `H − u − v`. -/
theorem exists_isPerfectMatchingOn_of_cutGraph {huv : u ≠ v} {M : (H.cutGraph u v huv).Subgraph}
    (hM : M.IsPerfectMatching) :
    ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P := by
  classical
  have hmate : ∀ a, ∃ w, M.Adj a w ∧ ∀ y, M.Adj a y → y = w := fun a ↦
    (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM a)
  choose mate hmate using hmate
  have hadj : ∀ a, (H.cutGraph u v huv).Adj a (mate a) := fun a ↦ M.adj_sub (hmate a).1
  have hmate_mate : ∀ a, mate (mate a) = a := fun a ↦ ((hmate (mate a)).2 a (hmate a).1.symm).symm
  have hjoin : ∀ a, a ≠ u → a ≠ v → ∃ e, H.Joins e a (mate a) := fun a hau hav ↦
    (cutGraph_adj_of_ne hau hav (hadj a)).2.2.2
  have hne : ∀ a, a ≠ u → a ≠ v → a ≠ mate a := fun a hau hav ↦
    (cutGraph_adj_of_ne hau hav (hadj a)).1
  have hmate_ne : ∀ a, a ≠ u → a ≠ v → mate a ≠ u ∧ mate a ≠ v := fun a hau hav ↦
    ⟨(cutGraph_adj_of_ne hau hav (hadj a)).2.1, (cutGraph_adj_of_ne hau hav (hadj a)).2.2.1⟩
  let P : Finset E := Finset.univ.filter fun e ↦
    ∃ a, ∃ hau : a ≠ u, ∃ hav : a ≠ v, e = H.pick (hjoin a hau hav)
  have hmemP : ∀ e, e ∈ P ↔ ∃ a, ∃ hau : a ≠ u, ∃ hav : a ≠ v, e = H.pick (hjoin a hau hav) := by
    intro e
    simp [P]
  refine ⟨P, ?_, ?_⟩
  · intro e he k
    obtain ⟨a, hau, hav, rfl⟩ := (hmemP e).mp he
    have hk := (H.pick_spec (hjoin a hau hav)).endAt_mem k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rcases hk with hk | hk
    · rw [hk]
      exact ⟨hav, hau⟩
    · rw [hk]
      exact ⟨(hmate_ne a hau hav).2, (hmate_ne a hau hav).1⟩
  · intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
    obtain ⟨hwv, hwu⟩ := hw
    obtain ⟨kw, hkw⟩ := (H.pick_spec (hjoin w hwu hwv)).exists_end
    unfold degreeIn
    rw [Finset.card_eq_one]
    refine ⟨(H.pick (hjoin w hwu hwv), kw), ?_⟩
    ext ⟨e, k⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hk⟩
      obtain ⟨a, hau, hav, rfl⟩ := (hmemP e).mp he
      have hpa := H.pick_spec (hjoin a hau hav)
      rcases hpa.endAt_mem k with hka | hka
      · -- the end is `a`, so `a = w`
        have haw : a = w := hka.symm.trans hk
        subst haw
        exact ⟨rfl, hpa.end_unique (hne a hau hav) hk hkw⟩
      · -- the end is `mate a`, so `mate a = w` and `mate w = a`
        have hmw : mate a = w := hka.symm.trans hk
        have hwa : mate w = a := by rw [← hmw, hmate_mate]
        have heq : H.pick (hjoin a hau hav) = H.pick (hjoin w hwu hwv) := by
          have h1 : ∃ e, H.Joins e a w := hmw ▸ hjoin a hau hav
          have h2 : ∃ e, H.Joins e w a := hwa ▸ hjoin w hwu hwv
          calc H.pick (hjoin a hau hav) = H.pick h1 := by
                apply choose_congr
                funext e
                rw [hmw]
            _ = H.pick h2 := H.pick_symm h1 h2
            _ = H.pick (hjoin w hwu hwv) := by
                apply choose_congr
                funext e
                rw [hwa]
        refine ⟨heq, ?_⟩
        rw [heq] at hk
        exact (H.pick_spec (hjoin w hwu hwv)).end_unique (hne w hwu hwv) hk hkw
    · rintro ⟨rfl, rfl⟩
      exact ⟨(hmemP _).mpr ⟨w, hwu, hwv, rfl⟩, hkw⟩

end CutGraph

end LoopMultigraph

namespace SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- Vertices reachable from a vertex of a set closed under adjacency stay in the set. -/
private theorem mem_of_walk {G : SimpleGraph W} {T : Set W}
    (hT : ∀ x ∈ T, ∀ y, G.Adj x y → y ∈ T) {a c : W} (p : G.Walk a c) (ha : a ∈ T) : c ∈ T := by
  induction p with
  | nil => exact ha
  | cons h _ ih => exact ih (hT _ ha _ h)

/-- The components of `G − X` as a family of vertex finsets: a partition of the complement of `X`
into nonempty sets closed under adjacency outside `X`, each minimal with that property, with as
many odd members as there are odd components. -/
theorem exists_components_finsets (G : SimpleGraph W) (X : Finset W) :
    ∃ Ps : Finset (Finset W),
      (Ps.filter fun Q ↦ Odd Q.card).card =
        ((⊤ : G.Subgraph).deleteVerts (X : Set W)).coe.oddComponents.ncard ∧
      (∀ Q ∈ Ps, Q.Nonempty) ∧
      (∀ Q ∈ Ps, ∀ w ∈ Q, w ∉ X) ∧
      (∀ Q ∈ Ps, ∀ w ∈ Q, ∀ w', w' ∉ X → G.Adj w w' → w' ∈ Q) ∧
      (∀ Q ∈ Ps, ∀ Q' ∈ Ps, Q ≠ Q' → Disjoint Q Q') ∧
      (∀ w, w ∉ X → ∃ Q ∈ Ps, w ∈ Q) ∧
      (∀ Q ∈ Ps, ∀ w ∈ Q, ∀ T : Finset W,
        (∀ x ∈ T, ∀ y, y ∉ X → G.Adj x y → y ∈ T) → w ∈ T → Q ⊆ T) := by
  classical
  let D := (⊤ : G.Subgraph).deleteVerts (X : Set W)
  have hmemV : ∀ w, w ∈ D.verts ↔ w ∉ X := by
    intro w
    simp [D]
  have hDadj : ∀ (a b : D.verts), D.coe.Adj a b ↔ G.Adj a.1 b.1 := by
    intro a b
    change D.Adj a.1 b.1 ↔ _
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    constructor
    · exact fun h ↦ h.2.2.2.2
    · intro h
      exact ⟨Set.mem_univ _, ((hmemV _).mp a.2), Set.mem_univ _, ((hmemV _).mp b.2), h⟩
  let toF : D.coe.ConnectedComponent → Finset W := fun c ↦
    Finset.univ.filter fun w ↦ ∃ h : w ∈ D.verts, D.coe.connectedComponentMk ⟨w, h⟩ = c
  have hmem : ∀ c w, w ∈ toF c ↔ ∃ h : w ∈ D.verts, D.coe.connectedComponentMk ⟨w, h⟩ = c := by
    intro c w
    simp [toF]
  have hcoe : ∀ c, (toF c : Set W) = Subtype.val '' c.supp := by
    intro c
    ext w
    simp only [Finset.mem_coe, hmem, Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨h, hc⟩
      exact ⟨⟨w, h⟩, hc, rfl⟩
    · rintro ⟨⟨w', h⟩, hc, rfl⟩
      exact ⟨h, hc⟩
  have hcard : ∀ c, (toF c).card = c.supp.ncard := by
    intro c
    rw [← Set.ncard_coe_finset, hcoe, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hinj : ∀ c c', toF c = toF c' → c = c' := by
    intro c c' h
    obtain ⟨⟨w, hw⟩, hc⟩ := c.nonempty_supp
    have h1 : w ∈ toF c := (hmem c w).mpr ⟨hw, hc⟩
    rw [h] at h1
    obtain ⟨hw', hc'⟩ := (hmem c' w).mp h1
    rw [← hc', ← hc]
  refine ⟨(Set.toFinite (Set.univ : Set D.coe.ConnectedComponent)).toFinset.image toF,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : ((Set.toFinite (Set.univ : Set D.coe.ConnectedComponent)).toFinset.image toF).filter
        (fun Q ↦ Odd Q.card) = (Set.toFinite D.coe.oddComponents).toFinset.image toF := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨c, rfl⟩, hodd⟩
        refine ⟨c, ?_, rfl⟩
        rw [hcard] at hodd
        exact hodd
      · rintro ⟨c, hc, rfl⟩
        refine ⟨⟨c, rfl⟩, ?_⟩
        rw [hcard]
        exact hc
    rw [heq, Finset.card_image_of_injOn (fun c _ c' _ h ↦ hinj c c' h),
      Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  · intro Q hQ
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨⟨w, hw⟩, hc⟩ := c.nonempty_supp
    exact ⟨w, (hmem c w).mpr ⟨hw, hc⟩⟩
  · intro Q hQ w hw
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨h, -⟩ := (hmem c w).mp hw
    exact (hmemV w).mp h
  · intro Q hQ w hw w' hw' hadj
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨h, hc⟩ := (hmem c w).mp hw
    have h' : w' ∈ D.verts := (hmemV w').mpr hw'
    refine (hmem c w').mpr ⟨h', ?_⟩
    rw [← hc]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ((hDadj ⟨w', h'⟩ ⟨w, h⟩).mpr hadj.symm)
  · intro Q hQ Q' hQ' hne
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hQ'
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨h, hc⟩ := (hmem c w).mp hw
    obtain ⟨h', hc'⟩ := (hmem c' w).mp hw'
    apply hne
    rw [← hc, ← hc']
  · intro w hw
    have h : w ∈ D.verts := (hmemV w).mpr hw
    refine ⟨toF (D.coe.connectedComponentMk ⟨w, h⟩), ?_, (hmem _ w).mpr ⟨h, rfl⟩⟩
    exact Finset.mem_image.mpr ⟨_, (Set.Finite.mem_toFinset _).mpr (Set.mem_univ _), rfl⟩
  · intro Q hQ w hw T hT hwT
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨h, hc⟩ := (hmem c w).mp hw
    intro x hx
    obtain ⟨hx', hcx⟩ := (hmem c x).mp hx
    have hreach : D.coe.Reachable ⟨w, h⟩ ⟨x, hx'⟩ :=
      SimpleGraph.ConnectedComponent.exact (hc.trans hcx.symm)
    obtain ⟨p⟩ := hreach
    have key := mem_of_walk (G := D.coe) (T := {a : D.verts | a.1 ∈ T}) ?_ p hwT
    · exact key
    · intro a ha b hab
      exact hT a.1 ha b.1 ((hmemV b.1).mp b.2) ((hDadj a b).mp hab)

end SimpleGraph
end GraphPuzzles
