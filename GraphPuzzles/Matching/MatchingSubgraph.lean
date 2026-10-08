import GraphPuzzles.Matching.MatchingHub

/-! Perfect matchings and component families in spanning edge restrictions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The spanning subgraph retaining the labelled edges in `S`. -/
def restrictEdges (H : LoopMultigraph V E) (S : Finset E) : LoopMultigraph V S :=
  ⟨fun e k ↦ H.endAt e.1 k⟩

/-- The simple graph obtained by forgetting edge labels, loops and multiplicities. -/
def underlying (H : LoopMultigraph V E) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e, H.Joins e a b
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.imp fun _ he ↦ H.joins_comm.mp he⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

omit [DecidableEq V] [DecidableEq E] in
theorem pick_congr {a b a' b' : V} (h : ∃ e, H.Joins e a b)
    (h' : ∃ e, H.Joins e a' b') (ha : a = a') (hb : b = b') : H.pick h = H.pick h' := by
  subst a'
  subst b'
  rfl

/-- A simple-graph perfect matching lifts by choosing one labelled edge for each pair. -/
theorem exists_perfectMatching_of_underlying {N : H.underlying.Subgraph}
    (hN : N.IsPerfectMatching) : ∃ M, H.IsPerfectMatching M := by
  classical
  have hex : ∀ a, ∃ b, N.Adj a b ∧ ∀ c, N.Adj a c → c = b :=
    SimpleGraph.Subgraph.isPerfectMatching_iff.mp hN
  choose mate hmate using hex
  have hinv : ∀ a, mate (mate a) = a :=
    fun a ↦ ((hmate (mate a)).2 a (hmate a).1.symm).symm
  have hjoin : ∀ a, ∃ e, H.Joins e a (mate a) := fun a ↦ (N.adj_sub (hmate a).1).2
  have hne : ∀ a, a ≠ mate a := fun a ↦ (N.adj_sub (hmate a).1).1
  let edge (a : V) := H.pick (hjoin a)
  have hedge (a : V) : H.Joins (edge a) a (mate a) := H.pick_spec (hjoin a)
  have hsame (a : V) : edge (mate a) = edge a := by
    have hrev : ∃ e, H.Joins e (mate a) a :=
      (hjoin a).imp fun _ he ↦ H.joins_comm.mp he
    exact (pick_congr (hjoin (mate a)) hrev rfl (hinv a)).trans (H.pick_symm (hjoin a) hrev).symm
  let M := Finset.univ.image edge
  refine ⟨M, fun v ↦ ?_⟩
  obtain ⟨k, hk⟩ := (hedge v).exists_end
  unfold degreeIn
  rw [Finset.card_eq_one]
  refine ⟨(edge v, k), ?_⟩
  ext ⟨e, i⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨he, hi⟩
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    have hea : edge a = edge v := by
      rcases (hedge a).endAt_mem i with h | h
      · rw [h.symm.trans hi]
      · rw [← hsame a, h.symm.trans hi]
    refine ⟨hea, ?_⟩
    rw [hea] at hi
    exact (hedge v).end_unique (hne v) hi hk
  · rintro ⟨rfl, rfl⟩
    exact ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, hk⟩

omit [DecidableEq E] in
/-- Components of the underlying simple graph give endpoint-graph component families. -/
theorem exists_componentFamily (H : LoopMultigraph V E) (Z : Finset V) :
    ∃ F : H.ComponentFamily Z, F.odd.card =
      ((⊤ : H.underlying.Subgraph).deleteVerts (Z : Set V)).coe.oddComponents.ncard := by
  obtain ⟨Ps, hcard, hne, havoid, hclosed, hdisj, hcover, _⟩ :=
    GraphPuzzles.SimpleGraph.exists_components_finsets H.underlying Z
  refine ⟨⟨Ps, hne, havoid, ?_, hdisj, hcover⟩, hcard⟩
  intro Q hQ e k hk hn
  by_cases he : H.endAt e k = H.endAt e (Fin.rev k)
  · exact he ▸ hk
  · apply hclosed Q hQ _ hk _ hn
    refine ⟨he, e, ?_⟩
    fin_cases k
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Tutte's theorem expressed entirely through endpoint-graph component families. -/
theorem exists_perfectMatching_of_component_bound
    (h : ∀ Z : Finset V, ∀ F : H.ComponentFamily Z, F.odd.card ≤ Z.card) :
    ∃ M, H.IsPerfectMatching M := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : H.underlying.Subgraph, N.IsPerfectMatching := by
    apply SimpleGraph.tutte.mpr
    intro Z hZ
    obtain ⟨F, hF⟩ := H.exists_componentFamily Z.toFinset
    have hb := h Z.toFinset F
    rw [hF, Set.coe_toFinset, Set.toFinset_card] at hb
    change Z.ncard < _ at hZ
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hZ
    exact (not_lt_of_ge hb) hZ
  exact exists_perfectMatching_of_underlying hN

/-- Mapping an edge-restricted matching back preserves all vertex degrees. -/
theorem restrictEdges_degreeIn (S : Finset E) (M : Finset S) (v : V) :
    H.degreeIn (M.image Subtype.val) v = (H.restrictEdges S).degreeIn M v := by
  unfold degreeIn
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product]
  rw [Finset.sum_image]
  · rfl
  · intro e _ f _ h
    exact Subtype.ext h

theorem IsPerfectMatching.of_restrictEdges {S : Finset E} {M : Finset S}
    (hM : (H.restrictEdges S).IsPerfectMatching M) :
    H.IsPerfectMatching (M.image Subtype.val) := by
  intro v
  rw [restrictEdges_degreeIn, hM v]

end GraphPuzzles.LoopMultigraph
