import GraphPuzzles.Reduction.Wheels.DegreeTwoContraction
import GraphPuzzles.Cuts.Shores.UniqueShoreNeighbors
import GraphPuzzles.Matching.FourVertexMatching

/-! The three-vertex tight shore obtained by deleting an un-paralleled spoke. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace OddWheel

variable {v : V} (W : H.OddWheel v)

/-- Display the two neighbors of a selected rim vertex and the remaining
even path around a rim of length at least five. -/
theorem exists_rim_neighbor_path (h5 : 5 ≤ W.labels.length) (u : V) (hu : u ≠ v) :
    ∃ a b l, (u :: a :: l ++ [b]).Nodup ∧
      (u :: a :: l ++ [b]).toFinset = Finset.univ.erase v ∧
      Even l.length ∧ 2 ≤ l.length ∧
      (∃ e, H.Joins e u a) ∧ (∃ e, H.Joins e b u) ∧
      (a :: l ++ [b]).IsChain (fun x y ↦ ∃ e, H.Joins e x y) := by
  obtain ⟨A, es, hw, hV, _, hlen⟩ := W.exists_rooted_rim u hu
  have hs : A.start = u := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = u := Finset.mem_singleton.mp A.finish_mem
  have hi4 : 4 ≤ A.interior.length := by
    have hh := hw.length
    simp only [List.length_append, List.length_singleton] at hh
    omega
  cases hi : A.interior with
  | nil => simp [hi] at hi4
  | cons a t =>
    rcases List.eq_nil_or_concat' t with rfl | ⟨l, b, rfl⟩
    · simp [hi] at hi4
    have hw' : H.EdgeChain u es (a :: (l ++ b :: [u])) := by
      simpa only [hs, ht, hi, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hw
    cases hw' with
    | @cons _ _ e es _ hea htail =>
      obtain ⟨fs, gs, _, hm, hg⟩ := htail.split l [u]
      cases hg with
      | @cons _ _ f fs _ hbu hn =>
        cases hn
        refine ⟨a, b, l, ?_, ?_, ?_, ?_, ⟨e, hea⟩, ⟨f, hbu⟩, hm.isChain⟩
        · apply List.nodup_cons.mpr
          refine ⟨fun hh ↦ A.avoids u (hi.symm ▸ hh) (Finset.mem_singleton_self _), ?_⟩
          change (a :: (l ++ [b])).Nodup
          exact hi ▸ A.nodup
        · simpa only [OddEar.vertices, hi, List.cons_append, List.toFinset_cons, Finset.singleton_union] using hV
        · have hh := A.even
          rw [Nat.even_iff] at hh ⊢
          simp only [hi, List.length_cons, List.length_append, List.length_nil] at hh
          omega
        · simp only [hi, List.length_cons, List.length_append, List.length_nil] at hi4
          omega

end OddWheel

omit [DecidableEq E] in
private theorem exists_contract_join {S : Finset V} {a b : V}
    (he : ∃ e, H.Joins e a b) (hm : a ∈ S ∨ b ∈ S) :
    ∃ f, (H.contract S).Joins f (contractVertex S a) (contractVertex S b) := by
  obtain ⟨e, he⟩ := he
  have hem : e ∈ H.meets S := by
    rcases hm with ha | hb
    · obtain ⟨k, hk⟩ := he.exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ ha⟩
    · obtain ⟨k, hk⟩ := (H.joins_comm.mp he).exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ hb⟩
  exact ⟨⟨e, hem⟩, he.contract hem⟩

omit [DecidableEq E] in
private theorem chain_contract_from_retained {S : Finset V} {a b : V} (l : List V)
    (hc : (a :: l ++ [b]).IsChain (fun x y ↦ ∃ e, H.Joins e x y))
    (ha : a ∈ S) (hl : ∀ x ∈ l, x ∈ S) :
    ((a :: l ++ [b]).map (contractVertex S)).IsChain
      (fun x y ↦ ∃ e, (H.contract S).Joins e x y) := by
  induction l generalizing a with
  | nil =>
    exact List.isChain_cons_cons.mpr
      ⟨exists_contract_join hc.rel_head (Or.inl ha), .singleton _⟩
  | cons c l ih =>
    exact List.isChain_cons_cons.mpr
      ⟨exists_contract_join hc.rel_head (Or.inl ha),
        ih hc.tail (hl c (by simp)) (fun x hx ↦ hl x (by simp [hx]))⟩

omit [DecidableEq E] in
private theorem chain_contract_between_ends {S : Finset V} {a b : V} {l : List V}
    (hc : (a :: l ++ [b]).IsChain (fun x y ↦ ∃ e, H.Joins e x y))
    (hne : l ≠ []) (hl : ∀ x ∈ l, x ∈ S) :
    ((a :: l ++ [b]).map (contractVertex S)).IsChain
      (fun x y ↦ ∃ e, (H.contract S).Joins e x y) := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons c l =>
    exact List.isChain_cons_cons.mpr
      ⟨exists_contract_join hc.rel_head (Or.inr (hl c (by simp))),
        chain_contract_from_retained l hc.tail (hl c (by simp))
          (fun x hx ↦ hl x (by simp [hx]))⟩

namespace OddWheel

variable {v : V} (W : H.OddWheel v)

include W

/-- Collapsing a rim vertex and its two neighbors after deleting its
spoke leaves a graph containing a spanning odd wheel, hence a brick. -/
theorem isBrick_bicontract_spoke_of_path {u a b : V} {l : List V} {e : E}
    (he : H.Joins e v u) (hnd : (u :: a :: l ++ [b]).Nodup)
    (hcover : (u :: a :: l ++ [b]).toFinset = Finset.univ.erase v)
    (heven : Even l.length) (h2 : 2 ≤ l.length)
    (hc : (a :: l ++ [b]).IsChain (fun x y ↦ ∃ f, H.Joins f x y)) :
    ((H.deleteEdge e).contract (Finset.univ \ {u, a, b})).IsBrick := by
  let T : Finset V := {u, a, b}
  let S := Finset.univ \ T
  let J := H.deleteEdge e
  let K := J.contract S
  let q := contractVertex S
  have hnu := (List.nodup_cons.mp hnd).1
  have hpathnd := (List.nodup_cons.mp hnd).2
  have hna := (List.nodup_cons.mp hpathnd).1
  have htailnd := (List.nodup_cons.mp hpathnd).2
  have hln := (List.nodup_append.mp htailnd).1
  have hbn : b ∉ l := by
    intro hb
    exact (List.nodup_append.mp htailnd).2.2 b hb b (by simp) rfl
  have hS (z : V) (hz : z ∈ l) : z ∈ S := by
    have hzu : z ≠ u := fun h ↦ hnu (by simp [← h, hz])
    have hza : z ≠ a := fun h ↦ hna (by simp [← h, hz])
    have hzb : z ≠ b := fun h ↦ hbn (h ▸ hz)
    simp [S, T, hzu, hza, hzb]
  have hnotv (z : V) (hz : z ∈ u :: a :: l ++ [b]) : z ≠ v := by
    have hh := hcover ▸ List.mem_toFinset.mpr hz
    exact (Finset.mem_erase.mp hh).1
  have huv := hnotv u (by simp)
  have hav := hnotv a (by simp)
  have hbv := hnotv b (by simp)
  have hvS : v ∈ S := by simp [S, T, Ne.symm huv, Ne.symm hav, Ne.symm hbv]
  let pole : Option S := some ⟨v, hvS⟩
  have hqv : q v = pole := contractVertex_some S ⟨v, hvS⟩
  have hqa : q a = none := by simp [q, contractVertex, S, T]
  have hqb : q b = none := by simp [q, contractVertex, S, T]
  have hcJ : (a :: l ++ [b]).IsChain (fun x y ↦ ∃ f, J.Joins f x y) := by
    apply hc.imp_of_mem_imp
    intro x y hx hy hxy
    obtain ⟨f, hf⟩ := hxy
    have hfe : f ≠ e := (he.ne_of_left_not_end hf
      (Ne.symm (hnotv x (List.mem_cons_of_mem _ hx)))
      (Ne.symm (hnotv y (List.mem_cons_of_mem _ hy)))).symm
    exact ⟨⟨f, by simp [hfe]⟩, hf⟩
  have hcK := chain_contract_between_ends (H := J) (S := S) hcJ
    (by intro hh; simp [hh] at h2) hS
  let B : K.OddEar {none} := {
    start := none
    finish := none
    interior := l.map q
    start_mem := Finset.mem_singleton_self _
    finish_mem := Finset.mem_singleton_self _
    nodup := hln.map_on (by
      intro x hx y hy heq
      simpa only [q, contractVertex, dif_pos (hS x hx), dif_pos (hS y hy),
        Option.some.injEq, Subtype.mk.injEq] using heq)
    avoids := by
      intro z hz hn
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have hn' := Finset.mem_singleton.mp hn
      simp only [q, contractVertex, dif_pos (hS x hx)] at hn'
      contradiction
    even := by simpa only [List.length_map] using heven
    chain := by
      change ((a :: l ++ [b]).map q).IsChain _ at hcK
      simpa only [List.map_cons, List.map_append, List.map_nil, hqa, hqb] using hcK }
  have hmapmem (z : S) : some z ∈ l.map q ↔ z.1 ∈ l := by
    constructor
    · intro hh
      obtain ⟨x, hx, heq⟩ := List.mem_map.mp hh
      have heq' : x = z.1 := by
        have hxs := hS x hx
        have hh : (⟨x, hxs⟩ : S) = z := by
          simpa only [q, contractVertex, dif_pos hxs, Option.some.injEq] using heq
        exact congrArg Subtype.val hh
      exact heq' ▸ hx
    · intro hz
      exact List.mem_map.mpr ⟨z.1, hz, contractVertex_some S z⟩
  have hBV : B.vertices = Finset.univ.erase pole := by
    ext z
    cases z with
    | none => simp [OddEar.vertices, B, pole]
    | some z =>
      have hzS : z.1 ≠ u ∧ z.1 ≠ a ∧ z.1 ≠ b := by
        simpa only [S, T, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, not_or] using z.2
      have hzL : z.1 ∈ l ↔ z.1 ≠ v := by
        have hh := Finset.ext_iff.mp hcover z.1
        simpa only [List.mem_toFinset, List.mem_cons, List.mem_append,
          List.mem_singleton, List.not_mem_nil, hzS.1, hzS.2.1, hzS.2.2, false_or, or_false,
          Finset.mem_erase, Finset.mem_univ, and_true] using hh
      have hneq : (some z : Option S) ≠ pole ↔ z.1 ≠ v := by
        constructor
        · intro hn hh
          exact hn (congrArg some (Subtype.ext hh))
        · intro hn hh
          exact hn (congrArg Subtype.val (Option.some.inj hh))
      simpa only [OddEar.vertices, B, Finset.mem_union, Finset.mem_singleton,
        Option.some_ne_none, false_or, List.mem_toFinset, hmapmem, Finset.mem_erase,
        Finset.mem_univ, and_true, hneq] using hzL
  have hspoke (w : V) (hwv : w ≠ v) (hwu : w ≠ u) : ∃ f, K.Joins f pole (q w) := by
    obtain ⟨f, hf⟩ := W.spokes w hwv
    have hfe : f ≠ e := fun hh ↦ hwu (hf.right_unique (hh.symm ▸ he))
    let d : Finset.univ.erase e := ⟨f, by simp [hfe]⟩
    have hd : J.Joins d v w := hf
    have hm : d ∈ J.meets S := by
      obtain ⟨k, hk⟩ := hd.exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ hvS⟩
    exact ⟨⟨d, hm⟩, hqv ▸ hd.contract hm⟩
  have hspokes (z : Option S) (hz : z ≠ pole) : ∃ f, K.Joins f pole z := by
    cases z with
    | none =>
      have hau : a ≠ u := fun h ↦ hnu (by simp [h])
      simpa only [hqa] using hspoke a hav hau
    | some z =>
      have hzv : z.1 ≠ v := fun h ↦ hz (congrArg some (Subtype.ext h))
      have hzu : z.1 ≠ u := fun h ↦ (Finset.mem_sdiff.mp z.2).2 (by simp [T, h])
      simpa only [q, contractVertex_some] using hspoke z.1 hzv hzu
  have hloop : ∀ f, K.endAt f 0 ≠ K.endAt f 1 :=
    contract_loopless S (fun f ↦ W.loopless f.1)
  obtain ⟨labels, hlabels⟩ := B.exists_labels
  let F : K.OddWheelFrame pole := {
    root := none
    root_ne := by simp [pole]
    rim := B
    labels := labels
    walk := hlabels
    vertices_eq := hBV
    length_three := B.three_le_labels_length hlabels hloop
    spokes := hspokes
    loopless := hloop }
  exact F.isBrick

/-- Deleting a spoke that has no parallel mate exposes the tight
three-vertex shore of its rim endpoint. Its discarded contraction is
bipartite and its retained contraction is a brick. -/
theorem exists_spoke_bicontraction (h5 : 5 ≤ W.labels.length) {e : E} {u : V}
    (he : H.Joins e v u) (hu : u ≠ v)
    (huniq : ∀ f, H.Joins f v u → f = e) :
    ∃ a b, ({u, a, b} : Finset V).card = 3 ∧ v ∉ ({u, a, b} : Finset V) ∧
      (∀ (d : Finset.univ.erase e) k, (H.deleteEdge e).endAt d k = u →
        (H.deleteEdge e).endAt d (Fin.rev k) = a ∨
          (H.deleteEdge e).endAt d (Fin.rev k) = b) ∧
      (H.deleteEdge e).IsTightCut {u, a, b} ∧
      ((H.deleteEdge e).contract {u, a, b}).IsBipartite ∧
      ((H.deleteEdge e).contract (Finset.univ \ {u, a, b})).IsBrick := by
  obtain ⟨a, b, l, hnd, hcover, heven, h2, ⟨f, hfa⟩, ⟨g, hgb⟩, hc⟩ :=
    W.exists_rim_neighbor_path h5 u hu
  have hnu := (List.nodup_cons.mp hnd).1
  have hpathnd := (List.nodup_cons.mp hnd).2
  have hna := (List.nodup_cons.mp hpathnd).1
  have htailnd := (List.nodup_cons.mp hpathnd).2
  have hbn : b ∉ l := by
    intro hb
    exact (List.nodup_append.mp htailnd).2.2 b hb b (by simp) rfl
  have hua : u ≠ a := fun hh ↦ hnu (by simp [hh])
  have hub : u ≠ b := fun hh ↦ hnu (by simp [hh])
  have hab : a ≠ b := fun hh ↦ hna (by simp [hh])
  have hnotv (z : V) (hz : z ∈ u :: a :: l ++ [b]) : z ≠ v := by
    have hh := hcover ▸ List.mem_toFinset.mpr hz
    exact (Finset.mem_erase.mp hh).1
  have hav := hnotv a (by simp)
  have hbv := hnotv b (by simp)
  have hR {d : E} {x y : V} (hd : H.Joins d x y) (hx : x ≠ v) (hy : y ≠ v) :
      d ∈ H.edgesIn (Finset.univ.erase v) := by
    apply mem_edgesIn.mpr
    intro k
    rcases hd.endAt_mem k with hk | hk <;> simp [hk, hx, hy]
  have hfR := hR hfa hu hav
  have hgR := hR hgb hbv hu
  have hneighbor {d : E} {z : V} (hd : H.Joins d u z) (hz : z ≠ v) : z = a ∨ z = b :=
    neighbors_of_degreeIn_le_two (W.rim_degree_two hu).le hab hfR hgR hfa
      (H.joins_comm.mp hgb) (hR hd hu hz) hd
  have hn : ∀ (d : Finset.univ.erase e) k,
      (H.deleteEdge e).endAt d k = u →
      (H.deleteEdge e).endAt d (Fin.rev k) = a ∨
        (H.deleteEdge e).endAt d (Fin.rev k) = b := by
    intro d k hk
    have hd : H.Joins d.1 u (H.endAt d.1 (Fin.rev k)) := by
      fin_cases k
      · exact Or.inl ⟨hk, rfl⟩
      · exact Or.inr ⟨rfl, hk⟩
    have hz : H.endAt d.1 (Fin.rev k) ≠ v := by
      intro hz
      have heq := huniq d.1 (H.joins_comm.mp (hz ▸ hd))
      exact (Finset.mem_erase.mp d.2).1 heq
    exact hneighbor hd hz
  have hnoab : ∀ d, ¬ H.Joins d a b := by
    cases l with
    | nil => simp at h2
    | cons c l =>
      obtain ⟨r, hr⟩ := hc.rel_head
      have hcv := hnotv c (by simp)
      have huc : u ≠ c := fun hh ↦ hnu (by simp [hh])
      have hbc : b ≠ c := fun hh ↦ hbn (by simp [hh])
      intro d hd
      have hz := neighbors_of_degreeIn_le_two (W.rim_degree_two hav).le huc
        hfR (hR hr hav hcv) (H.joins_comm.mp hfa) hr (hR hd hav hbv) hd
      exact hz.elim (Ne.symm hub) hbc
  refine ⟨a, b, by simp [hua, hub, hab], by simp [Ne.symm hu, Ne.symm hav, Ne.symm hbv], hn,
    isTightCut_neighbor_triple hua hub hab hn,
    isBipartite_contract_neighbor_triple (fun d ↦ W.loopless d.1) hn
      (fun d ↦ hnoab d.1), ?_⟩
  exact W.isBrick_bicontract_spoke_of_path he hnd hcover heven h2 hc

end OddWheel

end GraphPuzzles.LoopMultigraph
