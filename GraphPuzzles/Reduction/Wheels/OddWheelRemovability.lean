import GraphPuzzles.Reduction.Wheels.OddWheel
import GraphPuzzles.Reduction.Parallel.ParallelEdges

/-! Removability of spokes of odd wheels with rim length at least five. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
private theorem EdgeChain.append_singleton_of_incident_finish {a r : V} {es : List E}
    {l : List V} (h : H.EdgeChain a es (l ++ [r])) (ha : a ≠ r)
    (hl : ∀ x ∈ l, x ≠ r) {e : E} (he : e ∈ es) (hk : ∃ k, H.endAt e k = r) :
    ∃ ps, es = ps ++ [e] := by
  induction l generalizing a es with
  | nil =>
    cases h with
    | cons hg ht =>
      cases ht
      have heq := List.mem_singleton.mp he
      subst e
      exact ⟨[], rfl⟩
  | cons b l ih =>
    cases h with
    | @cons _ _ g gs _ hg ht =>
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨k, hk⟩ := hk
        rcases hg.endAt_mem k with hk' | hk'
        · exact (ha (hk'.symm.trans hk)).elim
        · exact (hl b (by simp) (hk'.symm.trans hk)).elim
      · obtain ⟨ps, hps⟩ := ih ht (hl b (by simp)) (fun x hx ↦ hl x (by simp [hx])) he
        exact ⟨g :: ps, by simp only [hps, List.cons_append]⟩

namespace OddWheel

variable {v : V} (W : H.OddWheel v)

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

omit [DecidableEq E] in
private theorem punctured_path_of_first_edge {r : V} (A : H.OddEar {r})
    {e : E} {es : List E} (hw : H.EdgeChain A.start (e :: es) (A.interior ++ [A.finish]))
    (h5 : 5 ≤ (e :: es).length) :
    ∃ a b l, H.Joins e a b ∧ (a :: b :: l).Nodup ∧
      l.IsChain (fun x y ↦ ∃ f, H.Joins f x y) ∧ Odd l.length ∧ 3 ≤ l.length ∧
      (a :: b :: l).toFinset = A.vertices := by
  have hs : A.start = r := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = r := Finset.mem_singleton.mp A.finish_mem
  cases hi : A.interior with
  | nil =>
    have hh := hw.length
    simp only [hi, List.nil_append, List.length_singleton] at hh
    omega
  | cons b l =>
    have hchain : H.EdgeChain r (e :: es) (b :: (l ++ [r])) := by
      simpa only [hs, ht, hi, List.cons_append] using hw
    cases hchain with
    | cons he htail =>
      refine ⟨r, b, l, he, ?_, htail.isChain.tail.left_of_append, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, hi ▸ A.nodup⟩
        intro hr
        exact A.avoids r (by simpa only [hi] using hr) (Finset.mem_singleton_self _)
      · have hh := A.even
        rw [hi, Nat.even_iff] at hh
        rw [Nat.odd_iff]
        simp only [List.length_cons] at hh
        omega
      · have hh := hw.length
        simp only [hi, List.length_append, List.length_cons, List.length_nil] at hh h5
        omega
      · simp only [OddEar.vertices, hi, List.toFinset_cons, Finset.singleton_union]

/-- Removing the endpoints of a prescribed rim edge leaves an odd path with at least
three vertices. The prescribed labelled edge itself is retained in the conclusion. -/
theorem exists_punctured_rim (h5 : 5 ≤ W.labels.length) {e : E}
    (he : e ∈ H.edgesIn (Finset.univ.erase v)) :
    ∃ a b l, H.Joins e a b ∧ (a :: b :: l).Nodup ∧
      l.IsChain (fun x y ↦ ∃ f, H.Joins f x y) ∧ Odd l.length ∧ 3 ≤ l.length ∧
      (a :: b :: l).toFinset = Finset.univ.erase v := by
  have hav : H.endAt e 0 ≠ v := (Finset.mem_erase.mp ((mem_edgesIn.mp he) 0)).1
  obtain ⟨A, es, hw, hV, hF, hlen⟩ := W.exists_rooted_rim (H.endAt e 0) hav
  have hees : e ∈ es := List.mem_toFinset.mp (hF.symm ▸ W.edges_eq.symm ▸ he)
  have hs : A.start = H.endAt e 0 := Finset.mem_singleton.mp A.start_mem
  have ht : A.finish = H.endAt e 0 := Finset.mem_singleton.mp A.finish_mem
  cases hi : A.interior with
  | nil =>
    have hh := hw.length
    simp only [hi, List.nil_append, List.length_singleton] at hh
    omega
  | cons b l =>
    have hw' : H.EdgeChain (H.endAt e 0) es (b :: (l ++ [H.endAt e 0])) := by
      simpa only [hs, ht, hi, List.cons_append] using hw
    cases hw' with
    | @cons _ _ f fs _ hf htail =>
      by_cases hef : e = f
      · subst f
        obtain ⟨a, b, l, he, hn, hc, ho, hlen', hset⟩ :=
          punctured_path_of_first_edge A hw (by omega)
        exact ⟨a, b, l, he, hn, hc, ho, hlen', hset.trans hV⟩
      · have heb : b ≠ H.endAt e 0 := fun hh ↦ A.avoids b (by simp [hi])
          (Finset.mem_singleton.mpr hh)
        have hel : ∀ x ∈ l, x ≠ H.endAt e 0 := fun x hx hh ↦
          A.avoids x (by simp [hi, hx]) (Finset.mem_singleton.mpr hh)
        have hefs : e ∈ fs := (List.mem_cons.mp hees).resolve_left hef
        obtain ⟨ps, hps⟩ := htail.append_singleton_of_incident_finish heb hel hefs ⟨0, rfl⟩
        have hrev : H.EdgeChain A.reverse.start (e :: (f :: ps).reverse)
            (A.reverse.interior ++ [A.reverse.finish]) := by
          simpa only [hps, List.reverse_cons, List.reverse_append, List.reverse_singleton,
            List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append]
            using A.reverse_walk hw
        obtain ⟨a, b, l, he, hn, hc, ho, hlen', hset⟩ :=
          punctured_path_of_first_edge A.reverse hrev (by
            simp only [List.length_cons, List.length_reverse] at h5 ⊢
            simp only [hps, List.length_cons, List.length_append, List.length_nil] at hlen
            omega)
        exact ⟨a, b, l, he, hn, hc, ho, hlen', hset.trans (A.reverse_vertices.trans hV)⟩

private theorem matching_omit_third {a b c : V} {l : List V} {e : E}
    (he : H.Joins e a b) (hn : (a :: b :: c :: l).Nodup)
    (hc : l.IsChain (fun x y ↦ ∃ f, H.Joins f x y)) (hev : Even l.length) :
    ∃ M, H.IsPerfectMatchingOn ((a :: b :: c :: l).toFinset.erase c) M ∧ e ∈ M := by
  have hna := List.nodup_cons.mp hn
  have hnb := List.nodup_cons.mp hna.2
  have hnc := List.nodup_cons.mp hnb.2
  have hab : a ≠ b := fun h ↦ hna.1 (by simp [h])
  obtain ⟨M, hM⟩ := exists_matchingOn_of_even_chain l hnc.2 hc hev
  have hd : Disjoint ({a, b} : Finset V) l.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hxl
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hna.1 (by simp [List.mem_toFinset.mp hxl])
    · exact hnb.1 (by simp [← Finset.mem_singleton.mp hx, List.mem_toFinset.mp hxl])
  have hS : ({a, b} : Finset V) ∪ l.toFinset = (a :: b :: c :: l).toFinset.erase c := by
    have hac : a ≠ c := fun h ↦ hna.1 (by simp [h])
    have hbc : b ≠ c := fun h ↦ hnb.1 (by simp [h])
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
      Finset.mem_erase, List.mem_cons]
    constructor
    · rintro ((rfl | rfl) | hx)
      · exact ⟨hac, Or.inl rfl⟩
      · exact ⟨hbc, Or.inr (Or.inl rfl)⟩
      · exact ⟨fun heq ↦ hnc.1 (heq ▸ hx), Or.inr (Or.inr (Or.inr hx))⟩
    · rintro ⟨hxc, rfl | rfl | rfl | hx⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact (hxc rfl).elim
      · exact Or.inr hx
  exact ⟨{e} ∪ M, hS ▸ (he.isPerfectMatchingOn hab).union hM hd, by simp⟩

/-- A rim edge extends to a rim matching leaving an exposed vertex different from any
one forbidden rim vertex. The two ends of the remaining odd path provide the choices. -/
theorem exists_matchingOn_rim_erase_through_avoiding (h5 : 5 ≤ W.labels.length)
    {e : E} (he : e ∈ H.edgesIn (Finset.univ.erase v)) (w : V) :
    ∃ x, x ∈ Finset.univ.erase v ∧ x ≠ w ∧
      ∃ M, H.IsPerfectMatchingOn ((Finset.univ.erase v).erase x) M ∧ e ∈ M := by
  obtain ⟨a, b, l, heab, hn, hc, ho, hl, hset⟩ := W.exists_punctured_rim h5 he
  cases l with
  | nil => simp at hl
  | cons c t =>
    have ht : t ≠ [] := by intro hh; simp [hh] at hl
    obtain ⟨m, z, htz⟩ := (List.eq_nil_or_concat' t).resolve_left ht
    subst t
    have hcz : c ≠ z := by
      have hh := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
      intro heq
      exact hh (by simp [heq])
    have hEven : Even (m ++ [z]).length := by
      rw [Nat.odd_iff] at ho
      rw [Nat.even_iff]
      simp only [List.length_cons] at ho
      omega
    by_cases hcw : c ≠ w
    · obtain ⟨M, hM, heM⟩ := matching_omit_third heab hn hc.tail hEven
      exact ⟨c, hset ▸ (by simp), hcw, M, hset ▸ hM, heM⟩
    · have hcw' : c = w := not_ne_iff.mp hcw
      have hchain : (m.reverse ++ [c]).IsChain (fun x y ↦ ∃ f, H.Joins f x y) := by
        have hh := List.isChain_reverse.mpr
          (hc.imp fun _ _ hh ↦ hh.imp fun _ hf ↦ H.joins_comm.mp hf)
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append,
          List.tail_cons] using hh.tail
      have hnfull : (a :: b :: z :: (m.reverse ++ [c])).Nodup := by
        have hna := List.nodup_cons.mp hn
        have hnb := List.nodup_cons.mp hna.2
        have hnr := List.nodup_reverse.mpr hnb.2
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
        · simpa only [List.mem_cons, List.mem_reverse, List.mem_append, List.mem_singleton,
            or_comm, or_left_comm, or_assoc] using hna.1
        · simpa only [List.mem_cons, List.mem_reverse, List.mem_append, List.mem_singleton,
            or_comm, or_left_comm, or_assoc] using hnb.1
        · simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
            List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append] using hnr
      have hev : Even (m.reverse ++ [c]).length := by
        simpa only [List.length_append, List.length_reverse, List.length_singleton] using hEven
      obtain ⟨M, hM, heM⟩ := matching_omit_third heab hnfull hchain hev
      have heq : (a :: b :: z :: (m.reverse ++ [c])).toFinset = Finset.univ.erase v := by
        rw [← hset]
        ext x
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_reverse]
        tauto
      exact ⟨z, heq ▸ (by simp), fun hz ↦ hcz (hcw'.trans hz.symm), M, heq ▸ hM, heM⟩

include W in
theorem factorCritical_rim : H.IsFactorCritical (Finset.univ.erase v) :=
  W.vertices_eq ▸ W.rim.isFactorCritical
    (HasOddEarConstruction.singleton W.root).isFactorCritical

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

omit [DecidableEq V] [DecidableEq E] in
private theorem joins_right_unique {e : E} {a b c : V}
    (he : H.Joins e a b) (hf : H.Joins e a c) : b = c := by
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    rcases hf with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> simp_all

omit [DecidableEq V] [DecidableEq E] in
private theorem chain_color_constant {a : V} {es : List E} {vs : List V}
    (h : H.EdgeChain a es vs) (d : V → Bool)
    (hc : ∀ e ∈ es, d (H.endAt e 0) = d (H.endAt e 1)) :
    ∀ x ∈ a :: vs, d x = d a := by
  induction h with
  | nil => intro x hx; exact congrArg d (List.mem_singleton.mp hx)
  | @cons a b e es vs he ht ih =>
    have hab : d a = d b := by
      have hh := hc e (by simp)
      rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simpa only [h0, h1] using hh
      · simpa only [h0, h1] using hh.symm
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact (ih (fun f hf ↦ hc f (by simp [hf])) x hx).trans hab.symm

include W in
/-- Removing a spoke keeps the whole rim connected to the hub through another spoke. -/
theorem connected_delete_spoke {e : E} {w : V} (he : H.Joins e v w) :
    (H.deleteEdge e).IsConnected := by
  have hvw : v ≠ w := by
    intro hh
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact W.loopless e (h0.trans (hh.trans h1.symm))
    · exact W.loopless e (h0.trans (hh.symm.trans h1.symm))
  have heR : e ∉ H.edgesIn (Finset.univ.erase v) := by
    intro hh
    obtain ⟨k, hk⟩ := he.exists_end
    have hv := (mem_edgesIn.mp hh) k
    simp [hk] at hv
  intro d hd
  have hlabels : ∀ f ∈ W.labels, d (H.endAt f 0) = d (H.endAt f 1) := by
    intro f hf
    have hfR : f ∈ H.edgesIn (Finset.univ.erase v) := W.edges_eq ▸ List.mem_toFinset.mpr hf
    have hfe : f ≠ e := fun hh ↦ heR (hh ▸ hfR)
    exact hd ⟨f, Finset.mem_erase.mpr ⟨hfe, Finset.mem_univ _⟩⟩
  have hs : W.rim.start = W.root := Finset.mem_singleton.mp W.rim.start_mem
  have hconst (x : V) (hx : x ≠ v) : d x = d W.root := by
    have hxR : x ∈ W.rim.vertices := W.vertices_eq.symm ▸ (by simp [hx])
    rcases Finset.mem_union.mp hxR with hxold | hxnew
    · exact congrArg d (Finset.mem_singleton.mp hxold)
    · have hh := chain_color_constant W.walk d hlabels x
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_toFinset.mp hxnew)))
      simpa only [hs] using hh
  have hwR : w ∈ Finset.univ.erase v := by simp [Ne.symm hvw]
  have hcard := Finset.card_erase_add_one hwR
  have hrim := W.rim_card_eq_length
  have hlen := W.length_three
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
    0 < ((Finset.univ.erase v).erase w).card)
  obtain ⟨hzw, hzR⟩ := Finset.mem_erase.mp hz
  have hzv : z ≠ v := (Finset.mem_erase.mp hzR).1
  obtain ⟨g, hg⟩ := W.spokes z hzv
  have hge : g ≠ e := by
    intro hge
    subst g
    exact hzw (joins_right_unique hg he)
  have hvz : d v = d z := by
    have hh := hd ⟨g, Finset.mem_erase.mpr ⟨hge, Finset.mem_univ _⟩⟩
    change d (H.endAt g 0) = d (H.endAt g 1) at hh
    rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hh
    · simpa only [h0, h1] using hh.symm
  have hall (x : V) : d x = d W.root := by
    by_cases hx : x = v
    · exact hx ▸ hvz.trans (hconst z hzv)
    · exact hconst x hx
  exact fun x y ↦ (hall x).trans (hall y).symm

private theorem insert_spoke_avoiding {e g : E} {w x : V} {M : Finset E}
    (he : H.Joins e v w) (hg : H.Joins g v x) (hge : g ≠ e) (hx : x ≠ v)
    (hM : H.IsPerfectMatchingOn ((Finset.univ.erase v).erase x) M) :
    H.IsPerfectMatching (insert g M) ∧ insert g M ⊆ Finset.univ.erase e := by
  refine ⟨hM.insert_perfect hg hx.symm, ?_⟩
  intro f hf
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact hge
  · intro hfe
    subst f
    obtain ⟨k, hk⟩ := he.exists_end
    have hh := hM.1 e hf k
    simp [hk] at hh

/-- Every spoke of an odd wheel with rim length at least five is removable, including
when other spokes have parallel labels. -/
theorem isRemovable_spoke (h5 : 5 ≤ W.labels.length) {e : E} {w : V}
    (he : H.Joins e v w) : H.IsRemovable e := by
  apply isMatchingCovered_restrictEdges_of_cover (W.connected_delete_spoke he)
  intro f hf
  have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
  by_cases hfR : f ∈ H.edgesIn (Finset.univ.erase v)
  · obtain ⟨x, hxR, hxw, M, hM, hfM⟩ :=
      W.exists_matchingOn_rim_erase_through_avoiding h5 hfR w
    have hxv := (Finset.mem_erase.mp hxR).1
    obtain ⟨g, hg⟩ := W.spokes x hxv
    have hge : g ≠ e := by
      intro hge
      subst g
      exact hxw (joins_right_unique hg he)
    have hh := insert_spoke_avoiding he hg hge hxv hM
    exact ⟨insert g M, hh.1, hh.2, Finset.mem_insert_of_mem hfM⟩
  · obtain ⟨k, hk⟩ : ∃ k, H.endAt f k = v := by
      by_contra hn
      push Not at hn
      exact hfR (mem_edgesIn.mpr fun k ↦ by simp [hn k])
    have hx : H.endAt f (Fin.rev k) ≠ v := by
      intro hh
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact W.loopless f (hk.trans hh.symm)
      · exact W.loopless f (hh.trans hk.symm)
    have hfJ : H.Joins f v (H.endAt f (Fin.rev k)) := by
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact Or.inl ⟨hk, rfl⟩
      · exact Or.inr ⟨rfl, hk⟩
    obtain ⟨M, hM⟩ := W.factorCritical_rim (H.endAt f (Fin.rev k)) (by simp [hx])
    have hh := insert_spoke_avoiding he hfJ hfe hx hM
    exact ⟨insert f M, hh.1, hh.2, Finset.mem_insert_self _ _⟩

end OddWheel
end GraphPuzzles.LoopMultigraph
