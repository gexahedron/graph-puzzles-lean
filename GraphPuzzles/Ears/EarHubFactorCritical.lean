import GraphPuzzles.Ears.EarChordHub

/-! Factor-criticality of the last ear's interior together with its deleted hub. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype V] [DecidableEq V] in
private theorem nodup_two_ends {a b : V} {l : List V} (hn : l.Nodup)
    (ha : a ∉ l) (hb : b ∉ l) (hab : a ≠ b) : (a :: (l ++ [b])).Nodup := by
  refine List.nodup_cons.mpr ⟨by simpa using ⟨ha, hab⟩, ?_⟩
  refine List.nodup_append.mpr ⟨hn, by simp, ?_⟩
  intro x hx y hy hxy
  exact hb ((hxy.trans (List.mem_singleton.mp hy)) ▸ hx)

/-- Match pairwise disjoint even paths independently. -/
theorem exists_matchingOn_of_even_chain_chunks (ls : List (List V))
    (hn : ls.flatten.Nodup)
    (hc : ∀ l ∈ ls, l.IsChain (fun a b ↦ ∃ e, H.Joins e a b))
    (he : ∀ l ∈ ls, Even l.length) :
    ∃ M, H.IsPerfectMatchingOn ls.flatten.toFinset M := by
  induction ls with
  | nil => exact ⟨∅, by simp [IsPerfectMatchingOn]⟩
  | cons l ls ih =>
    have hh := List.nodup_append.mp hn
    obtain ⟨A, hA⟩ := exists_matchingOn_of_even_chain l hh.1 (hc l (by simp)) (he l (by simp))
    obtain ⟨B, hB⟩ := ih hh.2.1 (fun x hx ↦ hc x (by simp [hx])) (fun x hx ↦ he x (by simp [hx]))
    have hd : Disjoint l.toFinset ls.flatten.toFinset := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      exact hh.2.2 x (List.mem_toFinset.mp hx) x (List.mem_toFinset.mp hx') rfl
    exact ⟨A ∪ B, by simpa only [List.flatten_cons, List.toFinset_append] using hA.union hB hd⟩

/-- Replace each of two matched connector vertices by its factor-critical block. -/
theorem IsFactorCritical.matchingOn_union_two {A B C : Finset V}
    (hA : H.IsFactorCritical A) (hB : H.IsFactorCritical B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) {M : Finset E}
    (hM : H.IsPerfectMatchingOn (insert a (insert b C)) M) :
    ∃ N, H.IsPerfectMatchingOn (A ∪ B ∪ C) N := by
  have hAb : b ∉ A := fun h ↦ Finset.disjoint_left.mp hAB h hb
  have hA' : Disjoint A (insert b C) := Finset.disjoint_insert_right.mpr ⟨hAb, hAC⟩
  obtain ⟨P, hP⟩ := hA.matchingOn_union_of_matchingOn_insert ha hA' hM
  have hP' : H.IsPerfectMatchingOn (insert b (A ∪ C)) P := by
    simpa only [Finset.union_insert] using hP
  obtain ⟨Q, hQ⟩ := hB.matchingOn_union_of_matchingOn_insert hb
    (Finset.disjoint_union_right.mpr ⟨hAB.symm, hBC⟩) hP'
  exact ⟨Q, by simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hQ⟩

/-- An odd cycle is factor-critical, recorded with one distinguished vertex. -/
theorem isFactorCritical_of_odd_cycle (a : V) (l : List V)
    (hn : (a :: l).Nodup) (he : Even l.length)
    (hc : (a :: (l ++ [a])).IsChain (fun x y ↦ ∃ e, H.Joins e x y)) :
    H.IsFactorCritical (a :: l).toFinset := by
  let A : H.OddEar {a} := {
    start := a
    finish := a
    interior := l
    start_mem := by simp
    finish_mem := by simp
    nodup := (List.nodup_cons.mp hn).2
    avoids := fun w hw hwa ↦ (List.nodup_cons.mp hn).1 ((Finset.mem_singleton.mp hwa) ▸ hw)
    even := he
    chain := hc }
  have hfc : H.IsFactorCritical {a} := (HasOddEarConstruction.singleton a).isFactorCritical
  simpa only [OddEar.vertices, A, Finset.singleton_union, List.toFinset_cons] using A.isFactorCritical hfc

/-- Two disjoint factor-critical blocks connected by an odd path become
factor-critical after adding a hub adjacent to one vertex in each block. -/
theorem IsFactorCritical.two_blocks_hub {A B : Finset V}
    (hA : H.IsFactorCritical A) (hB : H.IsFactorCritical B) (hAB : Disjoint A B)
    {v x y i j : V} (hvA : v ∉ A) (hvB : v ∉ B)
    (hx : x ∈ A) (hy : y ∈ B) (hi : i ∈ A) (hj : j ∈ B)
    (hvi : ∃ e, H.Joins e v i) (hvj : ∃ e, H.Joins e v j)
    (p : List V) (hn : p.Nodup) (he : Even p.length)
    (hp : (x :: (p ++ [y])).IsChain (fun a b ↦ ∃ e, H.Joins e a b))
    (havoid : ∀ w ∈ p, w ∉ A ∧ w ∉ B ∧ w ≠ v) :
    H.IsFactorCritical (insert v (A ∪ B ∪ p.toFinset)) := by
  have hAp : Disjoint A p.toFinset := Finset.disjoint_right.mpr
    (fun w hw hwa ↦ (havoid w (List.mem_toFinset.mp hw)).1 hwa)
  have hBp : Disjoint B p.toFinset := Finset.disjoint_right.mpr
    (fun w hw hwb ↦ (havoid w (List.mem_toFinset.mp hw)).2.1 hwb)
  have hvp : v ∉ p := fun hw ↦ (havoid v hw).2.2 rfl
  have hxP : x ∉ p := fun hw ↦ (havoid x hw).1 hx
  have hyP : y ∉ p := fun hw ↦ (havoid y hw).2.1 hy
  have hiP : i ∉ p := fun hw ↦ (havoid i hw).1 hi
  have hjP : j ∉ p := fun hw ↦ (havoid j hw).2.1 hj
  have hxy : x ≠ y := fun h ↦ Finset.disjoint_left.mp hAB (h ▸ hx) hy
  have hiv : i ≠ v := fun h ↦ hvA (h ▸ hi)
  have hjv : j ≠ v := fun h ↦ hvB (h ▸ hj)
  have hxv : x ≠ v := fun h ↦ hvA (h ▸ hx)
  have hyv : y ≠ v := fun h ↦ hvB (h ▸ hy)
  have hiy : i ≠ y := fun h ↦ Finset.disjoint_left.mp hAB (h ▸ hi) hy
  have hxj : x ≠ j := fun h ↦ Finset.disjoint_left.mp hAB (h ▸ hx) hj
  have hpchain : p.IsChain (fun a b ↦ ∃ e, H.Joins e a b) := hp.tail.left_of_append
  have hpair (z : V) (hzv : z ≠ v) (hzP : z ∉ p)
      (hvz : ∃ e, H.Joins e v z) :
      ∃ Q, H.IsPerfectMatchingOn (insert z (insert v p.toFinset)) Q := by
    have hn' : ([v, z] ++ p).Nodup := by
      simp only [List.cons_append, List.nil_append, List.nodup_cons]
      exact ⟨by simpa using ⟨hzv.symm, hvp⟩, hzP, hn⟩
    obtain ⟨Q, hQ⟩ := exists_matchingOn_of_even_chain_chunks (H := H) [[v, z], p]
      (by simpa using hn')
      (by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · exact List.isChain_pair.mpr hvz
          · exact hpchain)
      (by intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · simp
          · exact he)
    exact ⟨Q, by simpa [Finset.insert_comm] using hQ⟩
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · obtain ⟨P, hP⟩ := exists_matchingOn_of_even_chain (H := H) (x :: (p ++ [y]))
      (nodup_two_ends hn hxP hyP hxy) hp (by
        rw [Nat.even_iff] at he ⊢
        simp only [List.length_cons, List.length_append, List.length_nil]
        omega)
    have hP' : H.IsPerfectMatchingOn (insert x (insert y p.toFinset)) P := by
      simpa [Finset.insert_comm] using hP
    obtain ⟨Q, hQ⟩ := hA.matchingOn_union_two hB hAB hAp hBp hx hy hP'
    exact ⟨Q, by simpa [Finset.erase_insert, Finset.erase_union_distrib, hvA, hvB, hvp] using hQ⟩
  · rcases Finset.mem_union.mp hw with hw | hwp
    · rcases Finset.mem_union.mp hw with hwA | hwB
      · have hwB : w ∉ B := fun hh ↦ Finset.disjoint_left.mp hAB hwA hh
        have hwp : w ∉ p := fun hh ↦ (havoid w hh).1 hwA
        have hwv : w ≠ v := fun hh ↦ hvA (hh ▸ hwA)
        obtain ⟨P, hP⟩ := hA w hwA
        obtain ⟨Q, hQ⟩ := hpair j hjv hjP hvj
        obtain ⟨R, hR⟩ := hB.matchingOn_union_of_matchingOn_insert hj
          (Finset.disjoint_insert_right.mpr ⟨hvB, hBp⟩) hQ
        have hdisj : Disjoint (A.erase w) (B ∪ insert v p.toFinset) := by
          apply Finset.disjoint_left.mpr
          intro z hz hz'
          have hzA := Finset.mem_of_mem_erase hz
          rcases Finset.mem_union.mp hz' with hzB | hz'
          · exact Finset.disjoint_left.mp hAB hzA hzB
          · rcases Finset.mem_insert.mp hz' with rfl | hzp
            · exact hvA hzA
            · exact (havoid z (List.mem_toFinset.mp hzp)).1 hzA
        refine ⟨P ∪ R, ?_⟩
        have hh := hP.union hR hdisj
        convert hh using 1
        ext z
        by_cases hzw : z = w
        · subst z
          simp [hwB, hwp, hwv]
        · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_union,
            List.mem_toFinset]
          clear * - hzw
          tauto
      · have hwA : w ∉ A := fun hh ↦ Finset.disjoint_left.mp hAB hh hwB
        have hwp : w ∉ p := fun hh ↦ (havoid w hh).2.1 hwB
        have hwv : w ≠ v := fun hh ↦ hvB (hh ▸ hwB)
        obtain ⟨P, hP⟩ := hB w hwB
        obtain ⟨Q, hQ⟩ := hpair i hiv hiP hvi
        obtain ⟨R, hR⟩ := hA.matchingOn_union_of_matchingOn_insert hi
          (Finset.disjoint_insert_right.mpr ⟨hvA, hAp⟩) hQ
        have hdisj : Disjoint (B.erase w) (A ∪ insert v p.toFinset) := by
          apply Finset.disjoint_left.mpr
          intro z hz hz'
          have hzB := Finset.mem_of_mem_erase hz
          rcases Finset.mem_union.mp hz' with hzA | hz'
          · exact Finset.disjoint_left.mp hAB hzA hzB
          · rcases Finset.mem_insert.mp hz' with rfl | hzp
            · exact hvB hzB
            · exact (havoid z (List.mem_toFinset.mp hzp)).2.1 hzB
        refine ⟨P ∪ R, ?_⟩
        have hh := hP.union hR hdisj
        convert hh using 1
        ext z
        by_cases hzw : z = w
        · subst z
          simp [hwA, hwp, hwv]
        · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_union,
            List.mem_toFinset]
          clear * - hzw
          tauto
    · have hwpl := List.mem_toFinset.mp hwp
      obtain ⟨l, r, hsplit⟩ := List.append_of_mem hwpl
      have hns := List.nodup_append.mp (hsplit ▸ hn)
      have hnr := List.nodup_cons.mp hns.2.1
      have hnlr : (l ++ r).Nodup := List.nodup_append.mpr
        ⟨hns.1, hnr.2, fun a ha b hb hab ↦ hns.2.2 a ha b (List.mem_cons_of_mem _ hb) hab⟩
      have hmem : ∀ a ∈ l ++ r, a ∈ p := by
        intro a ha
        simp only [hsplit, List.mem_append, List.mem_cons] at ha ⊢
        tauto
      have havoid' : ∀ a ∈ l ++ r, a ∉ A ∧ a ∉ B ∧ a ≠ v :=
        fun a ha ↦ havoid a (hmem a ha)
      have hAC : Disjoint A (insert v (l ++ r).toFinset) := by
        apply Finset.disjoint_right.mpr
        intro a ha haA
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hvA haA
        · exact (havoid' a (List.mem_toFinset.mp ha)).1 haA
      have hBC : Disjoint B (insert v (l ++ r).toFinset) := by
        apply Finset.disjoint_right.mpr
        intro a ha haB
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hvB haB
        · exact (havoid' a (List.mem_toFinset.mp ha)).2.1 haB
      have hcov : (insert v (A ∪ B ∪ p.toFinset)).erase w =
          A ∪ B ∪ insert v (l ++ r).toFinset := by
        have hwA := (havoid w hwpl).1
        have hwB := (havoid w hwpl).2.1
        have hwv := (havoid w hwpl).2.2
        have hwl : w ∉ l := fun hh ↦ hns.2.2 w hh w (by simp) rfl
        have hwr : w ∉ r := hnr.1
        ext a
        by_cases haw : a = w
        · subst a
          simp [hwA, hwB, hwv, hwl, hwr]
        · simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_union,
            List.mem_toFinset, hsplit, List.mem_append, List.mem_cons, haw, false_or]
          clear * - haw
          tauto
      by_cases hl : Even l.length
      · have hr : Even (r ++ [y]).length := by
          rw [hsplit, Nat.even_iff] at he
          rw [Nat.even_iff] at hl ⊢
          simp only [List.length_append, List.length_cons, List.length_nil] at he ⊢
          omega
        have hn' : (v :: i :: ((l ++ r) ++ [y])).Nodup := by
          refine List.nodup_cons.mpr ⟨?_, nodup_two_ends hnlr
            (fun hh ↦ hiP (hmem i hh)) (fun hh ↦ hyP (hmem y hh)) hiy⟩
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
          exact ⟨hiv.symm, ⟨fun hh ↦ hvp (hmem v (List.mem_append_left _ hh)),
            fun hh ↦ hvp (hmem v (List.mem_append_right _ hh))⟩, hyv.symm⟩
        have hlchain : l.IsChain (fun a b ↦ ∃ e, H.Joins e a b) :=
          (hsplit ▸ hpchain).left_of_append
        have hrchain : (r ++ [y]).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
          have hh : (p ++ [y]).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := hp.tail
          rw [hsplit] at hh
          have hh' : (l ++ w :: (r ++ [y])).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
            simpa only [List.append_assoc, List.cons_append] using hh
          exact hh'.right_of_append.tail
        obtain ⟨P, hP⟩ := exists_matchingOn_of_even_chain_chunks (H := H) [[v, i], l, r ++ [y]]
          (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
            List.cons_append, List.nil_append, List.append_assoc] using hn')
          (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl | rfl
              · exact List.isChain_pair.mpr hvi
              · exact hlchain
              · exact hrchain)
          (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl | rfl
              · simp
              · exact hl
              · exact hr)
        have hP' : H.IsPerfectMatchingOn (insert i (insert y (insert v (l ++ r).toFinset))) P := by
          simpa [Finset.insert_comm, Finset.union_assoc] using hP
        obtain ⟨Q, hQ⟩ := hA.matchingOn_union_two hB hAB hAC hBC hi hy hP'
        exact ⟨Q, hcov.symm ▸ hQ⟩
      · have hl' : Even (x :: l).length := by rw [Nat.even_iff] at hl ⊢; simp; omega
        have hr : Even r.length := by
          rw [hsplit, Nat.even_iff] at he
          rw [Nat.even_iff] at hl ⊢
          simp only [List.length_append, List.length_cons] at he
          omega
        have hn' : ((x :: (l ++ r)) ++ [v, j]).Nodup := by
          refine List.nodup_append.mpr ⟨List.nodup_cons.mpr
            ⟨fun hh ↦ hxP (hmem x hh), hnlr⟩, by simpa using hjv.symm, ?_⟩
          intro a ha b hb hab
          rcases List.mem_cons.mp ha with rfl | ha
          · rcases List.mem_cons.mp hb with rfl | hb
            · exact hxv hab
            · exact hxj (hab.trans (List.mem_singleton.mp hb))
          · rcases List.mem_cons.mp hb with rfl | hb
            · exact (havoid' a ha).2.2 hab
            · exact hjP ((hab.trans (List.mem_singleton.mp hb)) ▸ hmem a ha)
        have hlchain : (x :: l).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
          have hh : ((x :: l) ++ w :: (r ++ [y])).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
            simpa only [hsplit, List.cons_append, List.append_assoc] using hp
          exact hh.left_of_append
        have hrchain : r.IsChain (fun a b ↦ ∃ e, H.Joins e a b) :=
          (hsplit ▸ hpchain).right_of_append.tail
        obtain ⟨P, hP⟩ := exists_matchingOn_of_even_chain_chunks (H := H) [x :: l, r, [v, j]]
          (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
            List.cons_append, List.append_assoc] using hn')
          (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl | rfl
              · exact hlchain
              · exact hrchain
              · exact List.isChain_pair.mpr hvj)
          (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl | rfl
              · exact hl'
              · exact hr
              · simp)
        have hP' : H.IsPerfectMatchingOn (insert x (insert j (insert v (l ++ r).toFinset))) P := by
          simpa [Finset.insert_comm, Finset.union_assoc] using hP
        obtain ⟨Q, hQ⟩ := hA.matchingOn_union_two hB hAB hAC hBC hx hj hP'
        exact ⟨Q, hcov.symm ▸ hQ⟩


/-- List form of the two-block construction, with disjointness supplied by
the original path's distinct vertices. -/
theorem isFactorCritical_of_two_chain_blocks (a p b : List V)
    (hn : (a ++ (p ++ b)).Nodup) {v x y i j : V} (hv : v ∉ a ++ (p ++ b))
    (hA : H.IsFactorCritical a.toFinset) (hB : H.IsFactorCritical b.toFinset)
    (hx : x ∈ a) (hy : y ∈ b) (hi : i ∈ a) (hj : j ∈ b)
    (hvi : ∃ e, H.Joins e v i) (hvj : ∃ e, H.Joins e v j)
    (he : Even p.length)
    (hc : (x :: (p ++ [y])).IsChain (fun u w ↦ ∃ e, H.Joins e u w)) :
    H.IsFactorCritical (insert v (a ++ (p ++ b)).toFinset) := by
  have hnA := List.nodup_append.mp hn
  have hnP := List.nodup_append.mp hnA.2.1
  have hAB : Disjoint a.toFinset b.toFinset := by
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    exact hnA.2.2 z (List.mem_toFinset.mp hza) z
      (List.mem_append_right _ (List.mem_toFinset.mp hzb)) rfl
  have havoid : ∀ w ∈ p, w ∉ a.toFinset ∧ w ∉ b.toFinset ∧ w ≠ v := by
    intro w hw
    refine ⟨?_, ?_, ?_⟩
    · intro hwa
      exact hnA.2.2 w (List.mem_toFinset.mp hwa) w (List.mem_append_left _ hw) rfl
    · intro hwb
      exact hnP.2.2 w hw w (List.mem_toFinset.mp hwb) rfl
    · intro hwv
      exact hv (by simp [← hwv, hw])
  have hfc := hA.two_blocks_hub hB hAB
    (fun hh ↦ hv (List.mem_append_left _ (List.mem_toFinset.mp hh)))
    (fun hh ↦ hv (List.mem_append_right _ (List.mem_append_right _ (List.mem_toFinset.mp hh))))
    (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr hy)
    (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj) hvi hvj p hnP.1 he hc havoid
  simpa only [List.toFinset_append, Finset.union_assoc, Finset.union_comm,
    Finset.union_left_comm] using hfc

/-- Closing an even-length path with a chord gives an odd factor-critical cycle. -/
theorem isFactorCritical_of_even_chord {x y : V} (p : List V)
    (hn : (x :: (p ++ [y])).Nodup)
    (hc : (x :: (p ++ [y])).IsChain (fun a b ↦ ∃ e, H.Joins e a b))
    (he : Even (p.length + 1)) (hj : ∃ e, H.Joins e x y) :
    H.IsFactorCritical (x :: (p ++ [y])).toFinset := by
  apply isFactorCritical_of_odd_cycle x (p ++ [y]) hn
    (by simpa only [List.length_append, List.length_singleton] using he)
  have hj' : ∃ e, H.Joins e y x := hj.imp fun _ he ↦ H.joins_comm.mp he
  have hh := List.isChain_cons_split.mpr ⟨hc, List.isChain_pair.mpr hj'⟩
  simpa only [List.append_assoc, List.singleton_append] using hh


omit [DecidableEq E] in
private theorem tail_matching_joins_ne {M : Finset E} {e : E} {x y : V}
    (he : e ∈ M) (hj : H.Joins e x y) (hd : H.degreeIn M x ≤ 1) : x ≠ y := by
  intro hxy
  have h0 : H.endAt e 0 = x := by rcases hj with hj | hj <;> simp_all
  have h1 : H.endAt e 1 = x := by rcases hj with hj | hj <;> simp_all
  have hinc : (e, (0 : Fin 2)) = (e, (1 : Fin 2)) := by
    apply Finset.card_le_one_iff.mp hd
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, h0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩, h1⟩
  have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd hinc
  norm_num at h01

namespace LastOutsideOddEar

variable {M G : Finset E} {r : V} {q : ℕ} {T : Finset V}
variable (L : H.LastOutsideOddEar M r q T G)

private theorem interior_chain : L.ear.interior.IsChain (fun a b ↦ ∃ e, H.Joins e a b) :=
  L.ear.chain.tail.left_of_append

private theorem hub_not_mem_interior {v : V} (hT : T = Finset.univ.erase v) :
    v ∉ L.ear.interior := by
  intro hv
  have hh : v ∈ T := L.vertices_eq ▸
    Finset.mem_union_right L.oldVertices (List.mem_toFinset.mpr hv)
  simp [hT] at hh

/-- A first internal vertex not adjacent to the hub starts an odd chord cycle,
strictly before the last internal vertex. -/
private theorem first_tail_chord {v x y : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    (p : List V) (hi : L.ear.interior = x :: (p ++ [y]))
    (hno : ¬ ∃ e, H.Joins e v x) :
    ∃ (a b : List V) (k i : V) (e : E), p = a ++ k :: b ∧
      e ∈ G \ (L.oldEdges ∪ L.labels.toFinset) ∧ H.Joins e x k ∧
      Even (a.length + 1) ∧ i ∈ a ∧ ∃ f, H.Joins f v i := by
  have hGS : G ⊆ H.edgesIn T := by rw [hT, hG]
  have hxI : x ∈ L.ear.interior := by simp [hi]
  have hxT : x ∈ T := L.vertices_eq ▸
    Finset.mem_union_right L.oldVertices (List.mem_toFinset.mpr hxI)
  rcases L.internal_hub_or_tail hT hG hxI (hdeg x hxT) with hh | ⟨e, he, s, hs⟩
  · exact (hno hh).elim
  · let k := H.endAt e (Fin.rev s)
    have hxk : H.Joins e x k := by
      fin_cases s
      · exact Or.inl ⟨hs, rfl⟩
      · exact Or.inr ⟨rfl, hs⟩
    have hne := tail_matching_joins_ne (L.tail_mem he) hxk (hd x hxT)
    have hk := L.tail_edge_ends_internal hmax hGS hd he (Fin.rev s)
    have hkp : k ∈ p := by
      have hh : k = x ∨ k ∈ p ∨ k = y := by
        simpa only [hi, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hk
      rcases hh with hkx | hkp | hky
      · exact (hne hkx.symm).elim
      · exact hkp
      · have hxy : H.Joins e x y := by simpa only [hky] using hxk
        have hp := L.tail_edge_even_segment hmax hGS hd he hxy [] p []
          (by simpa only [List.nil_append] using hi)
        have ho := L.ear.even
        rw [hi, Nat.even_iff] at ho
        rw [Nat.even_iff] at hp
        simp only [List.length_cons, List.length_append, List.length_nil] at ho
        omega
    obtain ⟨a, b, hp⟩ := List.append_of_mem hkp
    have hi' : L.ear.interior = [] ++ x :: (a ++ k :: (b ++ [y])) := by
      simp only [hi, hp, List.nil_append, List.append_assoc, List.cons_append]
    have ha := L.tail_edge_even_segment hmax hGS hd he hxk [] a (b ++ [y]) hi'
    obtain ⟨i, hia, hvi⟩ := L.tail_edge_segment_has_hub hT hG hmax hd hdeg he hxk
      [] a (b ++ [y]) hi'
    exact ⟨a, b, k, i, e, hp, he, hxk, ha, hia, hvi⟩

/-- The reversed form of the first chord selection. -/
private theorem last_tail_chord {v x y : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    (p : List V) (hi : L.ear.interior = x :: (p ++ [y]))
    (hno : ¬ ∃ e, H.Joins e v y) :
    ∃ (a b : List V) (k : V) (e : E), p = a ++ k :: b ∧
      e ∈ G \ (L.oldEdges ∪ L.labels.toFinset) ∧ H.Joins e k y := by
  have hr : L.reverse.ear.interior = y :: (p.reverse ++ [x]) := by
    simp [reverse, OddEar.reverse, hi]
  obtain ⟨a, b, k, i, e, hp, he, hj, _, _, _⟩ :=
    L.reverse.first_tail_chord hT hG hmax hd hdeg p.reverse hr hno
  have hp' : p = b.reverse ++ k :: a.reverse := by
    have hh := congrArg List.reverse hp
    simpa only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append] using hh
  exact ⟨b.reverse, a.reverse, k, e, hp', by simpa [reverse] using he, H.joins_comm.mp hj⟩

/-- If the last internal vertex meets the hub, a first chord cycle (or a
singleton first block) and the singleton last block suffice. -/
private theorem factorCritical_hub_of_last_adjacent {v x y : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    (p : List V) (hi : L.ear.interior = x :: (p ++ [y]))
    (hvy : ∃ e, H.Joins e v y) :
    H.IsFactorCritical (insert v L.ear.interior.toFinset) := by
  have hv := L.hub_not_mem_interior hT
  have hc := L.interior_chain
  have hsingle (z : V) : H.IsFactorCritical [z].toFinset := by
    simpa using (HasOddEarConstruction.singleton (H := H) z).isFactorCritical
  by_cases hvx : ∃ e, H.Joins e v x
  · have he : Even p.length := by
      have hh := L.ear.even
      rw [hi, Nat.even_iff] at hh
      rw [Nat.even_iff]
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
    have hh := isFactorCritical_of_two_chain_blocks (H := H) (v := v) (x := x) (y := y)
      (i := x) (j := y) [x] p [y]
      (by simpa only [List.singleton_append, hi] using L.ear.nodup)
      (by simpa only [List.singleton_append, hi] using hv)
      (hsingle x) (hsingle y) (by simp) (by simp) (by simp) (by simp) hvx hvy he
      (by simpa only [hi] using hc)
    simpa only [List.singleton_append, ← hi] using hh
  · obtain ⟨a, b, k, i, e, hp, he, hxk, ha, hia, hvi⟩ :=
      L.first_tail_chord hT hG hmax hd hdeg p hi hvx
    have hfull : L.ear.interior = (x :: (a ++ [k])) ++ (b ++ [y]) := by
      simp only [hi, hp, List.cons_append, List.append_assoc, List.nil_append]
    have hn := List.nodup_append.mp (hfull ▸ L.ear.nodup)
    have hc' : (x :: (a ++ k :: (b ++ [y]))).IsChain (fun u w ↦ ∃ e, H.Joins e u w) := by
      simpa only [hi, hp, List.append_assoc, List.cons_append] using hc
    have hcs := List.isChain_cons_split.mp hc'
    have hfc := isFactorCritical_of_even_chord a hn.1 hcs.1 ha ⟨e, hxk⟩
    have hb : Even b.length := by
      have hh := L.ear.even
      rw [hfull, Nat.even_iff] at hh
      rw [Nat.even_iff] at ha ⊢
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
    have hh := isFactorCritical_of_two_chain_blocks (H := H) (v := v) (x := k) (y := y)
      (i := i) (j := y) (x :: (a ++ [k])) b [y]
      (hfull ▸ L.ear.nodup) (hfull ▸ hv) hfc (hsingle y)
      (by simp) (by simp) (by simp [hia]) (by simp) hvi hvy hb hcs.2
    exact hfull.symm ▸ hh

set_option maxHeartbeats 600000 in
/-- The two endpoint chord cycles are disjoint: otherwise their crossing
would force an odd segment at the far end to be even. -/
private theorem factorCritical_hub_of_neither_adjacent {v x y : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    (p : List V) (hi : L.ear.interior = x :: (p ++ [y]))
    (hvx : ¬ ∃ e, H.Joins e v x) (hvy : ¬ ∃ e, H.Joins e v y) :
    H.IsFactorCritical (insert v L.ear.interior.toFinset) := by
  have hGS : G ⊆ H.edgesIn T := by rw [hT, hG]
  obtain ⟨a, b, k, i, e, hp, he, hxk, ha, hia, hvi⟩ :=
    L.first_tail_chord hT hG hmax hd hdeg p hi hvx
  obtain ⟨c, d, z, f, hp', hf, hzy⟩ := L.last_tail_chord hT hG hmax hd hdeg p hi hvy
  have hbEven : Even b.length := by
    have hh := L.ear.even
    rw [hi, hp, Nat.even_iff] at hh
    rw [Nat.even_iff] at ha ⊢
    simp only [List.length_cons, List.length_append, List.length_nil] at hh
    omega
  have hz : z ∈ a ∨ z = k ∨ z ∈ b := by
    have hzp : z ∈ p := by simp [hp']
    simpa only [hp, List.mem_append, List.mem_cons] using hzp
  have hzb : z ∈ b := by
    rcases hz with hza | hzk | hzb
    · obtain ⟨s, t, hza⟩ := List.append_of_mem hza
      have hs : L.ear.interior = [] ++ x :: (s ++ z :: (t ++ k :: (b ++ y :: []))) := by
        simp only [hi, hp, hza, List.nil_append, List.append_assoc, List.cons_append]
      have hh := (L.tail_crossing_even_segments hmax hGS hd he hf hxk hzy [] s t b [] hs).2.2
      rw [Nat.even_iff] at hh hbEven
      omega
    · have hky : H.Joins f k y := by simpa only [hzk] using hzy
      have hs : L.ear.interior = (x :: a) ++ k :: (b ++ y :: []) := by
        simp only [hi, hp, List.append_assoc, List.cons_append]
      have hh := L.tail_edge_even_segment hmax hGS hd hf hky (x :: a) b [] hs
      rw [Nat.even_iff] at hh hbEven
      omega
    · exact hzb
  obtain ⟨l, m, hb⟩ := List.append_of_mem hzb
  have hs : L.ear.interior = ((x :: a) ++ k :: l) ++ z :: (m ++ y :: []) := by
    simp only [hi, hp, hb, List.append_assoc, List.cons_append]
  have hm := L.tail_edge_even_segment hmax hGS hd hf hzy ((x :: a) ++ k :: l) m [] hs
  obtain ⟨j, hjm, hvj⟩ := L.tail_edge_segment_has_hub hT hG hmax hd hdeg hf hzy
    ((x :: a) ++ k :: l) m [] hs
  have hfull : L.ear.interior = (x :: (a ++ [k])) ++ (l ++ (z :: (m ++ [y]))) := by
    simp only [hi, hp, hb, List.append_assoc, List.cons_append, List.nil_append]
  have hn := List.nodup_append.mp (hfull ▸ L.ear.nodup)
  have hn' := List.nodup_append.mp hn.2.1
  have hc : (x :: (a ++ k :: (l ++ z :: (m ++ [y])))).IsChain
      (fun u w ↦ ∃ e, H.Joins e u w) := by
    simpa only [hi, hp, hb, List.append_assoc, List.cons_append] using L.interior_chain
  have hcA := List.isChain_cons_split.mp hc
  have hcB := List.isChain_cons_split.mp hcA.2
  have hfcA := isFactorCritical_of_even_chord a hn.1 hcA.1 ha ⟨e, hxk⟩
  have hfcB := isFactorCritical_of_even_chord m hn'.2.1 hcB.2 hm ⟨f, hzy⟩
  have hl : Even l.length := by
    rw [hb, Nat.even_iff] at hbEven
    rw [Nat.even_iff] at hm ⊢
    simp only [List.length_append, List.length_cons] at hbEven
    omega
  have hh := isFactorCritical_of_two_chain_blocks (H := H) (v := v) (x := k) (y := z)
    (i := i) (j := j) (x :: (a ++ [k])) l (z :: (m ++ [y]))
    (hfull ▸ L.ear.nodup) (hfull ▸ L.hub_not_mem_interior hT) hfcA hfcB
    (by simp) (by simp) (by simp [hia]) (by simp [hjm]) hvi hvj hl hcB.1
  exact hfull.symm ▸ hh

/-- Proposition 5.10: the internal vertices of a nontrivial last nonmatching
ear together with the deleted hub induce a factor-critical shore. -/
theorem factorCritical_hub {v : V}
    (hT : T = Finset.univ.erase v) (hG : G = H.edgesIn (Finset.univ.erase v))
    (hmax : H.IsMaximumOddEarIndex M T G q)
    (hd : ∀ w ∈ T, H.degreeIn M w ≤ 1) (hdeg : ∀ w ∈ T, 3 ≤ H.degree w)
    (hne : L.ear.interior ≠ []) :
    H.IsFactorCritical (insert v L.ear.interior.toFinset) := by
  cases hi : L.ear.interior with
  | nil => exact (hne hi).elim
  | cons x t =>
    cases ht : t.reverse with
    | nil =>
      have ht' : t = [] := List.reverse_eq_nil_iff.mp ht
      have hh := L.ear.even
      simp [hi, ht'] at hh
    | cons y p =>
      have hi' : L.ear.interior = x :: (p.reverse ++ [y]) := by
        have hh := congrArg List.reverse ht
        simpa only [hi, List.reverse_reverse, List.reverse_cons] using congrArg (List.cons x) hh
      by_cases hvy : ∃ e, H.Joins e v y
      · simpa only [hi] using
          L.factorCritical_hub_of_last_adjacent hT hG hmax hd hdeg p.reverse hi' hvy
      · by_cases hvx : ∃ e, H.Joins e v x
        · have hr : L.reverse.ear.interior = y :: (p ++ [x]) := by
            simp [reverse, OddEar.reverse, hi']
          have hh := L.reverse.factorCritical_hub_of_last_adjacent hT hG hmax hd hdeg p hr hvx
          simpa [reverse, OddEar.reverse, hi] using hh
        · simpa only [hi] using
            L.factorCritical_hub_of_neither_adjacent hT hG hmax hd hdeg p.reverse hi' hvx hvy

end LastOutsideOddEar

end GraphPuzzles.LoopMultigraph
