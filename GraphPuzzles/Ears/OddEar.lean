import GraphPuzzles.Matching.PathMatching

/-! Odd ears preserve factor-criticality (the extension step of Proposition 5.3). -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- An odd ear relative to an old vertex set. Its endpoints belong to the
old set; its even number of distinct internal vertices avoid that set.
The endpoints may coincide, allowing a closed odd ear. Consecutive vertices
are joined by labelled edges of the ambient multigraph. -/
structure OddEar (H : LoopMultigraph V E) (S : Finset V) where
  start : V
  finish : V
  interior : List V
  start_mem : start ∈ S
  finish_mem : finish ∈ S
  nodup : interior.Nodup
  avoids : ∀ w ∈ interior, w ∉ S
  even : Even interior.length
  chain : (start :: interior ++ [finish]).IsChain (fun a b ↦ ∃ e, H.Joins e a b)

namespace OddEar

variable {S : Finset V} (A : H.OddEar S)

/-- The old shore together with the ear's interior. -/
def vertices : Finset V := S ∪ A.interior.toFinset

/-- Reversing an ear exchanges its endpoints and reverses its interior. -/
def reverse : H.OddEar S where
  start := A.finish
  finish := A.start
  interior := A.interior.reverse
  start_mem := A.finish_mem
  finish_mem := A.start_mem
  nodup := by simpa only [List.nodup_reverse] using A.nodup
  avoids := fun w hw ↦ A.avoids w (List.mem_reverse.mp hw)
  even := by simpa only [List.length_reverse] using A.even
  chain := by
    have hc := List.isChain_reverse.mpr (A.chain.imp fun _ _ h ↦
      h.imp fun _ he ↦ H.joins_comm.mp he)
    simpa only [List.reverse_cons, List.reverse_append, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons_append] using hc

omit [DecidableEq E] in
@[simp] theorem reverse_vertices : A.reverse.vertices = A.vertices := by
  simp [vertices, reverse]

/-- Pair consecutive internal vertices, leaving both attachment vertices
available for a matching of the old shore. -/
theorem exists_matchingOn_interior : ∃ M, H.IsPerfectMatchingOn A.interior.toFinset M :=
  exists_matchingOn_of_even_chain A.interior A.nodup A.chain.tail.left_of_append A.even

private theorem matching_after_delete_even_prefix (hfc : H.IsFactorCritical S)
    {w : V} {L R : List V} (hsplit : A.interior = L ++ w :: R) (hL : Even L.length) :
    ∃ M, H.IsPerfectMatchingOn (A.vertices.erase w) M := by
  have hn := List.nodup_append.mp (hsplit ▸ A.nodup)
  have hnR := List.nodup_cons.mp hn.2.1
  have hw : w ∈ A.interior := by simp [hsplit]
  have havoid (x : V) (hx : x ∈ L ∨ x ∈ R) : x ∉ S := by
    apply A.avoids x
    simp only [hsplit, List.mem_append, List.mem_cons]
    tauto
  have hc : (L ++ w :: (R ++ [A.finish])).IsChain (fun a b ↦ ∃ e, H.Joins e a b) := by
    simpa only [hsplit, List.append_assoc, List.cons_append, List.tail_cons] using A.chain.tail
  have hR : Even (R ++ [A.finish]).length := by
    have he := A.even
    rw [hsplit] at he
    rw [Nat.even_iff] at he hL ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at he ⊢
    omega
  have hnR' : (R ++ [A.finish]).Nodup := List.nodup_append.mpr
    ⟨hnR.2, by simp, fun x hx y hy hxy ↦
      havoid x (Or.inr hx) (hxy.symm ▸ (List.mem_singleton.mp hy).symm ▸ A.finish_mem)⟩
  obtain ⟨P, hP⟩ := exists_matchingOn_of_even_chain L hn.1 hc.left_of_append hL
  obtain ⟨Q, hQ⟩ := exists_matchingOn_of_even_chain (R ++ [A.finish]) hnR'
    hc.right_of_append.tail hR
  have hd : Disjoint L.toFinset (R ++ [A.finish]).toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxL := List.mem_toFinset.mp hx
    rcases List.mem_append.mp (List.mem_toFinset.mp hx') with hxR | hxb
    · exact hn.2.2 x hxL x (List.mem_cons_of_mem _ hxR) rfl
    · exact havoid x (Or.inl hxL) ((List.mem_singleton.mp hxb).symm ▸ A.finish_mem)
  have heq : L.toFinset ∪ (R ++ [A.finish]).toFinset =
      insert A.finish (L.toFinset ∪ R.toFinset) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      List.mem_append, List.mem_singleton]
    tauto
  have hPQ : H.IsPerfectMatchingOn (insert A.finish (L.toFinset ∪ R.toFinset)) (P ∪ Q) :=
    heq ▸ hP.union hQ hd
  have hST : Disjoint S (L.toFinset ∪ R.toFinset) := by
    apply Finset.disjoint_right.mpr
    intro x hx hxS
    exact havoid x (by simpa only [Finset.mem_union, List.mem_toFinset] using hx) hxS
  obtain ⟨M, hM⟩ := hfc.matchingOn_union_of_matchingOn_insert A.finish_mem hST hPQ
  have hsets : S ∪ (L.toFinset ∪ R.toFinset) = A.vertices.erase w := by
    ext x
    have hws := A.avoids w hw
    have hwL : w ∉ L := fun h ↦ hn.2.2 w h w (by simp) rfl
    have hwR : w ∉ R := hnR.1
    simp only [vertices, hsplit, Finset.mem_erase, Finset.mem_union,
      List.mem_toFinset, List.mem_append, List.mem_cons]
    by_cases hxw : x = w
    · subst x
      simp [hws, hwL, hwR]
    · tauto
  exact ⟨M, hsets ▸ hM⟩

/-- Delete an internal vertex and pair each remaining segment from the
appropriate endpoint. Exactly one old endpoint is used by the ear matching. -/
theorem exists_matchingOn_delete_interior (hfc : H.IsFactorCritical S)
    {w : V} (hw : w ∈ A.interior) :
    ∃ M, H.IsPerfectMatchingOn (A.vertices.erase w) M := by
  obtain ⟨L, R, hs⟩ := List.append_of_mem hw
  by_cases hL : Even L.length
  · exact A.matching_after_delete_even_prefix hfc hs hL
  · have hR : Even R.length := by
      have he := A.even
      rw [hs] at he
      rw [Nat.even_iff] at he hL ⊢
      simp only [List.length_append, List.length_cons] at he
      omega
    have hs' : A.reverse.interior = R.reverse ++ w :: L.reverse := by
      simp only [reverse, hs, List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append]
    have hr := A.reverse.matching_after_delete_even_prefix hfc hs'
      (by simpa only [List.length_reverse] using hR)
    simpa only [reverse_vertices] using hr

/-- Attaching an odd open or closed ear to a factor-critical shore preserves
factor-criticality. Extra ambient edges do not affect the construction. -/
theorem isFactorCritical (hfc : H.IsFactorCritical S) : H.IsFactorCritical A.vertices := by
  intro w hw
  by_cases hwS : w ∈ S
  · obtain ⟨P, hP⟩ := hfc w hwS
    obtain ⟨Q, hQ⟩ := A.exists_matchingOn_interior
    have hd : Disjoint (S.erase w) A.interior.toFinset := by
      apply Finset.disjoint_right.mpr
      intro x hx hxS
      exact A.avoids x (List.mem_toFinset.mp hx) (Finset.mem_of_mem_erase hxS)
    have hwi : w ∉ A.interior.toFinset := fun h ↦ A.avoids w (List.mem_toFinset.mp h) hwS
    have heq : S.erase w ∪ A.interior.toFinset = A.vertices.erase w := by
      ext x
      simp only [vertices, Finset.mem_union, Finset.mem_erase]
      by_cases hxw : x = w
      · subst x
        simp [hwi]
      · tauto
    exact ⟨P ∪ Q, heq ▸ hP.union hQ hd⟩
  · exact A.exists_matchingOn_delete_interior hfc
      (List.mem_toFinset.mp ((Finset.mem_union.mp hw).resolve_left hwS))

end OddEar

/-- A shore obtained from a single vertex by finitely many odd-ear
attachments. Ambient edges not used by the construction are allowed. -/
inductive HasOddEarConstruction (H : LoopMultigraph V E) : Finset V → Prop
  | singleton (v : V) : HasOddEarConstruction H {v}
  | attach {S : Finset V} (old : HasOddEarConstruction H S) (ear : H.OddEar S) :
      HasOddEarConstruction H ear.vertices

/-- The converse direction used in Proposition 5.3: a finite odd-ear
construction from one vertex produces a factor-critical shore. -/
theorem HasOddEarConstruction.isFactorCritical {S : Finset V}
    (h : H.HasOddEarConstruction S) : H.IsFactorCritical S := by
  induction h with
  | singleton v =>
    intro w hw
    have hwv := Finset.mem_singleton.mp hw
    subst w
    exact ⟨∅, by simp [IsPerfectMatchingOn]⟩
  | attach _ ear ih => exact ear.isFactorCritical ih

end GraphPuzzles.LoopMultigraph
