import GraphPuzzles.Matching.AlternatingPrefix
import GraphPuzzles.Ears.OddEar
import GraphPuzzles.Cuts.SeparatingCutTheory

/-! Extending a shore closed under a fixed near-perfect matching by an odd ear. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype V] in
private theorem exists_first_mem (S : Finset V) (l : List V) (h : ∃ x ∈ l, x ∈ S) :
    ∃ L t R, l = L ++ t :: R ∧ t ∈ S ∧ ∀ x ∈ L, x ∉ S := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a ∈ S
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · have hx : ∃ x ∈ l, x ∈ S := by
        obtain ⟨x, hx, hxS⟩ := h
        exact ⟨x, (List.mem_cons.mp hx).resolve_left (fun hh ↦ ha (hh ▸ hxS)), hxS⟩
      obtain ⟨L, t, R, heq, ht, hout⟩ := ih hx
      refine ⟨a :: L, t, R, by simp [heq], ht, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hout x hx

/-- In a factor-critical graph, every proper shore containing the omitted
vertex and closed under a fixed near-perfect matching can be enlarged by
an odd ear while preserving closure under that same matching. -/
theorem IsFactorCritical.exists_oddEar_closed (hfc : H.IsFactorCritical Finset.univ)
    {r : V} {M : Finset E} (hM : H.IsPerfectMatchingOn (Finset.univ.erase r) M)
    {S : Finset V} (hr : r ∈ S)
    (hclosed : ∀ a b, (∃ e ∈ M, H.Joins e a b) → (a ∈ S ↔ b ∈ S))
    (hproper : (Finset.univ \ S).Nonempty) :
    ∃ A : H.OddEar S, S ⊂ A.vertices ∧
      ∀ a b, (∃ e ∈ M, H.Joins e a b) → (a ∈ A.vertices ↔ b ∈ A.vertices) := by
  obtain ⟨e, he⟩ := hfc.isConnected.dangling_nonempty ⟨r, hr⟩ hproper
  have hab : ∃ a ∈ S, ∃ b, b ∉ S ∧ H.Joins e a b := by
    have hd := mem_dangling.mp he
    by_cases h0 : H.endAt e 0 ∈ S
    · exact ⟨H.endAt e 0, h0, H.endAt e 1, fun h1 ↦ hd (by simp [h0, h1]),
        Or.inl ⟨rfl, rfl⟩⟩
    · have h1 : H.endAt e 1 ∈ S := by tauto
      exact ⟨H.endAt e 1, h1, H.endAt e 0, h0, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨a, haS, b, hbS, heab⟩ := hab
  obtain ⟨N, hN⟩ := hfc b (Finset.mem_univ _)
  obtain ⟨p, hp⟩ := (hM.reachable_holes hN).symm.exists_isPath
  obtain ⟨L, t, R, hs, ht, hout⟩ := exists_first_mem S p.support ⟨r, p.end_mem_support, hr⟩
  have hpre : L ++ [t] <+: p.support := ⟨R, by simp [hs, List.append_assoc]⟩
  have hn := hpre.sublist.nodup hp.support_nodup
  have hc : (L ++ [t]).IsChain (fun x y ↦ ∃ f ∈ M ∪ N, H.Joins f x y) :=
    (p.isChain_adj_support.prefix hpre).imp fun _ _ h ↦ by
      obtain ⟨f, hf⟩ := h.2
      exact ⟨f.1, f.2, hf⟩
  have hLhead : L.head? = some b := by
    have hh : p.support.head? = some b := by rw [← p.cons_tail_support]; rfl
    rw [hs] at hh
    cases L with
    | nil =>
      have htb : t = b := Option.some.inj hh
      exact (hbS (htb ▸ ht)).elim
    | cons x L => exact hh
  have hhead : (L ++ [t]).head? = some b := by simp [List.head?_append, hLhead]
  have hfirst : ∀ x ∈ (L ++ [t]).head?, ∀ y ∈ (L ++ [t]).tail,
      ¬ ∃ f ∈ N, H.Joins f x y := by
    intro x hx y _ hxy
    have hxb : x = b := (show b = x from by
      simpa only [hhead, Option.mem_some_iff] using hx).symm
    obtain ⟨f, hfN, hfxy⟩ := hxy
    obtain ⟨k, hk⟩ := hfxy.exists_end
    have hh := hN.1 f hfN k
    exact (Finset.mem_erase.mp hh).1 (hk.trans hxb)
  obtain ⟨P, hP, hPM⟩ := matchingOn_prefix_of_closed_shore hM hN hclosed L ht hn hc hout hfirst
  have hnL := (List.nodup_append.mp hn).1
  have hLeven : Even L.length := by
    simpa only [List.toFinset_card_of_nodup hnL] using hP.card_even
  let A : H.OddEar S := {
    start := a
    finish := t
    interior := L
    start_mem := haS
    finish_mem := ht
    nodup := hnL
    avoids := hout
    even := hLeven
    chain := (hc.imp fun _ _ h ↦ by obtain ⟨f, _, hf⟩ := h; exact ⟨f, hf⟩).cons (by
      intro x hx
      have hxb : x = b := (show b = x from by
        simpa only [hhead, Option.mem_some_iff] using hx).symm
      exact ⟨e, hxb.symm ▸ heab⟩) }
  refine ⟨A, ?_, ?_⟩
  · apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_union_left, fun heq ↦ ?_⟩
    have hbL : b ∈ L.toFinset := List.mem_toFinset.mpr
      (List.mem_of_mem_head? (by simp [hLhead]))
    exact hbS (heq.symm ▸ Finset.mem_union_right S hbL)
  · intro x y hxy
    have hS := hclosed x y hxy
    have hL := hP.closed_of_subset hM hPM x y hxy
    change x ∈ S ∪ L.toFinset ↔ y ∈ S ∪ L.toFinset
    simp only [Finset.mem_union]
    tauto

/-- A nonempty factor-critical graph has an odd-ear construction covering
every vertex. The proof extends shores closed under a fixed near-perfect
matching. -/
theorem IsFactorCritical.hasOddEarConstruction (hfc : H.IsFactorCritical Finset.univ)
    (r : V) : H.HasOddEarConstruction Finset.univ := by
  classical
  obtain ⟨M, hM⟩ := hfc r (Finset.mem_univ _)
  let C : Finset (Finset V) := Finset.univ.filter fun S ↦
    H.HasOddEarConstruction S ∧ r ∈ S ∧
      ∀ a b, (∃ e ∈ M, H.Joins e a b) → (a ∈ S ↔ b ∈ S)
  have hstart : {r} ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, .singleton r,
      Finset.mem_singleton_self _, ?_⟩
    intro a b hab
    obtain ⟨e, heM, heab⟩ := hab
    obtain ⟨i, hi⟩ := heab.exists_end
    obtain ⟨j, hj⟩ := (H.joins_comm.mp heab).exists_end
    have har : a ≠ r := fun hh ↦
      (Finset.mem_erase.mp (hM.1 e heM i)).1 (hi.trans hh)
    have hbr : b ≠ r := fun hh ↦
      (Finset.mem_erase.mp (hM.1 e heM j)).1 (hj.trans hh)
    simp [har, hbr]
  obtain ⟨S, hSC, hmax⟩ := C.exists_max_image Finset.card ⟨{r}, hstart⟩
  obtain ⟨hbuild, hr, hclosed⟩ := (Finset.mem_filter.mp hSC).2
  suffices hS : S = Finset.univ from hS ▸ hbuild
  by_contra hS
  have hp : (Finset.univ \ S).Nonempty := Finset.sdiff_nonempty.mpr fun h ↦
    hS (Finset.Subset.antisymm (Finset.subset_univ _) h)
  obtain ⟨A, hSA, hAclosed⟩ := hfc.exists_oddEar_closed hM hr hclosed hp
  have hAC : A.vertices ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hbuild.attach A, (Finset.ssubset_iff_subset_ne.mp hSA).1 hr, hAclosed⟩
  exact (Nat.not_lt_of_ge (hmax A.vertices hAC)) (Finset.card_lt_card hSA)

/-- The vertex-covering form of the odd-ear characterization. A root is
explicit because the empty vertex type has no singleton starting shore. -/
theorem isFactorCritical_iff_hasOddEarConstruction (r : V) :
    H.IsFactorCritical Finset.univ ↔ H.HasOddEarConstruction Finset.univ :=
  ⟨fun h ↦ h.hasOddEarConstruction r, HasOddEarConstruction.isFactorCritical⟩

end GraphPuzzles.LoopMultigraph
