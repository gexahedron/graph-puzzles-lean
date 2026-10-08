import GraphPuzzles.Matching.PathMatching

/-! Connectivity between the holes of two near-perfect matchings. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
/-- Once one end of a joining edge is specified, its other end is determined. -/
theorem Joins.endAt_rev_of_end {e : E} {a b : V} (he : H.Joins e a b)
    {k : Fin 2} (hk : H.endAt e k = a) : H.endAt e (Fin.rev k) = b := by
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases k <;> simp_all

omit [DecidableEq E] in
/-- A vertex covered by a matching has only one neighbour in its edges. -/
theorem IsPerfectMatchingOn.joins_unique {S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn S M) {e f : E} (he : e ∈ M) (hf : f ∈ M)
    {a b c : V} (heb : H.Joins e a b) (hfc : H.Joins f a c) : b = c := by
  obtain ⟨i, hi⟩ := heb.exists_end
  obtain ⟨j, hj⟩ := hfc.exists_end
  have ha : a ∈ S := hi ▸ hM.1 e he i
  have hh := eq_incidence_of_degreeIn_one (hM.2 a ha) he hf hi hj
  have ho := congrArg (fun p : E × Fin 2 ↦ H.endAt p.1 (Fin.rev p.2)) hh
  simpa only [heb.endAt_rev_of_end hi, hfc.endAt_rev_of_end hj] using ho

omit [DecidableEq E] in
/-- A submatching that covers a shore makes that shore closed under the
edges of the larger matching. -/
theorem IsPerfectMatchingOn.closed_of_subset {S T : Finset V} {P M : Finset E}
    (hP : H.IsPerfectMatchingOn T P) (hM : H.IsPerfectMatchingOn S M) (hPM : P ⊆ M)
    (a b : V) (hab : ∃ e ∈ M, H.Joins e a b) : a ∈ T ↔ b ∈ T := by
  have step {a b : V} (hab : ∃ e ∈ M, H.Joins e a b) (ha : a ∈ T) : b ∈ T := by
    obtain ⟨e, heM, heab⟩ := hab
    obtain ⟨i, hi⟩ := heab.exists_end
    have hp : 0 < H.degreeIn P a := by rw [hP.2 a ha]; decide
    obtain ⟨⟨f, k⟩, hf⟩ := Finset.card_pos.mp hp
    obtain ⟨hfprod, hfk⟩ := Finset.mem_filter.mp hf
    have hfP := (Finset.mem_product.mp hfprod).1
    have haS := hi ▸ hM.1 e heM i
    have hef : e = f := congrArg Prod.fst
      (eq_incidence_of_degreeIn_one (hM.2 a haS) heM (hPM hfP) hi hfk)
    have heP : e ∈ P := hef.symm ▸ hfP
    exact heab.endAt_rev_of_end hi ▸ hP.1 e heP (Fin.rev i)
  exact ⟨step hab, step (by
    obtain ⟨e, heM, heab⟩ := hab
    exact ⟨e, heM, H.joins_comm.mp heab⟩)⟩

/-- The two omitted vertices of near-perfect matchings lie in the same
component of their union. Otherwise restriction to one component gives
perfect matchings on vertex sets whose cardinalities differ by one. -/
theorem IsPerfectMatchingOn.reachable_holes {u v : V} {M N : Finset E}
    (hM : H.IsPerfectMatchingOn (Finset.univ.erase u) M)
    (hN : H.IsPerfectMatchingOn (Finset.univ.erase v) N) :
    (H.restrictEdges (M ∪ N)).underlying.Reachable u v := by
  classical
  let G := (H.restrictEdges (M ∪ N)).underlying
  let R : Finset V := Finset.univ.filter fun w ↦ G.Reachable u w
  have hu : u ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .rfl⟩
  have hc (e : E) (he : e ∈ M ∪ N) (k : Fin 2) (hk : H.endAt e k ∈ R) :
      H.endAt e (Fin.rev k) ∈ R := by
    by_cases hh : H.endAt e k = H.endAt e (Fin.rev k)
    · exact hh ▸ hk
    · have ha : G.Adj (H.endAt e k) (H.endAt e (Fin.rev k)) := by
        refine ⟨hh, ⟨e, he⟩, ?_⟩
        fin_cases k
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hk).2).trans ha.reachable⟩
  by_contra hv
  have hvR : v ∉ R := fun h ↦ hv (Finset.mem_filter.mp h).2
  have hMR := hM.restrict (S := R.erase u)
    (fun w hw ↦ Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ _⟩)
    (fun e he k hk ↦ Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hM.1 e he _)).1,
      hc e (Finset.mem_union_left _ he) k (Finset.mem_of_mem_erase hk)⟩)
  have hNR := hN.restrict (S := R)
    (fun w hw ↦ Finset.mem_erase.mpr ⟨fun hh ↦ hvR (hh ▸ hw), Finset.mem_univ _⟩)
    (fun e he k hk ↦ hc e (Finset.mem_union_right _ he) k hk)
  have heM := hMR.card_even
  have heN := hNR.card_even
  have hcard := Finset.card_erase_add_one hu
  rw [Nat.even_iff] at heM heN
  omega

/-- A factor-critical graph is connected: any two vertices are the holes
of two near-perfect matchings, and their union connects those holes. -/
theorem IsFactorCritical.isConnected (hfc : H.IsFactorCritical Finset.univ) :
    H.IsConnected := by
  intro c hc u v
  obtain ⟨M, hM⟩ := hfc u (Finset.mem_univ _)
  obtain ⟨N, hN⟩ := hfc v (Finset.mem_univ _)
  obtain ⟨p⟩ := hM.reachable_holes hN
  have hed {a b : V} (ha : (H.restrictEdges (M ∪ N)).underlying.Adj a b) : c a = c b := by
    obtain ⟨e, he⟩ := ha.2
    have hh := hc e.1
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact h0 ▸ h1 ▸ hh
    · exact (h0 ▸ h1 ▸ hh).symm
  clear hM hN
  induction p with
  | nil => rfl
  | cons h p ih => exact (hed h).trans ih

end GraphPuzzles.LoopMultigraph
