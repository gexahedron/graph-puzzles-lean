import GraphPuzzles.Bricks.Brick

/-! Induced endpoint graphs and matchings on a specified vertex set. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The induced graph retains exactly the vertices of `S` and the edges internal to `S`. -/
def induced (H : LoopMultigraph V E) (S : Finset V) : LoopMultigraph S (H.edgesIn S) :=
  ⟨fun e k ↦ ⟨H.endAt e.1 k, (mem_edgesIn.mp e.2) k⟩⟩

omit [DecidableEq E] in
theorem induced_endAt (S : Finset V) (e : H.edgesIn S) (k : Fin 2) :
    ((H.induced S).endAt e k).1 = H.endAt e.1 k := rfl

theorem induced_degreeIn (S : Finset V) (M : Finset (H.edgesIn S)) (v : S) :
    H.degreeIn (M.image Subtype.val) v.1 = (H.induced S).degreeIn M v := by
  unfold degreeIn
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Subtype.ext_iff, induced_endAt]
  · intro e _ f _ h
    exact Subtype.ext h

/-- Restrict an original edge set to the induced graph. -/
def inducedMatching (S : Finset V) (M : Finset E) : Finset (H.edgesIn S) :=
  Finset.univ.filter fun e ↦ e.1 ∈ M

@[simp] theorem mem_inducedMatching (S : Finset V) (M : Finset E) (e : H.edgesIn S) :
    e ∈ H.inducedMatching S M ↔ e.1 ∈ M := by simp [inducedMatching]

theorem image_inducedMatching (S : Finset V) (M : Finset E) (hM : M ⊆ H.edgesIn S) :
    (H.inducedMatching S M).image Subtype.val = M := by
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (mem_inducedMatching S M f).mp hf
  · intro he
    exact Finset.mem_image.mpr ⟨⟨e, hM he⟩, (mem_inducedMatching S M _).mpr he, rfl⟩

/-- A matching on a shore is a perfect matching of its induced graph. -/
theorem IsPerfectMatchingOn.induced {S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn S M) :
    (H.induced S).IsPerfectMatching (H.inducedMatching S M) := by
  intro v
  rw [← induced_degreeIn, image_inducedMatching S M
    (fun e he ↦ mem_edgesIn.mpr (hM.1 e he))]
  exact hM.2 v.1 v.2

/-- A matching in an induced graph gives a matching on the corresponding original vertices. -/
theorem IsPerfectMatchingOn.of_induced {S : Finset V} {T : Finset S}
    {M : Finset (H.edgesIn S)} (hM : (H.induced S).IsPerfectMatchingOn T M) :
    H.IsPerfectMatchingOn (T.image Subtype.val) (M.image Subtype.val) := by
  constructor
  · intro e he k
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨(H.induced S).endAt f k, hM.1 f hf k, rfl⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [induced_degreeIn]
    exact hM.2 w hw

/-- Lift a full perfect matching of an induced graph. -/
theorem IsPerfectMatching.of_induced {S : Finset V} {M : Finset (H.edgesIn S)}
    (hM : (H.induced S).IsPerfectMatching M) :
    H.IsPerfectMatchingOn S (M.image Subtype.val) := by
  constructor
  · intro e he k
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact (mem_edgesIn.mp f.2) k
  · intro v hv
    exact (induced_degreeIn S M ⟨v, hv⟩).trans (hM ⟨v, hv⟩)

theorem exists_perfectMatching_induced_iff (S : Finset V) :
    (∃ M, (H.induced S).IsPerfectMatching M) ↔ ∃ M, H.IsPerfectMatchingOn S M :=
  ⟨fun ⟨M, hM⟩ ↦ ⟨M.image Subtype.val, hM.of_induced⟩,
    fun ⟨M, hM⟩ ↦ ⟨H.inducedMatching S M, hM.induced⟩⟩

theorem IsPerfectMatchingOn.card_even {S : Finset V} {M : Finset E}
    (hM : H.IsPerfectMatchingOn S M) : Even S.card := by
  simpa only [Fintype.card_coe] using hM.induced.isFractional.card_even

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A vertex set of the induced graph, viewed in the original graph, has the same size. -/
theorem card_image_induced_vertices {S : Finset V} (T : Finset S) :
    (T.image Subtype.val).card = T.card :=
  Finset.card_image_of_injective T Subtype.val_injective

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem image_induced_vertices_subset {S : Finset V} (T : Finset S) :
    T.image Subtype.val ⊆ S := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_image_induced_vertices {S : Finset V} (T : Finset S) (v : S) :
    v.1 ∈ T.image Subtype.val ↔ v ∈ T := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
    exact (Subtype.ext he : w = v) ▸ hw
  · intro h
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

namespace ComponentFamily

variable {S : Finset V} {B : Finset S} (F : (H.induced S).ComponentFamily B)

omit [DecidableEq E] in
/-- Lift a component family from an induced graph; all omitted original vertices
are placed in the separator. -/
def of_induced : H.ComponentFamily ((Finset.univ \ S) ∪ B.image Subtype.val) where
  parts := F.parts.image fun Q ↦ Q.image Subtype.val
  nonempty := by
    intro Q hQ
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    exact (F.nonempty R hR).image _
  avoid := by
    intro Q hQ w hw hz
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rcases Finset.mem_union.mp hz with hs | hb
    · exact (Finset.mem_sdiff.mp hs).2 v.2
    · exact F.avoid R hR v hv ((mem_image_induced_vertices B v).mp hb)
  closed := by
    intro Q hQ e k hk hn
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    have h0 : H.endAt e k ∈ S := image_induced_vertices_subset R hk
    have h1 : H.endAt e (Fin.rev k) ∈ S := by
      by_contra h
      exact hn (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))
    have he : e ∈ H.edgesIn S := by
      apply mem_edgesIn.mpr
      intro j
      fin_cases k <;> fin_cases j <;> assumption
    let f : H.edgesIn S := ⟨e, he⟩
    have hk' : (H.induced S).endAt f k ∈ R :=
      (mem_image_induced_vertices R _).mp hk
    have hn' : (H.induced S).endAt f (Fin.rev k) ∉ B := fun h ↦
      hn (Finset.mem_union_right _ ((mem_image_induced_vertices B _).mpr h))
    exact (mem_image_induced_vertices R _).mpr (F.closed R hR f k hk' hn')
  pairwise := by
    intro Q hQ R hR hne
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
    have hne' : Q' ≠ R' := fun h ↦ hne (congrArg (Finset.image Subtype.val) h)
    apply Finset.disjoint_left.mpr
    intro w hwQ hwR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwQ
    exact Finset.disjoint_left.mp (F.pairwise Q' hQ' R' hR' hne') hv
      ((mem_image_induced_vertices R' v).mp hwR)
  cover := by
    intro w hw
    have hwS : w ∈ S := by
      by_contra hn
      exact hw (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))
    have hwB : (⟨w, hwS⟩ : S) ∉ B := fun h ↦ hw
      (Finset.mem_union_right _ ((mem_image_induced_vertices B ⟨w, hwS⟩).mpr h))
    obtain ⟨Q, hQ, hv⟩ := F.cover ⟨w, hwS⟩ hwB
    exact ⟨Q.image Subtype.val, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩,
      (mem_image_induced_vertices Q ⟨w, hwS⟩).mpr hv⟩

omit [DecidableEq E] in
theorem of_induced_odd : F.of_induced.odd = F.odd.image (Finset.image Subtype.val) := by
  ext Q
  constructor
  · intro h
    obtain ⟨hp, ho⟩ := F.of_induced.mem_odd.mp h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hp
    rw [card_image_induced_vertices] at ho
    exact Finset.mem_image.mpr ⟨R, F.mem_odd.mpr ⟨hR, ho⟩, rfl⟩
  · intro h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp h
    apply F.of_induced.mem_odd.mpr
    refine ⟨Finset.mem_image.mpr ⟨R, (F.mem_odd.mp hR).1, rfl⟩, ?_⟩
    rw [card_image_induced_vertices]
    exact (F.mem_odd.mp hR).2

omit [DecidableEq E] in
theorem of_induced_odd_card : F.of_induced.odd.card = F.odd.card := by
  rw [F.of_induced_odd]
  exact Finset.card_image_of_injective _ (Finset.image_injective Subtype.val_injective)

end ComponentFamily

/-- Tutte's obstruction on an arbitrary induced shore, expressed in the original graph. -/
theorem exists_componentFamily_of_no_matchingOn (S : Finset V)
    (hno : ¬ ∃ M, H.IsPerfectMatchingOn S M) :
    ∃ B ⊆ S, ∃ F : H.ComponentFamily ((Finset.univ \ S) ∪ B), B.card < F.odd.card := by
  classical
  have hn : ¬ ∀ (B : Finset S) (F : (H.induced S).ComponentFamily B), F.odd.card ≤ B.card := by
    intro h
    exact hno ((exists_perfectMatching_induced_iff S).mp (exists_perfectMatching_of_component_bound h))
  push Not at hn
  obtain ⟨B, F, hlt⟩ := hn
  exact ⟨B.image Subtype.val, image_induced_vertices_subset B, F.of_induced,
    by simpa only [card_image_induced_vertices, F.of_induced_odd_card] using hlt⟩

/-- On an even shore, Tutte parity strengthens the obstruction by two. -/
theorem exists_componentFamily_of_no_matchingOn_even (S : Finset V) (heven : Even S.card)
    (hno : ¬ ∃ M, H.IsPerfectMatchingOn S M) :
    ∃ B ⊆ S, ∃ F : H.ComponentFamily ((Finset.univ \ S) ∪ B), B.card + 2 ≤ F.odd.card := by
  obtain ⟨B, hBS, F, hlt⟩ := exists_componentFamily_of_no_matchingOn S hno
  refine ⟨B, hBS, F, ?_⟩
  have hpar := F.odd_card_mod_two
  have heq : Finset.univ \ ((Finset.univ \ S) ∪ B) = S \ B := by
    ext v
    simp
  rw [heq, Finset.card_sdiff_of_subset hBS] at hpar
  have hle := Finset.card_le_card hBS
  rw [Nat.even_iff] at heven
  omega

end GraphPuzzles.LoopMultigraph
