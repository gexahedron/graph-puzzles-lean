import GraphPuzzles.Reduction.Removable.RemovableContractionBasics
import GraphPuzzles.Reduction.Removable.RemovableClass

/-! Transport removable edge classes through separating-cut contractions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The removable-class alternative with its prescribed matching and hub. -/
def HasAvoidingRemovableClass (H : LoopMultigraph V E) (v : V) (M : Finset E) : Prop :=
  ∃ e, e ∉ M ∧ (∀ k, H.endAt e k ≠ v) ∧
    (H.IsRemovable e ∨ ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
      H.IsRemovableDoubleton e f)

/-- Retaining every edge changes only the edge subtype. -/
def restrictEdgesUnivIso : EndpointIso (H.restrictEdges Finset.univ) H where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.subtypeUnivEquiv (fun e ↦ Finset.mem_univ e)
  endEquiv _ := Equiv.refl _
  map_endAt _ _ := rfl

/-- Edge restriction preserves matching-coveredness when both contracted
restrictions are matching covered. -/
theorem isMatchingCovered_of_contract_restrictions (S : Finset E) (X : Finset V)
    (hXC : (Finset.univ \ X).Nonempty)
    (hl : ((H.contract X).restrictEdges
      (Finset.univ.filter fun e ↦ e.1 ∈ S)).IsMatchingCovered)
    (hr : ((H.contract (Finset.univ \ X)).restrictEdges
      (Finset.univ.filter fun e ↦ e.1 ∈ S)).IsMatchingCovered) :
    (H.restrictEdges S).IsMatchingCovered := by
  exact (show (H.restrictEdges S).IsSeparatingCut X from
    ⟨(restrictContractIso S X).symm.isMatchingCovered hl,
      (restrictContractIso S (Finset.univ \ X)).symm.isMatchingCovered hr⟩).isMatchingCovered hXC

/-- Deleting a pair of retained edges commutes with contraction. -/
def deletePairContractIso (X : Finset V) (e f : H.meets X) :
    EndpointIso ((H.deletePair e.1 f.1).contract X)
      ((H.contract X).deletePair e f) := by
  have heq : (Finset.univ.filter fun g : H.meets X ↦
      g.1 ∈ Finset.univ \ {e.1, f.1}) = Finset.univ \ {e, f} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, Subtype.val_inj]
  have hi := restrictContractIso (H := H) (Finset.univ \ {e.1, f.1}) X
  rw [heq] at hi
  exact hi

/-- Deleting edges that miss a shore leaves its contraction unchanged. -/
def deletePairAwayContractIso (X : Finset V) (e f : E)
    (he : e ∉ H.meets X) (hf : f ∉ H.meets X) :
    EndpointIso ((H.deletePair e f).contract X) (H.contract X) := by
  have heq : (Finset.univ.filter fun g : H.meets X ↦
      g.1 ∈ Finset.univ \ {e, f}) = Finset.univ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    exact iff_true_intro (by rintro (h | h); exact he (h ▸ g.2); exact hf (h ▸ g.2))
  have hi := restrictContractIso (H := H) (Finset.univ \ {e, f}) X
  rw [heq] at hi
  exact hi.trans restrictEdgesUnivIso

/-- If only one edge of a deleted pair meets a shore, its contraction
loses just that edge. -/
def deletePairOneContractIso (X : Finset V) (e : H.meets X) (f : E)
    (hf : f ∉ H.meets X) :
    EndpointIso ((H.deletePair e.1 f).contract X) ((H.contract X).deleteEdge e) := by
  have heq : (Finset.univ.filter fun g : H.meets X ↦
      g.1 ∈ Finset.univ \ {e.1, f}) = Finset.univ.erase e := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, and_true]
    have hg : g.1 ≠ f := fun h ↦ hf (h ▸ g.2)
    simp [hg]
  have hi := restrictContractIso (H := H) (Finset.univ \ {e.1, f}) X
  rw [heq] at hi
  exact hi

/-- An internal pair with matching-covered deletion in one contraction
has matching-covered deletion before the splice. -/
theorem IsSeparatingCut.deletePair_of_internal {X : Finset V}
    (hs : H.IsSeparatingCut X) (hXC : (Finset.univ \ X).Nonempty)
    {e f : H.meets X} (he : ∀ k, H.endAt e.1 k ∈ X)
    (hf : ∀ k, H.endAt f.1 k ∈ X)
    (hr : ((H.contract X).deletePair e f).IsMatchingCovered) :
    (H.deletePair e.1 f.1).IsMatchingCovered := by
  have miss {g : E} (hg : ∀ k, H.endAt g k ∈ X) :
      g ∉ H.meets (Finset.univ \ X) := by
    rintro h
    obtain ⟨k, hk⟩ := mem_meets.mp h
    exact (Finset.mem_sdiff.mp hk).2 (hg k)
  exact (show (H.deletePair e.1 f.1).IsSeparatingCut X from
    ⟨(deletePairContractIso X e f).symm.isMatchingCovered hr,
      (deletePairAwayContractIso (Finset.univ \ X) e.1 f.1 (miss he) (miss hf)).symm.isMatchingCovered hs.2⟩).isMatchingCovered hXC

/-- A pair consisting of a cut edge and an internal edge lifts when the
cut edge is removable in the opposite contraction. -/
theorem deletePair_of_one_boundary {X : Finset V}
    (hXC : (Finset.univ \ X).Nonempty) {e f : H.meets X}
    (he : e.1 ∈ H.meets (Finset.univ \ X))
    (hf : ∀ k, H.endAt f.1 k ∈ X)
    (hl : ((H.contract X).deletePair e f).IsMatchingCovered)
    (hr : (H.contract (Finset.univ \ X)).IsRemovable ⟨e.1, he⟩) :
    (H.deletePair e.1 f.1).IsMatchingCovered := by
  have hf' : f.1 ∉ H.meets (Finset.univ \ X) := by
    intro h
    obtain ⟨k, hk⟩ := mem_meets.mp h
    exact (Finset.mem_sdiff.mp hk).2 (hf k)
  exact (show (H.deletePair e.1 f.1).IsSeparatingCut X from
    ⟨(deletePairContractIso X e f).symm.isMatchingCovered hl,
      (deletePairOneContractIso (Finset.univ \ X) ⟨e.1, he⟩ f.1 hf').symm.isMatchingCovered hr⟩).isMatchingCovered hXC

omit [DecidableEq E] in
/-- Two dependent edges incident with the same vertex must be equal. -/
theorem EdgeDepends.eq_of_common_vertex {e f : E} (hdep : H.EdgeDepends e f)
    (hm : H.IsMatchingCovered) {i j : Fin 2}
    (hij : H.endAt e i = H.endAt f j) : e = f := by
  obtain ⟨M, hM, heM⟩ := hm.2 e
  exact congrArg Prod.fst (eq_incidence_of_degreeIn_one (hM _) heM (hdep M hM heM) hij rfl)

/-- A matching-covered pair deletion gives a removable edge or a
removable doubleton, with any common edge property retained. -/
theorem removable_or_doubleton_of_deletePair {P : E → Prop} {e f : E}
    (hne : e ≠ f) (he : P e) (hf : P f)
    (hr : (H.deletePair e f).IsMatchingCovered) :
    ∃ a, P a ∧ (H.IsRemovable a ∨ ∃ b, P b ∧ H.IsRemovableDoubleton a b) := by
  by_cases her : H.IsRemovable e
  · exact ⟨e, he, Or.inl her⟩
  by_cases hfr : H.IsRemovable f
  · exact ⟨f, hf, Or.inl hfr⟩
  exact ⟨e, he, Or.inr ⟨f, hf, ⟨hne, hr, her, hfr⟩⟩⟩

/-- A removable class avoiding the contraction pole is internal and
therefore lifts while avoiding every vertex outside the retained shore. -/
theorem HasAvoidingRemovableClass.of_internal_contract {X : Finset V}
    (hs : H.IsSeparatingCut X) (hXC : (Finset.univ \ X).Nonempty)
    {v : V} {M : Finset E} (hv : v ∉ X)
    (hr : (H.contract X).HasAvoidingRemovableClass none (H.contractMatching X M)) :
    H.HasAvoidingRemovableClass v M := by
  have internal {e : H.meets X} (he : ∀ k, (H.contract X).endAt e k ≠ none) :
      ∀ k, H.endAt e.1 k ∈ X := by
    intro k
    by_contra h
    exact he k ((contract_endAt_eq_none_iff X e k).mpr h)
  obtain ⟨e, heM, he, hr⟩ := hr
  have hei := internal he
  have heM' : e.1 ∉ M := fun h ↦ heM ((mem_contractMatching X M e).mpr h)
  have hev : ∀ k, H.endAt e.1 k ≠ v := fun k h ↦ hv (h ▸ hei k)
  rcases hr with hr | ⟨f, hfM, hf, hrf⟩
  · exact ⟨e.1, heM', hev, Or.inl (hs.removable_of_internal hXC hei hr)⟩
  · have hfi := internal hf
    have hfM' : f.1 ∉ M := fun h ↦ hfM ((mem_contractMatching X M f).mpr h)
    have hfv : ∀ k, H.endAt f.1 k ≠ v := fun k h ↦ hv (h ▸ hfi k)
    have hpair := hs.deletePair_of_internal hXC hei hfi hrf.matchingCovered
    obtain ⟨a, ⟨haM, hav⟩, har⟩ := removable_or_doubleton_of_deletePair
      (P := fun a ↦ a ∉ M ∧ ∀ k, H.endAt a k ≠ v)
      (fun h ↦ hrf.ne (Subtype.ext h)) ⟨heM', hev⟩ ⟨hfM', hfv⟩ hpair
    rcases har with har | ⟨b, ⟨hbM, hbv⟩, hab⟩
    · exact ⟨a, haM, hav, Or.inl har⟩
    · exact ⟨a, haM, hav, Or.inr ⟨b, hbM, hbv, hab⟩⟩

/-- A removable boundary edge on one side selects a dependent removable
class on the near-brick side. The class lifts and retains matching and
hub avoidance. -/
theorem IsSeparatingCut.avoiding_class_of_removable_boundary {X : Finset V}
    (hs : H.IsSeparatingCut X) (hXC : (Finset.univ \ X).Nonempty)
    (hn : (H.contract X).IsNearBrick) (h3 : (H.contract X).IsThreeEdgeConnected)
    {v : V} {M : Finset E} (hv : v ∉ X)
    (hM : (H.contract X).IsPerfectMatching (H.contractMatching X M))
    {e : E} (heX : e ∈ H.dangling X) (heM : e ∉ M)
    (hev : ∀ k, H.endAt e k ≠ v)
    (heR : (H.contract (Finset.univ \ X)).IsRemovable
      ⟨e, dangling_subset_meets _ (by simpa only [dangling_compl] using heX)⟩) :
    H.HasAvoidingRemovableClass v M := by
  let a : H.meets X := ⟨e, dangling_subset_meets X heX⟩
  have heC : e ∈ H.meets (Finset.univ \ X) :=
    dangling_subset_meets _ (by simpa only [dangling_compl] using heX)
  have ha : ∃ j, (H.contract X).endAt a j = none := by
    have hh := mem_dangling.mp heX
    by_cases h0 : H.endAt e 0 ∈ X
    · exact ⟨1, (contract_endAt_eq_none_iff X a 1).mpr (fun h1 ↦ hh ⟨fun _ ↦ h1, fun _ ↦ h0⟩)⟩
    · exact ⟨0, (contract_endAt_eq_none_iff X a 0).mpr h0⟩
  obtain ⟨j, hj⟩ := ha
  have key {f : H.meets X} (hf : (H.contract X).EdgeDepends f a) :
      f.1 ∉ M ∧ (∀ k, H.endAt f.1 k ≠ v) ∧
        ((∀ k, H.endAt f.1 k ∈ X) ∨ f = a) := by
    have hfM : f.1 ∉ M := by
      intro hfM
      exact heM ((mem_contractMatching X M a).mp
        (hf _ hM ((mem_contractMatching X M f).mpr hfM)))
    have hcases : (∀ k, H.endAt f.1 k ∈ X) ∨ f = a := by
      by_cases hi : ∀ k, H.endAt f.1 k ∈ X
      · exact Or.inl hi
      · push Not at hi
        obtain ⟨k, hk⟩ := hi
        exact Or.inr (hf.eq_of_common_vertex hn.matchingCovered
          (((contract_endAt_eq_none_iff X f k).mpr hk).trans hj.symm))
    refine ⟨hfM, ?_, hcases⟩
    rcases hcases with hi | rfl
    · exact fun k hk ↦ hv (hk ▸ hi k)
    · exact hev
  obtain ⟨f, hf, hfr⟩ := hn.exists_removable_or_doubleton_dependingOn h3 a
  obtain ⟨hfM, hfv, hfi⟩ := key hf
  rcases hfr with hfr | ⟨g, hg, hfg⟩
  · refine ⟨f.1, hfM, hfv, Or.inl ?_⟩
    rcases hfi with hi | rfl
    · exact hs.removable_of_internal hXC hi hfr
    · exact removable_of_both_contractions hXC a.2 heC hfr heR
  · obtain ⟨hgM, hgv, hgi⟩ := key hg
    have hp : (H.deletePair f.1 g.1).IsMatchingCovered := by
      rcases hfi with hi | rfl
      · rcases hgi with hgi | rfl
        · exact hs.deletePair_of_internal hXC hi hgi hfg.matchingCovered
        · have hh := deletePair_of_one_boundary hXC heC hi hfg.symm.matchingCovered heR
          change (H.restrictEdges (Finset.univ \ {f.1, a.1})).IsMatchingCovered
          rw [Finset.pair_comm]
          exact hh
      · rcases hgi with hgi | rfl
        · exact deletePair_of_one_boundary hXC heC hgi hfg.matchingCovered heR
        · exact (hfg.ne rfl).elim
    obtain ⟨b, ⟨hbM, hbv⟩, hbr⟩ := removable_or_doubleton_of_deletePair
      (P := fun b ↦ b ∉ M ∧ ∀ k, H.endAt b k ≠ v)
      (fun h ↦ hfg.ne (Subtype.ext h)) ⟨hfM, hfv⟩ ⟨hgM, hgv⟩ hp
    rcases hbr with hbr | ⟨c, ⟨hcM, hcv⟩, hbc⟩
    · exact ⟨b, hbM, hbv, Or.inl hbr⟩
    · exact ⟨b, hbM, hbv, Or.inr ⟨c, hcM, hcv, hbc⟩⟩

end GraphPuzzles.LoopMultigraph
