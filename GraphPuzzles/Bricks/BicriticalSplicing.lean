import GraphPuzzles.Bricks.BrickCharacterization
import GraphPuzzles.Matching.MatchingOn

/-! Bicriticality is preserved when two separating-cut contractions are spliced. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A partial matching avoiding a contraction pole lifts to its original vertices. -/
theorem IsPerfectMatchingOn.of_contract {X : Finset V} {S : Finset (Option X)}
    {M : Finset (H.meets X)} (hM : (H.contract X).IsPerfectMatchingOn S M)
    (hn : none ∉ S) : H.IsPerfectMatchingOn (sourceShore X S) (M.image Subtype.val) := by
  constructor
  · intro e he k
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (contract_mem_sourceShore X S hn f k).mpr (hM.1 f hf k)
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [← contract_degreeIn_image_some X M w]
    exact hM.2 (some w) (Finset.mem_filter.mp hw).2

/-- Deleting the pole and a retained vertex in a bicritical contraction gives
a matching on the original shore minus that vertex. -/
theorem IsBicritical.factorCritical_shore {X : Finset V}
    (hb : (H.contract X).IsBicritical) : H.IsFactorCritical X := by
  intro u hu
  obtain ⟨M, hM⟩ := hb none (some ⟨u, hu⟩) (by simp)
  have hh := hM.of_contract (by simp)
  have hS : sourceShore X ((Finset.univ.erase none).erase (some ⟨u, hu⟩)) = X.erase u := by
    rw [← contractShore_erase, sourceShore_contractShore]
    exact Finset.inter_eq_right.mpr (Finset.erase_subset _ _)
  exact ⟨_, hS ▸ hh⟩

/-- A matching of a contraction after deleting two retained vertices extends
over any matching-covered opposite contraction. -/
theorem IsPerfectMatchingOn.extend_contract_erase_pair {X : Finset V} {u v : X}
    {M : Finset (H.meets X)}
    (hM : (H.contract X).IsPerfectMatchingOn
      ((Finset.univ.erase (some u)).erase (some v)) M)
    (hopp : (H.contract (Finset.univ \ X)).IsMatchingCovered) :
    ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u.1).erase v.1) P := by
  let P := M.image Subtype.val
  have hPsub : P ⊆ H.meets X := by
    intro e he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact f.2
  have hPavoid : ∀ e ∈ P, ∀ k, H.endAt e k ≠ u.1 ∧ H.endAt e k ≠ v.1 := by
    intro e he k
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have hh := hM.1 f hf k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hh
    exact ⟨fun he ↦ hh.2 ((contract_endAt_eq_some_iff X f k u).mpr he),
      fun he ↦ hh.1 ((contract_endAt_eq_some_iff X f k v).mpr he)⟩
  have hPdeg : ∀ w ∈ X, w ≠ u.1 → w ≠ v.1 → H.degreeIn P w = 1 := by
    intro w hw hwu hwv
    rw [← contract_degreeIn_image_some X M ⟨w, hw⟩]
    apply hM.2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h ↦ hwv (congrArg Subtype.val (Option.some.inj h)),
      fun h ↦ hwu (congrArg Subtype.val (Option.some.inj h))⟩
  have hcard : (P ∩ H.dangling X).card = 1 := by
    rw [← contract_degreeIn_none X M]
    exact hM.2 none (by simp)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  have heX : e ∈ H.dangling X :=
    (Finset.mem_inter.mp (he.symm ▸ Finset.mem_singleton_self e)).2
  have heXC : e ∈ H.dangling (Finset.univ \ X) := by
    simpa only [dangling_compl] using heX
  obtain ⟨N, hN, heN⟩ := hopp.2 ⟨e, dangling_subset_meets _ heXC⟩
  let Q := N.image Subtype.val
  have heQ : e ∈ Q := Finset.mem_image.mpr ⟨_, heN, rfl⟩
  have hNe : hN.contractBoundary = e := ((hN.contract_boundary_iff heXC).mp heQ).symm
  have hag : ∀ f ∈ H.dangling X, f ∈ P ↔ f ∈ Q := by
    intro f hf
    have hf' : f ∈ H.dangling (Finset.univ \ X) := by
      simpa only [dangling_compl] using hf
    have hp : f ∈ P ↔ f = e := by
      calc
        f ∈ P ↔ f ∈ P ∩ H.dangling X := by simp [hf]
        _ ↔ f = e := by rw [he, Finset.mem_singleton]
    change f ∈ P ↔ f ∈ N.image Subtype.val
    rw [hN.contract_boundary_iff hf', hNe]
    exact hp
  have hQpole := hN.contract_to_pole.1
  have hQavoid : ∀ f ∈ Q, ∀ k, H.endAt f k ≠ u.1 ∧ H.endAt f k ≠ v.1 := by
    intro f hf k
    constructor
    · intro hfu
      have hd : f ∈ H.dangling X := mem_dangling_of_mem_meets
        (X := X) (Y := Finset.univ \ X)
        (fun _ hx hxc ↦ (Finset.mem_sdiff.mp hxc).2 hx) (hQpole.1 hf) (hfu ▸ u.2)
      exact (hPavoid f ((hag f hd).mpr hf) k).1 hfu
    · intro hfv
      have hd : f ∈ H.dangling X := mem_dangling_of_mem_meets
        (X := X) (Y := Finset.univ \ X)
        (fun _ hx hxc ↦ (Finset.mem_sdiff.mp hxc).2 hx) (hQpole.1 hf) (hfv ▸ v.2)
      exact (hPavoid f ((hag f hd).mpr hf) k).2 hfv
  refine ⟨P ∪ Q, ?_, ?_⟩
  · intro f hf k
    have hh := (Finset.mem_union.mp hf).elim (fun hf ↦ hPavoid f hf k)
      (fun hf ↦ hQavoid f hf k)
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hh.2, hh.1⟩
  · intro w hw
    have hwu := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    have hwv := (Finset.mem_erase.mp hw).1
    by_cases hwX : w ∈ X
    · rw [degreeIn_union_eq_left_of]
      · exact hPdeg w hwX hwu hwv
      · rintro f hf ⟨k, hk⟩
        have hd : f ∈ H.dangling X := mem_dangling_of_mem_meets
          (X := X) (Y := Finset.univ \ X)
          (fun _ hx hxc ↦ (Finset.mem_sdiff.mp hxc).2 hx) (hQpole.1 hf) (hk ▸ hwX)
        exact (hag f hd).mpr hf
    · rw [Finset.union_comm, degreeIn_union_eq_left_of]
      · exact hQpole.2 w (by simp [hwX])
      · rintro f hf ⟨k, hk⟩
        have hm : f ∈ H.meets (Finset.univ \ X) := mem_meets.mpr ⟨k, by simp [hk, hwX]⟩
        obtain ⟨j, hj⟩ := mem_meets.mp (hPsub hf)
        have hd : f ∈ H.dangling X := mem_dangling_of_mem_meets
          (X := X) (Y := Finset.univ \ X)
          (fun _ hx hxc ↦ (Finset.mem_sdiff.mp hxc).2 hx) hm hj
        exact (hag f hd).mp hf

/-- The bicritical assertion of Campos--Lucchesi Lemma 2.11. -/
theorem IsSeparatingCut.isBicritical_of_contractions {X : Finset V}
    (hs : H.IsSeparatingCut X) (hl : (H.contract X).IsBicritical)
    (hr : (H.contract (Finset.univ \ X)).IsBicritical) : H.IsBicritical := by
  have same (Y : Finset V) (hb : (H.contract Y).IsBicritical)
      (ho : (H.contract (Finset.univ \ Y)).IsMatchingCovered)
      (u v : V) (hu : u ∈ Y) (hv : v ∈ Y) (hne : u ≠ v) :
      ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P := by
    obtain ⟨M, hM⟩ := hb (some ⟨u, hu⟩) (some ⟨v, hv⟩)
      (fun h ↦ hne (congrArg Subtype.val (Option.some.inj h)))
    exact hM.extend_contract_erase_pair ho
  have opposite (u v : V) (hu : u ∈ X) (hv : v ∉ X) :
      ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P := by
    obtain ⟨M, hM⟩ := hl.factorCritical_shore u hu
    obtain ⟨N, hN⟩ := hr.factorCritical_shore v (by simp [hv])
    have hd : Disjoint (X.erase u) ((Finset.univ \ X).erase v) := by
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      exact (Finset.mem_sdiff.mp (Finset.mem_erase.mp hw').2).2 (Finset.mem_erase.mp hw).2
    have hset : X.erase u ∪ (Finset.univ \ X).erase v =
        (Finset.univ.erase u).erase v := by
      ext w
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff,
        Finset.mem_univ, true_and, and_true]
      constructor
      · rintro (⟨hwu, hw⟩ | ⟨hwv, hw⟩)
        · exact ⟨fun h ↦ hv (h ▸ hw), hwu⟩
        · exact ⟨hwv, fun h ↦ hw (h ▸ hu)⟩
      · rintro ⟨hwv, hwu⟩
        by_cases hw : w ∈ X
        · exact Or.inl ⟨hwu, hw⟩
        · exact Or.inr ⟨hwv, hw⟩
    exact ⟨M ∪ N, hset ▸ hM.union hN hd⟩
  intro u v huv
  by_cases hu : u ∈ X
  · by_cases hv : v ∈ X
    · exact same X hl hs.2 u v hu hv huv
    · exact opposite u v hu hv
  · by_cases hv : v ∈ X
    · obtain ⟨M, hM⟩ := opposite v u hv hu
      have hset : (Finset.univ.erase v).erase u = (Finset.univ.erase u).erase v :=
        Finset.erase_right_comm
      exact ⟨M, hset ▸ hM⟩
    · apply same (Finset.univ \ X) hr
      · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
        exact hs.1
      · simpa using hu
      · simpa using hv
      · exact huv

end GraphPuzzles.LoopMultigraph
