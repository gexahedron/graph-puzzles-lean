import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Max

/-! The finite Hall argument for the bipartite core in Dulmage--Mendelsohn decomposition. -/

namespace GraphPuzzles.HallCore

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Every nonempty proper set of left vertices has more neighbours than vertices. -/
def StrictHall (t : A → Finset B) : Prop :=
  ∀ S : Finset A, S.Nonempty → S ≠ Finset.univ → S.card < (S.biUnion t).card

/-- Strict Hall inequalities allow any one prescribed incidence to be used in
a bijective matching, when the two sides have the same size. -/
theorem exists_bijective_through (t : A → Finset B) (ht : StrictHall t)
    (hcard : Fintype.card A = Fintype.card B) (a : A) (b : B) (hab : b ∈ t a) :
    ∃ f : A → B, Function.Bijective f ∧ (∀ x, f x ∈ t x) ∧ f a = b := by
  let t' : {x : A // x ≠ a} → Finset B := fun x ↦ (t x.1).erase b
  have hall : ∀ S : Finset {x : A // x ≠ a}, S.card ≤ (S.biUnion t').card := by
    intro S
    by_cases hs : S.Nonempty
    · let T := S.image Subtype.val
      have hcT : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
      have hTne : T.Nonempty := hs.image _
      have haT : a ∉ T := by
        intro h
        obtain ⟨x, _, he⟩ := Finset.mem_image.mp h
        exact x.2 he
      have hTnot : T ≠ Finset.univ := fun he ↦ haT (he.symm ▸ Finset.mem_univ a)
      have hlt := ht T hTne hTnot
      have he : S.biUnion t' = (T.biUnion t).erase b := by
        ext y
        simp only [Finset.mem_biUnion, t', T, Finset.mem_erase, Finset.mem_image]
        constructor
        · rintro ⟨x, hx, hne, hy⟩
          exact ⟨hne, x.1, ⟨x, hx, rfl⟩, hy⟩
        · rintro ⟨hne, x, ⟨z, hz, rfl⟩, hy⟩
          exact ⟨z, hz, hne, hy⟩
      rw [he]
      have hc := Finset.card_erase_le (s := T.biUnion t) (a := b)
      have hc' : (T.biUnion t).card ≤ ((T.biUnion t).erase b).card + 1 := by
        by_cases hb : b ∈ T.biUnion t
        · exact (Finset.card_erase_add_one hb).ge
        · rw [Finset.erase_eq_of_notMem hb]
          omega
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs
      simp [hs]
  obtain ⟨g, hginj, hg⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t').mp hall
  have hg_ne (x : {x : A // x ≠ a}) : g x ≠ b := (Finset.mem_erase.mp (hg x)).1
  let f : A → B := fun x ↦ if h : x = a then b else g ⟨x, h⟩
  have hfinj : Function.Injective f := by
    intro x y he
    by_cases hx : x = a <;> by_cases hy : y = a
    · exact hx.trans hy.symm
    · simp only [f, dif_pos hx, dif_neg hy] at he
      exact (hg_ne ⟨y, hy⟩ he.symm).elim
    · simp only [f, dif_neg hx, dif_pos hy] at he
      exact (hg_ne ⟨x, hx⟩ he).elim
    · simp only [f, dif_neg hx, dif_neg hy] at he
      exact congrArg Subtype.val (hginj he)
  refine ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩, ?_, ?_⟩
  · intro x
    by_cases hx : x = a
    · simpa [f, hx] using hab
    · simpa only [f, dif_neg hx] using (Finset.mem_erase.mp (hg ⟨x, hx⟩)).2
  · simp [f]

omit [Fintype B] [DecidableEq A] in
/-- A nonempty balanced Hall family has a minimal nonempty tight subset;
every nonempty proper subset of it satisfies strict Hall. -/
theorem exists_minimal_tight_set (t : A → Finset B)
    (hall : ∀ S : Finset A, S.card ≤ (S.biUnion t).card)
    (hbal : (Finset.univ.biUnion t).card = Fintype.card A) [Nonempty A] :
    ∃ S : Finset A, S.Nonempty ∧ (S.biUnion t).card = S.card ∧
      ∀ T ⊆ S, T.Nonempty → T ≠ S → T.card < (T.biUnion t).card := by
  classical
  let C := Finset.univ.filter fun S : Finset A ↦ S.Nonempty ∧ (S.biUnion t).card = S.card
  have hC : Finset.univ ∈ C := by simp [C, hbal]
  obtain ⟨S, hS, hmin⟩ := C.exists_min_image Finset.card ⟨Finset.univ, hC⟩
  obtain ⟨hSne, hSeq⟩ := (Finset.mem_filter.mp hS).2
  refine ⟨S, hSne, hSeq, ?_⟩
  intro T hTS hTne hne
  have hle := hall T
  by_contra hn
  have hTeq : (T.biUnion t).card = T.card := by omega
  have hTC : T ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTne, hTeq⟩
  have hh := hmin T hTC
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
  omega

/-- The neighbours of a vertex in a chosen left shore, viewed in its neighbour set. -/
def restrictNeighbors (t : A → Finset B) (S : Finset A) (a : S) : Finset (S.biUnion t) :=
  Finset.univ.filter fun b ↦ b.1 ∈ t a.1

omit [Fintype A] [Fintype B] [DecidableEq A] in
@[simp] theorem mem_restrictNeighbors (t : A → Finset B) (S : Finset A)
    (a : S) (b : S.biUnion t) : b ∈ restrictNeighbors t S a ↔ b.1 ∈ t a.1 := by
  simp [restrictNeighbors]

omit [Fintype A] [Fintype B] in
theorem image_biUnion_restrictNeighbors (t : A → Finset B) (S : Finset A) (U : Finset S) :
    (U.biUnion (restrictNeighbors t S)).image Subtype.val = (U.image Subtype.val).biUnion t := by
  ext b
  constructor
  · intro hb
    obtain ⟨b, hbU, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_biUnion.mp hbU
    exact Finset.mem_biUnion.mpr ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      (mem_restrictNeighbors t S a b).mp hab⟩
  · intro hb
    obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp ha
    have hbS : b ∈ S.biUnion t := Finset.mem_biUnion.mpr ⟨a.1, a.2, hb⟩
    exact Finset.mem_image.mpr ⟨⟨b, hbS⟩, Finset.mem_biUnion.mpr
      ⟨a, haU, (mem_restrictNeighbors t S a ⟨b, hbS⟩).mpr hb⟩, rfl⟩

omit [Fintype A] [Fintype B] in
/-- Minimality among nonempty Hall-tight sets becomes strict Hall in the induced core. -/
theorem strictHall_restrictNeighbors (t : A → Finset B) (S : Finset A)
    (hS : ∀ T ⊆ S, T.Nonempty → T ≠ S → T.card < (T.biUnion t).card) :
    StrictHall (restrictNeighbors t S) := by
  intro U hUne hU
  let T := U.image Subtype.val
  have hTS : T ⊆ S := by
    intro a ha
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
    exact a.2
  have hTne : T.Nonempty := hUne.image _
  have hT : T ≠ S := by
    intro he
    apply hU
    apply Finset.eq_univ_of_forall
    intro a
    have ha : a.1 ∈ T := he.symm ▸ a.2
    obtain ⟨a', ha', hea⟩ := Finset.mem_image.mp ha
    have haa : a' = a := Subtype.ext hea
    exact haa ▸ ha'
  have hh := hS T hTS hTne hT
  have hcardT : T.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcardN : (U.biUnion (restrictNeighbors t S)).card = (T.biUnion t).card := by
    rw [← image_biUnion_restrictNeighbors t S U,
      Finset.card_image_of_injective _ Subtype.val_injective]
  omega

omit [Fintype B] in
/-- Strict Hall and a perfect matching force the incidence graph to be connected. -/
theorem StrictHall.constant_of_incidence {t : A → Finset B} (ht : StrictHall t)
    (f : A → B) (hf : Function.Bijective f) (hm : ∀ a, f a ∈ t a)
    (cA : A → Bool) (cB : B → Bool) (hc : ∀ a b, b ∈ t a → cA a = cB b)
    (a : A) (b : B) : cA a = cB b := by
  let S := Finset.univ.filter fun x ↦ cA x = cA a
  have ha : a ∈ S := by simp [S]
  have hN : S.biUnion t = S.image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨z, rfl⟩ := hf.2 y
      have hxcol : cA x = cA a := (Finset.mem_filter.mp hx).2
      have hzcol : cA z = cA a := (hc z _ (hm z)).trans ((hc x _ hy).symm.trans hxcol)
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzcol⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_biUnion.mpr ⟨x, hx, hm x⟩
  have hcard : (S.biUnion t).card = S.card := by
    rw [hN, Finset.card_image_of_injective _ hf.1]
  have hS : S = Finset.univ := by
    by_contra hn
    have hh := ht S ⟨a, ha⟩ hn
    omega
  obtain ⟨z, rfl⟩ := hf.2 b
  have hz : z ∈ S := hS.symm ▸ Finset.mem_univ z
  exact ((Finset.mem_filter.mp hz).2).symm.trans (hc z _ (hm z))

omit [Fintype B] in
/-- A finite balanced Hall family has a nonempty induced core in which every
incidence extends to a perfect matching and all vertices are connected. -/
theorem exists_matchingCovered_core (t : A → Finset B)
    (hall : ∀ S : Finset A, S.card ≤ (S.biUnion t).card)
    (hbal : (Finset.univ.biUnion t).card = Fintype.card A) [Nonempty A] :
    ∃ S : Finset A, S.Nonempty ∧ (S.biUnion t).card = S.card ∧
      (∀ (a : S) (b : S.biUnion t), b.1 ∈ t a.1 →
        ∃ f : S → S.biUnion t, Function.Bijective f ∧
          (∀ x, (f x).1 ∈ t x.1) ∧ f a = b) ∧
      (∀ (cA : S → Bool) (cB : S.biUnion t → Bool),
        (∀ a b, b.1 ∈ t a.1 → cA a = cB b) → ∀ a b, cA a = cB b) := by
  obtain ⟨S, hSne, hSeq, hS⟩ := exists_minimal_tight_set t hall hbal
  have ht := strictHall_restrictNeighbors t S hS
  have hcard : Fintype.card S = Fintype.card (S.biUnion t) := by
    simpa only [Fintype.card_coe] using hSeq.symm
  have hthrough (a : S) (b : S.biUnion t) (hab : b.1 ∈ t a.1) :
      ∃ f : S → S.biUnion t, Function.Bijective f ∧
        (∀ x, (f x).1 ∈ t x.1) ∧ f a = b := by
    simpa only [mem_restrictNeighbors] using exists_bijective_through
      (restrictNeighbors t S) ht hcard a b ((mem_restrictNeighbors t S a b).mpr hab)
  refine ⟨S, hSne, hSeq, hthrough, ?_⟩
  intro cA cB hc a b
  have hNne : (S.biUnion t).Nonempty := Finset.card_pos.mp (by
    rw [hSeq]
    exact Finset.card_pos.mpr hSne)
  obtain ⟨b₀, hb₀⟩ := hNne
  obtain ⟨a₀, ha₀, hab₀⟩ := Finset.mem_biUnion.mp hb₀
  obtain ⟨f, hf, hm, _⟩ := hthrough ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ hab₀
  exact ht.constant_of_incidence f hf
    (fun x ↦ (mem_restrictNeighbors t S x (f x)).mpr (hm x)) cA cB
    (fun x y hxy ↦ hc x y ((mem_restrictNeighbors t S x y).mp hxy)) a b

end GraphPuzzles.HallCore
