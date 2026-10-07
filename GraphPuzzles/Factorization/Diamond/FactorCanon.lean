import GraphPuzzles.Factorization.FactorPoleIso
import GraphPuzzles.FinGraph.FinGraphIsoMk

/-!
# The canonical double completion

For nested shores `X ⊆ W` of a closed cubic graph, the two ways of decomposing along both cuts
(first along `∂W`, then along the projection of `∂X`, or the other way round) produce graphs on
the middle part `M = W \ X` with gadgets attached at both cuts.  We describe such a graph
canonically, `can`, in terms of the middle part, the two cuts, their partner functions and the
gadget types, in a way that is manifestly symmetric in the two cuts (`can_symm`).  Both double
completions are shown to be isomorphic to `can` in the files `FactorDbl*.lean`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Partner

variable {P : FinGraph} (hP : P.IsPole4) (m : Fin 3)

/-- The partner of a dangling edge in the pairing `m` (junk elsewhere). -/
noncomputable def partner (d : ℕ) : ℕ :=
  if h : d ∈ P.dangling then bdEmb hP (pairing m (exists_bdEmb_eq hP h).choose) else d

theorem partner_bdEmb (k : Fin 4) : partner hP m (bdEmb hP k) = bdEmb hP (pairing m k) := by
  unfold partner
  rw [dif_pos (bdEmb_mem hP k)]
  congr 2
  exact bdEmb_injective hP (exists_bdEmb_eq hP (bdEmb_mem hP k)).choose_spec

theorem partner_of_notMem {d : ℕ} (hd : d ∉ P.dangling) : partner hP m d = d := by
  unfold partner
  rw [dif_neg hd]

theorem partner_mem {d : ℕ} (hd : d ∈ P.dangling) : partner hP m d ∈ P.dangling := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
  rw [partner_bdEmb]
  exact bdEmb_mem hP _

theorem partner_partner {d : ℕ} (hd : d ∈ P.dangling) : partner hP m (partner hP m d) = d := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
  rw [partner_bdEmb, partner_bdEmb, pairing_involutive]

theorem partner_ne {d : ℕ} (hd : d ∈ P.dangling) : partner hP m d ≠ d := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
  rw [partner_bdEmb]
  intro h
  exact pairing_ne m k (bdEmb_injective hP h)

theorem partner_inj {d d' : ℕ} (hd : d ∈ P.dangling) (hd' : d' ∈ P.dangling)
    (h : partner hP m d = partner hP m d') : d = d' := by
  rw [← partner_partner hP m hd, h, partner_partner hP m hd']

theorem couple₁_eq : couple₁ hP m = {bdEmb hP 0, partner hP m (bdEmb hP 0)} := by
  rw [couple₁, partner_bdEmb]

theorem couple₂_eq : couple₂ hP m = {bdEmb hP (other m), partner hP m (bdEmb hP (other m))} := by
  rw [couple₂, partner_bdEmb]

theorem mem_couple₁_iff' {d : ℕ} : d ∈ couple₁ hP m ↔ d = bdEmb hP 0 ∨ partner hP m d = bdEmb hP 0 := by
  rw [couple₁_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right; exact partner_partner hP m (bdEmb_mem hP 0)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [← h]
      by_cases hd : d ∈ P.dangling
      · rw [partner_partner hP m hd]
      · rw [partner_of_notMem hP m hd] at h
        rw [h] at hd
        exact absurd (bdEmb_mem hP 0) hd

theorem mem_couple₂_iff' {d : ℕ} : d ∈ couple₂ hP m ↔
    d = bdEmb hP (other m) ∨ partner hP m d = bdEmb hP (other m) := by
  rw [couple₂_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right; exact partner_partner hP m (bdEmb_mem hP _)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [← h]
      by_cases hd : d ∈ P.dangling
      · rw [partner_partner hP m hd]
      · rw [partner_of_notMem hP m hd] at h
        rw [h] at hd
        exact absurd (bdEmb_mem hP _) hd

/-- Partners lie in the same couple. -/
theorem partner_mem_couple₁_iff {d : ℕ} (hd : d ∈ P.dangling) :
    partner hP m d ∈ couple₁ hP m ↔ d ∈ couple₁ hP m := by
  rw [mem_couple₁_iff', mem_couple₁_iff', partner_partner hP m hd, or_comm]

theorem partner_congr {P' : FinGraph} (hP' : P'.IsPole4) (h : P.dangling = P'.dangling) (d : ℕ) :
    partner hP m d = partner hP' m d := by
  by_cases hd : d ∈ P.dangling
  · obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
    rw [partner_bdEmb, bdEmb_congr hP hP' h k, bdEmb_congr hP hP' h, partner_bdEmb]
  · rw [partner_of_notMem hP m hd, partner_of_notMem hP' m (h ▸ hd)]

end Partner

section Canon

variable (Δ : FinGraph) (M S T : Finset ℕ) (p : ℕ → ℕ) (g : Bool)

/-- The end of an edge inside the middle part `M`. -/
def innerE (e : ℕ) : ℕ := if Δ.ends e 0 ∈ M then Δ.ends e 0 else Δ.ends e 1

/-- The distinguished element of the cut `S` relative to the other cut `T`. -/
def first : ℕ := (S \ T).sup id

/-- The first token vertex of the gadget at `S`. -/
def tokU : ℕ := freshV Δ + 2 * first S T

/-- The label of the internal edge of the cap gadget at `S`. -/
def tokE : ℕ := freshE Δ + 2 * first S T

/-- The token vertex to which the dangling edge `d` of `S` is attached. -/
def tok (d : ℕ) : ℕ := if d = first S T ∨ p d = first S T then tokU Δ S T else tokU Δ S T + 1

/-- The end of a through edge on the side of the cut `S`. -/
def thruEnd (e : ℕ) : ℕ := if g then tok Δ S T p e else innerE Δ M (p e)

/-- The labels of the pair edges of the join gadget at `S`. -/
def pairLabels : Finset ℕ := (S \ T).filter fun d ↦ p d ∉ T ∧ d ≤ p d

/-- The token vertices of the gadget at `S`. -/
def toks : Finset ℕ := if g then {tokU Δ S T, tokU Δ S T + 1} else ∅

/-- The edges of the gadget at `S` (other than through edges). -/
def surv : Finset ℕ := if g then insert (tokE Δ S T) (S \ T) else pairLabels S T p

/-- The ends of a gadget edge at `S`. -/
def sideEnds (e : ℕ) (i : Fin 2) : ℕ :=
  if g then
    (if e = tokE Δ S T then (if i = 0 then tokU Δ S T else tokU Δ S T + 1)
      else (if Δ.ends e i ∈ M then Δ.ends e i else tok Δ S T p e))
  else (if i = 0 then innerE Δ M e else innerE Δ M (p e))

variable (SX SW : Finset ℕ) (pX pW : ℕ → ℕ) (gX gW : Bool)

/-- **The canonical double completion.** -/
def can : FinGraph where
  Vs := M ∪ toks Δ SX SW gX ∪ toks Δ SW SX gW
  Es := Δ.edgesIn M ∪ (SX ∩ SW) ∪ surv Δ SX SW pX gX ∪ surv Δ SW SX pW gW
  ends e i :=
    if e ∈ SX ∩ SW then (if i = 0 then thruEnd Δ M SX SW pX gX e else thruEnd Δ M SW SX pW gW e)
    else if e ∈ SX \ SW ∨ e = tokE Δ SX SW then sideEnds Δ M SX SW pX gX e i
    else if e ∈ SW \ SX ∨ e = tokE Δ SW SX then sideEnds Δ M SW SX pW gW e i
    else Δ.ends e i

theorem can_Vs : (can Δ M SX SW pX pW gX gW).Vs = M ∪ toks Δ SX SW gX ∪ toks Δ SW SX gW := rfl
theorem can_Es : (can Δ M SX SW pX pW gX gW).Es =
    Δ.edgesIn M ∪ (SX ∩ SW) ∪ surv Δ SX SW pX gX ∪ surv Δ SW SX pW gW := rfl

theorem can_ends_thru {e : ℕ} (he : e ∈ SX ∩ SW) (i : Fin 2) :
    (can Δ M SX SW pX pW gX gW).ends e i =
      if i = 0 then thruEnd Δ M SX SW pX gX e else thruEnd Δ M SW SX pW gW e := by
  show (if e ∈ SX ∩ SW then _ else _) = _
  rw [if_pos he]

theorem can_ends_X {e : ℕ} (he : e ∉ SX ∩ SW) (h : e ∈ SX \ SW ∨ e = tokE Δ SX SW) (i : Fin 2) :
    (can Δ M SX SW pX pW gX gW).ends e i = sideEnds Δ M SX SW pX gX e i := by
  show (if e ∈ SX ∩ SW then _ else if _ then _ else _) = _
  rw [if_neg he, if_pos h]

theorem can_ends_W {e : ℕ} (he : e ∉ SX ∩ SW) (h₁ : ¬ (e ∈ SX \ SW ∨ e = tokE Δ SX SW))
    (h : e ∈ SW \ SX ∨ e = tokE Δ SW SX) (i : Fin 2) :
    (can Δ M SX SW pX pW gX gW).ends e i = sideEnds Δ M SW SX pW gW e i := by
  show (if e ∈ SX ∩ SW then _ else if _ then _ else if _ then _ else _) = _
  rw [if_neg he, if_neg h₁, if_pos h]

theorem can_ends_old {e : ℕ} (he : e ∉ SX ∩ SW) (h₁ : ¬ (e ∈ SX \ SW ∨ e = tokE Δ SX SW))
    (h₂ : ¬ (e ∈ SW \ SX ∨ e = tokE Δ SW SX)) (i : Fin 2) :
    (can Δ M SX SW pX pW gX gW).ends e i = Δ.ends e i := by
  show (if e ∈ SX ∩ SW then _ else if _ then _ else if _ then _ else _) = _
  rw [if_neg he, if_neg h₁, if_neg h₂]

/-- The distinguished element lies in `S \ T`. -/
theorem first_mem (h : (S \ T).Nonempty) : first S T ∈ S \ T := by
  obtain ⟨d, hd, hd'⟩ := Finset.exists_mem_eq_sup (S \ T) h id
  rw [first, hd']
  exact hd

theorem tokE_notMem (_hS : S ⊆ Δ.Es) (e : ℕ) (he : e ∈ Δ.Es) : e ≠ tokE Δ S T := by
  intro h
  have := Finset.le_sup (f := id) he
  simp only [id] at this
  unfold tokE freshE at h
  omega

theorem tokU_notMem (v : ℕ) (hv : v ∈ Δ.Vs) : v ≠ tokU Δ S T ∧ v ≠ tokU Δ S T + 1 := by
  have := Finset.le_sup (f := id) hv
  simp only [id] at this
  unfold tokU freshV
  omega

omit p g in
theorem first_ne (hS : (S \ T).Nonempty) (hT : (T \ S).Nonempty) : first S T ≠ first T S := by
  intro h
  have h1 := first_mem S T hS
  have h2 := first_mem T S hT
  rw [h] at h1
  rw [Finset.mem_sdiff] at h1 h2
  exact h1.2 h2.1

theorem tokE_ne (hS : (S \ T).Nonempty) (hT : (T \ S).Nonempty) : tokE Δ S T ≠ tokE Δ T S := by
  intro h
  unfold tokE at h
  exact first_ne S T hS hT (by omega)

theorem tokU_ne (hS : (S \ T).Nonempty) (hT : (T \ S).Nonempty) :
    tokU Δ S T ≠ tokU Δ T S ∧ tokU Δ S T ≠ tokU Δ T S + 1 ∧ tokU Δ S T + 1 ≠ tokU Δ T S := by
  have := first_ne S T hS hT
  unfold tokU
  omega

/-- The symmetry of the canonical double completion in the two cuts. -/
noncomputable def canSymm (hSX : SX ⊆ Δ.Es) (hSW : SW ⊆ Δ.Es) (hX : (SX \ SW).Nonempty)
    (hW : (SW \ SX).Nonempty) :
    Iso (can Δ M SX SW pX pW gX gW) (can Δ M SW SX pW pX gW gX) :=
  Iso.ofEq (by rw [can_Vs, can_Vs, Finset.union_right_comm])
    (by rw [can_Es, can_Es, Finset.inter_comm, Finset.union_right_comm])
    (fun e ↦ decide (e ∈ SX ∩ SW)) (by
      intro e he i
      by_cases hthru : e ∈ SX ∩ SW
      · simp only [hthru, decide_true, sw, if_true]
        have hthru' : e ∈ SW ∩ SX := by rw [Finset.inter_comm]; exact hthru
        rw [can_ends_thru _ _ _ _ _ _ _ _ hthru, can_ends_thru _ _ _ _ _ _ _ _ hthru']
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · rw [Iso.rev_zero']; simp
        · rw [Iso.rev_one']; simp
      · simp only [hthru, decide_false, sw, Bool.false_eq_true, if_false]
        have hthru' : e ∉ SW ∩ SX := by rw [Finset.inter_comm]; exact hthru
        by_cases hX' : e ∈ SX \ SW ∨ e = tokE Δ SX SW
        · rw [can_ends_X _ _ _ _ _ _ _ _ hthru hX']
          have hW' : ¬ (e ∈ SW \ SX ∨ e = tokE Δ SW SX) := by
            rintro (h | h)
            · rcases hX' with h' | h'
              · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp h').1
              · exact tokE_notMem Δ SX SW hSX e (hSW (Finset.mem_sdiff.mp h).1) h'
            · rcases hX' with h' | h'
              · exact tokE_notMem Δ SW SX hSW e (hSX (Finset.mem_sdiff.mp h').1) h
              · exact tokE_ne Δ SX SW hX hW (h'.symm.trans h)
          rw [can_ends_W _ _ _ _ _ _ _ _ hthru' hW' hX']
        · by_cases hW' : e ∈ SW \ SX ∨ e = tokE Δ SW SX
          · rw [can_ends_W _ _ _ _ _ _ _ _ hthru hX' hW', can_ends_X _ _ _ _ _ _ _ _ hthru' hW']
          · rw [can_ends_old _ _ _ _ _ _ _ _ hthru hX' hW', can_ends_old _ _ _ _ _ _ _ _ hthru' hW' hX'])

end Canon

end FinGraph
end GraphPuzzles
