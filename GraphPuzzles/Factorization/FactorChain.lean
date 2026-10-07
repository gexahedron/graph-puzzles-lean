import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Tactic.Cases
import GraphPuzzles.Core.Tactics

/-!
# Abstract unique factorisation

A *decomposition system* consists of a ternary step relation `Step G A B` ("`G` decomposes into
the two factors `A` and `B`"), a size function decreasing along steps, an equivalence `R`
(isomorphism) along which steps transport, and a class `P` closed under steps.  A *chain* from
`G` is a multiset of terminal objects obtained by repeatedly decomposing.

The *atom property* says: every non-terminal `G` of the class has a distinguished step
`{A₀, B₀}` such that every other step `{C, D}` either produces the same pair up to `R`, or
closes a diamond: the factor containing the atom decomposes further into `{A₀', C'}` with
`A₀' ≈ A₀`, and `B₀` decomposes into `{C'', D'}` with `C'' ≈ C'`, `D' ≈ D`.  Under the atom
property any two chains from an object of the class are equal as multisets up to `R`.
This is the abstract content of Chladný–Škoviera's Lemmas 10.1–10.2 and Theorem 10.3, with the
height induction replaced by strong induction on the size.
-/

namespace GraphPuzzles

/-- A decomposition system. -/
structure DecompSystem (α : Type*) where
  /-- `Step G A B`: `G` decomposes into the factors `A` and `B`. -/
  Step : α → α → α → Prop
  /-- A size measure, decreasing along steps. -/
  size : α → ℕ
  /-- The equivalence (isomorphism). -/
  R : α → α → Prop
  /-- The class of objects for which uniqueness is claimed. -/
  P : α → Prop
  R_refl : ∀ x, R x x
  R_symm : ∀ {x y}, R x y → R y x
  R_trans : ∀ {x y z}, R x y → R y z → R x z
  step_symm : ∀ {G A B}, Step G A B → Step G B A
  size_lt : ∀ {G A B}, Step G A B → size A < size G ∧ size B < size G
  step_transport : ∀ {G G' A B}, R G G' → Step G A B → ∃ A' B', Step G' A' B' ∧ R A A' ∧ R B B'
  P_step : ∀ {G A B}, P G → Step G A B → P A ∧ P B

namespace DecompSystem

variable {α : Type*} (S : DecompSystem α)

/-- Terminal objects have no step. -/
def Terminal (G : α) : Prop := ¬ ∃ A B, S.Step G A B

/-- The chains: multisets of terminal objects reachable from `G`. -/
inductive Chain (S : DecompSystem α) : α → Multiset α → Prop
  | terminal {G : α} : S.Terminal G → Chain S G {G}
  | step {G A B : α} {M N : Multiset α} : S.Step G A B → Chain S A M → Chain S B N →
      Chain S G (M + N)

/-- Members of a chain of a good decomposition system belong to the class and are terminal. -/
theorem Chain.mem_P {α : Type*} {S : DecompSystem α} {G : α} {M : Multiset α}
    (hM : S.Chain G M) (hG : S.P G) : ∀ H ∈ M, S.P H ∧ S.Terminal H := by
  induction hM with
  | terminal hT => intro H hH; rw [Multiset.mem_singleton] at hH; subst hH; exact ⟨hG, hT⟩
  | step hs _ _ ihA ihB =>
    intro H hH
    rw [Multiset.mem_add] at hH
    obtain ⟨hA, hB⟩ := S.P_step hG hs
    rcases hH with hH | hH
    · exact ihA hA H hH
    · exact ihB hB H hH

/-- The diamond closing a step `{C, D}` against the distinguished step `{A₀, B₀}`, with the atom
inherited by `C`. -/
def Diamond (A₀ B₀ C D : α) : Prop :=
  ∃ A₀' C' C'' D', S.Step C A₀' C' ∧ S.R A₀' A₀ ∧ S.Step B₀ C'' D' ∧ S.R C'' C' ∧ S.R D' D

/-- The atom property. -/
def AtomProperty : Prop :=
  ∀ G, S.P G → (∃ A B, S.Step G A B) → ∃ A₀ B₀, S.Step G A₀ B₀ ∧
    ∀ C D, S.Step G C D →
      (S.R C A₀ ∧ S.R D B₀) ∨ (S.R C B₀ ∧ S.R D A₀) ∨ S.Diamond A₀ B₀ C D ∨ S.Diamond A₀ B₀ D C

/-- Equality of multisets up to `R`. -/
def MRel (M N : Multiset α) : Prop := Multiset.Rel S.R M N

theorem MRel.refl (M : Multiset α) : S.MRel M M :=
  Multiset.rel_refl_of_refl_on fun x _ ↦ S.R_refl x

theorem MRel.symm {M N : Multiset α} (h : S.MRel M N) : S.MRel N M := by
  have : flip S.R = S.R := by
    funext x y
    exact propext ⟨fun h ↦ S.R_symm h, fun h ↦ S.R_symm h⟩
  unfold MRel
  rw [← this]
  exact Multiset.rel_flip.mpr h

theorem MRel.trans {M N K : Multiset α} (h₁ : S.MRel M N) (h₂ : S.MRel N K) : S.MRel M K := by
  haveI : IsTrans α S.R := ⟨fun _ _ _ ↦ S.R_trans⟩
  exact Multiset.Rel.trans S.R h₁ h₂

theorem MRel.add {M N K L : Multiset α} (h₁ : S.MRel M N) (h₂ : S.MRel K L) :
    S.MRel (M + K) (N + L) := Multiset.Rel.add h₁ h₂

theorem MRel.singleton {x y : α} (h : S.R x y) : S.MRel {x} {y} := by
  unfold MRel
  rw [Multiset.rel_iff]
  simp [h]

theorem MRel.add_comm (M N : Multiset α) : S.MRel (M + N) (N + M) := by
  rw [_root_.add_comm]
  exact MRel.refl S _

/-- Terminality transports along `R`. -/
theorem Terminal.transport {G G' : α} (h : S.R G G') (hG : S.Terminal G) : S.Terminal G' := by
  rintro ⟨A, B, hs⟩
  obtain ⟨A', B', hs', -, -⟩ := S.step_transport (S.R_symm h) hs
  exact hG ⟨A', B', hs'⟩

/-- Chains transport along `R`. -/
theorem Chain.transport {G G' : α} {M : Multiset α} (h : S.R G G') (hM : S.Chain G M) :
    ∃ M', S.Chain G' M' ∧ S.MRel M M' := by
  induction hM generalizing G' with
  | terminal hG => exact ⟨_, Chain.terminal (hG.transport S h), MRel.singleton S h⟩
  | step hs _ _ ihA ihB =>
    obtain ⟨A', B', hs', hA, hB⟩ := S.step_transport h hs
    obtain ⟨M', hM', hMM'⟩ := ihA hA
    obtain ⟨N', hN', hNN'⟩ := ihB hB
    exact ⟨M' + N', Chain.step hs' hM' hN', MRel.add S hMM' hNN'⟩

/-- Every object has a chain. -/
theorem exists_chain (G : α) : ∃ M, S.Chain G M := by
  induction' hn : S.size G using Nat.strong_induction_on with n ih generalizing G
  by_cases hT : S.Terminal G
  · exact ⟨_, Chain.terminal hT⟩
  · unfold Terminal at hT
    push Not at hT
    obtain ⟨A, B, hs⟩ := hT
    obtain ⟨hA, hB⟩ := S.size_lt hs
    obtain ⟨M, hM⟩ := ih _ (hn ▸ hA) A rfl
    obtain ⟨N, hN⟩ := ih _ (hn ▸ hB) B rfl
    exact ⟨M + N, Chain.step hs hM hN⟩

/-- A chain from a terminal object is the singleton. -/
theorem Chain.eq_singleton_of_terminal {G : α} {M : Multiset α} (hM : S.Chain G M)
    (hT : S.Terminal G) : M = {G} := by
  cases hM with
  | terminal _ => rfl
  | step hs _ _ => exact absurd ⟨_, _, hs⟩ hT

/-- **Abstract unique factorisation.**  Under the atom property, any two chains from an object of
the class are equal up to `R`. -/
theorem unique_chain (hatom : S.AtomProperty) :
    ∀ G, S.P G → ∀ M M', S.Chain G M → S.Chain G M' → S.MRel M M' := by
  intro G
  induction' hn : S.size G using Nat.strong_induction_on with n ih generalizing G
  intro hG M M' hM hM'
  by_cases hT : S.Terminal G
  · rw [hM.eq_singleton_of_terminal S hT, hM'.eq_singleton_of_terminal S hT]
    exact MRel.refl S _
  · have hT' : ∃ A B, S.Step G A B := by
      unfold Terminal at hT
      push Not at hT
      exact hT
    obtain ⟨A₀, B₀, hs₀, hatom'⟩ := hatom G hG hT'
    obtain ⟨hA₀, hB₀⟩ := S.size_lt hs₀
    obtain ⟨hPA₀, hPB₀⟩ := S.P_step hG hs₀
    obtain ⟨MA, hMA⟩ := S.exists_chain A₀
    obtain ⟨MB, hMB⟩ := S.exists_chain B₀
    -- uniqueness for smaller objects
    have ihs : ∀ X, S.size X < S.size G → S.P X → ∀ K K', S.Chain X K → S.Chain X K' →
        S.MRel K K' := fun X hX hPX K K' hK hK' ↦ ih _ (hn ▸ hX) X rfl hPX K K' hK hK'
    -- a chain of an object equivalent to a smaller object of the class is equivalent to any
    -- chain of the latter
    have key : ∀ X Y K L, S.size Y < S.size G → S.P Y → S.R X Y → S.Chain X K → S.Chain Y L →
        S.MRel K L := by
      intro X Y K L hY hPY hXY hK hL
      obtain ⟨K', hK', hKK'⟩ := hK.transport S hXY
      exact hKK'.trans S (ihs Y hY hPY K' L hK' hL)
    -- every chain from `G` is equivalent to `MA + MB`
    have main : ∀ K, S.Chain G K → S.MRel K (MA + MB) := by
      intro K hK
      cases hK with
      | terminal hT'' => exact absurd hT'' hT
      | step hs hC hD =>
        rename_i C D M₁ M₂
        obtain ⟨hCsz, hDsz⟩ := S.size_lt hs
        obtain ⟨hPC, hPD⟩ := S.P_step hG hs
        rcases hatom' C D hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hdia | hdia
        · exact MRel.add S (key C A₀ M₁ MA hA₀ hPA₀ h1 hC hMA)
            (key D B₀ M₂ MB hB₀ hPB₀ h2 hD hMB)
        · exact (MRel.add S (key C B₀ M₁ MB hB₀ hPB₀ h1 hC hMB)
            (key D A₀ M₂ MA hA₀ hPA₀ h2 hD hMA)).trans S (MRel.add_comm S _ _)
        · obtain ⟨A₀', C', C'', D', hsC, hA₀', hsB, hC'', hD'⟩ := hdia
          obtain ⟨hPA₀', hPC'⟩ := S.P_step hPC hsC
          obtain ⟨hPC'', hPD'⟩ := S.P_step hPB₀ hsB
          obtain ⟨MA', hMA'⟩ := S.exists_chain A₀'
          obtain ⟨MC', hMC'⟩ := S.exists_chain C'
          obtain ⟨MC'', hMC''⟩ := S.exists_chain C''
          obtain ⟨MD', hMD'⟩ := S.exists_chain D'
          have hsizeC' := (S.size_lt hsC).2
          have e1 : S.MRel M₁ (MA' + MC') :=
            ihs C hCsz hPC M₁ (MA' + MC') hC (Chain.step hsC hMA' hMC')
          have e2 : S.MRel MA' MA := key A₀' A₀ MA' MA hA₀ hPA₀ hA₀' hMA' hMA
          have e3 : S.MRel MB (MC'' + MD') :=
            ihs B₀ hB₀ hPB₀ MB (MC'' + MD') hMB (Chain.step hsB hMC'' hMD')
          have e4 : S.MRel MC'' MC' :=
            key C'' C' MC'' MC' (lt_trans hsizeC' hCsz) hPC' hC'' hMC'' hMC'
          have e5 : S.MRel MD' M₂ := key D' D MD' M₂ hDsz hPD hD' hMD' hD
          have s1 : S.MRel (M₁ + M₂) ((MA' + MC') + M₂) := MRel.add S e1 (MRel.refl S _)
          have s2 : S.MRel ((MA' + MC') + M₂) (MA + (MC'' + MD')) := by
            rw [add_assoc]
            exact MRel.add S e2 (MRel.add S (e4.symm S) (e5.symm S))
          have s3 : S.MRel (MA + (MC'' + MD')) (MA + MB) := MRel.add S (MRel.refl S _) (e3.symm S)
          exact (s1.trans S s2).trans S s3
        · obtain ⟨A₀', D', D'', C', hsD, hA₀', hsB, hD'', hC'⟩ := hdia
          obtain ⟨hPA₀', hPD'⟩ := S.P_step hPD hsD
          obtain ⟨hPD'', hPC'⟩ := S.P_step hPB₀ hsB
          obtain ⟨MA', hMA'⟩ := S.exists_chain A₀'
          obtain ⟨MD', hMD'⟩ := S.exists_chain D'
          obtain ⟨MD'', hMD''⟩ := S.exists_chain D''
          obtain ⟨MC', hMC'⟩ := S.exists_chain C'
          have hsizeD' := (S.size_lt hsD).2
          have e1 : S.MRel M₂ (MA' + MD') :=
            ihs D hDsz hPD M₂ (MA' + MD') hD (Chain.step hsD hMA' hMD')
          have e2 : S.MRel MA' MA := key A₀' A₀ MA' MA hA₀ hPA₀ hA₀' hMA' hMA
          have e3 : S.MRel MB (MD'' + MC') :=
            ihs B₀ hB₀ hPB₀ MB (MD'' + MC') hMB (Chain.step hsB hMD'' hMC')
          have e4 : S.MRel MD'' MD' :=
            key D'' D' MD'' MD' (lt_trans hsizeD' hDsz) hPD' hD'' hMD'' hMD'
          have e5 : S.MRel MC' M₁ := key C' C MC' M₁ hCsz hPC hC' hMC' hC
          have s0 : S.MRel (M₁ + M₂) (M₂ + M₁) := MRel.add_comm S _ _
          have s1 : S.MRel (M₂ + M₁) ((MA' + MD') + M₁) := MRel.add S e1 (MRel.refl S _)
          have s2 : S.MRel ((MA' + MD') + M₁) (MA + (MD'' + MC')) := by
            rw [add_assoc]
            exact MRel.add S e2 (MRel.add S (e4.symm S) (e5.symm S))
          have s3 : S.MRel (MA + (MD'' + MC')) (MA + MB) := MRel.add S (MRel.refl S _) (e3.symm S)
          exact ((s0.trans S s1).trans S s2).trans S s3
    exact (main M hM).trans S ((main M' hM').symm S)

end DecompSystem
end GraphPuzzles
