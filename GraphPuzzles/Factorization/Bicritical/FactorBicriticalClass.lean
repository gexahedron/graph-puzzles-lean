import GraphPuzzles.Factorization.Bicritical.FactorCapBicritical
import GraphPuzzles.Factorization.Bicritical.FactorJoinBicritical
import GraphPuzzles.Factorization.FactorMain

/-!
# Unique factorisation of bicritical snarks

The class of bicritical snarks with at least six vertices is a good class: it is closed under
the factors of decompositions along cycle-separating `4`-cuts (Chladný–Škoviera, Theorem B),
and its members have girth at least five and are cyclically `4`-edge-connected (Proposition
2.4).  Hence Theorem C applies: the multiset of terminal (cyclically `5`-edge-connected)
factors is unique up to isomorphism.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- **Bicritical snarks** with at least six vertices: closed cubic uncolourable graphs in which
removing any two distinct vertices leaves a colourable multipole. -/
def IsBicriticalSnark (Γ : FinGraph) : Prop :=
  Γ.IsClosed ∧ Γ.IsCubic ∧ ¬ Γ.Colourable ∧ Γ.IsBicritical ∧ 6 ≤ Γ.Vs.card

theorem IsBicriticalSnark.girth5 {Γ : FinGraph} (h : IsBicriticalSnark Γ) : Γ.Girth5 :=
  IsBicritical.girth5 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem IsBicriticalSnark.cyc4Conn {Γ : FinGraph} (h : IsBicriticalSnark Γ) : Γ.Cyc4Conn :=
  IsBicritical.cyc4Conn h.1 h.2.1 h.2.2.1 h.2.2.2.1 (by have := h.2.2.2.2; omega)

/-- A cycle-separating shore of a cubic graph of girth at least five has at least six vertices. -/
theorem CycSep.six_le {Γ : FinGraph} (hcub : Γ.IsCubic) (hg5 : Γ.Girth5) {X : Finset ℕ}
    (hX : Γ.CycSep X) : 6 ≤ X.card := by
  obtain ⟨hXV, hbd, ⟨F, hF, hne, hev⟩, -⟩ := hX
  have h5 := hg5 F (hF.trans (edgesIn_subset X)) hne hev
  have hle := Finset.card_le_card hF
  have := three_mul_card_eq hcub hXV
  omega

/-- **Theorem B (Chladný–Škoviera): bicritical snarks form a good class.** -/
theorem goodClass_bicritical : GoodClass IsBicriticalSnark where
  closed := fun _ h ↦ h.1
  cubic := fun _ h ↦ h.2.1
  girth := fun _ h ↦ h.girth5
  cyc4 := fun _ h ↦ h.cyc4Conn
  snark := fun _ h ↦ h.2.2.1
  pole_colourable := by
    intro Γ h X hX
    have hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1 :=
      fun e he ↦ h.girth5.no_loop he (h.1 e he 0)
    apply h.2.2.2.1.pole_colourable hX.1
    rcases hX.2.2.2.exists_loop_or_two with ⟨e, he, -, hl⟩ | h2
    · exact absurd hl (hloop e he)
    · exact h2
  cap_mem := by
    intro Γ h X m hP hv
    have hg5 := h.girth5
    have hc4 := h.cyc4Conn
    obtain ⟨hcl, hcub, hnc, hb, -⟩ := h
    obtain ⟨_, hiso⟩ := hv.iso
    obtain ⟨hPc, hhet⟩ := hv.het
    refine ⟨cap_isClosed hP m, cap_isCubic hP m, not_colourable_cap_of_isoWith hP m hiso,
      cap_isBicritical hcl hcub hnc hb hg5 hc4 hv.cycSep hP hPc m hhet, ?_⟩
    rw [cap_Vs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · have := CycSep.six_le hcub hg5 hv.cycSep
      rw [pole_Vs]; omega
    · exact freshV_succ_notMem
    · rw [Finset.mem_insert]
      rintro (h | h)
      · omega
      · exact freshV_notMem h
  join_mem := by
    intro Γ h X m hP hv
    have hg5 := h.girth5
    obtain ⟨hcl, hcub, hnc, hb, -⟩ := h
    obtain ⟨hP', hiso⟩ := hv.iso
    obtain ⟨_, hhet⟩ := hv.het
    refine ⟨join_isClosed hP m, join_isCubic hP m, not_colourable_join_of_hetWith hP m hhet,
      join_isBicritical hcl hb hv.cycSep.1 hP' hP m hiso, ?_⟩
    rw [join_Vs, pole_Vs]
    exact CycSep.six_le hcub hg5 (cycSep_compl hcl hv.cycSep)

/-- **Unique factorisation of bicritical snarks (Chladný–Škoviera, Theorem C).**  Any two
complete decompositions of a bicritical snark with at least six vertices along cycle-separating
`4`-cuts produce the same multiset of terminal factors up to isomorphism. -/
theorem bicritical_unique_factorisation {Δ : FinGraph} (hΔ : IsBicriticalSnark Δ)
    {M M' : Multiset FinGraph} (hM : (factorSystem goodClass_bicritical).Chain Δ M)
    (hM' : (factorSystem goodClass_bicritical).Chain Δ M') :
    Multiset.Rel (fun Γ₁ Γ₂ ↦ Nonempty (Iso Γ₁ Γ₂)) M M' :=
  unique_factorisation goodClass_bicritical hΔ hM hM'

/-- Every graph has a complete decomposition. -/
theorem bicritical_exists_factorisation (Δ : FinGraph) :
    ∃ M, (factorSystem goodClass_bicritical).Chain Δ M :=
  exists_factorisation goodClass_bicritical Δ

/-- Every terminal factor in a decomposition of a bicritical snark is bicritical. -/
theorem bicritical_factors {Γ : FinGraph} (hΓ : IsBicriticalSnark Γ)
    {M : Multiset FinGraph} (hM : (factorSystem goodClass_bicritical).Chain Γ M) :
    ∀ H ∈ M, IsBicriticalSnark H ∧ ∀ X, ¬ H.CycSep X := by
  intro H hH
  obtain ⟨hP, hT⟩ := hM.mem_P hΓ H hH
  exact ⟨hP, fun X hX ↦ hT ⟨_, _, exists_step_of_cycSep goodClass_bicritical hP hX⟩⟩

/-- The terminal members of the class are exactly those without cycle-separating `4`-cuts, i.e.
the cyclically `5`-edge-connected bicritical snarks. -/
theorem bicritical_terminal_iff {Γ : FinGraph} (h : IsBicriticalSnark Γ) :
    (factorSystem goodClass_bicritical).Terminal Γ ↔ ∀ X, ¬ Γ.CycSep X := by
  constructor
  · intro ht X hX
    exact ht ⟨_, _, exists_step_of_cycSep goodClass_bicritical h hX⟩
  · rintro hno ⟨A, B, Z, m, -, -, -, -, -, hv, -⟩
    exact hno Z hv.cycSep

end FinGraph
end GraphPuzzles
