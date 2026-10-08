import GraphPuzzles.Matching.MatchingOn

/-! Connectivity of induced shores, expressed by colourings of original vertices. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every colouring constant along edges inside the shore is constant on that shore. -/
def IsConnectedOn (H : LoopMultigraph V E) (X : Finset V) : Prop :=
  ∀ c : V → Bool,
    (∀ e, H.endAt e 0 ∈ X → H.endAt e 1 ∈ X → c (H.endAt e 0) = c (H.endAt e 1)) →
    ∀ a ∈ X, ∀ b ∈ X, c a = c b

omit [DecidableEq E] in
theorem induced_connected_iff (X : Finset V) : (H.induced X).IsConnected ↔ H.IsConnectedOn X := by
  classical
  constructor
  · intro hc c he a ha b hb
    apply hc (fun v ↦ c v.1) (fun e ↦ ?_) ⟨a, ha⟩ ⟨b, hb⟩
    exact he e.1 ((mem_edgesIn.mp e.2) 0) ((mem_edgesIn.mp e.2) 1)
  · intro hc c he a b
    let d : V → Bool := fun v ↦ if h : v ∈ X then c ⟨v, h⟩ else false
    have hlocal (e : E) (h0 : H.endAt e 0 ∈ X) (h1 : H.endAt e 1 ∈ X) :
        d (H.endAt e 0) = d (H.endAt e 1) := by
      have hm : e ∈ H.edgesIn X := mem_edgesIn.mpr (fun k ↦ by fin_cases k <;> assumption)
      have h0' : (H.induced X).endAt ⟨e, hm⟩ 0 = ⟨H.endAt e 0, h0⟩ := Subtype.ext rfl
      have h1' : (H.induced X).endAt ⟨e, hm⟩ 1 = ⟨H.endAt e 1, h1⟩ := Subtype.ext rfl
      have hh := he ⟨e, hm⟩
      rw [h0', h1'] at hh
      simpa only [d, dif_pos h0, dif_pos h1] using hh
    simpa only [d, dif_pos a.2, dif_pos b.2] using hc d hlocal a.1 a.2 b.1 b.2

omit [DecidableEq E] in
/-- Two vertices in a connected shore, on opposite sides of a second shore,
force an edge crossing the second shore entirely inside the first. -/
theorem IsConnectedOn.exists_boundary_within {X Q : Finset V} (hc : H.IsConnectedOn X)
    {a b : V} (haX : a ∈ X) (haQ : a ∈ Q) (hbX : b ∈ X) (hbQ : b ∉ Q) :
    ∃ e : E, ∃ k : Fin 2, H.endAt e k ∈ Q ∧ H.endAt e k ∈ X ∧
      H.endAt e (Fin.rev k) ∉ Q ∧ H.endAt e (Fin.rev k) ∈ X := by
  by_contra hn
  push Not at hn
  let c : V → Bool := fun v ↦ decide (v ∈ Q)
  have he (e : E) (h0 : H.endAt e 0 ∈ X) (h1 : H.endAt e 1 ∈ X) :
      c (H.endAt e 0) = c (H.endAt e 1) := by
    by_cases h0Q : H.endAt e 0 ∈ Q <;> by_cases h1Q : H.endAt e 1 ∈ Q
    · simp [c, h0Q, h1Q]
    · exact (hn e 0 h0Q h0 h1Q h1).elim
    · exact (hn e 1 h1Q h1 h0Q h0).elim
    · simp [c, h0Q, h1Q]
  have hh := hc c he a haX b hbX
  simp [c, haQ, hbQ] at hh

omit [DecidableEq E] in
/-- Connectivity of a subshore is unchanged when its vertices are viewed in
an induced graph or in the original graph. -/
theorem induced_connectedOn_iff (S : Finset V) (T : Finset S) :
    (H.induced S).IsConnectedOn T ↔ H.IsConnectedOn (T.image Subtype.val) := by
  classical
  constructor
  · intro hc c he a ha b hb
    obtain ⟨a, haT, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hb
    apply hc (fun v ↦ c v.1) (fun e h0 h1 ↦ ?_) a haT b hbT
    exact he e.1 ((mem_image_induced_vertices T _).mpr h0)
      ((mem_image_induced_vertices T _).mpr h1)
  · intro hc c he a ha b hb
    let d : V → Bool := fun v ↦ if h : v ∈ S then c ⟨v, h⟩ else false
    have hd (v : S) : d v.1 = c v := by simp [d, v.2]
    have hlocal (e : E) (h0 : H.endAt e 0 ∈ T.image Subtype.val)
        (h1 : H.endAt e 1 ∈ T.image Subtype.val) : d (H.endAt e 0) = d (H.endAt e 1) := by
      have h0S := image_induced_vertices_subset T h0
      have h1S := image_induced_vertices_subset T h1
      have hm : e ∈ H.edgesIn S := mem_edgesIn.mpr (fun k ↦ by fin_cases k <;> assumption)
      let f : H.edgesIn S := ⟨e, hm⟩
      have hh := he f ((mem_image_induced_vertices T _).mp h0)
        ((mem_image_induced_vertices T _).mp h1)
      exact (hd ((H.induced S).endAt f 0)).trans
        (hh.trans (hd ((H.induced S).endAt f 1)).symm)
    exact (hd a).symm.trans ((hc d hlocal a.1 ((mem_image_induced_vertices T a).mpr ha)
      b.1 ((mem_image_induced_vertices T b).mpr hb)).trans (hd b))

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem image_univ_erase_induced (S : Finset V) (v : S) :
    (Finset.univ.erase v).image Subtype.val = S.erase v.1 := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hx).1 (Subtype.ext h), x.2⟩
  · intro hw
    obtain ⟨hvw, hwS⟩ := Finset.mem_erase.mp hw
    exact Finset.mem_image.mpr ⟨⟨w, hwS⟩, Finset.mem_erase.mpr
      ⟨fun h ↦ hvw (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩

end GraphPuzzles.LoopMultigraph
