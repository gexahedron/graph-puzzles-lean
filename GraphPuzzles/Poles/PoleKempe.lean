import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import GraphPuzzles.Core.Tactics

/-!
# Kempe chains as deterministic walks

A Kempe chain of two colours in a properly edge-coloured cubic multipole is a component of the
subgraph formed by the edges of those two colours; every vertex has exactly one edge of each
colour, so the component through a dangling edge is a path ending at another dangling edge.
This module formalizes that path as a deterministic walk: the region `R` of vertices, the two
involutions `f` and `g` giving the other end of the edge of the first and the second colour (an
end outside `R` is a dangling edge), and the walk starting at the vertex `q₀` of a dangling edge
of the first colour, alternately following `g` and `f` until it reaches a dangling edge.

The results: the walk reaches a dangling edge (`exists_exit`), the set of visited vertices is
closed under both involutions inside `R` (`f_mem_visited`, `g_mem_visited`), a visited vertex
whose `g`-edge dangles is the last vertex of the walk and was entered along `f`
(`eq_last_of_g_exit`), a visited vertex other than `q₀` whose `f`-edge dangles is the last vertex
and was entered along `g` (`eq_last_of_f_exit`), and the walk never returns to `q₀`
(`walk_ne_start`).
-/

namespace GraphPuzzles

/-- A region with two edge-colour involutions and a starting vertex on a dangling edge of the
first colour. -/
structure KempeData where
  /-- The region of vertices. -/
  R : Finset ℕ
  /-- The other end of the edge of the first colour. -/
  f : ℕ → ℕ
  /-- The other end of the edge of the second colour. -/
  g : ℕ → ℕ
  f_ne : ∀ q ∈ R, f q ≠ q
  g_ne : ∀ q ∈ R, g q ≠ q
  f_f : ∀ q ∈ R, f q ∈ R → f (f q) = q
  g_g : ∀ q ∈ R, g q ∈ R → g (g q) = q
  /-- The starting vertex. -/
  q₀ : ℕ
  q₀_mem : q₀ ∈ R
  f_q₀ : f q₀ ∉ R

namespace KempeData

variable (K : KempeData)

/-- The walk: from an even step follow `g`, from an odd step follow `f`. -/
def walk : ℕ → ℕ
  | 0 => K.q₀
  | k + 1 => if Even k then K.g (walk k) else K.f (walk k)

/-- The walk exits at step `k` when the edge to be followed dangles. -/
def Exit (k : ℕ) : Prop := if Even k then K.g (K.walk k) ∉ K.R else K.f (K.walk k) ∉ K.R

instance : DecidablePred K.Exit := fun k ↦ by unfold Exit; infer_instance

theorem walk_zero : K.walk 0 = K.q₀ := rfl

theorem walk_succ (k : ℕ) :
    K.walk (k + 1) = if Even k then K.g (K.walk k) else K.f (K.walk k) := rfl

theorem walk_succ_even {k : ℕ} (hk : Even k) : K.walk (k + 1) = K.g (K.walk k) := by
  rw [walk_succ, if_pos hk]

theorem walk_succ_odd {k : ℕ} (hk : ¬ Even k) : K.walk (k + 1) = K.f (K.walk k) := by
  rw [walk_succ, if_neg hk]

theorem walk_succ_mem {k : ℕ} (hne : ¬ K.Exit k) :
    K.walk (k + 1) ∈ K.R := by
  unfold Exit at hne
  by_cases he : Even k
  · rw [if_pos he, not_not] at hne
    rw [walk_succ_even K he]
    exact hne
  · rw [if_neg he, not_not] at hne
    rw [walk_succ_odd K he]
    exact hne

theorem walk_mem_of_no_exit {j : ℕ} (h : ∀ k < j, ¬ K.Exit k) : ∀ k ≤ j, K.walk k ∈ K.R := by
  intro k
  induction k with
  | zero => intro _; exact K.q₀_mem
  | succ k ih =>
    intro hk
    exact K.walk_succ_mem (h k (by omega))

/-- Two steps of the same parity never visit the same vertex before the walk exits. -/
theorem walk_ne_of_parity {j : ℕ} (h : ∀ k < j, ¬ K.Exit k) :
    ∀ i < j, i % 2 = j % 2 → K.walk i ≠ K.walk j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hij hpar heq
    have hmem := K.walk_mem_of_no_exit h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- the start has no predecessor
      have hj : 2 ≤ j := by omega
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hodd : ¬ Even j' := by
        rw [Nat.even_iff]
        omega
      rw [walk_zero, walk_succ_odd K hodd] at heq
      have hj' : K.walk j' ∈ K.R := hmem j' (by omega)
      have hf : K.f K.q₀ ∈ K.R := by
        rw [heq, K.f_f _ hj' (heq ▸ K.q₀_mem)]
        exact hj'
      exact K.f_q₀ hf
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hi' : K.walk i' ∈ K.R := hmem i' (by omega)
      have hj' : K.walk j' ∈ K.R := hmem j' (by omega)
      have hpar' : i' % 2 = j' % 2 := by omega
      have hlt : i' < j' := by omega
      apply ih j' (by omega) (fun k hk ↦ h k (by omega)) i' hlt hpar'
      by_cases he : Even i'
      · have he' : Even j' := by
          rw [Nat.even_iff] at he ⊢
          omega
        rw [walk_succ_even K he, walk_succ_even K he'] at heq
        have hgi : K.g (K.walk i') ∈ K.R := by
          rw [heq]
          rw [← walk_succ_even K he']
          exact hmem (j' + 1) le_rfl
        rw [← K.g_g _ hi' hgi, heq, K.g_g _ hj' (heq ▸ hgi)]
      · have he' : ¬ Even j' := by
          rw [Nat.even_iff] at he ⊢
          omega
        rw [walk_succ_odd K he, walk_succ_odd K he'] at heq
        have hfi : K.f (K.walk i') ∈ K.R := by
          rw [heq]
          rw [← walk_succ_odd K he']
          exact hmem (j' + 1) le_rfl
        rw [← K.f_f _ hi' hfi, heq, K.f_f _ hj' (heq ▸ hfi)]

/-- The walk reaches a dangling edge. -/
theorem exists_exit : ∃ k, K.Exit k := by
  by_contra hno'
  have hno : ∀ k, ¬ K.Exit k := fun k hk ↦ hno' ⟨k, hk⟩
  have hmem : ∀ k, K.walk k ∈ K.R := fun k ↦
    K.walk_mem_of_no_exit (j := k) (fun k' _ ↦ hno k') k le_rfl
  have hmaps : ∀ k ∈ Finset.range (2 * K.R.card + 1),
      (K.walk k, k % 2) ∈ K.R ×ˢ Finset.range 2 := by
    intro k _
    rw [Finset.mem_product, Finset.mem_range]
    exact ⟨hmem k, Nat.mod_lt _ (by omega)⟩
  have hcard : (K.R ×ˢ Finset.range 2).card < (Finset.range (2 * K.R.card + 1)).card := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
    omega
  obtain ⟨x, -, y, -, hxy, hst⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Prod.mk.injEq] at hst
  rcases lt_or_gt_of_ne hxy with h | h
  · exact K.walk_ne_of_parity (fun k _ ↦ hno k) x h hst.2 hst.1
  · exact K.walk_ne_of_parity (fun k _ ↦ hno k) y h hst.2.symm hst.1.symm

/-- The first exit step. -/
noncomputable def last : ℕ := Nat.find K.exists_exit

theorem exit_last : K.Exit K.last := Nat.find_spec K.exists_exit

theorem not_exit_of_lt {k : ℕ} (hk : k < K.last) : ¬ K.Exit k := Nat.find_min K.exists_exit hk

theorem walk_mem {k : ℕ} (hk : k ≤ K.last) : K.walk k ∈ K.R :=
  K.walk_mem_of_no_exit (fun _ hk' ↦ K.not_exit_of_lt hk') k hk

/-- The set of vertices visited by the walk. -/
noncomputable def visited : Finset ℕ := (Finset.range (K.last + 1)).image K.walk

theorem mem_visited {q : ℕ} : q ∈ K.visited ↔ ∃ k ≤ K.last, K.walk k = q := by
  unfold visited
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, rfl⟩

theorem walk_mem_visited {k : ℕ} (hk : k ≤ K.last) : K.walk k ∈ K.visited :=
  K.mem_visited.mpr ⟨k, hk, rfl⟩

theorem start_mem_visited : K.q₀ ∈ K.visited := K.walk_mem_visited (Nat.zero_le _)

theorem visited_subset : K.visited ⊆ K.R := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := K.mem_visited.mp hq
  exact K.walk_mem hk

/-- The visited set is closed under `f` inside the region. -/
theorem f_mem_visited {q : ℕ} (hq : q ∈ K.visited) (hf : K.f q ∈ K.R) : K.f q ∈ K.visited := by
  obtain ⟨k, hk, rfl⟩ := K.mem_visited.mp hq
  by_cases he : Even k
  · -- entered along `f` (or the start)
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd hf (by rw [walk_zero]; exact K.f_q₀)
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have ho : ¬ Even k' := by
        rw [Nat.even_iff] at he ⊢
        omega
      rw [walk_succ_odd K ho]
      have hk' : K.walk k' ∈ K.R := K.walk_mem (by omega)
      rw [K.f_f _ hk' (by rw [← walk_succ_odd K ho]; exact K.walk_mem hk)]
      exact K.walk_mem_visited (by omega)
  · -- the next step follows `f`
    have hne : ¬ K.Exit k := by
      unfold Exit
      rw [if_neg he, not_not]
      exact hf
    have hlt : k < K.last := lt_of_le_of_ne hk (fun h ↦ (h ▸ hne) K.exit_last)
    rw [← walk_succ_odd K he]
    exact K.walk_mem_visited hlt

/-- The visited set is closed under `g` inside the region. -/
theorem g_mem_visited {q : ℕ} (hq : q ∈ K.visited) (hg : K.g q ∈ K.R) : K.g q ∈ K.visited := by
  obtain ⟨k, hk, rfl⟩ := K.mem_visited.mp hq
  by_cases he : Even k
  · have hne : ¬ K.Exit k := by
      unfold Exit
      rw [if_pos he, not_not]
      exact hg
    have hlt : k < K.last := lt_of_le_of_ne hk (fun h ↦ (h ▸ hne) K.exit_last)
    rw [← walk_succ_even K he]
    exact K.walk_mem_visited hlt
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by rw [Nat.even_iff] at he; omega⟩
    have he' : Even k' := by
      rw [Nat.even_iff] at he ⊢
      omega
    rw [walk_succ_even K he']
    have hk' : K.walk k' ∈ K.R := K.walk_mem (by omega)
    rw [K.g_g _ hk' (by rw [← walk_succ_even K he']; exact K.walk_mem hk)]
    exact K.walk_mem_visited (by omega)

/-- A visited vertex whose `g`-edge dangles is the last vertex, reached at an even step. -/
theorem eq_last_of_g_exit {q : ℕ} (hq : q ∈ K.visited) (hg : K.g q ∉ K.R) :
    q = K.walk K.last ∧ Even K.last := by
  obtain ⟨k, hk, rfl⟩ := K.mem_visited.mp hq
  by_cases he : Even k
  · have hex : K.Exit k := by
      unfold Exit
      rw [if_pos he]
      exact hg
    have : K.last ≤ k := Nat.find_min' K.exists_exit hex
    have hkl : k = K.last := le_antisymm hk this
    subst hkl
    exact ⟨rfl, he⟩
  · exfalso
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by rw [Nat.even_iff] at he; omega⟩
    have he' : Even k' := by
      rw [Nat.even_iff] at he ⊢
      omega
    rw [walk_succ_even K he'] at hg
    have hk' : K.walk k' ∈ K.R := K.walk_mem (by omega)
    rw [K.g_g _ hk' (by rw [← walk_succ_even K he']; exact K.walk_mem hk)] at hg
    exact hg hk'

/-- A visited vertex other than the start whose `f`-edge dangles is the last vertex, reached at
an odd step. -/
theorem eq_last_of_f_exit {q : ℕ} (hq : q ∈ K.visited) (hf : K.f q ∉ K.R) (hne : q ≠ K.q₀) :
    q = K.walk K.last ∧ ¬ Even K.last := by
  obtain ⟨k, hk, rfl⟩ := K.mem_visited.mp hq
  by_cases he : Even k
  · exfalso
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact hne rfl
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ho : ¬ Even k' := by
      rw [Nat.even_iff] at he ⊢
      omega
    rw [walk_succ_odd K ho] at hf
    have hk' : K.walk k' ∈ K.R := K.walk_mem (by omega)
    rw [K.f_f _ hk' (by rw [← walk_succ_odd K ho]; exact K.walk_mem hk)] at hf
    exact hf hk'
  · have hex : K.Exit k := by
      unfold Exit
      rw [if_neg he]
      exact hf
    have : K.last ≤ k := Nat.find_min' K.exists_exit hex
    have hkl : k = K.last := le_antisymm hk this
    subst hkl
    exact ⟨rfl, he⟩

/-- The reversed walk from a return to the start satisfies the same recursion. -/
theorem walk_reverse {k : ℕ} (hk : k ≤ K.last) (hodd : ¬ Even k) (hret : K.walk k = K.q₀) :
    ∀ j ≤ k, K.walk (k - j) = K.walk j := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.sub_zero, hret, walk_zero]
  | succ j ih =>
    intro hj
    have hjk : j ≤ k := by omega
    have ih' := ih hjk
    have hmemj : K.walk j ∈ K.R := K.walk_mem (by omega)
    have hmemkj1 : K.walk (k - j - 1) ∈ K.R := K.walk_mem (by omega)
    have hmemkj : K.walk (k - j) ∈ K.R := K.walk_mem (by omega)
    have hstep : K.walk (k - j) = if Even (k - j - 1) then K.g (K.walk (k - j - 1))
        else K.f (K.walk (k - j - 1)) := by
      have : k - j = (k - j - 1) + 1 := by omega
      conv_lhs => rw [this]
      rfl
    rw [show k - (j + 1) = k - j - 1 by omega]
    by_cases he : Even j
    · have he' : Even (k - j - 1) := by
        rw [Nat.even_iff] at he hodd ⊢
        omega
      rw [if_pos he'] at hstep
      rw [walk_succ_even K he, ← ih', hstep, K.g_g _ hmemkj1 (hstep ▸ hmemkj)]
    · have he' : ¬ Even (k - j - 1) := by
        rw [Nat.even_iff] at he hodd ⊢
        omega
      rw [if_neg he'] at hstep
      rw [walk_succ_odd K he, ← ih', hstep, K.f_f _ hmemkj1 (hstep ▸ hmemkj)]

/-- The walk never returns to its start. -/
theorem walk_ne_start {k : ℕ} (hk : 0 < k) (hkl : k ≤ K.last) : K.walk k ≠ K.q₀ := by
  intro hret
  by_cases he : Even k
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ho : ¬ Even k' := by
      rw [Nat.even_iff] at he ⊢
      omega
    rw [walk_succ_odd K ho] at hret
    have hk' : K.walk k' ∈ K.R := K.walk_mem (by omega)
    apply K.f_q₀
    rw [← hret, K.f_f _ hk' (hret ▸ K.q₀_mem)]
    exact hk'
  · have hrev := K.walk_reverse hkl he hret
    set j := (k - 1) / 2 with hj
    have hjk : k - j = j + 1 := by
      rw [Nat.even_iff] at he
      omega
    have h1 := hrev j (by omega)
    rw [hjk] at h1
    have hmemj : K.walk j ∈ K.R := K.walk_mem (by omega)
    by_cases hej : Even j
    · rw [walk_succ_even K hej] at h1
      exact K.g_ne _ hmemj h1
    · rw [walk_succ_odd K hej] at h1
      exact K.f_ne _ hmemj h1

end KempeData
end GraphPuzzles
