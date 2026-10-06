import GraphPuzzles.DefectThree.HexagonCore

/-! The alternating cycle formed by two matchings on six labelled vertices. -/

namespace GraphPuzzles.LoopMultigraph.Hexagon

/-- The other end of each of the three distinguished doubled edges. -/
def pairFlip : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

theorem pairFlip_involutive : Function.Involutive pairFlip := by
  change ∀ i, pairFlip (pairFlip i) = i
  decide

theorem pairFlip_ne (i : Fin 6) : pairFlip i ≠ i := by revert i; decide

theorem pairFlip_word (i : Fin 6) : hexWord (pairFlip i) = hexWord i := by revert i; decide

theorem word_eq_iff (i j : Fin 6) : hexWord i = hexWord j ↔ i = j ∨ i = pairFlip j := by
  revert i j
  decide

def evenPos (a : Fin 3) : Fin 6 := ⟨2 * a.val, by omega⟩

def pairIndex (q : Fin 6 → Fin 6) (a : Fin 3) : Fin 3 := hexWord (q (evenPos a))

theorem pairIndex_word (q : Fin 6 → Fin 6)
    (hq : ∀ i, q (pairFlip i) = pairFlip (q i)) (i : Fin 6) :
    pairIndex q (hexWord i) = hexWord (q i) := by
  have ht : ∀ i : Fin 6, i = evenPos (hexWord i) ∨ i = pairFlip (evenPos (hexWord i)) := by decide
  rcases ht i with h | h
  · exact congrArg (fun k ↦ hexWord (q k)) h.symm
  · calc
      pairIndex q (hexWord i) = hexWord (q (pairFlip (evenPos (hexWord i)))) := by
        rw [hq, pairFlip_word]; rfl
      _ = hexWord (q i) := by rw [← h]

theorem pairIndex_injective (q : Fin 6 → Fin 6) (hi : Function.Injective q)
    (hq : ∀ i, q (pairFlip i) = pairFlip (q i)) : Function.Injective (pairIndex q) := by
  intro a b h
  rcases (word_eq_iff _ _).mp h with h | h
  · exact (show Function.Injective evenPos by decide) (hi h)
  · rw [← hq] at h
    exact False.elim ((show ∀ a b : Fin 3, evenPos a ≠ pairFlip (evenPos b) by decide) a b (hi h))

def coreOrder (p : Fin 6 → Fin 6) : Fin 6 → Fin 6 :=
  ![0, 1, p 1, pairFlip (p 1), p (pairFlip (p 1)), pairFlip (p (pairFlip (p 1)))]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 2000000 in
/-- Excluding a parallel pair forces the union of the matchings to be one hexagon. -/
theorem coreOrder_spec (p : Fin 6 → Fin 6) (hp : ∀ i, p (p i) = i)
    (hn : ∀ i, hexWord (p i) ≠ hexWord i) :
    Function.Injective (coreOrder p) ∧
      (∀ i, coreOrder p (pairFlip i) = pairFlip (coreOrder p i)) ∧
      (∀ i, i.val % 2 = 1 → p (coreOrder p i) = coreOrder p (i + 1)) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  have n3 := hn 3
  have n4 := hn 4
  have n5 := hn 5
  clear hp hn
  generalize a0 : p 0 = x0 at *
  fin_cases x0 <;> simp_all [hexWord]
  all_goals
    generalize a1 : p 1 = x1 at *
    fin_cases x1 <;> simp_all
  all_goals
    generalize a2 : p 2 = x2 at *
    fin_cases x2 <;> simp_all
  all_goals
    generalize a3 : p 3 = x3 at *
    fin_cases x3 <;> simp_all
  all_goals
    generalize a4 : p 4 = x4 at *
    fin_cases x4 <;> simp_all
  all_goals
    generalize a5 : p 5 = x5 at *
    fin_cases x5 <;> simp_all
  all_goals
    simp_all [coreOrder, pairFlip, Function.Injective, Fin.forall_fin_succ]


end GraphPuzzles.LoopMultigraph.Hexagon
