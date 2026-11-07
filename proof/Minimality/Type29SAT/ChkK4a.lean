module

public import Minimality.Type29SAT.DataK4a
public import Minimality.Type29SAT.Top

@[expose] public section

/-!
# Type 29, core K4a: the kernel checks of all rows and the theorem `rupert_of_coreK4a`

Every row of `rowsK4a` passes the row check (families 8, 11 to 16, 20, 21), the rule check (17), the witness check (19),
the `T(L,L)` check (22) and the unit check (26, the class literals).  Together with the unsatisfiability of the
numbered clauses (`CoreUnsat rowsK4a`, kernel-checked in `UnsatK4a`), every shape of the class is Rupert.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The class literals of core K4a: the signs of the brackets `[0134]`, `[0245]`, `[1235]`. -/
def unitsK4a : List Lit := [(true, V.br 0 1 3 4), (true, V.ng (V.br 0 2 4 5)), (true, V.br 1 2 3 5)]

/-- All five row checks. -/
def allDK4a (n : Nat) : Bool :=
  rowD chunksK4a n && ruleD chunksK4a n && witD chunksK4a n && tllD chunksK4a n && unitD unitsK4a chunksK4a n && krelD chunksK4a n

/-- Chunk 0 of core K4a: all six row checks pass. -/
theorem chkK4a0 : (rowsK4a0.all allDK4a) = true := by decide +kernel

/-- Chunk 1 of core K4a: all six row checks pass. -/
theorem chkK4a1 : (rowsK4a1.all allDK4a) = true := by decide +kernel

/-- Chunk 2 of core K4a: all six row checks pass. -/
theorem chkK4a2 : (rowsK4a2.all allDK4a) = true := by decide +kernel

/-- Chunk 3 of core K4a: all six row checks pass. -/
theorem chkK4a3 : (rowsK4a3.all allDK4a) = true := by decide +kernel

/-- Chunk 4 of core K4a: all six row checks pass. -/
theorem chkK4a4 : (rowsK4a4.all allDK4a) = true := by decide +kernel

/-- Chunk 5 of core K4a: all six row checks pass. -/
theorem chkK4a5 : (rowsK4a5.all allDK4a) = true := by decide +kernel

/-- Chunk 6 of core K4a: all six row checks pass. -/
theorem chkK4a6 : (rowsK4a6.all allDK4a) = true := by decide +kernel

/-- Chunk 7 of core K4a: all six row checks pass. -/
theorem chkK4a7 : (rowsK4a7.all allDK4a) = true := by decide +kernel

/-- Chunk 8 of core K4a: all six row checks pass. -/
theorem chkK4a8 : (rowsK4a8.all allDK4a) = true := by decide +kernel

/-- Every row of core K4a passes all six checks. -/
theorem allOKK4a : ∀ ch ∈ rowsK4a, ∀ n ∈ ch, allDK4a n = true := by
  intro ch hch n hn
  simp only [rowsK4a, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkK4a0 n hn
  · exact List.all_eq_true.mp chkK4a1 n hn
  · exact List.all_eq_true.mp chkK4a2 n hn
  · exact List.all_eq_true.mp chkK4a3 n hn
  · exact List.all_eq_true.mp chkK4a4 n hn
  · exact List.all_eq_true.mp chkK4a5 n hn
  · exact List.all_eq_true.mp chkK4a6 n hn
  · exact List.all_eq_true.mp chkK4a7 n hn
  · exact List.all_eq_true.mp chkK4a8 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core K4a are true of the real data. -/
theorem unitsK4a_true (F : S0xFac 9 s0x_S29 x) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1)) :
    ∀ l ∈ unitsK4a, evalL (rho (geoF F)) l = true := by
  intro l hl
  have e : ∀ i < 7, (geoF F).x i = x (Fin.ofNat 7 i) := fun i _ => rfl
  simp only [unitsK4a, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [evalL, rho, Geo.atom, e]
    exact h0
  · simp [evalL, rho, Geo.atom, e]
    exact h1
  · simp [evalL, rho, Geo.atom, e]
    exact h2

/-- **Core K4a gives Rupert**: if the numbered clauses of core K4a are unsatisfiable, every type 29 shape with
`0 < [0123]` and the class brackets is Rupert. -/
theorem rupert_of_coreK4a (hU : CoreUnsat rowsK4a) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1)) : IsRupert (univ.image x) := by
  refine case_of_unsat chunksK4a rowsK4a unitsK4a hU ?_ F hchir (unitsK4a_true F h0 h1 h2)
  intro ch hch n hn
  have := allOKK4a ch hch n hn
  simp only [allDK4a, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Minimality.H29.SAT
