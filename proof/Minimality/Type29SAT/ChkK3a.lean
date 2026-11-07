module

public import Minimality.Type29SAT.DataK3a
public import Minimality.Type29SAT.Top

@[expose] public section

/-!
# Type 29, core K3a: the kernel checks of all rows and the theorem `rupert_of_coreK3a`

Every row of `rowsK3a` passes the row check (families 8, 11 to 16, 20, 21), the rule check (17), the witness check (19),
the `T(L,L)` check (22) and the unit check (26, the class literals).  Together with the unsatisfiability of the
numbered clauses (`CoreUnsat rowsK3a`, kernel-checked in `UnsatK3a`), every shape of the class is Rupert.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The class literals of core K3a: the signs of the brackets `[0134]`, `[0245]`, `[1235]`. -/
def unitsK3a : List Lit := [(true, V.br 0 1 3 4), (true, V.br 0 2 4 5), (true, V.ng (V.br 1 2 3 5))]

/-- All five row checks. -/
def allDK3a (n : Nat) : Bool :=
  rowD chunksK3a n && ruleD chunksK3a n && witD chunksK3a n && tllD chunksK3a n && unitD unitsK3a chunksK3a n && krelD chunksK3a n

/-- Chunk 0 of core K3a: all six row checks pass. -/
theorem chkK3a0 : (rowsK3a0.all allDK3a) = true := by decide +kernel

/-- Chunk 1 of core K3a: all six row checks pass. -/
theorem chkK3a1 : (rowsK3a1.all allDK3a) = true := by decide +kernel

/-- Chunk 2 of core K3a: all six row checks pass. -/
theorem chkK3a2 : (rowsK3a2.all allDK3a) = true := by decide +kernel

/-- Chunk 3 of core K3a: all six row checks pass. -/
theorem chkK3a3 : (rowsK3a3.all allDK3a) = true := by decide +kernel

/-- Chunk 4 of core K3a: all six row checks pass. -/
theorem chkK3a4 : (rowsK3a4.all allDK3a) = true := by decide +kernel

/-- Chunk 5 of core K3a: all six row checks pass. -/
theorem chkK3a5 : (rowsK3a5.all allDK3a) = true := by decide +kernel

/-- Chunk 6 of core K3a: all six row checks pass. -/
theorem chkK3a6 : (rowsK3a6.all allDK3a) = true := by decide +kernel

/-- Chunk 7 of core K3a: all six row checks pass. -/
theorem chkK3a7 : (rowsK3a7.all allDK3a) = true := by decide +kernel

/-- Chunk 8 of core K3a: all six row checks pass. -/
theorem chkK3a8 : (rowsK3a8.all allDK3a) = true := by decide +kernel

/-- Chunk 9 of core K3a: all six row checks pass. -/
theorem chkK3a9 : (rowsK3a9.all allDK3a) = true := by decide +kernel

/-- Chunk 10 of core K3a: all six row checks pass. -/
theorem chkK3a10 : (rowsK3a10.all allDK3a) = true := by decide +kernel

/-- Chunk 11 of core K3a: all six row checks pass. -/
theorem chkK3a11 : (rowsK3a11.all allDK3a) = true := by decide +kernel

/-- Every row of core K3a passes all six checks. -/
theorem allOKK3a : ∀ ch ∈ rowsK3a, ∀ n ∈ ch, allDK3a n = true := by
  intro ch hch n hn
  simp only [rowsK3a, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkK3a0 n hn
  · exact List.all_eq_true.mp chkK3a1 n hn
  · exact List.all_eq_true.mp chkK3a2 n hn
  · exact List.all_eq_true.mp chkK3a3 n hn
  · exact List.all_eq_true.mp chkK3a4 n hn
  · exact List.all_eq_true.mp chkK3a5 n hn
  · exact List.all_eq_true.mp chkK3a6 n hn
  · exact List.all_eq_true.mp chkK3a7 n hn
  · exact List.all_eq_true.mp chkK3a8 n hn
  · exact List.all_eq_true.mp chkK3a9 n hn
  · exact List.all_eq_true.mp chkK3a10 n hn
  · exact List.all_eq_true.mp chkK3a11 n hn

variable {x : Fin 7 → ℝ³}

/-- The class literals of core K3a are true of the real data. -/
theorem unitsK3a_true (F : S0xFac 9 s0x_S29 x) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h1 : 0 < det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0) :
    ∀ l ∈ unitsK3a, evalL (rho (geoF F)) l = true := by
  intro l hl
  have e : ∀ i < 7, (geoF F).x i = x (Fin.ofNat 7 i) := fun i _ => rfl
  simp only [unitsK3a, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [evalL, rho, Geo.atom, e]
    exact h0
  · simp [evalL, rho, Geo.atom, e]
    exact h1
  · simp [evalL, rho, Geo.atom, e]
    exact h2

/-- **Core K3a gives Rupert**: if the numbered clauses of core K3a are unsatisfiable, every type 29 shape with
`0 < [0123]` and the class brackets is Rupert. -/
theorem rupert_of_coreK3a (hU : CoreUnsat rowsK3a) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0)) (h1 : 0 < det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0)) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0) : IsRupert (univ.image x) := by
  refine case_of_unsat chunksK3a rowsK3a unitsK3a hU ?_ F hchir (unitsK3a_true F h0 h1 h2)
  intro ch hch n hn
  have := allOKK3a ch hch n hn
  simp only [allDK3a, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Minimality.H29.SAT
