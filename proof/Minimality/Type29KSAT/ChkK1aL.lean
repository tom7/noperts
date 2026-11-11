module

public import Minimality.Type29KSAT.DataK1aL
public import Minimality.Type29KSAT.NfZB
public import Minimality.Type29KSAT.K1Corner

@[expose] public section

/-!
# Type 29, class K1a on the corner stratum `Z`: core K1aL, the kernel checks of all rows (dispatcher `rowKs`, class
literals `unitsK1a` and the corner clauses `clausesK1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT Minimality.H29K1

/-- The row check of core K1aL. -/
def allDK1aL (n : Nat) : Bool := rowKs unitsK1a clausesK1 chunksK1aL n

/-- Chunk 0 of core K1aL: all rows pass. -/
theorem chkK1aL0 : (rowsK1aL0.all allDK1aL) = true := by decide +kernel

/-- Chunk 1 of core K1aL: all rows pass. -/
theorem chkK1aL1 : (rowsK1aL1.all allDK1aL) = true := by decide +kernel

/-- Chunk 2 of core K1aL: all rows pass. -/
theorem chkK1aL2 : (rowsK1aL2.all allDK1aL) = true := by decide +kernel

/-- Chunk 3 of core K1aL: all rows pass. -/
theorem chkK1aL3 : (rowsK1aL3.all allDK1aL) = true := by decide +kernel

/-- Chunk 4 of core K1aL: all rows pass. -/
theorem chkK1aL4 : (rowsK1aL4.all allDK1aL) = true := by decide +kernel

/-- Every row of core K1aL passes the check. -/
theorem allOKK1aL : ∀ ch ∈ rowsK1aL, ∀ n ∈ ch, allDK1aL n = true := by
  intro ch hch n hn
  simp only [rowsK1aL, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkK1aL0 n hn
  · exact List.all_eq_true.mp chkK1aL1 n hn
  · exact List.all_eq_true.mp chkK1aL2 n hn
  · exact List.all_eq_true.mp chkK1aL3 n hn
  · exact List.all_eq_true.mp chkK1aL4 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core K1aL gives Rupert**: if the numbered clauses of core K1aL are unsatisfiable, every type 29 shape with
`0 < [0123]`, `0 < [0134]`, `[0245] < 0`, `[1235] < 0` and a trirectangular vertex `6` is Rupert. -/
theorem rupert_of_coreK1aL (hU : CoreUnsat rowsK1aL) (F : S0xFac 9 s0x_S29 x)
    (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)) (h0 : 0 < det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0))
    (h1 : det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0) (h2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0)
    (hZ : CornerZ x) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksK1aL rowsK1aL unitsK1a clausesK1 hU allOKK1aL F hchir
    (unitsK1a_true F h0 h1 h2 hZ) (clausesK1_true F hZ hNR))

end Minimality.H29K.SAT
