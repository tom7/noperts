module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29TSAT.ProofB0
public import Minimality.Type29TSAT.ChkB0

@[expose] public section

/-!
# L29T, T7: core B0, `CoreUnsat rowsB0` from the kernel-checked LRAT proof, and `rupert_of_B0`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem B0e0 : (B0Cnf.drop (0)).take rowsB00.length = cnfOfRows [rowsB00] := by decide +kernel
theorem B0e1 : (B0Cnf.drop (0 + rowsB00.length)).take rowsB01.length = cnfOfRows [rowsB01] := by decide +kernel
theorem B0e2 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length)).take rowsB02.length = cnfOfRows [rowsB02] := by decide +kernel
theorem B0e3 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length)).take rowsB03.length = cnfOfRows [rowsB03] := by decide +kernel
theorem B0e4 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length)).take rowsB04.length = cnfOfRows [rowsB04] := by decide +kernel
theorem B0e5 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length)).take rowsB05.length = cnfOfRows [rowsB05] := by decide +kernel
theorem B0e6 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length + rowsB05.length)).take rowsB06.length = cnfOfRows [rowsB06] := by decide +kernel
theorem B0e7 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length + rowsB05.length + rowsB06.length)).take rowsB07.length = cnfOfRows [rowsB07] := by decide +kernel
theorem B0e8 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length + rowsB05.length + rowsB06.length + rowsB07.length)).take rowsB08.length = cnfOfRows [rowsB08] := by decide +kernel
theorem B0e9 : (B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length + rowsB05.length + rowsB06.length + rowsB07.length + rowsB08.length)).take rowsB09.length = cnfOfRows [rowsB09] := by decide +kernel
theorem B0eEnd : B0Cnf.drop (0 + rowsB00.length + rowsB01.length + rowsB02.length + rowsB03.length + rowsB04.length + rowsB05.length + rowsB06.length + rowsB07.length + rowsB08.length + rowsB09.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core B0, chunk by chunk. -/
theorem cnf_eqB0 : cnfOfRows rowsB0 = B0Cnf := by
  have h := cnfOfRows_of_chkAt rowsB0 B0Cnf 0 ⟨B0e0, B0e1, B0e2, B0e3, B0e4, B0e5, B0e6, B0e7, B0e8, B0e9, B0eEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29T.SAT
open Minimality.H29.SAT

/-- **The numbered clauses of core B0 are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatB0 : CoreUnsat rowsB0 := by
  intro ρ hρ
  have h := K29.B0unsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqB0] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

variable {x : Fin 7 → ℝ³}

/-- **Core B0 closes the case `[0134] = 0`.**  Every type 29 shape (an `S0xFac 9 s0x_S29` configuration) in the chirality
`0 < [0123] = det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0)` with `[0134] = det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0` is
Rupert.  The only inputs are the kernel-checked LRAT proof `B0unsat` and the row checks of `ChkB0`. -/
theorem B0_of_core (F : S0xFac 9 s0x_S29 x) (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0))
    (h0 : det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = 0) : IsRupert (univ.image x) :=
  rupert_of_coreB0 coreUnsatB0 F hchir h0

end Minimality.H29T.SAT
