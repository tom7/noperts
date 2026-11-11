module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMPMU
public import Minimality.Type16SAT.ChkZMPMU

@[expose] public section

/-!
# Type 16, J7/J8: core ZMPMU, `CoreUnsat rowsZMPMU` from the kernel-checked LRAT proof, and `rupert_of_coreZMPMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMPMUe0 : (ZMPMUCnf.drop (0)).take rowsZMPMU0.length = cnfOfRows16 [rowsZMPMU0] := by decide +kernel
theorem ZMPMUe1 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length)).take rowsZMPMU1.length = cnfOfRows16 [rowsZMPMU1] := by decide +kernel
theorem ZMPMUe2 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length)).take rowsZMPMU2.length = cnfOfRows16 [rowsZMPMU2] := by decide +kernel
theorem ZMPMUe3 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length)).take rowsZMPMU3.length = cnfOfRows16 [rowsZMPMU3] := by decide +kernel
theorem ZMPMUe4 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length)).take rowsZMPMU4.length = cnfOfRows16 [rowsZMPMU4] := by decide +kernel
theorem ZMPMUe5 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length)).take rowsZMPMU5.length = cnfOfRows16 [rowsZMPMU5] := by decide +kernel
theorem ZMPMUe6 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length + rowsZMPMU5.length)).take rowsZMPMU6.length = cnfOfRows16 [rowsZMPMU6] := by decide +kernel
theorem ZMPMUe7 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length + rowsZMPMU5.length + rowsZMPMU6.length)).take rowsZMPMU7.length = cnfOfRows16 [rowsZMPMU7] := by decide +kernel
theorem ZMPMUe8 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length + rowsZMPMU5.length + rowsZMPMU6.length + rowsZMPMU7.length)).take rowsZMPMU8.length = cnfOfRows16 [rowsZMPMU8] := by decide +kernel
theorem ZMPMUe9 : (ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length + rowsZMPMU5.length + rowsZMPMU6.length + rowsZMPMU7.length + rowsZMPMU8.length)).take rowsZMPMU9.length = cnfOfRows16 [rowsZMPMU9] := by decide +kernel
theorem ZMPMUeEnd : ZMPMUCnf.drop (0 + rowsZMPMU0.length + rowsZMPMU1.length + rowsZMPMU2.length + rowsZMPMU3.length + rowsZMPMU4.length + rowsZMPMU5.length + rowsZMPMU6.length + rowsZMPMU7.length + rowsZMPMU8.length + rowsZMPMU9.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMPMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMPMU : cnfOfRows16 rowsZMPMU = ZMPMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMPMU ZMPMUCnf 0 ⟨ZMPMUe0, ZMPMUe1, ZMPMUe2, ZMPMUe3, ZMPMUe4, ZMPMUe5, ZMPMUe6, ZMPMUe7, ZMPMUe8, ZMPMUe9, ZMPMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMPMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMPMU : Minimality.H16.SAT.CoreUnsat rowsZMPMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMPMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMPMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0-+-` of type 16 is Rupert**: `Core16TW 0 (-1) 1 (-1)`. -/
theorem rupert_of_coreZMPMU : Minimality.H16.SAT.Core16TW 0 (-1) 1 (-1) := rupert_of_core_dataZMPMU coreUnsatZMPMU

end Minimality.H16K.SAT
