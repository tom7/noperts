module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMZMU
public import Minimality.Type16SAT.ChkZMZMU

@[expose] public section

/-!
# Type 16, J7/J8: core ZMZMU, `CoreUnsat rowsZMZMU` from the kernel-checked LRAT proof, and `rupert_of_coreZMZMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMZMUe0 : (ZMZMUCnf.drop (0)).take rowsZMZMU0.length = cnfOfRows16 [rowsZMZMU0] := by decide +kernel
theorem ZMZMUe1 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length)).take rowsZMZMU1.length = cnfOfRows16 [rowsZMZMU1] := by decide +kernel
theorem ZMZMUe2 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length)).take rowsZMZMU2.length = cnfOfRows16 [rowsZMZMU2] := by decide +kernel
theorem ZMZMUe3 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length)).take rowsZMZMU3.length = cnfOfRows16 [rowsZMZMU3] := by decide +kernel
theorem ZMZMUe4 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length)).take rowsZMZMU4.length = cnfOfRows16 [rowsZMZMU4] := by decide +kernel
theorem ZMZMUe5 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length)).take rowsZMZMU5.length = cnfOfRows16 [rowsZMZMU5] := by decide +kernel
theorem ZMZMUe6 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length)).take rowsZMZMU6.length = cnfOfRows16 [rowsZMZMU6] := by decide +kernel
theorem ZMZMUe7 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length)).take rowsZMZMU7.length = cnfOfRows16 [rowsZMZMU7] := by decide +kernel
theorem ZMZMUe8 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length)).take rowsZMZMU8.length = cnfOfRows16 [rowsZMZMU8] := by decide +kernel
theorem ZMZMUe9 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length)).take rowsZMZMU9.length = cnfOfRows16 [rowsZMZMU9] := by decide +kernel
theorem ZMZMUe10 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length + rowsZMZMU9.length)).take rowsZMZMU10.length = cnfOfRows16 [rowsZMZMU10] := by decide +kernel
theorem ZMZMUe11 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length + rowsZMZMU9.length + rowsZMZMU10.length)).take rowsZMZMU11.length = cnfOfRows16 [rowsZMZMU11] := by decide +kernel
theorem ZMZMUe12 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length + rowsZMZMU9.length + rowsZMZMU10.length + rowsZMZMU11.length)).take rowsZMZMU12.length = cnfOfRows16 [rowsZMZMU12] := by decide +kernel
theorem ZMZMUe13 : (ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length + rowsZMZMU9.length + rowsZMZMU10.length + rowsZMZMU11.length + rowsZMZMU12.length)).take rowsZMZMU13.length = cnfOfRows16 [rowsZMZMU13] := by decide +kernel
theorem ZMZMUeEnd : ZMZMUCnf.drop (0 + rowsZMZMU0.length + rowsZMZMU1.length + rowsZMZMU2.length + rowsZMZMU3.length + rowsZMZMU4.length + rowsZMZMU5.length + rowsZMZMU6.length + rowsZMZMU7.length + rowsZMZMU8.length + rowsZMZMU9.length + rowsZMZMU10.length + rowsZMZMU11.length + rowsZMZMU12.length + rowsZMZMU13.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMZMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMZMU : cnfOfRows16 rowsZMZMU = ZMZMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMZMU ZMZMUCnf 0 ⟨ZMZMUe0, ZMZMUe1, ZMZMUe2, ZMZMUe3, ZMZMUe4, ZMZMUe5, ZMZMUe6, ZMZMUe7, ZMZMUe8, ZMZMUe9, ZMZMUe10, ZMZMUe11, ZMZMUe12, ZMZMUe13, ZMZMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMZMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMZMU : Minimality.H16.SAT.CoreUnsat rowsZMZMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMZMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMZMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0-0-` of type 16 is Rupert**: `Core16TW 0 (-1) 0 (-1)`. -/
theorem rupert_of_coreZMZMU : Minimality.H16.SAT.Core16TW 0 (-1) 0 (-1) := rupert_of_core_dataZMZMU coreUnsatZMZMU

end Minimality.H16K.SAT
