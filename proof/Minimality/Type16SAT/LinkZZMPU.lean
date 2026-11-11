module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMPU
public import Minimality.Type16SAT.ChkZZMPU

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMPU, `CoreUnsat rowsZZMPU` from the kernel-checked LRAT proof, and `rupert_of_coreZZMPU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMPUe0 : (ZZMPUCnf.drop (0)).take rowsZZMPU0.length = cnfOfRows16 [rowsZZMPU0] := by decide +kernel
theorem ZZMPUe1 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length)).take rowsZZMPU1.length = cnfOfRows16 [rowsZZMPU1] := by decide +kernel
theorem ZZMPUe2 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length)).take rowsZZMPU2.length = cnfOfRows16 [rowsZZMPU2] := by decide +kernel
theorem ZZMPUe3 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length)).take rowsZZMPU3.length = cnfOfRows16 [rowsZZMPU3] := by decide +kernel
theorem ZZMPUe4 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length)).take rowsZZMPU4.length = cnfOfRows16 [rowsZZMPU4] := by decide +kernel
theorem ZZMPUe5 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length)).take rowsZZMPU5.length = cnfOfRows16 [rowsZZMPU5] := by decide +kernel
theorem ZZMPUe6 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length)).take rowsZZMPU6.length = cnfOfRows16 [rowsZZMPU6] := by decide +kernel
theorem ZZMPUe7 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length + rowsZZMPU6.length)).take rowsZZMPU7.length = cnfOfRows16 [rowsZZMPU7] := by decide +kernel
theorem ZZMPUe8 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length + rowsZZMPU6.length + rowsZZMPU7.length)).take rowsZZMPU8.length = cnfOfRows16 [rowsZZMPU8] := by decide +kernel
theorem ZZMPUe9 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length + rowsZZMPU6.length + rowsZZMPU7.length + rowsZZMPU8.length)).take rowsZZMPU9.length = cnfOfRows16 [rowsZZMPU9] := by decide +kernel
theorem ZZMPUe10 : (ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length + rowsZZMPU6.length + rowsZZMPU7.length + rowsZZMPU8.length + rowsZZMPU9.length)).take rowsZZMPU10.length = cnfOfRows16 [rowsZZMPU10] := by decide +kernel
theorem ZZMPUeEnd : ZZMPUCnf.drop (0 + rowsZZMPU0.length + rowsZZMPU1.length + rowsZZMPU2.length + rowsZZMPU3.length + rowsZZMPU4.length + rowsZZMPU5.length + rowsZZMPU6.length + rowsZZMPU7.length + rowsZZMPU8.length + rowsZZMPU9.length + rowsZZMPU10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMPU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMPU : cnfOfRows16 rowsZZMPU = ZZMPUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMPU ZZMPUCnf 0 ⟨ZZMPUe0, ZZMPUe1, ZZMPUe2, ZZMPUe3, ZZMPUe4, ZZMPUe5, ZZMPUe6, ZZMPUe7, ZZMPUe8, ZZMPUe9, ZZMPUe10, ZZMPUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMPU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMPU : Minimality.H16.SAT.CoreUnsat rowsZZMPU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMPUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMPU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00-+` of type 16 is Rupert**: `Core16TW 0 0 (-1) 1`. -/
theorem rupert_of_coreZZMPU : Minimality.H16.SAT.Core16TW 0 0 (-1) 1 := rupert_of_core_dataZZMPU coreUnsatZZMPU

end Minimality.H16K.SAT
