module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMMU
public import Minimality.Type16SAT.ChkZZMMU

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMMU, `CoreUnsat rowsZZMMU` from the kernel-checked LRAT proof, and `rupert_of_coreZZMMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMMUe0 : (ZZMMUCnf.drop (0)).take rowsZZMMU0.length = cnfOfRows16 [rowsZZMMU0] := by decide +kernel
theorem ZZMMUe1 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length)).take rowsZZMMU1.length = cnfOfRows16 [rowsZZMMU1] := by decide +kernel
theorem ZZMMUe2 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length)).take rowsZZMMU2.length = cnfOfRows16 [rowsZZMMU2] := by decide +kernel
theorem ZZMMUe3 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length)).take rowsZZMMU3.length = cnfOfRows16 [rowsZZMMU3] := by decide +kernel
theorem ZZMMUe4 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length)).take rowsZZMMU4.length = cnfOfRows16 [rowsZZMMU4] := by decide +kernel
theorem ZZMMUe5 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length)).take rowsZZMMU5.length = cnfOfRows16 [rowsZZMMU5] := by decide +kernel
theorem ZZMMUe6 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length)).take rowsZZMMU6.length = cnfOfRows16 [rowsZZMMU6] := by decide +kernel
theorem ZZMMUe7 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length)).take rowsZZMMU7.length = cnfOfRows16 [rowsZZMMU7] := by decide +kernel
theorem ZZMMUe8 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length)).take rowsZZMMU8.length = cnfOfRows16 [rowsZZMMU8] := by decide +kernel
theorem ZZMMUe9 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length + rowsZZMMU8.length)).take rowsZZMMU9.length = cnfOfRows16 [rowsZZMMU9] := by decide +kernel
theorem ZZMMUe10 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length + rowsZZMMU8.length + rowsZZMMU9.length)).take rowsZZMMU10.length = cnfOfRows16 [rowsZZMMU10] := by decide +kernel
theorem ZZMMUe11 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length + rowsZZMMU8.length + rowsZZMMU9.length + rowsZZMMU10.length)).take rowsZZMMU11.length = cnfOfRows16 [rowsZZMMU11] := by decide +kernel
theorem ZZMMUe12 : (ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length + rowsZZMMU8.length + rowsZZMMU9.length + rowsZZMMU10.length + rowsZZMMU11.length)).take rowsZZMMU12.length = cnfOfRows16 [rowsZZMMU12] := by decide +kernel
theorem ZZMMUeEnd : ZZMMUCnf.drop (0 + rowsZZMMU0.length + rowsZZMMU1.length + rowsZZMMU2.length + rowsZZMMU3.length + rowsZZMMU4.length + rowsZZMMU5.length + rowsZZMMU6.length + rowsZZMMU7.length + rowsZZMMU8.length + rowsZZMMU9.length + rowsZZMMU10.length + rowsZZMMU11.length + rowsZZMMU12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMMU : cnfOfRows16 rowsZZMMU = ZZMMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMMU ZZMMUCnf 0 ⟨ZZMMUe0, ZZMMUe1, ZZMMUe2, ZZMMUe3, ZZMMUe4, ZZMMUe5, ZZMMUe6, ZZMMUe7, ZZMMUe8, ZZMMUe9, ZZMMUe10, ZZMMUe11, ZZMMUe12, ZZMMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMMU : Minimality.H16.SAT.CoreUnsat rowsZZMMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00--` of type 16 is Rupert**: `Core16TW 0 0 (-1) (-1)`. -/
theorem rupert_of_coreZZMMU : Minimality.H16.SAT.Core16TW 0 0 (-1) (-1) := rupert_of_core_dataZZMMU coreUnsatZZMMU

end Minimality.H16K.SAT
