module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMZU
public import Minimality.Type16SAT.ChkZZMZU

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMZU, `CoreUnsat rowsZZMZU` from the kernel-checked LRAT proof, and `rupert_of_coreZZMZU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMZUe0 : (ZZMZUCnf.drop (0)).take rowsZZMZU0.length = cnfOfRows16 [rowsZZMZU0] := by decide +kernel
theorem ZZMZUe1 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length)).take rowsZZMZU1.length = cnfOfRows16 [rowsZZMZU1] := by decide +kernel
theorem ZZMZUe2 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length)).take rowsZZMZU2.length = cnfOfRows16 [rowsZZMZU2] := by decide +kernel
theorem ZZMZUe3 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length)).take rowsZZMZU3.length = cnfOfRows16 [rowsZZMZU3] := by decide +kernel
theorem ZZMZUe4 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length)).take rowsZZMZU4.length = cnfOfRows16 [rowsZZMZU4] := by decide +kernel
theorem ZZMZUe5 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length)).take rowsZZMZU5.length = cnfOfRows16 [rowsZZMZU5] := by decide +kernel
theorem ZZMZUe6 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length + rowsZZMZU5.length)).take rowsZZMZU6.length = cnfOfRows16 [rowsZZMZU6] := by decide +kernel
theorem ZZMZUe7 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length + rowsZZMZU5.length + rowsZZMZU6.length)).take rowsZZMZU7.length = cnfOfRows16 [rowsZZMZU7] := by decide +kernel
theorem ZZMZUe8 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length + rowsZZMZU5.length + rowsZZMZU6.length + rowsZZMZU7.length)).take rowsZZMZU8.length = cnfOfRows16 [rowsZZMZU8] := by decide +kernel
theorem ZZMZUe9 : (ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length + rowsZZMZU5.length + rowsZZMZU6.length + rowsZZMZU7.length + rowsZZMZU8.length)).take rowsZZMZU9.length = cnfOfRows16 [rowsZZMZU9] := by decide +kernel
theorem ZZMZUeEnd : ZZMZUCnf.drop (0 + rowsZZMZU0.length + rowsZZMZU1.length + rowsZZMZU2.length + rowsZZMZU3.length + rowsZZMZU4.length + rowsZZMZU5.length + rowsZZMZU6.length + rowsZZMZU7.length + rowsZZMZU8.length + rowsZZMZU9.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMZU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMZU : cnfOfRows16 rowsZZMZU = ZZMZUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMZU ZZMZUCnf 0 ⟨ZZMZUe0, ZZMZUe1, ZZMZUe2, ZZMZUe3, ZZMZUe4, ZZMZUe5, ZZMZUe6, ZZMZUe7, ZZMZUe8, ZZMZUe9, ZZMZUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMZU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMZU : Minimality.H16.SAT.CoreUnsat rowsZZMZU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMZUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMZU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00-0` of type 16 is Rupert**: `Core16TW 0 0 (-1) 0`. -/
theorem rupert_of_coreZZMZU : Minimality.H16.SAT.Core16TW 0 0 (-1) 0 := rupert_of_core_dataZZMZU coreUnsatZZMZU

end Minimality.H16K.SAT
