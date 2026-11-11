module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMMMU
public import Minimality.Type16SAT.ChkZMMMU

@[expose] public section

/-!
# Type 16, J7/J8: core ZMMMU, `CoreUnsat rowsZMMMU` from the kernel-checked LRAT proof, and `rupert_of_coreZMMMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMMMUe0 : (ZMMMUCnf.drop (0)).take rowsZMMMU0.length = cnfOfRows16 [rowsZMMMU0] := by decide +kernel
theorem ZMMMUe1 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length)).take rowsZMMMU1.length = cnfOfRows16 [rowsZMMMU1] := by decide +kernel
theorem ZMMMUe2 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length)).take rowsZMMMU2.length = cnfOfRows16 [rowsZMMMU2] := by decide +kernel
theorem ZMMMUe3 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length)).take rowsZMMMU3.length = cnfOfRows16 [rowsZMMMU3] := by decide +kernel
theorem ZMMMUe4 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length)).take rowsZMMMU4.length = cnfOfRows16 [rowsZMMMU4] := by decide +kernel
theorem ZMMMUe5 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length)).take rowsZMMMU5.length = cnfOfRows16 [rowsZMMMU5] := by decide +kernel
theorem ZMMMUe6 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length)).take rowsZMMMU6.length = cnfOfRows16 [rowsZMMMU6] := by decide +kernel
theorem ZMMMUe7 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length)).take rowsZMMMU7.length = cnfOfRows16 [rowsZMMMU7] := by decide +kernel
theorem ZMMMUe8 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length)).take rowsZMMMU8.length = cnfOfRows16 [rowsZMMMU8] := by decide +kernel
theorem ZMMMUe9 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length + rowsZMMMU8.length)).take rowsZMMMU9.length = cnfOfRows16 [rowsZMMMU9] := by decide +kernel
theorem ZMMMUe10 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length + rowsZMMMU8.length + rowsZMMMU9.length)).take rowsZMMMU10.length = cnfOfRows16 [rowsZMMMU10] := by decide +kernel
theorem ZMMMUe11 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length + rowsZMMMU8.length + rowsZMMMU9.length + rowsZMMMU10.length)).take rowsZMMMU11.length = cnfOfRows16 [rowsZMMMU11] := by decide +kernel
theorem ZMMMUe12 : (ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length + rowsZMMMU8.length + rowsZMMMU9.length + rowsZMMMU10.length + rowsZMMMU11.length)).take rowsZMMMU12.length = cnfOfRows16 [rowsZMMMU12] := by decide +kernel
theorem ZMMMUeEnd : ZMMMUCnf.drop (0 + rowsZMMMU0.length + rowsZMMMU1.length + rowsZMMMU2.length + rowsZMMMU3.length + rowsZMMMU4.length + rowsZMMMU5.length + rowsZMMMU6.length + rowsZMMMU7.length + rowsZMMMU8.length + rowsZMMMU9.length + rowsZMMMU10.length + rowsZMMMU11.length + rowsZMMMU12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMMMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMMMU : cnfOfRows16 rowsZMMMU = ZMMMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMMMU ZMMMUCnf 0 ⟨ZMMMUe0, ZMMMUe1, ZMMMUe2, ZMMMUe3, ZMMMUe4, ZMMMUe5, ZMMMUe6, ZMMMUe7, ZMMMUe8, ZMMMUe9, ZMMMUe10, ZMMMUe11, ZMMMUe12, ZMMMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMMMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMMMU : Minimality.H16.SAT.CoreUnsat rowsZMMMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMMMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMMMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0---` of type 16 is Rupert**: `Core16TW 0 (-1) (-1) (-1)`. -/
theorem rupert_of_coreZMMMU : Minimality.H16.SAT.Core16TW 0 (-1) (-1) (-1) := rupert_of_core_dataZMMMU coreUnsatZMMMU

end Minimality.H16K.SAT
