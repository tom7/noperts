module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZMMU
public import Minimality.Type16SAT.ChkMZMMU

@[expose] public section

/-!
# Type 16, J7/J8: core MZMMU, `CoreUnsat rowsMZMMU` from the kernel-checked LRAT proof, and `rupert_of_coreMZMMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZMMUe0 : (MZMMUCnf.drop (0)).take rowsMZMMU0.length = cnfOfRows16 [rowsMZMMU0] := by decide +kernel
theorem MZMMUe1 : (MZMMUCnf.drop (0 + rowsMZMMU0.length)).take rowsMZMMU1.length = cnfOfRows16 [rowsMZMMU1] := by decide +kernel
theorem MZMMUe2 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length)).take rowsMZMMU2.length = cnfOfRows16 [rowsMZMMU2] := by decide +kernel
theorem MZMMUe3 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length)).take rowsMZMMU3.length = cnfOfRows16 [rowsMZMMU3] := by decide +kernel
theorem MZMMUe4 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length)).take rowsMZMMU4.length = cnfOfRows16 [rowsMZMMU4] := by decide +kernel
theorem MZMMUe5 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length)).take rowsMZMMU5.length = cnfOfRows16 [rowsMZMMU5] := by decide +kernel
theorem MZMMUe6 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length)).take rowsMZMMU6.length = cnfOfRows16 [rowsMZMMU6] := by decide +kernel
theorem MZMMUe7 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length)).take rowsMZMMU7.length = cnfOfRows16 [rowsMZMMU7] := by decide +kernel
theorem MZMMUe8 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length + rowsMZMMU7.length)).take rowsMZMMU8.length = cnfOfRows16 [rowsMZMMU8] := by decide +kernel
theorem MZMMUe9 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length + rowsMZMMU7.length + rowsMZMMU8.length)).take rowsMZMMU9.length = cnfOfRows16 [rowsMZMMU9] := by decide +kernel
theorem MZMMUe10 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length + rowsMZMMU7.length + rowsMZMMU8.length + rowsMZMMU9.length)).take rowsMZMMU10.length = cnfOfRows16 [rowsMZMMU10] := by decide +kernel
theorem MZMMUe11 : (MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length + rowsMZMMU7.length + rowsMZMMU8.length + rowsMZMMU9.length + rowsMZMMU10.length)).take rowsMZMMU11.length = cnfOfRows16 [rowsMZMMU11] := by decide +kernel
theorem MZMMUeEnd : MZMMUCnf.drop (0 + rowsMZMMU0.length + rowsMZMMU1.length + rowsMZMMU2.length + rowsMZMMU3.length + rowsMZMMU4.length + rowsMZMMU5.length + rowsMZMMU6.length + rowsMZMMU7.length + rowsMZMMU8.length + rowsMZMMU9.length + rowsMZMMU10.length + rowsMZMMU11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZMMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZMMU : cnfOfRows16 rowsMZMMU = MZMMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZMMU MZMMUCnf 0 ⟨MZMMUe0, MZMMUe1, MZMMUe2, MZMMUe3, MZMMUe4, MZMMUe5, MZMMUe6, MZMMUe7, MZMMUe8, MZMMUe9, MZMMUe10, MZMMUe11, MZMMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZMMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZMMU : Minimality.H16.SAT.CoreUnsat rowsMZMMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZMMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZMMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0--` of type 16 is Rupert**: `Core16TW (-1) 0 (-1) (-1)`. -/
theorem rupert_of_coreMZMMU : Minimality.H16.SAT.Core16TW (-1) 0 (-1) (-1) := rupert_of_core_dataMZMMU coreUnsatMZMMU

end Minimality.H16K.SAT
