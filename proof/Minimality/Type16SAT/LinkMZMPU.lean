module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZMPU
public import Minimality.Type16SAT.ChkMZMPU

@[expose] public section

/-!
# Type 16, J7/J8: core MZMPU, `CoreUnsat rowsMZMPU` from the kernel-checked LRAT proof, and `rupert_of_coreMZMPU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZMPUe0 : (MZMPUCnf.drop (0)).take rowsMZMPU0.length = cnfOfRows16 [rowsMZMPU0] := by decide +kernel
theorem MZMPUe1 : (MZMPUCnf.drop (0 + rowsMZMPU0.length)).take rowsMZMPU1.length = cnfOfRows16 [rowsMZMPU1] := by decide +kernel
theorem MZMPUe2 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length)).take rowsMZMPU2.length = cnfOfRows16 [rowsMZMPU2] := by decide +kernel
theorem MZMPUe3 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length)).take rowsMZMPU3.length = cnfOfRows16 [rowsMZMPU3] := by decide +kernel
theorem MZMPUe4 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length)).take rowsMZMPU4.length = cnfOfRows16 [rowsMZMPU4] := by decide +kernel
theorem MZMPUe5 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length + rowsMZMPU4.length)).take rowsMZMPU5.length = cnfOfRows16 [rowsMZMPU5] := by decide +kernel
theorem MZMPUe6 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length + rowsMZMPU4.length + rowsMZMPU5.length)).take rowsMZMPU6.length = cnfOfRows16 [rowsMZMPU6] := by decide +kernel
theorem MZMPUe7 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length + rowsMZMPU4.length + rowsMZMPU5.length + rowsMZMPU6.length)).take rowsMZMPU7.length = cnfOfRows16 [rowsMZMPU7] := by decide +kernel
theorem MZMPUe8 : (MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length + rowsMZMPU4.length + rowsMZMPU5.length + rowsMZMPU6.length + rowsMZMPU7.length)).take rowsMZMPU8.length = cnfOfRows16 [rowsMZMPU8] := by decide +kernel
theorem MZMPUeEnd : MZMPUCnf.drop (0 + rowsMZMPU0.length + rowsMZMPU1.length + rowsMZMPU2.length + rowsMZMPU3.length + rowsMZMPU4.length + rowsMZMPU5.length + rowsMZMPU6.length + rowsMZMPU7.length + rowsMZMPU8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZMPU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZMPU : cnfOfRows16 rowsMZMPU = MZMPUCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZMPU MZMPUCnf 0 ⟨MZMPUe0, MZMPUe1, MZMPUe2, MZMPUe3, MZMPUe4, MZMPUe5, MZMPUe6, MZMPUe7, MZMPUe8, MZMPUeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZMPU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZMPU : Minimality.H16.SAT.CoreUnsat rowsMZMPU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZMPUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZMPU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0-+` of type 16 is Rupert**: `Core16TW (-1) 0 (-1) 1`. -/
theorem rupert_of_coreMZMPU : Minimality.H16.SAT.Core16TW (-1) 0 (-1) 1 := rupert_of_core_dataMZMPU coreUnsatMZMPU

end Minimality.H16K.SAT
