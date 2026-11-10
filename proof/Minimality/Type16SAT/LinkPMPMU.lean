module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMPMU
public import Minimality.Type16SAT.ChkPMPMU

@[expose] public section

/-!
# Type 16, J7/J8: core PMPMU, `CoreUnsat rowsPMPMU` from the kernel-checked LRAT proof, and `rupert_of_corePMPMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMPMUe0 : (PMPMUCnf.drop (0)).take rowsPMPMU0.length = cnfOfRows16 [rowsPMPMU0] := by decide +kernel
theorem PMPMUe1 : (PMPMUCnf.drop (0 + rowsPMPMU0.length)).take rowsPMPMU1.length = cnfOfRows16 [rowsPMPMU1] := by decide +kernel
theorem PMPMUe2 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length)).take rowsPMPMU2.length = cnfOfRows16 [rowsPMPMU2] := by decide +kernel
theorem PMPMUe3 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length)).take rowsPMPMU3.length = cnfOfRows16 [rowsPMPMU3] := by decide +kernel
theorem PMPMUe4 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length)).take rowsPMPMU4.length = cnfOfRows16 [rowsPMPMU4] := by decide +kernel
theorem PMPMUe5 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length)).take rowsPMPMU5.length = cnfOfRows16 [rowsPMPMU5] := by decide +kernel
theorem PMPMUe6 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length)).take rowsPMPMU6.length = cnfOfRows16 [rowsPMPMU6] := by decide +kernel
theorem PMPMUe7 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length)).take rowsPMPMU7.length = cnfOfRows16 [rowsPMPMU7] := by decide +kernel
theorem PMPMUe8 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length)).take rowsPMPMU8.length = cnfOfRows16 [rowsPMPMU8] := by decide +kernel
theorem PMPMUe9 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length + rowsPMPMU8.length)).take rowsPMPMU9.length = cnfOfRows16 [rowsPMPMU9] := by decide +kernel
theorem PMPMUe10 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length + rowsPMPMU8.length + rowsPMPMU9.length)).take rowsPMPMU10.length = cnfOfRows16 [rowsPMPMU10] := by decide +kernel
theorem PMPMUe11 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length + rowsPMPMU8.length + rowsPMPMU9.length + rowsPMPMU10.length)).take rowsPMPMU11.length = cnfOfRows16 [rowsPMPMU11] := by decide +kernel
theorem PMPMUe12 : (PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length + rowsPMPMU8.length + rowsPMPMU9.length + rowsPMPMU10.length + rowsPMPMU11.length)).take rowsPMPMU12.length = cnfOfRows16 [rowsPMPMU12] := by decide +kernel
theorem PMPMUeEnd : PMPMUCnf.drop (0 + rowsPMPMU0.length + rowsPMPMU1.length + rowsPMPMU2.length + rowsPMPMU3.length + rowsPMPMU4.length + rowsPMPMU5.length + rowsPMPMU6.length + rowsPMPMU7.length + rowsPMPMU8.length + rowsPMPMU9.length + rowsPMPMU10.length + rowsPMPMU11.length + rowsPMPMU12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMPMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMPMU : cnfOfRows16 rowsPMPMU = PMPMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMPMU PMPMUCnf 0 ⟨PMPMUe0, PMPMUe1, PMPMUe2, PMPMUe3, PMPMUe4, PMPMUe5, PMPMUe6, PMPMUe7, PMPMUe8, PMPMUe9, PMPMUe10, PMPMUe11, PMPMUe12, PMPMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMPMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMPMU : Minimality.H16.SAT.CoreUnsat rowsPMPMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMPMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMPMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+-+-` of type 16 is Rupert**: `Core16T 1 (-1) 1 (-1)`. -/
theorem rupert_of_corePMPMU : Minimality.H16.SAT.Core16T 1 (-1) 1 (-1) := rupert_of_core_dataPMPMU coreUnsatPMPMU

end Minimality.H16K.SAT
