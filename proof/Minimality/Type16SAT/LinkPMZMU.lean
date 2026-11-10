module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMZMU
public import Minimality.Type16SAT.ChkPMZMU

@[expose] public section

/-!
# Type 16, J7/J8: core PMZMU, `CoreUnsat rowsPMZMU` from the kernel-checked LRAT proof, and `rupert_of_corePMZMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMZMUe0 : (PMZMUCnf.drop (0)).take rowsPMZMU0.length = cnfOfRows16 [rowsPMZMU0] := by decide +kernel
theorem PMZMUe1 : (PMZMUCnf.drop (0 + rowsPMZMU0.length)).take rowsPMZMU1.length = cnfOfRows16 [rowsPMZMU1] := by decide +kernel
theorem PMZMUe2 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length)).take rowsPMZMU2.length = cnfOfRows16 [rowsPMZMU2] := by decide +kernel
theorem PMZMUe3 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length)).take rowsPMZMU3.length = cnfOfRows16 [rowsPMZMU3] := by decide +kernel
theorem PMZMUe4 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length)).take rowsPMZMU4.length = cnfOfRows16 [rowsPMZMU4] := by decide +kernel
theorem PMZMUe5 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length)).take rowsPMZMU5.length = cnfOfRows16 [rowsPMZMU5] := by decide +kernel
theorem PMZMUe6 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length)).take rowsPMZMU6.length = cnfOfRows16 [rowsPMZMU6] := by decide +kernel
theorem PMZMUe7 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length)).take rowsPMZMU7.length = cnfOfRows16 [rowsPMZMU7] := by decide +kernel
theorem PMZMUe8 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length)).take rowsPMZMU8.length = cnfOfRows16 [rowsPMZMU8] := by decide +kernel
theorem PMZMUe9 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length)).take rowsPMZMU9.length = cnfOfRows16 [rowsPMZMU9] := by decide +kernel
theorem PMZMUe10 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length + rowsPMZMU9.length)).take rowsPMZMU10.length = cnfOfRows16 [rowsPMZMU10] := by decide +kernel
theorem PMZMUe11 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length + rowsPMZMU9.length + rowsPMZMU10.length)).take rowsPMZMU11.length = cnfOfRows16 [rowsPMZMU11] := by decide +kernel
theorem PMZMUe12 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length + rowsPMZMU9.length + rowsPMZMU10.length + rowsPMZMU11.length)).take rowsPMZMU12.length = cnfOfRows16 [rowsPMZMU12] := by decide +kernel
theorem PMZMUe13 : (PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length + rowsPMZMU9.length + rowsPMZMU10.length + rowsPMZMU11.length + rowsPMZMU12.length)).take rowsPMZMU13.length = cnfOfRows16 [rowsPMZMU13] := by decide +kernel
theorem PMZMUeEnd : PMZMUCnf.drop (0 + rowsPMZMU0.length + rowsPMZMU1.length + rowsPMZMU2.length + rowsPMZMU3.length + rowsPMZMU4.length + rowsPMZMU5.length + rowsPMZMU6.length + rowsPMZMU7.length + rowsPMZMU8.length + rowsPMZMU9.length + rowsPMZMU10.length + rowsPMZMU11.length + rowsPMZMU12.length + rowsPMZMU13.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMZMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMZMU : cnfOfRows16 rowsPMZMU = PMZMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMZMU PMZMUCnf 0 ⟨PMZMUe0, PMZMUe1, PMZMUe2, PMZMUe3, PMZMUe4, PMZMUe5, PMZMUe6, PMZMUe7, PMZMUe8, PMZMUe9, PMZMUe10, PMZMUe11, PMZMUe12, PMZMUe13, PMZMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMZMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMZMU : Minimality.H16.SAT.CoreUnsat rowsPMZMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMZMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMZMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+-0-` of type 16 is Rupert**: `Core16TW 1 (-1) 0 (-1)`. -/
theorem rupert_of_corePMZMU : Minimality.H16.SAT.Core16TW 1 (-1) 0 (-1) := rupert_of_core_dataPMZMU coreUnsatPMZMU

end Minimality.H16K.SAT
