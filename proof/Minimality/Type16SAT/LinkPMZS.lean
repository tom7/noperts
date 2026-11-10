module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMZS
public import Minimality.Type16SAT.ChkPMZS

@[expose] public section

/-!
# Type 16, J7/J8: core PMZS, `CoreUnsat rowsPMZS` from the kernel-checked LRAT proof, and `rupert_of_corePMZS`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMZSe0 : (PMZSCnf.drop (0)).take rowsPMZS0.length = cnfOfRows16 [rowsPMZS0] := by decide +kernel
theorem PMZSe1 : (PMZSCnf.drop (0 + rowsPMZS0.length)).take rowsPMZS1.length = cnfOfRows16 [rowsPMZS1] := by decide +kernel
theorem PMZSe2 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length)).take rowsPMZS2.length = cnfOfRows16 [rowsPMZS2] := by decide +kernel
theorem PMZSe3 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length)).take rowsPMZS3.length = cnfOfRows16 [rowsPMZS3] := by decide +kernel
theorem PMZSe4 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length)).take rowsPMZS4.length = cnfOfRows16 [rowsPMZS4] := by decide +kernel
theorem PMZSe5 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length)).take rowsPMZS5.length = cnfOfRows16 [rowsPMZS5] := by decide +kernel
theorem PMZSe6 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length)).take rowsPMZS6.length = cnfOfRows16 [rowsPMZS6] := by decide +kernel
theorem PMZSe7 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length)).take rowsPMZS7.length = cnfOfRows16 [rowsPMZS7] := by decide +kernel
theorem PMZSe8 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length)).take rowsPMZS8.length = cnfOfRows16 [rowsPMZS8] := by decide +kernel
theorem PMZSe9 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length + rowsPMZS8.length)).take rowsPMZS9.length = cnfOfRows16 [rowsPMZS9] := by decide +kernel
theorem PMZSe10 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length + rowsPMZS8.length + rowsPMZS9.length)).take rowsPMZS10.length = cnfOfRows16 [rowsPMZS10] := by decide +kernel
theorem PMZSe11 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length + rowsPMZS8.length + rowsPMZS9.length + rowsPMZS10.length)).take rowsPMZS11.length = cnfOfRows16 [rowsPMZS11] := by decide +kernel
theorem PMZSe12 : (PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length + rowsPMZS8.length + rowsPMZS9.length + rowsPMZS10.length + rowsPMZS11.length)).take rowsPMZS12.length = cnfOfRows16 [rowsPMZS12] := by decide +kernel
theorem PMZSeEnd : PMZSCnf.drop (0 + rowsPMZS0.length + rowsPMZS1.length + rowsPMZS2.length + rowsPMZS3.length + rowsPMZS4.length + rowsPMZS5.length + rowsPMZS6.length + rowsPMZS7.length + rowsPMZS8.length + rowsPMZS9.length + rowsPMZS10.length + rowsPMZS11.length + rowsPMZS12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMZS (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMZS : cnfOfRows16 rowsPMZS = PMZSCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMZS PMZSCnf 0 ⟨PMZSe0, PMZSe1, PMZSe2, PMZSe3, PMZSe4, PMZSe5, PMZSe6, PMZSe7, PMZSe8, PMZSe9, PMZSe10, PMZSe11, PMZSe12, PMZSeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMZS are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMZS : Minimality.H16.SAT.CoreUnsat rowsPMZS := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMZSunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMZS] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+---` of type 16 is Rupert**: `Core16Z 1 (-1) (-1) (-1)`. -/
theorem rupert_of_corePMZS : Minimality.H16.SAT.Core16Z 1 (-1) (-1) (-1) := rupert_of_core_dataPMZS coreUnsatPMZS

end Minimality.H16K.SAT
