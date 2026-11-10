module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZPM
public import Minimality.Type16SAT.ChkMZPM

@[expose] public section

/-!
# Type 16, J7/J8: core MZPM, `CoreUnsat rowsMZPM` from the kernel-checked LRAT proof, and `rupert_of_coreMZPM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZPMe0 : (MZPMCnf.drop (0)).take rowsMZPM0.length = cnfOfRows16 [rowsMZPM0] := by decide +kernel
theorem MZPMe1 : (MZPMCnf.drop (0 + rowsMZPM0.length)).take rowsMZPM1.length = cnfOfRows16 [rowsMZPM1] := by decide +kernel
theorem MZPMe2 : (MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length)).take rowsMZPM2.length = cnfOfRows16 [rowsMZPM2] := by decide +kernel
theorem MZPMe3 : (MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length + rowsMZPM2.length)).take rowsMZPM3.length = cnfOfRows16 [rowsMZPM3] := by decide +kernel
theorem MZPMe4 : (MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length + rowsMZPM2.length + rowsMZPM3.length)).take rowsMZPM4.length = cnfOfRows16 [rowsMZPM4] := by decide +kernel
theorem MZPMe5 : (MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length + rowsMZPM2.length + rowsMZPM3.length + rowsMZPM4.length)).take rowsMZPM5.length = cnfOfRows16 [rowsMZPM5] := by decide +kernel
theorem MZPMe6 : (MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length + rowsMZPM2.length + rowsMZPM3.length + rowsMZPM4.length + rowsMZPM5.length)).take rowsMZPM6.length = cnfOfRows16 [rowsMZPM6] := by decide +kernel
theorem MZPMeEnd : MZPMCnf.drop (0 + rowsMZPM0.length + rowsMZPM1.length + rowsMZPM2.length + rowsMZPM3.length + rowsMZPM4.length + rowsMZPM5.length + rowsMZPM6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZPM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZPM : cnfOfRows16 rowsMZPM = MZPMCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZPM MZPMCnf 0 ⟨MZPMe0, MZPMe1, MZPMe2, MZPMe3, MZPMe4, MZPMe5, MZPMe6, MZPMeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZPM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZPM : Minimality.H16.SAT.CoreUnsat rowsMZPM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZPMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZPM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0+-` of type 16 is Rupert**: `Core16W (-1) 0 1 (-1)`. -/
theorem rupert_of_coreMZPM : Minimality.H16.SAT.Core16W (-1) 0 1 (-1) := rupert_of_core_dataMZPM coreUnsatMZPM

end Minimality.H16K.SAT
