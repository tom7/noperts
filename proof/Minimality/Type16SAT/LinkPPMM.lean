module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPPMM
public import Minimality.Type16SAT.ChkPPMM

@[expose] public section

/-!
# Type 16, J7/J8: core PPMM, `CoreUnsat rowsPPMM` from the kernel-checked LRAT proof, and `rupert_of_corePPMM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PPMMe0 : (PPMMCnf.drop (0)).take rowsPPMM0.length = cnfOfRows16 [rowsPPMM0] := by decide +kernel
theorem PPMMe1 : (PPMMCnf.drop (0 + rowsPPMM0.length)).take rowsPPMM1.length = cnfOfRows16 [rowsPPMM1] := by decide +kernel
theorem PPMMe2 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length)).take rowsPPMM2.length = cnfOfRows16 [rowsPPMM2] := by decide +kernel
theorem PPMMe3 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length)).take rowsPPMM3.length = cnfOfRows16 [rowsPPMM3] := by decide +kernel
theorem PPMMe4 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length)).take rowsPPMM4.length = cnfOfRows16 [rowsPPMM4] := by decide +kernel
theorem PPMMe5 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length)).take rowsPPMM5.length = cnfOfRows16 [rowsPPMM5] := by decide +kernel
theorem PPMMe6 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length)).take rowsPPMM6.length = cnfOfRows16 [rowsPPMM6] := by decide +kernel
theorem PPMMe7 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length)).take rowsPPMM7.length = cnfOfRows16 [rowsPPMM7] := by decide +kernel
theorem PPMMe8 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length + rowsPPMM7.length)).take rowsPPMM8.length = cnfOfRows16 [rowsPPMM8] := by decide +kernel
theorem PPMMe9 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length + rowsPPMM7.length + rowsPPMM8.length)).take rowsPPMM9.length = cnfOfRows16 [rowsPPMM9] := by decide +kernel
theorem PPMMe10 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length + rowsPPMM7.length + rowsPPMM8.length + rowsPPMM9.length)).take rowsPPMM10.length = cnfOfRows16 [rowsPPMM10] := by decide +kernel
theorem PPMMe11 : (PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length + rowsPPMM7.length + rowsPPMM8.length + rowsPPMM9.length + rowsPPMM10.length)).take rowsPPMM11.length = cnfOfRows16 [rowsPPMM11] := by decide +kernel
theorem PPMMeEnd : PPMMCnf.drop (0 + rowsPPMM0.length + rowsPPMM1.length + rowsPPMM2.length + rowsPPMM3.length + rowsPPMM4.length + rowsPPMM5.length + rowsPPMM6.length + rowsPPMM7.length + rowsPPMM8.length + rowsPPMM9.length + rowsPPMM10.length + rowsPPMM11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PPMM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPPMM : cnfOfRows16 rowsPPMM = PPMMCnf := by
  have h := cnfOfRows16_of_chkAt rowsPPMM PPMMCnf 0 ⟨PPMMe0, PPMMe1, PPMMe2, PPMMe3, PPMMe4, PPMMe5, PPMMe6, PPMMe7, PPMMe8, PPMMe9, PPMMe10, PPMMe11, PPMMeEnd⟩
  simpa using h

/-- **The numbered clauses of core PPMM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPPMM : Minimality.H16.SAT.CoreUnsat rowsPPMM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PPMMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPPMM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `++--` of type 16 is Rupert**: `Core16 1 1 (-1) (-1)`. -/
theorem rupert_of_corePPMM : Minimality.H16.SAT.Core16 1 1 (-1) (-1) := rupert_of_core_dataPPMM coreUnsatPPMM

end Minimality.H16K.SAT
