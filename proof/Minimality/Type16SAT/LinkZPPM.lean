module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZPPM
public import Minimality.Type16SAT.ChkZPPM

@[expose] public section

/-!
# Type 16, J7/J8: core ZPPM, `CoreUnsat rowsZPPM` from the kernel-checked LRAT proof, and `rupert_of_coreZPPM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZPPMe0 : (ZPPMCnf.drop (0)).take rowsZPPM0.length = cnfOfRows16 [rowsZPPM0] := by decide +kernel
theorem ZPPMe1 : (ZPPMCnf.drop (0 + rowsZPPM0.length)).take rowsZPPM1.length = cnfOfRows16 [rowsZPPM1] := by decide +kernel
theorem ZPPMe2 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length)).take rowsZPPM2.length = cnfOfRows16 [rowsZPPM2] := by decide +kernel
theorem ZPPMe3 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length)).take rowsZPPM3.length = cnfOfRows16 [rowsZPPM3] := by decide +kernel
theorem ZPPMe4 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length + rowsZPPM3.length)).take rowsZPPM4.length = cnfOfRows16 [rowsZPPM4] := by decide +kernel
theorem ZPPMe5 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length + rowsZPPM3.length + rowsZPPM4.length)).take rowsZPPM5.length = cnfOfRows16 [rowsZPPM5] := by decide +kernel
theorem ZPPMe6 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length + rowsZPPM3.length + rowsZPPM4.length + rowsZPPM5.length)).take rowsZPPM6.length = cnfOfRows16 [rowsZPPM6] := by decide +kernel
theorem ZPPMe7 : (ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length + rowsZPPM3.length + rowsZPPM4.length + rowsZPPM5.length + rowsZPPM6.length)).take rowsZPPM7.length = cnfOfRows16 [rowsZPPM7] := by decide +kernel
theorem ZPPMeEnd : ZPPMCnf.drop (0 + rowsZPPM0.length + rowsZPPM1.length + rowsZPPM2.length + rowsZPPM3.length + rowsZPPM4.length + rowsZPPM5.length + rowsZPPM6.length + rowsZPPM7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZPPM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZPPM : cnfOfRows16 rowsZPPM = ZPPMCnf := by
  have h := cnfOfRows16_of_chkAt rowsZPPM ZPPMCnf 0 ⟨ZPPMe0, ZPPMe1, ZPPMe2, ZPPMe3, ZPPMe4, ZPPMe5, ZPPMe6, ZPPMe7, ZPPMeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZPPM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZPPM : Minimality.H16.SAT.CoreUnsat rowsZPPM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZPPMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZPPM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0++-` of type 16 is Rupert**: `Core16W 0 1 1 (-1)`. -/
theorem rupert_of_coreZPPM : Minimality.H16.SAT.Core16W 0 1 1 (-1) := rupert_of_core_dataZPPM coreUnsatZPPM

end Minimality.H16K.SAT
