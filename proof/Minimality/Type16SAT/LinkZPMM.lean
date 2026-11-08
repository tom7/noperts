module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZPMM
public import Minimality.Type16SAT.ChkZPMM

@[expose] public section

/-!
# Type 16, J7/J8: core ZPMM, `CoreUnsat rowsZPMM` from the kernel-checked LRAT proof, and `rupert_of_coreZPMM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZPMMe0 : (ZPMMCnf.drop (0)).take rowsZPMM0.length = cnfOfRows16 [rowsZPMM0] := by decide +kernel
theorem ZPMMe1 : (ZPMMCnf.drop (0 + rowsZPMM0.length)).take rowsZPMM1.length = cnfOfRows16 [rowsZPMM1] := by decide +kernel
theorem ZPMMe2 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length)).take rowsZPMM2.length = cnfOfRows16 [rowsZPMM2] := by decide +kernel
theorem ZPMMe3 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length)).take rowsZPMM3.length = cnfOfRows16 [rowsZPMM3] := by decide +kernel
theorem ZPMMe4 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length)).take rowsZPMM4.length = cnfOfRows16 [rowsZPMM4] := by decide +kernel
theorem ZPMMe5 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length)).take rowsZPMM5.length = cnfOfRows16 [rowsZPMM5] := by decide +kernel
theorem ZPMMe6 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length)).take rowsZPMM6.length = cnfOfRows16 [rowsZPMM6] := by decide +kernel
theorem ZPMMe7 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length)).take rowsZPMM7.length = cnfOfRows16 [rowsZPMM7] := by decide +kernel
theorem ZPMMe8 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length)).take rowsZPMM8.length = cnfOfRows16 [rowsZPMM8] := by decide +kernel
theorem ZPMMe9 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length)).take rowsZPMM9.length = cnfOfRows16 [rowsZPMM9] := by decide +kernel
theorem ZPMMe10 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length + rowsZPMM9.length)).take rowsZPMM10.length = cnfOfRows16 [rowsZPMM10] := by decide +kernel
theorem ZPMMe11 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length + rowsZPMM9.length + rowsZPMM10.length)).take rowsZPMM11.length = cnfOfRows16 [rowsZPMM11] := by decide +kernel
theorem ZPMMe12 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length + rowsZPMM9.length + rowsZPMM10.length + rowsZPMM11.length)).take rowsZPMM12.length = cnfOfRows16 [rowsZPMM12] := by decide +kernel
theorem ZPMMe13 : (ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length + rowsZPMM9.length + rowsZPMM10.length + rowsZPMM11.length + rowsZPMM12.length)).take rowsZPMM13.length = cnfOfRows16 [rowsZPMM13] := by decide +kernel
theorem ZPMMeEnd : ZPMMCnf.drop (0 + rowsZPMM0.length + rowsZPMM1.length + rowsZPMM2.length + rowsZPMM3.length + rowsZPMM4.length + rowsZPMM5.length + rowsZPMM6.length + rowsZPMM7.length + rowsZPMM8.length + rowsZPMM9.length + rowsZPMM10.length + rowsZPMM11.length + rowsZPMM12.length + rowsZPMM13.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZPMM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZPMM : cnfOfRows16 rowsZPMM = ZPMMCnf := by
  have h := cnfOfRows16_of_chkAt rowsZPMM ZPMMCnf 0 ⟨ZPMMe0, ZPMMe1, ZPMMe2, ZPMMe3, ZPMMe4, ZPMMe5, ZPMMe6, ZPMMe7, ZPMMe8, ZPMMe9, ZPMMe10, ZPMMe11, ZPMMe12, ZPMMe13, ZPMMeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZPMM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZPMM : Minimality.H16.SAT.CoreUnsat rowsZPMM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZPMMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZPMM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0+--` of type 16 is Rupert**: `Core16W 0 1 (-1) (-1)`. -/
theorem rupert_of_coreZPMM : Minimality.H16.SAT.Core16W 0 1 (-1) (-1) := rupert_of_core_dataZPMM coreUnsatZPMM

end Minimality.H16K.SAT
