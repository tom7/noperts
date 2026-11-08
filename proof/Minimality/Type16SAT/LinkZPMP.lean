module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZPMP
public import Minimality.Type16SAT.ChkZPMP

@[expose] public section

/-!
# Type 16, J7/J8: core ZPMP, `CoreUnsat rowsZPMP` from the kernel-checked LRAT proof, and `rupert_of_coreZPMP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZPMPe0 : (ZPMPCnf.drop (0)).take rowsZPMP0.length = cnfOfRows16 [rowsZPMP0] := by decide +kernel
theorem ZPMPe1 : (ZPMPCnf.drop (0 + rowsZPMP0.length)).take rowsZPMP1.length = cnfOfRows16 [rowsZPMP1] := by decide +kernel
theorem ZPMPe2 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length)).take rowsZPMP2.length = cnfOfRows16 [rowsZPMP2] := by decide +kernel
theorem ZPMPe3 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length)).take rowsZPMP3.length = cnfOfRows16 [rowsZPMP3] := by decide +kernel
theorem ZPMPe4 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length)).take rowsZPMP4.length = cnfOfRows16 [rowsZPMP4] := by decide +kernel
theorem ZPMPe5 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length)).take rowsZPMP5.length = cnfOfRows16 [rowsZPMP5] := by decide +kernel
theorem ZPMPe6 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length)).take rowsZPMP6.length = cnfOfRows16 [rowsZPMP6] := by decide +kernel
theorem ZPMPe7 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length)).take rowsZPMP7.length = cnfOfRows16 [rowsZPMP7] := by decide +kernel
theorem ZPMPe8 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length + rowsZPMP7.length)).take rowsZPMP8.length = cnfOfRows16 [rowsZPMP8] := by decide +kernel
theorem ZPMPe9 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length + rowsZPMP7.length + rowsZPMP8.length)).take rowsZPMP9.length = cnfOfRows16 [rowsZPMP9] := by decide +kernel
theorem ZPMPe10 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length + rowsZPMP7.length + rowsZPMP8.length + rowsZPMP9.length)).take rowsZPMP10.length = cnfOfRows16 [rowsZPMP10] := by decide +kernel
theorem ZPMPe11 : (ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length + rowsZPMP7.length + rowsZPMP8.length + rowsZPMP9.length + rowsZPMP10.length)).take rowsZPMP11.length = cnfOfRows16 [rowsZPMP11] := by decide +kernel
theorem ZPMPeEnd : ZPMPCnf.drop (0 + rowsZPMP0.length + rowsZPMP1.length + rowsZPMP2.length + rowsZPMP3.length + rowsZPMP4.length + rowsZPMP5.length + rowsZPMP6.length + rowsZPMP7.length + rowsZPMP8.length + rowsZPMP9.length + rowsZPMP10.length + rowsZPMP11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZPMP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZPMP : cnfOfRows16 rowsZPMP = ZPMPCnf := by
  have h := cnfOfRows16_of_chkAt rowsZPMP ZPMPCnf 0 ⟨ZPMPe0, ZPMPe1, ZPMPe2, ZPMPe3, ZPMPe4, ZPMPe5, ZPMPe6, ZPMPe7, ZPMPe8, ZPMPe9, ZPMPe10, ZPMPe11, ZPMPeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZPMP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZPMP : Minimality.H16.SAT.CoreUnsat rowsZPMP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZPMPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZPMP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0+-+` of type 16 is Rupert**: `Core16W 0 1 (-1) 1`. -/
theorem rupert_of_coreZPMP : Minimality.H16.SAT.Core16W 0 1 (-1) 1 := rupert_of_core_dataZPMP coreUnsatZPMP

end Minimality.H16K.SAT
