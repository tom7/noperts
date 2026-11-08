module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMMP
public import Minimality.Type16SAT.ChkPMMP

@[expose] public section

/-!
# Type 16, J7/J8: core PMMP, `CoreUnsat rowsPMMP` from the kernel-checked LRAT proof, and `rupert_of_corePMMP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMMPe0 : (PMMPCnf.drop (0)).take rowsPMMP0.length = cnfOfRows16 [rowsPMMP0] := by decide +kernel
theorem PMMPe1 : (PMMPCnf.drop (0 + rowsPMMP0.length)).take rowsPMMP1.length = cnfOfRows16 [rowsPMMP1] := by decide +kernel
theorem PMMPe2 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length)).take rowsPMMP2.length = cnfOfRows16 [rowsPMMP2] := by decide +kernel
theorem PMMPe3 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length)).take rowsPMMP3.length = cnfOfRows16 [rowsPMMP3] := by decide +kernel
theorem PMMPe4 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length)).take rowsPMMP4.length = cnfOfRows16 [rowsPMMP4] := by decide +kernel
theorem PMMPe5 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length)).take rowsPMMP5.length = cnfOfRows16 [rowsPMMP5] := by decide +kernel
theorem PMMPe6 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length)).take rowsPMMP6.length = cnfOfRows16 [rowsPMMP6] := by decide +kernel
theorem PMMPe7 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length)).take rowsPMMP7.length = cnfOfRows16 [rowsPMMP7] := by decide +kernel
theorem PMMPe8 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length + rowsPMMP7.length)).take rowsPMMP8.length = cnfOfRows16 [rowsPMMP8] := by decide +kernel
theorem PMMPe9 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length + rowsPMMP7.length + rowsPMMP8.length)).take rowsPMMP9.length = cnfOfRows16 [rowsPMMP9] := by decide +kernel
theorem PMMPe10 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length + rowsPMMP7.length + rowsPMMP8.length + rowsPMMP9.length)).take rowsPMMP10.length = cnfOfRows16 [rowsPMMP10] := by decide +kernel
theorem PMMPe11 : (PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length + rowsPMMP7.length + rowsPMMP8.length + rowsPMMP9.length + rowsPMMP10.length)).take rowsPMMP11.length = cnfOfRows16 [rowsPMMP11] := by decide +kernel
theorem PMMPeEnd : PMMPCnf.drop (0 + rowsPMMP0.length + rowsPMMP1.length + rowsPMMP2.length + rowsPMMP3.length + rowsPMMP4.length + rowsPMMP5.length + rowsPMMP6.length + rowsPMMP7.length + rowsPMMP8.length + rowsPMMP9.length + rowsPMMP10.length + rowsPMMP11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMMP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMMP : cnfOfRows16 rowsPMMP = PMMPCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMMP PMMPCnf 0 ⟨PMMPe0, PMMPe1, PMMPe2, PMMPe3, PMMPe4, PMMPe5, PMMPe6, PMMPe7, PMMPe8, PMMPe9, PMMPe10, PMMPe11, PMMPeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMMP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMMP : Minimality.H16.SAT.CoreUnsat rowsPMMP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMMPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMMP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+--+` of type 16 is Rupert**: `Core16 1 (-1) (-1) 1`. -/
theorem rupert_of_corePMMP : Minimality.H16.SAT.Core16 1 (-1) (-1) 1 := rupert_of_core_dataPMMP coreUnsatPMMP

end Minimality.H16K.SAT
