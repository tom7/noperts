module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPPMP
public import Minimality.Type16SAT.ChkPPMP

@[expose] public section

/-!
# Type 16, J7/J8: core PPMP, `CoreUnsat rowsPPMP` from the kernel-checked LRAT proof, and `rupert_of_corePPMP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PPMPe0 : (PPMPCnf.drop (0)).take rowsPPMP0.length = cnfOfRows16 [rowsPPMP0] := by decide +kernel
theorem PPMPe1 : (PPMPCnf.drop (0 + rowsPPMP0.length)).take rowsPPMP1.length = cnfOfRows16 [rowsPPMP1] := by decide +kernel
theorem PPMPe2 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length)).take rowsPPMP2.length = cnfOfRows16 [rowsPPMP2] := by decide +kernel
theorem PPMPe3 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length)).take rowsPPMP3.length = cnfOfRows16 [rowsPPMP3] := by decide +kernel
theorem PPMPe4 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length)).take rowsPPMP4.length = cnfOfRows16 [rowsPPMP4] := by decide +kernel
theorem PPMPe5 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length)).take rowsPPMP5.length = cnfOfRows16 [rowsPPMP5] := by decide +kernel
theorem PPMPe6 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length)).take rowsPPMP6.length = cnfOfRows16 [rowsPPMP6] := by decide +kernel
theorem PPMPe7 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length + rowsPPMP6.length)).take rowsPPMP7.length = cnfOfRows16 [rowsPPMP7] := by decide +kernel
theorem PPMPe8 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length + rowsPPMP6.length + rowsPPMP7.length)).take rowsPPMP8.length = cnfOfRows16 [rowsPPMP8] := by decide +kernel
theorem PPMPe9 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length + rowsPPMP6.length + rowsPPMP7.length + rowsPPMP8.length)).take rowsPPMP9.length = cnfOfRows16 [rowsPPMP9] := by decide +kernel
theorem PPMPe10 : (PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length + rowsPPMP6.length + rowsPPMP7.length + rowsPPMP8.length + rowsPPMP9.length)).take rowsPPMP10.length = cnfOfRows16 [rowsPPMP10] := by decide +kernel
theorem PPMPeEnd : PPMPCnf.drop (0 + rowsPPMP0.length + rowsPPMP1.length + rowsPPMP2.length + rowsPPMP3.length + rowsPPMP4.length + rowsPPMP5.length + rowsPPMP6.length + rowsPPMP7.length + rowsPPMP8.length + rowsPPMP9.length + rowsPPMP10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PPMP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPPMP : cnfOfRows16 rowsPPMP = PPMPCnf := by
  have h := cnfOfRows16_of_chkAt rowsPPMP PPMPCnf 0 ⟨PPMPe0, PPMPe1, PPMPe2, PPMPe3, PPMPe4, PPMPe5, PPMPe6, PPMPe7, PPMPe8, PPMPe9, PPMPe10, PPMPeEnd⟩
  simpa using h

/-- **The numbered clauses of core PPMP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPPMP : Minimality.H16.SAT.CoreUnsat rowsPPMP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PPMPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPPMP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `++-+` of type 16 is Rupert**: `Core16 1 1 (-1) 1`. -/
theorem rupert_of_corePPMP : Minimality.H16.SAT.Core16 1 1 (-1) 1 := rupert_of_core_dataPPMP coreUnsatPPMP

end Minimality.H16K.SAT
