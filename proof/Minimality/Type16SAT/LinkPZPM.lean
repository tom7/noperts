module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZPM
public import Minimality.Type16SAT.ChkPZPM

@[expose] public section

/-!
# Type 16, J7/J8: core PZPM, `CoreUnsat rowsPZPM` from the kernel-checked LRAT proof, and `rupert_of_corePZPM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZPMe0 : (PZPMCnf.drop (0)).take rowsPZPM0.length = cnfOfRows16 [rowsPZPM0] := by decide +kernel
theorem PZPMe1 : (PZPMCnf.drop (0 + rowsPZPM0.length)).take rowsPZPM1.length = cnfOfRows16 [rowsPZPM1] := by decide +kernel
theorem PZPMe2 : (PZPMCnf.drop (0 + rowsPZPM0.length + rowsPZPM1.length)).take rowsPZPM2.length = cnfOfRows16 [rowsPZPM2] := by decide +kernel
theorem PZPMe3 : (PZPMCnf.drop (0 + rowsPZPM0.length + rowsPZPM1.length + rowsPZPM2.length)).take rowsPZPM3.length = cnfOfRows16 [rowsPZPM3] := by decide +kernel
theorem PZPMe4 : (PZPMCnf.drop (0 + rowsPZPM0.length + rowsPZPM1.length + rowsPZPM2.length + rowsPZPM3.length)).take rowsPZPM4.length = cnfOfRows16 [rowsPZPM4] := by decide +kernel
theorem PZPMeEnd : PZPMCnf.drop (0 + rowsPZPM0.length + rowsPZPM1.length + rowsPZPM2.length + rowsPZPM3.length + rowsPZPM4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZPM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZPM : cnfOfRows16 rowsPZPM = PZPMCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZPM PZPMCnf 0 ⟨PZPMe0, PZPMe1, PZPMe2, PZPMe3, PZPMe4, PZPMeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZPM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZPM : Minimality.H16.SAT.CoreUnsat rowsPZPM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZPMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZPM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0+-` of type 16 is Rupert**: `Core16W 1 0 1 (-1)`. -/
theorem rupert_of_corePZPM : Minimality.H16.SAT.Core16W 1 0 1 (-1) := rupert_of_core_dataPZPM coreUnsatPZPM

end Minimality.H16K.SAT
