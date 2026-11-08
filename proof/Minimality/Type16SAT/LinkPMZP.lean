module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMZP
public import Minimality.Type16SAT.ChkPMZP

@[expose] public section

/-!
# Type 16, J7/J8: core PMZP, `CoreUnsat rowsPMZP` from the kernel-checked LRAT proof, and `rupert_of_corePMZP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMZPe0 : (PMZPCnf.drop (0)).take rowsPMZP0.length = cnfOfRows16 [rowsPMZP0] := by decide +kernel
theorem PMZPe1 : (PMZPCnf.drop (0 + rowsPMZP0.length)).take rowsPMZP1.length = cnfOfRows16 [rowsPMZP1] := by decide +kernel
theorem PMZPe2 : (PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length)).take rowsPMZP2.length = cnfOfRows16 [rowsPMZP2] := by decide +kernel
theorem PMZPe3 : (PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length + rowsPMZP2.length)).take rowsPMZP3.length = cnfOfRows16 [rowsPMZP3] := by decide +kernel
theorem PMZPe4 : (PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length + rowsPMZP2.length + rowsPMZP3.length)).take rowsPMZP4.length = cnfOfRows16 [rowsPMZP4] := by decide +kernel
theorem PMZPe5 : (PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length + rowsPMZP2.length + rowsPMZP3.length + rowsPMZP4.length)).take rowsPMZP5.length = cnfOfRows16 [rowsPMZP5] := by decide +kernel
theorem PMZPe6 : (PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length + rowsPMZP2.length + rowsPMZP3.length + rowsPMZP4.length + rowsPMZP5.length)).take rowsPMZP6.length = cnfOfRows16 [rowsPMZP6] := by decide +kernel
theorem PMZPeEnd : PMZPCnf.drop (0 + rowsPMZP0.length + rowsPMZP1.length + rowsPMZP2.length + rowsPMZP3.length + rowsPMZP4.length + rowsPMZP5.length + rowsPMZP6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMZP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMZP : cnfOfRows16 rowsPMZP = PMZPCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMZP PMZPCnf 0 ⟨PMZPe0, PMZPe1, PMZPe2, PMZPe3, PMZPe4, PMZPe5, PMZPe6, PMZPeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMZP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMZP : Minimality.H16.SAT.CoreUnsat rowsPMZP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMZPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMZP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+-0+` of type 16 is Rupert**: `Core16W 1 (-1) 0 1`. -/
theorem rupert_of_corePMZP : Minimality.H16.SAT.Core16W 1 (-1) 0 1 := rupert_of_core_dataPMZP coreUnsatPMZP

end Minimality.H16K.SAT
