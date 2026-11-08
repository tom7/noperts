module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPPZP
public import Minimality.Type16SAT.ChkPPZP

@[expose] public section

/-!
# Type 16, J7/J8: core PPZP, `CoreUnsat rowsPPZP` from the kernel-checked LRAT proof, and `rupert_of_corePPZP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PPZPe0 : (PPZPCnf.drop (0)).take rowsPPZP0.length = cnfOfRows16 [rowsPPZP0] := by decide +kernel
theorem PPZPe1 : (PPZPCnf.drop (0 + rowsPPZP0.length)).take rowsPPZP1.length = cnfOfRows16 [rowsPPZP1] := by decide +kernel
theorem PPZPe2 : (PPZPCnf.drop (0 + rowsPPZP0.length + rowsPPZP1.length)).take rowsPPZP2.length = cnfOfRows16 [rowsPPZP2] := by decide +kernel
theorem PPZPeEnd : PPZPCnf.drop (0 + rowsPPZP0.length + rowsPPZP1.length + rowsPPZP2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PPZP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPPZP : cnfOfRows16 rowsPPZP = PPZPCnf := by
  have h := cnfOfRows16_of_chkAt rowsPPZP PPZPCnf 0 ⟨PPZPe0, PPZPe1, PPZPe2, PPZPeEnd⟩
  simpa using h

/-- **The numbered clauses of core PPZP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPPZP : Minimality.H16.SAT.CoreUnsat rowsPPZP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PPZPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPPZP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `++0+` of type 16 is Rupert**: `Core16W 1 1 0 1`. -/
theorem rupert_of_corePPZP : Minimality.H16.SAT.Core16W 1 1 0 1 := rupert_of_core_dataPPZP coreUnsatPPZP

end Minimality.H16K.SAT
