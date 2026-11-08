module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPPZM
public import Minimality.Type16SAT.ChkPPZM

@[expose] public section

/-!
# Type 16, J7/J8: core PPZM, `CoreUnsat rowsPPZM` from the kernel-checked LRAT proof, and `rupert_of_corePPZM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PPZMe0 : (PPZMCnf.drop (0)).take rowsPPZM0.length = cnfOfRows16 [rowsPPZM0] := by decide +kernel
theorem PPZMe1 : (PPZMCnf.drop (0 + rowsPPZM0.length)).take rowsPPZM1.length = cnfOfRows16 [rowsPPZM1] := by decide +kernel
theorem PPZMe2 : (PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length)).take rowsPPZM2.length = cnfOfRows16 [rowsPPZM2] := by decide +kernel
theorem PPZMe3 : (PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length + rowsPPZM2.length)).take rowsPPZM3.length = cnfOfRows16 [rowsPPZM3] := by decide +kernel
theorem PPZMe4 : (PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length + rowsPPZM2.length + rowsPPZM3.length)).take rowsPPZM4.length = cnfOfRows16 [rowsPPZM4] := by decide +kernel
theorem PPZMe5 : (PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length + rowsPPZM2.length + rowsPPZM3.length + rowsPPZM4.length)).take rowsPPZM5.length = cnfOfRows16 [rowsPPZM5] := by decide +kernel
theorem PPZMe6 : (PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length + rowsPPZM2.length + rowsPPZM3.length + rowsPPZM4.length + rowsPPZM5.length)).take rowsPPZM6.length = cnfOfRows16 [rowsPPZM6] := by decide +kernel
theorem PPZMeEnd : PPZMCnf.drop (0 + rowsPPZM0.length + rowsPPZM1.length + rowsPPZM2.length + rowsPPZM3.length + rowsPPZM4.length + rowsPPZM5.length + rowsPPZM6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PPZM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPPZM : cnfOfRows16 rowsPPZM = PPZMCnf := by
  have h := cnfOfRows16_of_chkAt rowsPPZM PPZMCnf 0 ⟨PPZMe0, PPZMe1, PPZMe2, PPZMe3, PPZMe4, PPZMe5, PPZMe6, PPZMeEnd⟩
  simpa using h

/-- **The numbered clauses of core PPZM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPPZM : Minimality.H16.SAT.CoreUnsat rowsPPZM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PPZMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPPZM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `++0-` of type 16 is Rupert**: `Core16W 1 1 0 (-1)`. -/
theorem rupert_of_corePPZM : Minimality.H16.SAT.Core16W 1 1 0 (-1) := rupert_of_core_dataPPZM coreUnsatPPZM

end Minimality.H16K.SAT
