module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMMM
public import Minimality.Type16SAT.ChkPMMM

@[expose] public section

/-!
# Type 16: core PMMM, `CoreUnsat rowsPMMM` from the kernel-checked LRAT proof, and `rupert_of_corePMMM`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMMMe0 : (PMMMCnf.drop (0)).take rowsPMMM0.length = cnfOfRows16 [rowsPMMM0] := by decide +kernel
theorem PMMMe1 : (PMMMCnf.drop (0 + rowsPMMM0.length)).take rowsPMMM1.length = cnfOfRows16 [rowsPMMM1] := by decide +kernel
theorem PMMMe2 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length)).take rowsPMMM2.length = cnfOfRows16 [rowsPMMM2] := by decide +kernel
theorem PMMMe3 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length)).take rowsPMMM3.length = cnfOfRows16 [rowsPMMM3] := by decide +kernel
theorem PMMMe4 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length)).take rowsPMMM4.length = cnfOfRows16 [rowsPMMM4] := by decide +kernel
theorem PMMMe5 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length)).take rowsPMMM5.length = cnfOfRows16 [rowsPMMM5] := by decide +kernel
theorem PMMMe6 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length)).take rowsPMMM6.length = cnfOfRows16 [rowsPMMM6] := by decide +kernel
theorem PMMMe7 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length + rowsPMMM6.length)).take rowsPMMM7.length = cnfOfRows16 [rowsPMMM7] := by decide +kernel
theorem PMMMe8 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length + rowsPMMM6.length + rowsPMMM7.length)).take rowsPMMM8.length = cnfOfRows16 [rowsPMMM8] := by decide +kernel
theorem PMMMe9 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length + rowsPMMM6.length + rowsPMMM7.length + rowsPMMM8.length)).take rowsPMMM9.length = cnfOfRows16 [rowsPMMM9] := by decide +kernel
theorem PMMMe10 : (PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length + rowsPMMM6.length + rowsPMMM7.length + rowsPMMM8.length + rowsPMMM9.length)).take rowsPMMM10.length = cnfOfRows16 [rowsPMMM10] := by decide +kernel
theorem PMMMeEnd : PMMMCnf.drop (0 + rowsPMMM0.length + rowsPMMM1.length + rowsPMMM2.length + rowsPMMM3.length + rowsPMMM4.length + rowsPMMM5.length + rowsPMMM6.length + rowsPMMM7.length + rowsPMMM8.length + rowsPMMM9.length + rowsPMMM10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMMM (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMMM : cnfOfRows16 rowsPMMM = PMMMCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMMM PMMMCnf 0 ⟨PMMMe0, PMMMe1, PMMMe2, PMMMe3, PMMMe4, PMMMe5, PMMMe6, PMMMe7, PMMMe8, PMMMe9, PMMMe10, PMMMeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMMM are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMMM : Minimality.H16.SAT.CoreUnsat rowsPMMM := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMMMunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMMM] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+---` of type 16 is Rupert**: `Core16T 1 (-1) (-1) (-1)`. -/
theorem rupert_of_corePMMM : Minimality.H16.SAT.Core16T 1 (-1) (-1) (-1) := rupert_of_core_dataPMMM coreUnsatPMMM

end Minimality.H16K.SAT
