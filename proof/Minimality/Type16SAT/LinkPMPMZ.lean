module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMPMZ
public import Minimality.Type16SAT.ChkPMPMZ

@[expose] public section

/-!
# Type 16, J7/J8: core PMPMZ, `CoreUnsat rowsPMPMZ` from the kernel-checked LRAT proof, and `rupert_of_corePMPMZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMPMZe0 : (PMPMZCnf.drop (0)).take rowsPMPMZ0.length = cnfOfRows16 [rowsPMPMZ0] := by decide +kernel
theorem PMPMZe1 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length)).take rowsPMPMZ1.length = cnfOfRows16 [rowsPMPMZ1] := by decide +kernel
theorem PMPMZe2 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length)).take rowsPMPMZ2.length = cnfOfRows16 [rowsPMPMZ2] := by decide +kernel
theorem PMPMZe3 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length)).take rowsPMPMZ3.length = cnfOfRows16 [rowsPMPMZ3] := by decide +kernel
theorem PMPMZe4 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length)).take rowsPMPMZ4.length = cnfOfRows16 [rowsPMPMZ4] := by decide +kernel
theorem PMPMZe5 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length)).take rowsPMPMZ5.length = cnfOfRows16 [rowsPMPMZ5] := by decide +kernel
theorem PMPMZe6 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length)).take rowsPMPMZ6.length = cnfOfRows16 [rowsPMPMZ6] := by decide +kernel
theorem PMPMZe7 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length)).take rowsPMPMZ7.length = cnfOfRows16 [rowsPMPMZ7] := by decide +kernel
theorem PMPMZe8 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length)).take rowsPMPMZ8.length = cnfOfRows16 [rowsPMPMZ8] := by decide +kernel
theorem PMPMZe9 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length + rowsPMPMZ8.length)).take rowsPMPMZ9.length = cnfOfRows16 [rowsPMPMZ9] := by decide +kernel
theorem PMPMZe10 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length + rowsPMPMZ8.length + rowsPMPMZ9.length)).take rowsPMPMZ10.length = cnfOfRows16 [rowsPMPMZ10] := by decide +kernel
theorem PMPMZe11 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length + rowsPMPMZ8.length + rowsPMPMZ9.length + rowsPMPMZ10.length)).take rowsPMPMZ11.length = cnfOfRows16 [rowsPMPMZ11] := by decide +kernel
theorem PMPMZe12 : (PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length + rowsPMPMZ8.length + rowsPMPMZ9.length + rowsPMPMZ10.length + rowsPMPMZ11.length)).take rowsPMPMZ12.length = cnfOfRows16 [rowsPMPMZ12] := by decide +kernel
theorem PMPMZeEnd : PMPMZCnf.drop (0 + rowsPMPMZ0.length + rowsPMPMZ1.length + rowsPMPMZ2.length + rowsPMPMZ3.length + rowsPMPMZ4.length + rowsPMPMZ5.length + rowsPMPMZ6.length + rowsPMPMZ7.length + rowsPMPMZ8.length + rowsPMPMZ9.length + rowsPMPMZ10.length + rowsPMPMZ11.length + rowsPMPMZ12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMPMZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMPMZ : cnfOfRows16 rowsPMPMZ = PMPMZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMPMZ PMPMZCnf 0 ⟨PMPMZe0, PMPMZe1, PMPMZe2, PMPMZe3, PMPMZe4, PMPMZe5, PMPMZe6, PMPMZe7, PMPMZe8, PMPMZe9, PMPMZe10, PMPMZe11, PMPMZe12, PMPMZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMPMZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMPMZ : Minimality.H16.SAT.CoreUnsat rowsPMPMZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMPMZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMPMZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+-+-` of type 16 is Rupert**: `Core16Z 1 (-1) 1 (-1)`. -/
theorem rupert_of_corePMPMZ : Minimality.H16.SAT.Core16Z 1 (-1) 1 (-1) := rupert_of_core_dataPMPMZ coreUnsatPMPMZ

end Minimality.H16K.SAT
