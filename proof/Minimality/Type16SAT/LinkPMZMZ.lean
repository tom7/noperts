module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPMZMZ
public import Minimality.Type16SAT.ChkPMZMZ

@[expose] public section

/-!
# Type 16, J7/J8: core PMZMZ, `CoreUnsat rowsPMZMZ` from the kernel-checked LRAT proof, and `rupert_of_corePMZMZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PMZMZe0 : (PMZMZCnf.drop (0)).take rowsPMZMZ0.length = cnfOfRows16 [rowsPMZMZ0] := by decide +kernel
theorem PMZMZe1 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length)).take rowsPMZMZ1.length = cnfOfRows16 [rowsPMZMZ1] := by decide +kernel
theorem PMZMZe2 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length)).take rowsPMZMZ2.length = cnfOfRows16 [rowsPMZMZ2] := by decide +kernel
theorem PMZMZe3 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length)).take rowsPMZMZ3.length = cnfOfRows16 [rowsPMZMZ3] := by decide +kernel
theorem PMZMZe4 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length)).take rowsPMZMZ4.length = cnfOfRows16 [rowsPMZMZ4] := by decide +kernel
theorem PMZMZe5 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length)).take rowsPMZMZ5.length = cnfOfRows16 [rowsPMZMZ5] := by decide +kernel
theorem PMZMZe6 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length)).take rowsPMZMZ6.length = cnfOfRows16 [rowsPMZMZ6] := by decide +kernel
theorem PMZMZe7 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length)).take rowsPMZMZ7.length = cnfOfRows16 [rowsPMZMZ7] := by decide +kernel
theorem PMZMZe8 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length)).take rowsPMZMZ8.length = cnfOfRows16 [rowsPMZMZ8] := by decide +kernel
theorem PMZMZe9 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length + rowsPMZMZ8.length)).take rowsPMZMZ9.length = cnfOfRows16 [rowsPMZMZ9] := by decide +kernel
theorem PMZMZe10 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length + rowsPMZMZ8.length + rowsPMZMZ9.length)).take rowsPMZMZ10.length = cnfOfRows16 [rowsPMZMZ10] := by decide +kernel
theorem PMZMZe11 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length + rowsPMZMZ8.length + rowsPMZMZ9.length + rowsPMZMZ10.length)).take rowsPMZMZ11.length = cnfOfRows16 [rowsPMZMZ11] := by decide +kernel
theorem PMZMZe12 : (PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length + rowsPMZMZ8.length + rowsPMZMZ9.length + rowsPMZMZ10.length + rowsPMZMZ11.length)).take rowsPMZMZ12.length = cnfOfRows16 [rowsPMZMZ12] := by decide +kernel
theorem PMZMZeEnd : PMZMZCnf.drop (0 + rowsPMZMZ0.length + rowsPMZMZ1.length + rowsPMZMZ2.length + rowsPMZMZ3.length + rowsPMZMZ4.length + rowsPMZMZ5.length + rowsPMZMZ6.length + rowsPMZMZ7.length + rowsPMZMZ8.length + rowsPMZMZ9.length + rowsPMZMZ10.length + rowsPMZMZ11.length + rowsPMZMZ12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PMZMZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPMZMZ : cnfOfRows16 rowsPMZMZ = PMZMZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPMZMZ PMZMZCnf 0 ⟨PMZMZe0, PMZMZe1, PMZMZe2, PMZMZe3, PMZMZe4, PMZMZe5, PMZMZe6, PMZMZe7, PMZMZe8, PMZMZe9, PMZMZe10, PMZMZe11, PMZMZe12, PMZMZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PMZMZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPMZMZ : Minimality.H16.SAT.CoreUnsat rowsPMZMZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PMZMZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPMZMZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+-0-` of type 16 is Rupert**: `Core16ZW 1 (-1) 0 (-1)`. -/
theorem rupert_of_corePMZMZ : Minimality.H16.SAT.Core16ZW 1 (-1) 0 (-1) := rupert_of_core_dataPMZMZ coreUnsatPMZMZ

end Minimality.H16K.SAT
