module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZMMZ
public import Minimality.Type16SAT.ChkMZMMZ

@[expose] public section

/-!
# Type 16, J7/J8: core MZMMZ, `CoreUnsat rowsMZMMZ` from the kernel-checked LRAT proof, and `rupert_of_coreMZMMZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZMMZe0 : (MZMMZCnf.drop (0)).take rowsMZMMZ0.length = cnfOfRows16 [rowsMZMMZ0] := by decide +kernel
theorem MZMMZe1 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length)).take rowsMZMMZ1.length = cnfOfRows16 [rowsMZMMZ1] := by decide +kernel
theorem MZMMZe2 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length)).take rowsMZMMZ2.length = cnfOfRows16 [rowsMZMMZ2] := by decide +kernel
theorem MZMMZe3 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length)).take rowsMZMMZ3.length = cnfOfRows16 [rowsMZMMZ3] := by decide +kernel
theorem MZMMZe4 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length)).take rowsMZMMZ4.length = cnfOfRows16 [rowsMZMMZ4] := by decide +kernel
theorem MZMMZe5 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length)).take rowsMZMMZ5.length = cnfOfRows16 [rowsMZMMZ5] := by decide +kernel
theorem MZMMZe6 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length)).take rowsMZMMZ6.length = cnfOfRows16 [rowsMZMMZ6] := by decide +kernel
theorem MZMMZe7 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length)).take rowsMZMMZ7.length = cnfOfRows16 [rowsMZMMZ7] := by decide +kernel
theorem MZMMZe8 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length)).take rowsMZMMZ8.length = cnfOfRows16 [rowsMZMMZ8] := by decide +kernel
theorem MZMMZe9 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length + rowsMZMMZ8.length)).take rowsMZMMZ9.length = cnfOfRows16 [rowsMZMMZ9] := by decide +kernel
theorem MZMMZe10 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length + rowsMZMMZ8.length + rowsMZMMZ9.length)).take rowsMZMMZ10.length = cnfOfRows16 [rowsMZMMZ10] := by decide +kernel
theorem MZMMZe11 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length + rowsMZMMZ8.length + rowsMZMMZ9.length + rowsMZMMZ10.length)).take rowsMZMMZ11.length = cnfOfRows16 [rowsMZMMZ11] := by decide +kernel
theorem MZMMZe12 : (MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length + rowsMZMMZ8.length + rowsMZMMZ9.length + rowsMZMMZ10.length + rowsMZMMZ11.length)).take rowsMZMMZ12.length = cnfOfRows16 [rowsMZMMZ12] := by decide +kernel
theorem MZMMZeEnd : MZMMZCnf.drop (0 + rowsMZMMZ0.length + rowsMZMMZ1.length + rowsMZMMZ2.length + rowsMZMMZ3.length + rowsMZMMZ4.length + rowsMZMMZ5.length + rowsMZMMZ6.length + rowsMZMMZ7.length + rowsMZMMZ8.length + rowsMZMMZ9.length + rowsMZMMZ10.length + rowsMZMMZ11.length + rowsMZMMZ12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZMMZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZMMZ : cnfOfRows16 rowsMZMMZ = MZMMZCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZMMZ MZMMZCnf 0 ⟨MZMMZe0, MZMMZe1, MZMMZe2, MZMMZe3, MZMMZe4, MZMMZe5, MZMMZe6, MZMMZe7, MZMMZe8, MZMMZe9, MZMMZe10, MZMMZe11, MZMMZe12, MZMMZeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZMMZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZMMZ : Minimality.H16.SAT.CoreUnsat rowsMZMMZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZMMZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZMMZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0--` of type 16 is Rupert**: `Core16ZW (-1) 0 (-1) (-1)`. -/
theorem rupert_of_coreMZMMZ : Minimality.H16.SAT.Core16ZW (-1) 0 (-1) (-1) := rupert_of_core_dataMZMMZ coreUnsatMZMMZ

end Minimality.H16K.SAT
