module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMMZ
public import Minimality.Type16SAT.ChkPZMMZ

@[expose] public section

/-!
# Type 16, J7/J8: core PZMMZ, `CoreUnsat rowsPZMMZ` from the kernel-checked LRAT proof, and `rupert_of_corePZMMZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMMZe0 : (PZMMZCnf.drop (0)).take rowsPZMMZ0.length = cnfOfRows16 [rowsPZMMZ0] := by decide +kernel
theorem PZMMZe1 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length)).take rowsPZMMZ1.length = cnfOfRows16 [rowsPZMMZ1] := by decide +kernel
theorem PZMMZe2 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length)).take rowsPZMMZ2.length = cnfOfRows16 [rowsPZMMZ2] := by decide +kernel
theorem PZMMZe3 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length)).take rowsPZMMZ3.length = cnfOfRows16 [rowsPZMMZ3] := by decide +kernel
theorem PZMMZe4 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length)).take rowsPZMMZ4.length = cnfOfRows16 [rowsPZMMZ4] := by decide +kernel
theorem PZMMZe5 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length)).take rowsPZMMZ5.length = cnfOfRows16 [rowsPZMMZ5] := by decide +kernel
theorem PZMMZe6 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length)).take rowsPZMMZ6.length = cnfOfRows16 [rowsPZMMZ6] := by decide +kernel
theorem PZMMZe7 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length)).take rowsPZMMZ7.length = cnfOfRows16 [rowsPZMMZ7] := by decide +kernel
theorem PZMMZe8 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length + rowsPZMMZ7.length)).take rowsPZMMZ8.length = cnfOfRows16 [rowsPZMMZ8] := by decide +kernel
theorem PZMMZe9 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length + rowsPZMMZ7.length + rowsPZMMZ8.length)).take rowsPZMMZ9.length = cnfOfRows16 [rowsPZMMZ9] := by decide +kernel
theorem PZMMZe10 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length + rowsPZMMZ7.length + rowsPZMMZ8.length + rowsPZMMZ9.length)).take rowsPZMMZ10.length = cnfOfRows16 [rowsPZMMZ10] := by decide +kernel
theorem PZMMZe11 : (PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length + rowsPZMMZ7.length + rowsPZMMZ8.length + rowsPZMMZ9.length + rowsPZMMZ10.length)).take rowsPZMMZ11.length = cnfOfRows16 [rowsPZMMZ11] := by decide +kernel
theorem PZMMZeEnd : PZMMZCnf.drop (0 + rowsPZMMZ0.length + rowsPZMMZ1.length + rowsPZMMZ2.length + rowsPZMMZ3.length + rowsPZMMZ4.length + rowsPZMMZ5.length + rowsPZMMZ6.length + rowsPZMMZ7.length + rowsPZMMZ8.length + rowsPZMMZ9.length + rowsPZMMZ10.length + rowsPZMMZ11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMMZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMMZ : cnfOfRows16 rowsPZMMZ = PZMMZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMMZ PZMMZCnf 0 ⟨PZMMZe0, PZMMZe1, PZMMZe2, PZMMZe3, PZMMZe4, PZMMZe5, PZMMZe6, PZMMZe7, PZMMZe8, PZMMZe9, PZMMZe10, PZMMZe11, PZMMZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMMZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMMZ : Minimality.H16.SAT.CoreUnsat rowsPZMMZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMMZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMMZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0--` of type 16 is Rupert**: `Core16ZW 1 0 (-1) (-1)`. -/
theorem rupert_of_corePZMMZ : Minimality.H16.SAT.Core16ZW 1 0 (-1) (-1) := rupert_of_core_dataPZMMZ coreUnsatPZMMZ

end Minimality.H16K.SAT
