module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMMZ
public import Minimality.Type16SAT.ChkZZMMZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMMZ, `CoreUnsat rowsZZMMZ` from the kernel-checked LRAT proof, and `rupert_of_coreZZMMZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMMZe0 : (ZZMMZCnf.drop (0)).take rowsZZMMZ0.length = cnfOfRows16 [rowsZZMMZ0] := by decide +kernel
theorem ZZMMZe1 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length)).take rowsZZMMZ1.length = cnfOfRows16 [rowsZZMMZ1] := by decide +kernel
theorem ZZMMZe2 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length)).take rowsZZMMZ2.length = cnfOfRows16 [rowsZZMMZ2] := by decide +kernel
theorem ZZMMZe3 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length)).take rowsZZMMZ3.length = cnfOfRows16 [rowsZZMMZ3] := by decide +kernel
theorem ZZMMZe4 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length)).take rowsZZMMZ4.length = cnfOfRows16 [rowsZZMMZ4] := by decide +kernel
theorem ZZMMZe5 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length)).take rowsZZMMZ5.length = cnfOfRows16 [rowsZZMMZ5] := by decide +kernel
theorem ZZMMZe6 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length)).take rowsZZMMZ6.length = cnfOfRows16 [rowsZZMMZ6] := by decide +kernel
theorem ZZMMZe7 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length + rowsZZMMZ6.length)).take rowsZZMMZ7.length = cnfOfRows16 [rowsZZMMZ7] := by decide +kernel
theorem ZZMMZe8 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length + rowsZZMMZ6.length + rowsZZMMZ7.length)).take rowsZZMMZ8.length = cnfOfRows16 [rowsZZMMZ8] := by decide +kernel
theorem ZZMMZe9 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length + rowsZZMMZ6.length + rowsZZMMZ7.length + rowsZZMMZ8.length)).take rowsZZMMZ9.length = cnfOfRows16 [rowsZZMMZ9] := by decide +kernel
theorem ZZMMZe10 : (ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length + rowsZZMMZ6.length + rowsZZMMZ7.length + rowsZZMMZ8.length + rowsZZMMZ9.length)).take rowsZZMMZ10.length = cnfOfRows16 [rowsZZMMZ10] := by decide +kernel
theorem ZZMMZeEnd : ZZMMZCnf.drop (0 + rowsZZMMZ0.length + rowsZZMMZ1.length + rowsZZMMZ2.length + rowsZZMMZ3.length + rowsZZMMZ4.length + rowsZZMMZ5.length + rowsZZMMZ6.length + rowsZZMMZ7.length + rowsZZMMZ8.length + rowsZZMMZ9.length + rowsZZMMZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMMZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMMZ : cnfOfRows16 rowsZZMMZ = ZZMMZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMMZ ZZMMZCnf 0 ⟨ZZMMZe0, ZZMMZe1, ZZMMZe2, ZZMMZe3, ZZMMZe4, ZZMMZe5, ZZMMZe6, ZZMMZe7, ZZMMZe8, ZZMMZe9, ZZMMZe10, ZZMMZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMMZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMMZ : Minimality.H16.SAT.CoreUnsat rowsZZMMZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMMZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMMZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00--` of type 16 is Rupert**: `Core16ZW 0 0 (-1) (-1)`. -/
theorem rupert_of_coreZZMMZ : Minimality.H16.SAT.Core16ZW 0 0 (-1) (-1) := rupert_of_core_dataZZMMZ coreUnsatZZMMZ

end Minimality.H16K.SAT
