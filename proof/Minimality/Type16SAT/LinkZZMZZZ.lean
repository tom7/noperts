module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMZZZ
public import Minimality.Type16SAT.ChkZZMZZZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMZZZ, `CoreUnsat rowsZZMZZZ` from the kernel-checked LRAT proof, and `rupert_of_coreZZMZZZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMZZZe0 : (ZZMZZZCnf.drop (0)).take rowsZZMZZZ0.length = cnfOfRows16 [rowsZZMZZZ0] := by decide +kernel
theorem ZZMZZZe1 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length)).take rowsZZMZZZ1.length = cnfOfRows16 [rowsZZMZZZ1] := by decide +kernel
theorem ZZMZZZe2 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length)).take rowsZZMZZZ2.length = cnfOfRows16 [rowsZZMZZZ2] := by decide +kernel
theorem ZZMZZZe3 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length)).take rowsZZMZZZ3.length = cnfOfRows16 [rowsZZMZZZ3] := by decide +kernel
theorem ZZMZZZe4 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length)).take rowsZZMZZZ4.length = cnfOfRows16 [rowsZZMZZZ4] := by decide +kernel
theorem ZZMZZZe5 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length)).take rowsZZMZZZ5.length = cnfOfRows16 [rowsZZMZZZ5] := by decide +kernel
theorem ZZMZZZe6 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length)).take rowsZZMZZZ6.length = cnfOfRows16 [rowsZZMZZZ6] := by decide +kernel
theorem ZZMZZZe7 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length + rowsZZMZZZ6.length)).take rowsZZMZZZ7.length = cnfOfRows16 [rowsZZMZZZ7] := by decide +kernel
theorem ZZMZZZe8 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length + rowsZZMZZZ6.length + rowsZZMZZZ7.length)).take rowsZZMZZZ8.length = cnfOfRows16 [rowsZZMZZZ8] := by decide +kernel
theorem ZZMZZZe9 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length + rowsZZMZZZ6.length + rowsZZMZZZ7.length + rowsZZMZZZ8.length)).take rowsZZMZZZ9.length = cnfOfRows16 [rowsZZMZZZ9] := by decide +kernel
theorem ZZMZZZe10 : (ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length + rowsZZMZZZ6.length + rowsZZMZZZ7.length + rowsZZMZZZ8.length + rowsZZMZZZ9.length)).take rowsZZMZZZ10.length = cnfOfRows16 [rowsZZMZZZ10] := by decide +kernel
theorem ZZMZZZeEnd : ZZMZZZCnf.drop (0 + rowsZZMZZZ0.length + rowsZZMZZZ1.length + rowsZZMZZZ2.length + rowsZZMZZZ3.length + rowsZZMZZZ4.length + rowsZZMZZZ5.length + rowsZZMZZZ6.length + rowsZZMZZZ7.length + rowsZZMZZZ8.length + rowsZZMZZZ9.length + rowsZZMZZZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMZZZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMZZZ : cnfOfRows16 rowsZZMZZZ = ZZMZZZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMZZZ ZZMZZZCnf 0 ⟨ZZMZZZe0, ZZMZZZe1, ZZMZZZe2, ZZMZZZe3, ZZMZZZe4, ZZMZZZe5, ZZMZZZe6, ZZMZZZe7, ZZMZZZe8, ZZMZZZe9, ZZMZZZe10, ZZMZZZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMZZZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMZZZ : Minimality.H16.SAT.CoreUnsat rowsZZMZZZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMZZZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMZZZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00-0` of type 16 is Rupert**: `Core16ZZW 0 0 (-1) 0`. -/
theorem rupert_of_coreZZMZZZ : Minimality.H16.SAT.Core16ZZW 0 0 (-1) 0 := rupert_of_core_dataZZMZZZ coreUnsatZZMZZZ

end Minimality.H16K.SAT
