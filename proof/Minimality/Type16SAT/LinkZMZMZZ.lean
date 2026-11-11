module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMZMZZ
public import Minimality.Type16SAT.ChkZMZMZZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZMZMZZ, `CoreUnsat rowsZMZMZZ` from the kernel-checked LRAT proof, and `rupert_of_coreZMZMZZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMZMZZe0 : (ZMZMZZCnf.drop (0)).take rowsZMZMZZ0.length = cnfOfRows16 [rowsZMZMZZ0] := by decide +kernel
theorem ZMZMZZe1 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length)).take rowsZMZMZZ1.length = cnfOfRows16 [rowsZMZMZZ1] := by decide +kernel
theorem ZMZMZZe2 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length)).take rowsZMZMZZ2.length = cnfOfRows16 [rowsZMZMZZ2] := by decide +kernel
theorem ZMZMZZe3 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length)).take rowsZMZMZZ3.length = cnfOfRows16 [rowsZMZMZZ3] := by decide +kernel
theorem ZMZMZZe4 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length)).take rowsZMZMZZ4.length = cnfOfRows16 [rowsZMZMZZ4] := by decide +kernel
theorem ZMZMZZe5 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length)).take rowsZMZMZZ5.length = cnfOfRows16 [rowsZMZMZZ5] := by decide +kernel
theorem ZMZMZZe6 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length)).take rowsZMZMZZ6.length = cnfOfRows16 [rowsZMZMZZ6] := by decide +kernel
theorem ZMZMZZe7 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length)).take rowsZMZMZZ7.length = cnfOfRows16 [rowsZMZMZZ7] := by decide +kernel
theorem ZMZMZZe8 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length)).take rowsZMZMZZ8.length = cnfOfRows16 [rowsZMZMZZ8] := by decide +kernel
theorem ZMZMZZe9 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length + rowsZMZMZZ8.length)).take rowsZMZMZZ9.length = cnfOfRows16 [rowsZMZMZZ9] := by decide +kernel
theorem ZMZMZZe10 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length + rowsZMZMZZ8.length + rowsZMZMZZ9.length)).take rowsZMZMZZ10.length = cnfOfRows16 [rowsZMZMZZ10] := by decide +kernel
theorem ZMZMZZe11 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length + rowsZMZMZZ8.length + rowsZMZMZZ9.length + rowsZMZMZZ10.length)).take rowsZMZMZZ11.length = cnfOfRows16 [rowsZMZMZZ11] := by decide +kernel
theorem ZMZMZZe12 : (ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length + rowsZMZMZZ8.length + rowsZMZMZZ9.length + rowsZMZMZZ10.length + rowsZMZMZZ11.length)).take rowsZMZMZZ12.length = cnfOfRows16 [rowsZMZMZZ12] := by decide +kernel
theorem ZMZMZZeEnd : ZMZMZZCnf.drop (0 + rowsZMZMZZ0.length + rowsZMZMZZ1.length + rowsZMZMZZ2.length + rowsZMZMZZ3.length + rowsZMZMZZ4.length + rowsZMZMZZ5.length + rowsZMZMZZ6.length + rowsZMZMZZ7.length + rowsZMZMZZ8.length + rowsZMZMZZ9.length + rowsZMZMZZ10.length + rowsZMZMZZ11.length + rowsZMZMZZ12.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMZMZZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMZMZZ : cnfOfRows16 rowsZMZMZZ = ZMZMZZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMZMZZ ZMZMZZCnf 0 ⟨ZMZMZZe0, ZMZMZZe1, ZMZMZZe2, ZMZMZZe3, ZMZMZZe4, ZMZMZZe5, ZMZMZZe6, ZMZMZZe7, ZMZMZZe8, ZMZMZZe9, ZMZMZZe10, ZMZMZZe11, ZMZMZZe12, ZMZMZZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMZMZZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMZMZZ : Minimality.H16.SAT.CoreUnsat rowsZMZMZZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMZMZZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMZMZZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0-0-` of type 16 is Rupert**: `Core16ZZW 0 (-1) 0 (-1)`. -/
theorem rupert_of_coreZMZMZZ : Minimality.H16.SAT.Core16ZZW 0 (-1) 0 (-1) := rupert_of_core_dataZMZMZZ coreUnsatZMZMZZ

end Minimality.H16K.SAT
