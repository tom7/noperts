module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMMMZZ
public import Minimality.Type16SAT.ChkZMMMZZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZMMMZZ, `CoreUnsat rowsZMMMZZ` from the kernel-checked LRAT proof, and `rupert_of_coreZMMMZZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMMMZZe0 : (ZMMMZZCnf.drop (0)).take rowsZMMMZZ0.length = cnfOfRows16 [rowsZMMMZZ0] := by decide +kernel
theorem ZMMMZZe1 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length)).take rowsZMMMZZ1.length = cnfOfRows16 [rowsZMMMZZ1] := by decide +kernel
theorem ZMMMZZe2 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length)).take rowsZMMMZZ2.length = cnfOfRows16 [rowsZMMMZZ2] := by decide +kernel
theorem ZMMMZZe3 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length)).take rowsZMMMZZ3.length = cnfOfRows16 [rowsZMMMZZ3] := by decide +kernel
theorem ZMMMZZe4 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length)).take rowsZMMMZZ4.length = cnfOfRows16 [rowsZMMMZZ4] := by decide +kernel
theorem ZMMMZZe5 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length)).take rowsZMMMZZ5.length = cnfOfRows16 [rowsZMMMZZ5] := by decide +kernel
theorem ZMMMZZe6 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length)).take rowsZMMMZZ6.length = cnfOfRows16 [rowsZMMMZZ6] := by decide +kernel
theorem ZMMMZZe7 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length)).take rowsZMMMZZ7.length = cnfOfRows16 [rowsZMMMZZ7] := by decide +kernel
theorem ZMMMZZe8 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length + rowsZMMMZZ7.length)).take rowsZMMMZZ8.length = cnfOfRows16 [rowsZMMMZZ8] := by decide +kernel
theorem ZMMMZZe9 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length + rowsZMMMZZ7.length + rowsZMMMZZ8.length)).take rowsZMMMZZ9.length = cnfOfRows16 [rowsZMMMZZ9] := by decide +kernel
theorem ZMMMZZe10 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length + rowsZMMMZZ7.length + rowsZMMMZZ8.length + rowsZMMMZZ9.length)).take rowsZMMMZZ10.length = cnfOfRows16 [rowsZMMMZZ10] := by decide +kernel
theorem ZMMMZZe11 : (ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length + rowsZMMMZZ7.length + rowsZMMMZZ8.length + rowsZMMMZZ9.length + rowsZMMMZZ10.length)).take rowsZMMMZZ11.length = cnfOfRows16 [rowsZMMMZZ11] := by decide +kernel
theorem ZMMMZZeEnd : ZMMMZZCnf.drop (0 + rowsZMMMZZ0.length + rowsZMMMZZ1.length + rowsZMMMZZ2.length + rowsZMMMZZ3.length + rowsZMMMZZ4.length + rowsZMMMZZ5.length + rowsZMMMZZ6.length + rowsZMMMZZ7.length + rowsZMMMZZ8.length + rowsZMMMZZ9.length + rowsZMMMZZ10.length + rowsZMMMZZ11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMMMZZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMMMZZ : cnfOfRows16 rowsZMMMZZ = ZMMMZZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMMMZZ ZMMMZZCnf 0 ⟨ZMMMZZe0, ZMMMZZe1, ZMMMZZe2, ZMMMZZe3, ZMMMZZe4, ZMMMZZe5, ZMMMZZe6, ZMMMZZe7, ZMMMZZe8, ZMMMZZe9, ZMMMZZe10, ZMMMZZe11, ZMMMZZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMMMZZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMMMZZ : Minimality.H16.SAT.CoreUnsat rowsZMMMZZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMMMZZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMMMZZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0---` of type 16 is Rupert**: `Core16ZZW 0 (-1) (-1) (-1)`. -/
theorem rupert_of_coreZMMMZZ : Minimality.H16.SAT.Core16ZZW 0 (-1) (-1) (-1) := rupert_of_core_dataZMMMZZ coreUnsatZMMMZZ

end Minimality.H16K.SAT
