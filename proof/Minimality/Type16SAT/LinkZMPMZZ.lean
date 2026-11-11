module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZMPMZZ
public import Minimality.Type16SAT.ChkZMPMZZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZMPMZZ, `CoreUnsat rowsZMPMZZ` from the kernel-checked LRAT proof, and `rupert_of_coreZMPMZZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZMPMZZe0 : (ZMPMZZCnf.drop (0)).take rowsZMPMZZ0.length = cnfOfRows16 [rowsZMPMZZ0] := by decide +kernel
theorem ZMPMZZe1 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length)).take rowsZMPMZZ1.length = cnfOfRows16 [rowsZMPMZZ1] := by decide +kernel
theorem ZMPMZZe2 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length)).take rowsZMPMZZ2.length = cnfOfRows16 [rowsZMPMZZ2] := by decide +kernel
theorem ZMPMZZe3 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length)).take rowsZMPMZZ3.length = cnfOfRows16 [rowsZMPMZZ3] := by decide +kernel
theorem ZMPMZZe4 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length)).take rowsZMPMZZ4.length = cnfOfRows16 [rowsZMPMZZ4] := by decide +kernel
theorem ZMPMZZe5 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length)).take rowsZMPMZZ5.length = cnfOfRows16 [rowsZMPMZZ5] := by decide +kernel
theorem ZMPMZZe6 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length)).take rowsZMPMZZ6.length = cnfOfRows16 [rowsZMPMZZ6] := by decide +kernel
theorem ZMPMZZe7 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length + rowsZMPMZZ6.length)).take rowsZMPMZZ7.length = cnfOfRows16 [rowsZMPMZZ7] := by decide +kernel
theorem ZMPMZZe8 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length + rowsZMPMZZ6.length + rowsZMPMZZ7.length)).take rowsZMPMZZ8.length = cnfOfRows16 [rowsZMPMZZ8] := by decide +kernel
theorem ZMPMZZe9 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length + rowsZMPMZZ6.length + rowsZMPMZZ7.length + rowsZMPMZZ8.length)).take rowsZMPMZZ9.length = cnfOfRows16 [rowsZMPMZZ9] := by decide +kernel
theorem ZMPMZZe10 : (ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length + rowsZMPMZZ6.length + rowsZMPMZZ7.length + rowsZMPMZZ8.length + rowsZMPMZZ9.length)).take rowsZMPMZZ10.length = cnfOfRows16 [rowsZMPMZZ10] := by decide +kernel
theorem ZMPMZZeEnd : ZMPMZZCnf.drop (0 + rowsZMPMZZ0.length + rowsZMPMZZ1.length + rowsZMPMZZ2.length + rowsZMPMZZ3.length + rowsZMPMZZ4.length + rowsZMPMZZ5.length + rowsZMPMZZ6.length + rowsZMPMZZ7.length + rowsZMPMZZ8.length + rowsZMPMZZ9.length + rowsZMPMZZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZMPMZZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZMPMZZ : cnfOfRows16 rowsZMPMZZ = ZMPMZZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZMPMZZ ZMPMZZCnf 0 ⟨ZMPMZZe0, ZMPMZZe1, ZMPMZZe2, ZMPMZZe3, ZMPMZZe4, ZMPMZZe5, ZMPMZZe6, ZMPMZZe7, ZMPMZZe8, ZMPMZZe9, ZMPMZZe10, ZMPMZZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZMPMZZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZMPMZZ : Minimality.H16.SAT.CoreUnsat rowsZMPMZZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZMPMZZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZMPMZZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0-+-` of type 16 is Rupert**: `Core16ZZW 0 (-1) 1 (-1)`. -/
theorem rupert_of_coreZMPMZZ : Minimality.H16.SAT.Core16ZZW 0 (-1) 1 (-1) := rupert_of_core_dataZMPMZZ coreUnsatZMPMZZ

end Minimality.H16K.SAT
