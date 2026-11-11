module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZZMPZ
public import Minimality.Type16SAT.ChkZZMPZ

@[expose] public section

/-!
# Type 16, J7/J8: core ZZMPZ, `CoreUnsat rowsZZMPZ` from the kernel-checked LRAT proof, and `rupert_of_coreZZMPZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZZMPZe0 : (ZZMPZCnf.drop (0)).take rowsZZMPZ0.length = cnfOfRows16 [rowsZZMPZ0] := by decide +kernel
theorem ZZMPZe1 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length)).take rowsZZMPZ1.length = cnfOfRows16 [rowsZZMPZ1] := by decide +kernel
theorem ZZMPZe2 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length)).take rowsZZMPZ2.length = cnfOfRows16 [rowsZZMPZ2] := by decide +kernel
theorem ZZMPZe3 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length)).take rowsZZMPZ3.length = cnfOfRows16 [rowsZZMPZ3] := by decide +kernel
theorem ZZMPZe4 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length)).take rowsZZMPZ4.length = cnfOfRows16 [rowsZZMPZ4] := by decide +kernel
theorem ZZMPZe5 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length)).take rowsZZMPZ5.length = cnfOfRows16 [rowsZZMPZ5] := by decide +kernel
theorem ZZMPZe6 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length)).take rowsZZMPZ6.length = cnfOfRows16 [rowsZZMPZ6] := by decide +kernel
theorem ZZMPZe7 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length + rowsZZMPZ6.length)).take rowsZZMPZ7.length = cnfOfRows16 [rowsZZMPZ7] := by decide +kernel
theorem ZZMPZe8 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length + rowsZZMPZ6.length + rowsZZMPZ7.length)).take rowsZZMPZ8.length = cnfOfRows16 [rowsZZMPZ8] := by decide +kernel
theorem ZZMPZe9 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length + rowsZZMPZ6.length + rowsZZMPZ7.length + rowsZZMPZ8.length)).take rowsZZMPZ9.length = cnfOfRows16 [rowsZZMPZ9] := by decide +kernel
theorem ZZMPZe10 : (ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length + rowsZZMPZ6.length + rowsZZMPZ7.length + rowsZZMPZ8.length + rowsZZMPZ9.length)).take rowsZZMPZ10.length = cnfOfRows16 [rowsZZMPZ10] := by decide +kernel
theorem ZZMPZeEnd : ZZMPZCnf.drop (0 + rowsZZMPZ0.length + rowsZZMPZ1.length + rowsZZMPZ2.length + rowsZZMPZ3.length + rowsZZMPZ4.length + rowsZZMPZ5.length + rowsZZMPZ6.length + rowsZZMPZ7.length + rowsZZMPZ8.length + rowsZZMPZ9.length + rowsZZMPZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZZMPZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZZMPZ : cnfOfRows16 rowsZZMPZ = ZZMPZCnf := by
  have h := cnfOfRows16_of_chkAt rowsZZMPZ ZZMPZCnf 0 ⟨ZZMPZe0, ZZMPZe1, ZZMPZe2, ZZMPZe3, ZZMPZe4, ZZMPZe5, ZZMPZe6, ZZMPZe7, ZZMPZe8, ZZMPZe9, ZZMPZe10, ZZMPZeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZZMPZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZZMPZ : Minimality.H16.SAT.CoreUnsat rowsZZMPZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZZMPZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZZMPZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `00-+` of type 16 is Rupert**: `Core16ZW 0 0 (-1) 1`. -/
theorem rupert_of_coreZZMPZ : Minimality.H16.SAT.Core16ZW 0 0 (-1) 1 := rupert_of_core_dataZZMPZ coreUnsatZZMPZ

end Minimality.H16K.SAT
