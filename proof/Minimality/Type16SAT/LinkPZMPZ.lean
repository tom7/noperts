module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMPZ
public import Minimality.Type16SAT.ChkPZMPZ

@[expose] public section

/-!
# Type 16, J7/J8: core PZMPZ, `CoreUnsat rowsPZMPZ` from the kernel-checked LRAT proof, and `rupert_of_corePZMPZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMPZe0 : (PZMPZCnf.drop (0)).take rowsPZMPZ0.length = cnfOfRows16 [rowsPZMPZ0] := by decide +kernel
theorem PZMPZe1 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length)).take rowsPZMPZ1.length = cnfOfRows16 [rowsPZMPZ1] := by decide +kernel
theorem PZMPZe2 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length)).take rowsPZMPZ2.length = cnfOfRows16 [rowsPZMPZ2] := by decide +kernel
theorem PZMPZe3 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length)).take rowsPZMPZ3.length = cnfOfRows16 [rowsPZMPZ3] := by decide +kernel
theorem PZMPZe4 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length)).take rowsPZMPZ4.length = cnfOfRows16 [rowsPZMPZ4] := by decide +kernel
theorem PZMPZe5 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length)).take rowsPZMPZ5.length = cnfOfRows16 [rowsPZMPZ5] := by decide +kernel
theorem PZMPZe6 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length)).take rowsPZMPZ6.length = cnfOfRows16 [rowsPZMPZ6] := by decide +kernel
theorem PZMPZe7 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length)).take rowsPZMPZ7.length = cnfOfRows16 [rowsPZMPZ7] := by decide +kernel
theorem PZMPZe8 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length + rowsPZMPZ7.length)).take rowsPZMPZ8.length = cnfOfRows16 [rowsPZMPZ8] := by decide +kernel
theorem PZMPZe9 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length + rowsPZMPZ7.length + rowsPZMPZ8.length)).take rowsPZMPZ9.length = cnfOfRows16 [rowsPZMPZ9] := by decide +kernel
theorem PZMPZe10 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length + rowsPZMPZ7.length + rowsPZMPZ8.length + rowsPZMPZ9.length)).take rowsPZMPZ10.length = cnfOfRows16 [rowsPZMPZ10] := by decide +kernel
theorem PZMPZe11 : (PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length + rowsPZMPZ7.length + rowsPZMPZ8.length + rowsPZMPZ9.length + rowsPZMPZ10.length)).take rowsPZMPZ11.length = cnfOfRows16 [rowsPZMPZ11] := by decide +kernel
theorem PZMPZeEnd : PZMPZCnf.drop (0 + rowsPZMPZ0.length + rowsPZMPZ1.length + rowsPZMPZ2.length + rowsPZMPZ3.length + rowsPZMPZ4.length + rowsPZMPZ5.length + rowsPZMPZ6.length + rowsPZMPZ7.length + rowsPZMPZ8.length + rowsPZMPZ9.length + rowsPZMPZ10.length + rowsPZMPZ11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMPZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMPZ : cnfOfRows16 rowsPZMPZ = PZMPZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMPZ PZMPZCnf 0 ⟨PZMPZe0, PZMPZe1, PZMPZe2, PZMPZe3, PZMPZe4, PZMPZe5, PZMPZe6, PZMPZe7, PZMPZe8, PZMPZe9, PZMPZe10, PZMPZe11, PZMPZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMPZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMPZ : Minimality.H16.SAT.CoreUnsat rowsPZMPZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMPZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMPZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0-+` of type 16 is Rupert**: `Core16ZW 1 0 (-1) 1`. -/
theorem rupert_of_corePZMPZ : Minimality.H16.SAT.Core16ZW 1 0 (-1) 1 := rupert_of_core_dataPZMPZ coreUnsatPZMPZ

end Minimality.H16K.SAT
