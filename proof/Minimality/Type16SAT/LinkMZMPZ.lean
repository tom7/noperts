module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZMPZ
public import Minimality.Type16SAT.ChkMZMPZ

@[expose] public section

/-!
# Type 16, J7/J8: core MZMPZ, `CoreUnsat rowsMZMPZ` from the kernel-checked LRAT proof, and `rupert_of_coreMZMPZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZMPZe0 : (MZMPZCnf.drop (0)).take rowsMZMPZ0.length = cnfOfRows16 [rowsMZMPZ0] := by decide +kernel
theorem MZMPZe1 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length)).take rowsMZMPZ1.length = cnfOfRows16 [rowsMZMPZ1] := by decide +kernel
theorem MZMPZe2 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length)).take rowsMZMPZ2.length = cnfOfRows16 [rowsMZMPZ2] := by decide +kernel
theorem MZMPZe3 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length)).take rowsMZMPZ3.length = cnfOfRows16 [rowsMZMPZ3] := by decide +kernel
theorem MZMPZe4 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length)).take rowsMZMPZ4.length = cnfOfRows16 [rowsMZMPZ4] := by decide +kernel
theorem MZMPZe5 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length)).take rowsMZMPZ5.length = cnfOfRows16 [rowsMZMPZ5] := by decide +kernel
theorem MZMPZe6 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length)).take rowsMZMPZ6.length = cnfOfRows16 [rowsMZMPZ6] := by decide +kernel
theorem MZMPZe7 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length + rowsMZMPZ6.length)).take rowsMZMPZ7.length = cnfOfRows16 [rowsMZMPZ7] := by decide +kernel
theorem MZMPZe8 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length + rowsMZMPZ6.length + rowsMZMPZ7.length)).take rowsMZMPZ8.length = cnfOfRows16 [rowsMZMPZ8] := by decide +kernel
theorem MZMPZe9 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length + rowsMZMPZ6.length + rowsMZMPZ7.length + rowsMZMPZ8.length)).take rowsMZMPZ9.length = cnfOfRows16 [rowsMZMPZ9] := by decide +kernel
theorem MZMPZe10 : (MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length + rowsMZMPZ6.length + rowsMZMPZ7.length + rowsMZMPZ8.length + rowsMZMPZ9.length)).take rowsMZMPZ10.length = cnfOfRows16 [rowsMZMPZ10] := by decide +kernel
theorem MZMPZeEnd : MZMPZCnf.drop (0 + rowsMZMPZ0.length + rowsMZMPZ1.length + rowsMZMPZ2.length + rowsMZMPZ3.length + rowsMZMPZ4.length + rowsMZMPZ5.length + rowsMZMPZ6.length + rowsMZMPZ7.length + rowsMZMPZ8.length + rowsMZMPZ9.length + rowsMZMPZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZMPZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZMPZ : cnfOfRows16 rowsMZMPZ = MZMPZCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZMPZ MZMPZCnf 0 ⟨MZMPZe0, MZMPZe1, MZMPZe2, MZMPZe3, MZMPZe4, MZMPZe5, MZMPZe6, MZMPZe7, MZMPZe8, MZMPZe9, MZMPZe10, MZMPZeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZMPZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZMPZ : Minimality.H16.SAT.CoreUnsat rowsMZMPZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZMPZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZMPZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0-+` of type 16 is Rupert**: `Core16ZW (-1) 0 (-1) 1`. -/
theorem rupert_of_coreMZMPZ : Minimality.H16.SAT.Core16ZW (-1) 0 (-1) 1 := rupert_of_core_dataMZMPZ coreUnsatMZMPZ

end Minimality.H16K.SAT
