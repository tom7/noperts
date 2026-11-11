module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMZZZ
public import Minimality.Type16SAT.ChkPZMZZZ

@[expose] public section

/-!
# Type 16, J7/J8: core PZMZZZ, `CoreUnsat rowsPZMZZZ` from the kernel-checked LRAT proof, and `rupert_of_corePZMZZZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMZZZe0 : (PZMZZZCnf.drop (0)).take rowsPZMZZZ0.length = cnfOfRows16 [rowsPZMZZZ0] := by decide +kernel
theorem PZMZZZe1 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length)).take rowsPZMZZZ1.length = cnfOfRows16 [rowsPZMZZZ1] := by decide +kernel
theorem PZMZZZe2 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length)).take rowsPZMZZZ2.length = cnfOfRows16 [rowsPZMZZZ2] := by decide +kernel
theorem PZMZZZe3 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length)).take rowsPZMZZZ3.length = cnfOfRows16 [rowsPZMZZZ3] := by decide +kernel
theorem PZMZZZe4 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length)).take rowsPZMZZZ4.length = cnfOfRows16 [rowsPZMZZZ4] := by decide +kernel
theorem PZMZZZe5 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length)).take rowsPZMZZZ5.length = cnfOfRows16 [rowsPZMZZZ5] := by decide +kernel
theorem PZMZZZe6 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length)).take rowsPZMZZZ6.length = cnfOfRows16 [rowsPZMZZZ6] := by decide +kernel
theorem PZMZZZe7 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length + rowsPZMZZZ6.length)).take rowsPZMZZZ7.length = cnfOfRows16 [rowsPZMZZZ7] := by decide +kernel
theorem PZMZZZe8 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length + rowsPZMZZZ6.length + rowsPZMZZZ7.length)).take rowsPZMZZZ8.length = cnfOfRows16 [rowsPZMZZZ8] := by decide +kernel
theorem PZMZZZe9 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length + rowsPZMZZZ6.length + rowsPZMZZZ7.length + rowsPZMZZZ8.length)).take rowsPZMZZZ9.length = cnfOfRows16 [rowsPZMZZZ9] := by decide +kernel
theorem PZMZZZe10 : (PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length + rowsPZMZZZ6.length + rowsPZMZZZ7.length + rowsPZMZZZ8.length + rowsPZMZZZ9.length)).take rowsPZMZZZ10.length = cnfOfRows16 [rowsPZMZZZ10] := by decide +kernel
theorem PZMZZZeEnd : PZMZZZCnf.drop (0 + rowsPZMZZZ0.length + rowsPZMZZZ1.length + rowsPZMZZZ2.length + rowsPZMZZZ3.length + rowsPZMZZZ4.length + rowsPZMZZZ5.length + rowsPZMZZZ6.length + rowsPZMZZZ7.length + rowsPZMZZZ8.length + rowsPZMZZZ9.length + rowsPZMZZZ10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMZZZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMZZZ : cnfOfRows16 rowsPZMZZZ = PZMZZZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMZZZ PZMZZZCnf 0 ⟨PZMZZZe0, PZMZZZe1, PZMZZZe2, PZMZZZe3, PZMZZZe4, PZMZZZe5, PZMZZZe6, PZMZZZe7, PZMZZZe8, PZMZZZe9, PZMZZZe10, PZMZZZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMZZZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMZZZ : Minimality.H16.SAT.CoreUnsat rowsPZMZZZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMZZZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMZZZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0-0` of type 16 is Rupert**: `Core16ZZW 1 0 (-1) 0`. -/
theorem rupert_of_corePZMZZZ : Minimality.H16.SAT.Core16ZZW 1 0 (-1) 0 := rupert_of_core_dataPZMZZZ coreUnsatPZMZZZ

end Minimality.H16K.SAT
