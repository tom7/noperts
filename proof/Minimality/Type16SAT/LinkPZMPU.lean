module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMPU
public import Minimality.Type16SAT.ChkPZMPU

@[expose] public section

/-!
# Type 16, J7/J8: core PZMPU, `CoreUnsat rowsPZMPU` from the kernel-checked LRAT proof, and `rupert_of_corePZMPU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMPUe0 : (PZMPUCnf.drop (0)).take rowsPZMPU0.length = cnfOfRows16 [rowsPZMPU0] := by decide +kernel
theorem PZMPUe1 : (PZMPUCnf.drop (0 + rowsPZMPU0.length)).take rowsPZMPU1.length = cnfOfRows16 [rowsPZMPU1] := by decide +kernel
theorem PZMPUe2 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length)).take rowsPZMPU2.length = cnfOfRows16 [rowsPZMPU2] := by decide +kernel
theorem PZMPUe3 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length)).take rowsPZMPU3.length = cnfOfRows16 [rowsPZMPU3] := by decide +kernel
theorem PZMPUe4 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length)).take rowsPZMPU4.length = cnfOfRows16 [rowsPZMPU4] := by decide +kernel
theorem PZMPUe5 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length)).take rowsPZMPU5.length = cnfOfRows16 [rowsPZMPU5] := by decide +kernel
theorem PZMPUe6 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length)).take rowsPZMPU6.length = cnfOfRows16 [rowsPZMPU6] := by decide +kernel
theorem PZMPUe7 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length + rowsPZMPU6.length)).take rowsPZMPU7.length = cnfOfRows16 [rowsPZMPU7] := by decide +kernel
theorem PZMPUe8 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length + rowsPZMPU6.length + rowsPZMPU7.length)).take rowsPZMPU8.length = cnfOfRows16 [rowsPZMPU8] := by decide +kernel
theorem PZMPUe9 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length + rowsPZMPU6.length + rowsPZMPU7.length + rowsPZMPU8.length)).take rowsPZMPU9.length = cnfOfRows16 [rowsPZMPU9] := by decide +kernel
theorem PZMPUe10 : (PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length + rowsPZMPU6.length + rowsPZMPU7.length + rowsPZMPU8.length + rowsPZMPU9.length)).take rowsPZMPU10.length = cnfOfRows16 [rowsPZMPU10] := by decide +kernel
theorem PZMPUeEnd : PZMPUCnf.drop (0 + rowsPZMPU0.length + rowsPZMPU1.length + rowsPZMPU2.length + rowsPZMPU3.length + rowsPZMPU4.length + rowsPZMPU5.length + rowsPZMPU6.length + rowsPZMPU7.length + rowsPZMPU8.length + rowsPZMPU9.length + rowsPZMPU10.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMPU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMPU : cnfOfRows16 rowsPZMPU = PZMPUCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMPU PZMPUCnf 0 ⟨PZMPUe0, PZMPUe1, PZMPUe2, PZMPUe3, PZMPUe4, PZMPUe5, PZMPUe6, PZMPUe7, PZMPUe8, PZMPUe9, PZMPUe10, PZMPUeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMPU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMPU : Minimality.H16.SAT.CoreUnsat rowsPZMPU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMPUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMPU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0-+` of type 16 is Rupert**: `Core16TW 1 0 (-1) 1`. -/
theorem rupert_of_corePZMPU : Minimality.H16.SAT.Core16TW 1 0 (-1) 1 := rupert_of_core_dataPZMPU coreUnsatPZMPU

end Minimality.H16K.SAT
