module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMMU
public import Minimality.Type16SAT.ChkPZMMU

@[expose] public section

/-!
# Type 16, J7/J8: core PZMMU, `CoreUnsat rowsPZMMU` from the kernel-checked LRAT proof, and `rupert_of_corePZMMU`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMMUe0 : (PZMMUCnf.drop (0)).take rowsPZMMU0.length = cnfOfRows16 [rowsPZMMU0] := by decide +kernel
theorem PZMMUe1 : (PZMMUCnf.drop (0 + rowsPZMMU0.length)).take rowsPZMMU1.length = cnfOfRows16 [rowsPZMMU1] := by decide +kernel
theorem PZMMUe2 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length)).take rowsPZMMU2.length = cnfOfRows16 [rowsPZMMU2] := by decide +kernel
theorem PZMMUe3 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length)).take rowsPZMMU3.length = cnfOfRows16 [rowsPZMMU3] := by decide +kernel
theorem PZMMUe4 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length)).take rowsPZMMU4.length = cnfOfRows16 [rowsPZMMU4] := by decide +kernel
theorem PZMMUe5 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length)).take rowsPZMMU5.length = cnfOfRows16 [rowsPZMMU5] := by decide +kernel
theorem PZMMUe6 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length)).take rowsPZMMU6.length = cnfOfRows16 [rowsPZMMU6] := by decide +kernel
theorem PZMMUe7 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length)).take rowsPZMMU7.length = cnfOfRows16 [rowsPZMMU7] := by decide +kernel
theorem PZMMUe8 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length + rowsPZMMU7.length)).take rowsPZMMU8.length = cnfOfRows16 [rowsPZMMU8] := by decide +kernel
theorem PZMMUe9 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length + rowsPZMMU7.length + rowsPZMMU8.length)).take rowsPZMMU9.length = cnfOfRows16 [rowsPZMMU9] := by decide +kernel
theorem PZMMUe10 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length + rowsPZMMU7.length + rowsPZMMU8.length + rowsPZMMU9.length)).take rowsPZMMU10.length = cnfOfRows16 [rowsPZMMU10] := by decide +kernel
theorem PZMMUe11 : (PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length + rowsPZMMU7.length + rowsPZMMU8.length + rowsPZMMU9.length + rowsPZMMU10.length)).take rowsPZMMU11.length = cnfOfRows16 [rowsPZMMU11] := by decide +kernel
theorem PZMMUeEnd : PZMMUCnf.drop (0 + rowsPZMMU0.length + rowsPZMMU1.length + rowsPZMMU2.length + rowsPZMMU3.length + rowsPZMMU4.length + rowsPZMMU5.length + rowsPZMMU6.length + rowsPZMMU7.length + rowsPZMMU8.length + rowsPZMMU9.length + rowsPZMMU10.length + rowsPZMMU11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMMU (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMMU : cnfOfRows16 rowsPZMMU = PZMMUCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMMU PZMMUCnf 0 ⟨PZMMUe0, PZMMUe1, PZMMUe2, PZMMUe3, PZMMUe4, PZMMUe5, PZMMUe6, PZMMUe7, PZMMUe8, PZMMUe9, PZMMUe10, PZMMUe11, PZMMUeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMMU are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMMU : Minimality.H16.SAT.CoreUnsat rowsPZMMU := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMMUunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMMU] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0--` of type 16 is Rupert**: `Core16TW 1 0 (-1) (-1)`. -/
theorem rupert_of_corePZMMU : Minimality.H16.SAT.Core16TW 1 0 (-1) (-1) := rupert_of_core_dataPZMMU coreUnsatPZMMU

end Minimality.H16K.SAT
