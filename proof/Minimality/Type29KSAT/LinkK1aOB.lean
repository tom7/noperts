module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29KSAT.ProofK1aOB
public import Minimality.Type29KSAT.ChkK1aOB

@[expose] public section

/-!
# Type 29, K1a off the obtuse corner `OB6`: core K1aOB, `CoreUnsat rowsK1aOB` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem K1aOBe0 : (K1aOBCnf.drop (0)).take rowsK1aOB0.length = cnfOfRows [rowsK1aOB0] := by decide +kernel
theorem K1aOBe1 : (K1aOBCnf.drop (0 + rowsK1aOB0.length)).take rowsK1aOB1.length = cnfOfRows [rowsK1aOB1] := by decide +kernel
theorem K1aOBe2 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length)).take rowsK1aOB2.length = cnfOfRows [rowsK1aOB2] := by decide +kernel
theorem K1aOBe3 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length)).take rowsK1aOB3.length = cnfOfRows [rowsK1aOB3] := by decide +kernel
theorem K1aOBe4 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length)).take rowsK1aOB4.length = cnfOfRows [rowsK1aOB4] := by decide +kernel
theorem K1aOBe5 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length)).take rowsK1aOB5.length = cnfOfRows [rowsK1aOB5] := by decide +kernel
theorem K1aOBe6 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length + rowsK1aOB5.length)).take rowsK1aOB6.length = cnfOfRows [rowsK1aOB6] := by decide +kernel
theorem K1aOBe7 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length + rowsK1aOB5.length + rowsK1aOB6.length)).take rowsK1aOB7.length = cnfOfRows [rowsK1aOB7] := by decide +kernel
theorem K1aOBe8 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length + rowsK1aOB5.length + rowsK1aOB6.length + rowsK1aOB7.length)).take rowsK1aOB8.length = cnfOfRows [rowsK1aOB8] := by decide +kernel
theorem K1aOBe9 : (K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length + rowsK1aOB5.length + rowsK1aOB6.length + rowsK1aOB7.length + rowsK1aOB8.length)).take rowsK1aOB9.length = cnfOfRows [rowsK1aOB9] := by decide +kernel
theorem K1aOBeEnd : K1aOBCnf.drop (0 + rowsK1aOB0.length + rowsK1aOB1.length + rowsK1aOB2.length + rowsK1aOB3.length + rowsK1aOB4.length + rowsK1aOB5.length + rowsK1aOB6.length + rowsK1aOB7.length + rowsK1aOB8.length + rowsK1aOB9.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core K1aOB, chunk by chunk. -/
theorem cnf_eqK1aOB : cnfOfRows rowsK1aOB = K1aOBCnf := by
  have h := cnfOfRows_of_chkAt rowsK1aOB K1aOBCnf 0 ⟨K1aOBe0, K1aOBe1, K1aOBe2, K1aOBe3, K1aOBe4, K1aOBe5, K1aOBe6, K1aOBe7, K1aOBe8, K1aOBe9, K1aOBeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- **The numbered clauses of core K1aOB are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatK1aOB : CoreUnsat rowsK1aOB := by
  intro ρ hρ
  have h := K29.K1aOBunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqK1aOB] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29K.SAT
