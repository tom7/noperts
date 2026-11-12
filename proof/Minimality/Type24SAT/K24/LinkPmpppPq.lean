module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPmpppPq
public import Minimality.Type24SAT.K24.ChkPmpppPq

@[expose] public section

/-!
# Type 24, class pmppp off `OB1`: core PmpppPq, `CoreUnsat rowsPmpppPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PmpppPqe0 : (PmpppPqCnf.drop (0)).take rowsPmpppPq0.length = cnfOfRows [rowsPmpppPq0] := by decide +kernel
theorem PmpppPqe1 : (PmpppPqCnf.drop (0 + rowsPmpppPq0.length)).take rowsPmpppPq1.length = cnfOfRows [rowsPmpppPq1] := by decide +kernel
theorem PmpppPqe2 : (PmpppPqCnf.drop (0 + rowsPmpppPq0.length + rowsPmpppPq1.length)).take rowsPmpppPq2.length = cnfOfRows [rowsPmpppPq2] := by decide +kernel
theorem PmpppPqe3 : (PmpppPqCnf.drop (0 + rowsPmpppPq0.length + rowsPmpppPq1.length + rowsPmpppPq2.length)).take rowsPmpppPq3.length = cnfOfRows [rowsPmpppPq3] := by decide +kernel
theorem PmpppPqeEnd : PmpppPqCnf.drop (0 + rowsPmpppPq0.length + rowsPmpppPq1.length + rowsPmpppPq2.length + rowsPmpppPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PmpppPq, chunk by chunk. -/
theorem cnf_eqPmpppPq : cnfOfRows rowsPmpppPq = PmpppPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPmpppPq PmpppPqCnf 0 ⟨PmpppPqe0, PmpppPqe1, PmpppPqe2, PmpppPqe3, PmpppPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PmpppPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPmpppPq : Minimality.H24.SAT.CoreUnsat rowsPmpppPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PmpppPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPmpppPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
