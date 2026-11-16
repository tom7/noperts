module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPzpppPq
public import Minimality.Type24SAT.K24.ChkPzpppPq

@[expose] public section

/-!
# Type 24, class pzppp off `OB1`: core PzpppPq, `CoreUnsat rowsPzpppPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PzpppPqe0 : (PzpppPqCnf.drop (0)).take rowsPzpppPq0.length = cnfOfRows [rowsPzpppPq0] := by decide +kernel
theorem PzpppPqe1 : (PzpppPqCnf.drop (0 + rowsPzpppPq0.length)).take rowsPzpppPq1.length = cnfOfRows [rowsPzpppPq1] := by decide +kernel
theorem PzpppPqe2 : (PzpppPqCnf.drop (0 + rowsPzpppPq0.length + rowsPzpppPq1.length)).take rowsPzpppPq2.length = cnfOfRows [rowsPzpppPq2] := by decide +kernel
theorem PzpppPqe3 : (PzpppPqCnf.drop (0 + rowsPzpppPq0.length + rowsPzpppPq1.length + rowsPzpppPq2.length)).take rowsPzpppPq3.length = cnfOfRows [rowsPzpppPq3] := by decide +kernel
theorem PzpppPqeEnd : PzpppPqCnf.drop (0 + rowsPzpppPq0.length + rowsPzpppPq1.length + rowsPzpppPq2.length + rowsPzpppPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PzpppPq, chunk by chunk. -/
theorem cnf_eqPzpppPq : cnfOfRows rowsPzpppPq = PzpppPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPzpppPq PzpppPqCnf 0 ⟨PzpppPqe0, PzpppPqe1, PzpppPqe2, PzpppPqe3, PzpppPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PzpppPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPzpppPq : Minimality.H24.SAT.CoreUnsat rowsPzpppPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PzpppPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPzpppPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
