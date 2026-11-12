module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmmmPq
public import Minimality.Type24SAT.K24.ChkMpmmmPq

@[expose] public section

/-!
# Type 24, class mpmmm off `OB1`: core MpmmmPq, `CoreUnsat rowsMpmmmPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmmmPqe0 : (MpmmmPqCnf.drop (0)).take rowsMpmmmPq0.length = cnfOfRows [rowsMpmmmPq0] := by decide +kernel
theorem MpmmmPqe1 : (MpmmmPqCnf.drop (0 + rowsMpmmmPq0.length)).take rowsMpmmmPq1.length = cnfOfRows [rowsMpmmmPq1] := by decide +kernel
theorem MpmmmPqe2 : (MpmmmPqCnf.drop (0 + rowsMpmmmPq0.length + rowsMpmmmPq1.length)).take rowsMpmmmPq2.length = cnfOfRows [rowsMpmmmPq2] := by decide +kernel
theorem MpmmmPqe3 : (MpmmmPqCnf.drop (0 + rowsMpmmmPq0.length + rowsMpmmmPq1.length + rowsMpmmmPq2.length)).take rowsMpmmmPq3.length = cnfOfRows [rowsMpmmmPq3] := by decide +kernel
theorem MpmmmPqeEnd : MpmmmPqCnf.drop (0 + rowsMpmmmPq0.length + rowsMpmmmPq1.length + rowsMpmmmPq2.length + rowsMpmmmPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmmmPq, chunk by chunk. -/
theorem cnf_eqMpmmmPq : cnfOfRows rowsMpmmmPq = MpmmmPqCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmmmPq MpmmmPqCnf 0 ⟨MpmmmPqe0, MpmmmPqe1, MpmmmPqe2, MpmmmPqe3, MpmmmPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmmmPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmmmPq : Minimality.H24.SAT.CoreUnsat rowsMpmmmPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmmmPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmmmPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
