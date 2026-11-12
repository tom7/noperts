module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpmPq
public import Minimality.Type24SAT.K24.ChkMpmpmPq

@[expose] public section

/-!
# Type 24, class mpmpm off `OB1`: core MpmpmPq, `CoreUnsat rowsMpmpmPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmpmPqe0 : (MpmpmPqCnf.drop (0)).take rowsMpmpmPq0.length = cnfOfRows [rowsMpmpmPq0] := by decide +kernel
theorem MpmpmPqe1 : (MpmpmPqCnf.drop (0 + rowsMpmpmPq0.length)).take rowsMpmpmPq1.length = cnfOfRows [rowsMpmpmPq1] := by decide +kernel
theorem MpmpmPqe2 : (MpmpmPqCnf.drop (0 + rowsMpmpmPq0.length + rowsMpmpmPq1.length)).take rowsMpmpmPq2.length = cnfOfRows [rowsMpmpmPq2] := by decide +kernel
theorem MpmpmPqe3 : (MpmpmPqCnf.drop (0 + rowsMpmpmPq0.length + rowsMpmpmPq1.length + rowsMpmpmPq2.length)).take rowsMpmpmPq3.length = cnfOfRows [rowsMpmpmPq3] := by decide +kernel
theorem MpmpmPqeEnd : MpmpmPqCnf.drop (0 + rowsMpmpmPq0.length + rowsMpmpmPq1.length + rowsMpmpmPq2.length + rowsMpmpmPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmpmPq, chunk by chunk. -/
theorem cnf_eqMpmpmPq : cnfOfRows rowsMpmpmPq = MpmpmPqCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpmPq MpmpmPqCnf 0 ⟨MpmpmPqe0, MpmpmPqe1, MpmpmPqe2, MpmpmPqe3, MpmpmPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmpmPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpmPq : Minimality.H24.SAT.CoreUnsat rowsMpmpmPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmpmPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmpmPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
