module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmzmPq
public import Minimality.Type24SAT.K24.ChkMpmzmPq

@[expose] public section

/-!
# Type 24, class mpmzm off `OB1`: core MpmzmPq, `CoreUnsat rowsMpmzmPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem MpmzmPqe0 : (MpmzmPqCnf.drop (0)).take rowsMpmzmPq0.length = cnfOfRows [rowsMpmzmPq0] := by decide +kernel
theorem MpmzmPqe1 : (MpmzmPqCnf.drop (0 + rowsMpmzmPq0.length)).take rowsMpmzmPq1.length = cnfOfRows [rowsMpmzmPq1] := by decide +kernel
theorem MpmzmPqe2 : (MpmzmPqCnf.drop (0 + rowsMpmzmPq0.length + rowsMpmzmPq1.length)).take rowsMpmzmPq2.length = cnfOfRows [rowsMpmzmPq2] := by decide +kernel
theorem MpmzmPqe3 : (MpmzmPqCnf.drop (0 + rowsMpmzmPq0.length + rowsMpmzmPq1.length + rowsMpmzmPq2.length)).take rowsMpmzmPq3.length = cnfOfRows [rowsMpmzmPq3] := by decide +kernel
theorem MpmzmPqeEnd : MpmzmPqCnf.drop (0 + rowsMpmzmPq0.length + rowsMpmzmPq1.length + rowsMpmzmPq2.length + rowsMpmzmPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmzmPq, chunk by chunk. -/
theorem cnf_eqMpmzmPq : cnfOfRows rowsMpmzmPq = MpmzmPqCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmzmPq MpmzmPqCnf 0 ⟨MpmzmPqe0, MpmzmPqe1, MpmzmPqe2, MpmzmPqe3, MpmzmPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmzmPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmzmPq : Minimality.H24.SAT.CoreUnsat rowsMpmzmPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.MpmzmPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqMpmzmPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
