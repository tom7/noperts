module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmpzPq
public import Minimality.Type24SAT.K24.ChkZpmpzPq

@[expose] public section

/-!
# Type 24, class zpmpz off `OB1`: core ZpmpzPq, `CoreUnsat rowsZpmpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem ZpmpzPqe0 : (ZpmpzPqCnf.drop (0)).take rowsZpmpzPq0.length = cnfOfRows [rowsZpmpzPq0] := by decide +kernel
theorem ZpmpzPqe1 : (ZpmpzPqCnf.drop (0 + rowsZpmpzPq0.length)).take rowsZpmpzPq1.length = cnfOfRows [rowsZpmpzPq1] := by decide +kernel
theorem ZpmpzPqe2 : (ZpmpzPqCnf.drop (0 + rowsZpmpzPq0.length + rowsZpmpzPq1.length)).take rowsZpmpzPq2.length = cnfOfRows [rowsZpmpzPq2] := by decide +kernel
theorem ZpmpzPqe3 : (ZpmpzPqCnf.drop (0 + rowsZpmpzPq0.length + rowsZpmpzPq1.length + rowsZpmpzPq2.length)).take rowsZpmpzPq3.length = cnfOfRows [rowsZpmpzPq3] := by decide +kernel
theorem ZpmpzPqeEnd : ZpmpzPqCnf.drop (0 + rowsZpmpzPq0.length + rowsZpmpzPq1.length + rowsZpmpzPq2.length + rowsZpmpzPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpmpzPq, chunk by chunk. -/
theorem cnf_eqZpmpzPq : cnfOfRows rowsZpmpzPq = ZpmpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmpzPq ZpmpzPqCnf 0 ⟨ZpmpzPqe0, ZpmpzPqe1, ZpmpzPqe2, ZpmpzPqe3, ZpmpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpmpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmpzPq : Minimality.H24.SAT.CoreUnsat rowsZpmpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.ZpmpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmpzPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
