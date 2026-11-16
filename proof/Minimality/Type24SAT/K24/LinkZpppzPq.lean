module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpppzPq
public import Minimality.Type24SAT.K24.ChkZpppzPq

@[expose] public section

/-!
# Type 24, class zpppz off `OB1`: core ZpppzPq, `CoreUnsat rowsZpppzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem ZpppzPqe0 : (ZpppzPqCnf.drop (0)).take rowsZpppzPq0.length = cnfOfRows [rowsZpppzPq0] := by decide +kernel
theorem ZpppzPqe1 : (ZpppzPqCnf.drop (0 + rowsZpppzPq0.length)).take rowsZpppzPq1.length = cnfOfRows [rowsZpppzPq1] := by decide +kernel
theorem ZpppzPqe2 : (ZpppzPqCnf.drop (0 + rowsZpppzPq0.length + rowsZpppzPq1.length)).take rowsZpppzPq2.length = cnfOfRows [rowsZpppzPq2] := by decide +kernel
theorem ZpppzPqe3 : (ZpppzPqCnf.drop (0 + rowsZpppzPq0.length + rowsZpppzPq1.length + rowsZpppzPq2.length)).take rowsZpppzPq3.length = cnfOfRows [rowsZpppzPq3] := by decide +kernel
theorem ZpppzPqe4 : (ZpppzPqCnf.drop (0 + rowsZpppzPq0.length + rowsZpppzPq1.length + rowsZpppzPq2.length + rowsZpppzPq3.length)).take rowsZpppzPq4.length = cnfOfRows [rowsZpppzPq4] := by decide +kernel
theorem ZpppzPqeEnd : ZpppzPqCnf.drop (0 + rowsZpppzPq0.length + rowsZpppzPq1.length + rowsZpppzPq2.length + rowsZpppzPq3.length + rowsZpppzPq4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpppzPq, chunk by chunk. -/
theorem cnf_eqZpppzPq : cnfOfRows rowsZpppzPq = ZpppzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsZpppzPq ZpppzPqCnf 0 ⟨ZpppzPqe0, ZpppzPqe1, ZpppzPqe2, ZpppzPqe3, ZpppzPqe4, ZpppzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpppzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpppzPq : Minimality.H24.SAT.CoreUnsat rowsZpppzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.ZpppzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqZpppzPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
