module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpzpzPq
public import Minimality.Type24SAT.K24.ChkZpzpzPq

@[expose] public section

/-!
# Type 24, class zpzpz off `OB1`: core ZpzpzPq, `CoreUnsat rowsZpzpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem ZpzpzPqe0 : (ZpzpzPqCnf.drop (0)).take rowsZpzpzPq0.length = cnfOfRows [rowsZpzpzPq0] := by decide +kernel
theorem ZpzpzPqe1 : (ZpzpzPqCnf.drop (0 + rowsZpzpzPq0.length)).take rowsZpzpzPq1.length = cnfOfRows [rowsZpzpzPq1] := by decide +kernel
theorem ZpzpzPqe2 : (ZpzpzPqCnf.drop (0 + rowsZpzpzPq0.length + rowsZpzpzPq1.length)).take rowsZpzpzPq2.length = cnfOfRows [rowsZpzpzPq2] := by decide +kernel
theorem ZpzpzPqeEnd : ZpzpzPqCnf.drop (0 + rowsZpzpzPq0.length + rowsZpzpzPq1.length + rowsZpzpzPq2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpzpzPq, chunk by chunk. -/
theorem cnf_eqZpzpzPq : cnfOfRows rowsZpzpzPq = ZpzpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsZpzpzPq ZpzpzPqCnf 0 ⟨ZpzpzPqe0, ZpzpzPqe1, ZpzpzPqe2, ZpzpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpzpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpzpzPq : Minimality.H24.SAT.CoreUnsat rowsZpzpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.ZpzpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqZpzpzPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
