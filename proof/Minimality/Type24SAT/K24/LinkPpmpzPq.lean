module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmpzPq
public import Minimality.Type24SAT.K24.ChkPpmpzPq

@[expose] public section

/-!
# Type 24, class ppmpz off `OB1`: core PpmpzPq, `CoreUnsat rowsPpmpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PpmpzPqe0 : (PpmpzPqCnf.drop (0)).take rowsPpmpzPq0.length = cnfOfRows [rowsPpmpzPq0] := by decide +kernel
theorem PpmpzPqe1 : (PpmpzPqCnf.drop (0 + rowsPpmpzPq0.length)).take rowsPpmpzPq1.length = cnfOfRows [rowsPpmpzPq1] := by decide +kernel
theorem PpmpzPqe2 : (PpmpzPqCnf.drop (0 + rowsPpmpzPq0.length + rowsPpmpzPq1.length)).take rowsPpmpzPq2.length = cnfOfRows [rowsPpmpzPq2] := by decide +kernel
theorem PpmpzPqe3 : (PpmpzPqCnf.drop (0 + rowsPpmpzPq0.length + rowsPpmpzPq1.length + rowsPpmpzPq2.length)).take rowsPpmpzPq3.length = cnfOfRows [rowsPpmpzPq3] := by decide +kernel
theorem PpmpzPqeEnd : PpmpzPqCnf.drop (0 + rowsPpmpzPq0.length + rowsPpmpzPq1.length + rowsPpmpzPq2.length + rowsPpmpzPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpmpzPq, chunk by chunk. -/
theorem cnf_eqPpmpzPq : cnfOfRows rowsPpmpzPq = PpmpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmpzPq PpmpzPqCnf 0 ⟨PpmpzPqe0, PpmpzPqe1, PpmpzPqe2, PpmpzPqe3, PpmpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpmpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmpzPq : Minimality.H24.SAT.CoreUnsat rowsPpmpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PpmpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpmpzPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
