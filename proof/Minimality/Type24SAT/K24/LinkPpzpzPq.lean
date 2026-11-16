module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpzpzPq
public import Minimality.Type24SAT.K24.ChkPpzpzPq

@[expose] public section

/-!
# Type 24, class ppzpz off `OB1`: core PpzpzPq, `CoreUnsat rowsPpzpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PpzpzPqe0 : (PpzpzPqCnf.drop (0)).take rowsPpzpzPq0.length = cnfOfRows [rowsPpzpzPq0] := by decide +kernel
theorem PpzpzPqe1 : (PpzpzPqCnf.drop (0 + rowsPpzpzPq0.length)).take rowsPpzpzPq1.length = cnfOfRows [rowsPpzpzPq1] := by decide +kernel
theorem PpzpzPqe2 : (PpzpzPqCnf.drop (0 + rowsPpzpzPq0.length + rowsPpzpzPq1.length)).take rowsPpzpzPq2.length = cnfOfRows [rowsPpzpzPq2] := by decide +kernel
theorem PpzpzPqeEnd : PpzpzPqCnf.drop (0 + rowsPpzpzPq0.length + rowsPpzpzPq1.length + rowsPpzpzPq2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpzpzPq, chunk by chunk. -/
theorem cnf_eqPpzpzPq : cnfOfRows rowsPpzpzPq = PpzpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPpzpzPq PpzpzPqCnf 0 ⟨PpzpzPqe0, PpzpzPqe1, PpzpzPqe2, PpzpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpzpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpzpzPq : Minimality.H24.SAT.CoreUnsat rowsPpzpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PpzpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpzpzPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
