module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpppzPq
public import Minimality.Type24SAT.K24.ChkPpppzPq

@[expose] public section

/-!
# Type 24, class ppppz off `OB1`: core PpppzPq, `CoreUnsat rowsPpppzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PpppzPqe0 : (PpppzPqCnf.drop (0)).take rowsPpppzPq0.length = cnfOfRows [rowsPpppzPq0] := by decide +kernel
theorem PpppzPqe1 : (PpppzPqCnf.drop (0 + rowsPpppzPq0.length)).take rowsPpppzPq1.length = cnfOfRows [rowsPpppzPq1] := by decide +kernel
theorem PpppzPqe2 : (PpppzPqCnf.drop (0 + rowsPpppzPq0.length + rowsPpppzPq1.length)).take rowsPpppzPq2.length = cnfOfRows [rowsPpppzPq2] := by decide +kernel
theorem PpppzPqe3 : (PpppzPqCnf.drop (0 + rowsPpppzPq0.length + rowsPpppzPq1.length + rowsPpppzPq2.length)).take rowsPpppzPq3.length = cnfOfRows [rowsPpppzPq3] := by decide +kernel
theorem PpppzPqe4 : (PpppzPqCnf.drop (0 + rowsPpppzPq0.length + rowsPpppzPq1.length + rowsPpppzPq2.length + rowsPpppzPq3.length)).take rowsPpppzPq4.length = cnfOfRows [rowsPpppzPq4] := by decide +kernel
theorem PpppzPqeEnd : PpppzPqCnf.drop (0 + rowsPpppzPq0.length + rowsPpppzPq1.length + rowsPpppzPq2.length + rowsPpppzPq3.length + rowsPpppzPq4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpppzPq, chunk by chunk. -/
theorem cnf_eqPpppzPq : cnfOfRows rowsPpppzPq = PpppzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPpppzPq PpppzPqCnf 0 ⟨PpppzPqe0, PpppzPqe1, PpppzPqe2, PpppzPqe3, PpppzPqe4, PpppzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpppzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpppzPq : Minimality.H24.SAT.CoreUnsat rowsPpppzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PpppzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpppzPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
