module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpzPq
public import Minimality.Type24SAT.K24.ChkMpmpzPq

@[expose] public section

/-!
# Type 24, class mpmpz off `OB1`: core MpmpzPq, `CoreUnsat rowsMpmpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem MpmpzPqe0 : (MpmpzPqCnf.drop (0)).take rowsMpmpzPq0.length = cnfOfRows [rowsMpmpzPq0] := by decide +kernel
theorem MpmpzPqe1 : (MpmpzPqCnf.drop (0 + rowsMpmpzPq0.length)).take rowsMpmpzPq1.length = cnfOfRows [rowsMpmpzPq1] := by decide +kernel
theorem MpmpzPqe2 : (MpmpzPqCnf.drop (0 + rowsMpmpzPq0.length + rowsMpmpzPq1.length)).take rowsMpmpzPq2.length = cnfOfRows [rowsMpmpzPq2] := by decide +kernel
theorem MpmpzPqe3 : (MpmpzPqCnf.drop (0 + rowsMpmpzPq0.length + rowsMpmpzPq1.length + rowsMpmpzPq2.length)).take rowsMpmpzPq3.length = cnfOfRows [rowsMpmpzPq3] := by decide +kernel
theorem MpmpzPqeEnd : MpmpzPqCnf.drop (0 + rowsMpmpzPq0.length + rowsMpmpzPq1.length + rowsMpmpzPq2.length + rowsMpmpzPq3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmpzPq, chunk by chunk. -/
theorem cnf_eqMpmpzPq : cnfOfRows rowsMpmpzPq = MpmpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpzPq MpmpzPqCnf 0 ⟨MpmpzPqe0, MpmpzPqe1, MpmpzPqe2, MpmpzPqe3, MpmpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpzPq : Minimality.H24.SAT.CoreUnsat rowsMpmpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.MpmpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqMpmpzPq] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
