module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpzpzPq
public import Minimality.Type24SAT.K24.ChkMpzpzPq

@[expose] public section

/-!
# Type 24, class mpzpz off `OB1`: core MpzpzPq, `CoreUnsat rowsMpzpzPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpzpzPqe0 : (MpzpzPqCnf.drop (0)).take rowsMpzpzPq0.length = cnfOfRows [rowsMpzpzPq0] := by decide +kernel
theorem MpzpzPqe1 : (MpzpzPqCnf.drop (0 + rowsMpzpzPq0.length)).take rowsMpzpzPq1.length = cnfOfRows [rowsMpzpzPq1] := by decide +kernel
theorem MpzpzPqe2 : (MpzpzPqCnf.drop (0 + rowsMpzpzPq0.length + rowsMpzpzPq1.length)).take rowsMpzpzPq2.length = cnfOfRows [rowsMpzpzPq2] := by decide +kernel
theorem MpzpzPqe3 : (MpzpzPqCnf.drop (0 + rowsMpzpzPq0.length + rowsMpzpzPq1.length + rowsMpzpzPq2.length)).take rowsMpzpzPq3.length = cnfOfRows [rowsMpzpzPq3] := by decide +kernel
theorem MpzpzPqe4 : (MpzpzPqCnf.drop (0 + rowsMpzpzPq0.length + rowsMpzpzPq1.length + rowsMpzpzPq2.length + rowsMpzpzPq3.length)).take rowsMpzpzPq4.length = cnfOfRows [rowsMpzpzPq4] := by decide +kernel
theorem MpzpzPqeEnd : MpzpzPqCnf.drop (0 + rowsMpzpzPq0.length + rowsMpzpzPq1.length + rowsMpzpzPq2.length + rowsMpzpzPq3.length + rowsMpzpzPq4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpzpzPq, chunk by chunk. -/
theorem cnf_eqMpzpzPq : cnfOfRows rowsMpzpzPq = MpzpzPqCnf := by
  have h := cnfOfRows_of_chkAt rowsMpzpzPq MpzpzPqCnf 0 ⟨MpzpzPqe0, MpzpzPqe1, MpzpzPqe2, MpzpzPqe3, MpzpzPqe4, MpzpzPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpzpzPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpzpzPq : Minimality.H24.SAT.CoreUnsat rowsMpzpzPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpzpzPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpzpzPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
