module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPppppPq
public import Minimality.Type24SAT.K24.ChkPppppPq

@[expose] public section

/-!
# Type 24, class ppppp off `OB1`: core PppppPq, `CoreUnsat rowsPppppPq` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PppppPqe0 : (PppppPqCnf.drop (0)).take rowsPppppPq0.length = cnfOfRows [rowsPppppPq0] := by decide +kernel
theorem PppppPqe1 : (PppppPqCnf.drop (0 + rowsPppppPq0.length)).take rowsPppppPq1.length = cnfOfRows [rowsPppppPq1] := by decide +kernel
theorem PppppPqe2 : (PppppPqCnf.drop (0 + rowsPppppPq0.length + rowsPppppPq1.length)).take rowsPppppPq2.length = cnfOfRows [rowsPppppPq2] := by decide +kernel
theorem PppppPqe3 : (PppppPqCnf.drop (0 + rowsPppppPq0.length + rowsPppppPq1.length + rowsPppppPq2.length)).take rowsPppppPq3.length = cnfOfRows [rowsPppppPq3] := by decide +kernel
theorem PppppPqe4 : (PppppPqCnf.drop (0 + rowsPppppPq0.length + rowsPppppPq1.length + rowsPppppPq2.length + rowsPppppPq3.length)).take rowsPppppPq4.length = cnfOfRows [rowsPppppPq4] := by decide +kernel
theorem PppppPqeEnd : PppppPqCnf.drop (0 + rowsPppppPq0.length + rowsPppppPq1.length + rowsPppppPq2.length + rowsPppppPq3.length + rowsPppppPq4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PppppPq, chunk by chunk. -/
theorem cnf_eqPppppPq : cnfOfRows rowsPppppPq = PppppPqCnf := by
  have h := cnfOfRows_of_chkAt rowsPppppPq PppppPqCnf 0 ⟨PppppPqe0, PppppPqe1, PppppPqe2, PppppPqe3, PppppPqe4, PppppPqeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PppppPq are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPppppPq : Minimality.H24.SAT.CoreUnsat rowsPppppPq := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PppppPqunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPppppPq] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
