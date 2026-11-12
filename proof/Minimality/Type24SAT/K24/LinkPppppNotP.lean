module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPppppNotP
public import Minimality.Type24SAT.K24.ChkPppppNotP

@[expose] public section

/-!
# Type 24, class ppppp off `OB1`: core PppppNotP, `CoreUnsat rowsPppppNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PppppNotPe0 : (PppppNotPCnf.drop (0)).take rowsPppppNotP0.length = cnfOfRows [rowsPppppNotP0] := by decide +kernel
theorem PppppNotPe1 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length)).take rowsPppppNotP1.length = cnfOfRows [rowsPppppNotP1] := by decide +kernel
theorem PppppNotPe2 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length)).take rowsPppppNotP2.length = cnfOfRows [rowsPppppNotP2] := by decide +kernel
theorem PppppNotPe3 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length + rowsPppppNotP2.length)).take rowsPppppNotP3.length = cnfOfRows [rowsPppppNotP3] := by decide +kernel
theorem PppppNotPe4 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length + rowsPppppNotP2.length + rowsPppppNotP3.length)).take rowsPppppNotP4.length = cnfOfRows [rowsPppppNotP4] := by decide +kernel
theorem PppppNotPe5 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length + rowsPppppNotP2.length + rowsPppppNotP3.length + rowsPppppNotP4.length)).take rowsPppppNotP5.length = cnfOfRows [rowsPppppNotP5] := by decide +kernel
theorem PppppNotPe6 : (PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length + rowsPppppNotP2.length + rowsPppppNotP3.length + rowsPppppNotP4.length + rowsPppppNotP5.length)).take rowsPppppNotP6.length = cnfOfRows [rowsPppppNotP6] := by decide +kernel
theorem PppppNotPeEnd : PppppNotPCnf.drop (0 + rowsPppppNotP0.length + rowsPppppNotP1.length + rowsPppppNotP2.length + rowsPppppNotP3.length + rowsPppppNotP4.length + rowsPppppNotP5.length + rowsPppppNotP6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PppppNotP, chunk by chunk. -/
theorem cnf_eqPppppNotP : cnfOfRows rowsPppppNotP = PppppNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPppppNotP PppppNotPCnf 0 ⟨PppppNotPe0, PppppNotPe1, PppppNotPe2, PppppNotPe3, PppppNotPe4, PppppNotPe5, PppppNotPe6, PppppNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PppppNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPppppNotP : Minimality.H24.SAT.CoreUnsat rowsPppppNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PppppNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPppppNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
