module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPmpppNotP
public import Minimality.Type24SAT.K24.ChkPmpppNotP

@[expose] public section

/-!
# Type 24, class pmppp off `OB1`: core PmpppNotP, `CoreUnsat rowsPmpppNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PmpppNotPe0 : (PmpppNotPCnf.drop (0)).take rowsPmpppNotP0.length = cnfOfRows [rowsPmpppNotP0] := by decide +kernel
theorem PmpppNotPe1 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length)).take rowsPmpppNotP1.length = cnfOfRows [rowsPmpppNotP1] := by decide +kernel
theorem PmpppNotPe2 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length)).take rowsPmpppNotP2.length = cnfOfRows [rowsPmpppNotP2] := by decide +kernel
theorem PmpppNotPe3 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length + rowsPmpppNotP2.length)).take rowsPmpppNotP3.length = cnfOfRows [rowsPmpppNotP3] := by decide +kernel
theorem PmpppNotPe4 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length + rowsPmpppNotP2.length + rowsPmpppNotP3.length)).take rowsPmpppNotP4.length = cnfOfRows [rowsPmpppNotP4] := by decide +kernel
theorem PmpppNotPe5 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length + rowsPmpppNotP2.length + rowsPmpppNotP3.length + rowsPmpppNotP4.length)).take rowsPmpppNotP5.length = cnfOfRows [rowsPmpppNotP5] := by decide +kernel
theorem PmpppNotPe6 : (PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length + rowsPmpppNotP2.length + rowsPmpppNotP3.length + rowsPmpppNotP4.length + rowsPmpppNotP5.length)).take rowsPmpppNotP6.length = cnfOfRows [rowsPmpppNotP6] := by decide +kernel
theorem PmpppNotPeEnd : PmpppNotPCnf.drop (0 + rowsPmpppNotP0.length + rowsPmpppNotP1.length + rowsPmpppNotP2.length + rowsPmpppNotP3.length + rowsPmpppNotP4.length + rowsPmpppNotP5.length + rowsPmpppNotP6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PmpppNotP, chunk by chunk. -/
theorem cnf_eqPmpppNotP : cnfOfRows rowsPmpppNotP = PmpppNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPmpppNotP PmpppNotPCnf 0 ⟨PmpppNotPe0, PmpppNotPe1, PmpppNotPe2, PmpppNotPe3, PmpppNotPe4, PmpppNotPe5, PmpppNotPe6, PmpppNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PmpppNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPmpppNotP : Minimality.H24.SAT.CoreUnsat rowsPmpppNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PmpppNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPmpppNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
