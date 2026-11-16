module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPzpppNotP
public import Minimality.Type24SAT.K24.ChkPzpppNotP

@[expose] public section

/-!
# Type 24, class pzppp off `OB1`: core PzpppNotP, `CoreUnsat rowsPzpppNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PzpppNotPe0 : (PzpppNotPCnf.drop (0)).take rowsPzpppNotP0.length = cnfOfRows [rowsPzpppNotP0] := by decide +kernel
theorem PzpppNotPe1 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length)).take rowsPzpppNotP1.length = cnfOfRows [rowsPzpppNotP1] := by decide +kernel
theorem PzpppNotPe2 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length)).take rowsPzpppNotP2.length = cnfOfRows [rowsPzpppNotP2] := by decide +kernel
theorem PzpppNotPe3 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length)).take rowsPzpppNotP3.length = cnfOfRows [rowsPzpppNotP3] := by decide +kernel
theorem PzpppNotPe4 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length + rowsPzpppNotP3.length)).take rowsPzpppNotP4.length = cnfOfRows [rowsPzpppNotP4] := by decide +kernel
theorem PzpppNotPe5 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length + rowsPzpppNotP3.length + rowsPzpppNotP4.length)).take rowsPzpppNotP5.length = cnfOfRows [rowsPzpppNotP5] := by decide +kernel
theorem PzpppNotPe6 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length + rowsPzpppNotP3.length + rowsPzpppNotP4.length + rowsPzpppNotP5.length)).take rowsPzpppNotP6.length = cnfOfRows [rowsPzpppNotP6] := by decide +kernel
theorem PzpppNotPe7 : (PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length + rowsPzpppNotP3.length + rowsPzpppNotP4.length + rowsPzpppNotP5.length + rowsPzpppNotP6.length)).take rowsPzpppNotP7.length = cnfOfRows [rowsPzpppNotP7] := by decide +kernel
theorem PzpppNotPeEnd : PzpppNotPCnf.drop (0 + rowsPzpppNotP0.length + rowsPzpppNotP1.length + rowsPzpppNotP2.length + rowsPzpppNotP3.length + rowsPzpppNotP4.length + rowsPzpppNotP5.length + rowsPzpppNotP6.length + rowsPzpppNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PzpppNotP, chunk by chunk. -/
theorem cnf_eqPzpppNotP : cnfOfRows rowsPzpppNotP = PzpppNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPzpppNotP PzpppNotPCnf 0 ⟨PzpppNotPe0, PzpppNotPe1, PzpppNotPe2, PzpppNotPe3, PzpppNotPe4, PzpppNotPe5, PzpppNotPe6, PzpppNotPe7, PzpppNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PzpppNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPzpppNotP : Minimality.H24.SAT.CoreUnsat rowsPzpppNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PzpppNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPzpppNotP] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
