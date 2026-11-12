module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmmmNotP
public import Minimality.Type24SAT.K24.ChkMpmmmNotP

@[expose] public section

/-!
# Type 24, class mpmmm off `OB1`: core MpmmmNotP, `CoreUnsat rowsMpmmmNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmmmNotPe0 : (MpmmmNotPCnf.drop (0)).take rowsMpmmmNotP0.length = cnfOfRows [rowsMpmmmNotP0] := by decide +kernel
theorem MpmmmNotPe1 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length)).take rowsMpmmmNotP1.length = cnfOfRows [rowsMpmmmNotP1] := by decide +kernel
theorem MpmmmNotPe2 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length)).take rowsMpmmmNotP2.length = cnfOfRows [rowsMpmmmNotP2] := by decide +kernel
theorem MpmmmNotPe3 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length + rowsMpmmmNotP2.length)).take rowsMpmmmNotP3.length = cnfOfRows [rowsMpmmmNotP3] := by decide +kernel
theorem MpmmmNotPe4 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length + rowsMpmmmNotP2.length + rowsMpmmmNotP3.length)).take rowsMpmmmNotP4.length = cnfOfRows [rowsMpmmmNotP4] := by decide +kernel
theorem MpmmmNotPe5 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length + rowsMpmmmNotP2.length + rowsMpmmmNotP3.length + rowsMpmmmNotP4.length)).take rowsMpmmmNotP5.length = cnfOfRows [rowsMpmmmNotP5] := by decide +kernel
theorem MpmmmNotPe6 : (MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length + rowsMpmmmNotP2.length + rowsMpmmmNotP3.length + rowsMpmmmNotP4.length + rowsMpmmmNotP5.length)).take rowsMpmmmNotP6.length = cnfOfRows [rowsMpmmmNotP6] := by decide +kernel
theorem MpmmmNotPeEnd : MpmmmNotPCnf.drop (0 + rowsMpmmmNotP0.length + rowsMpmmmNotP1.length + rowsMpmmmNotP2.length + rowsMpmmmNotP3.length + rowsMpmmmNotP4.length + rowsMpmmmNotP5.length + rowsMpmmmNotP6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmmmNotP, chunk by chunk. -/
theorem cnf_eqMpmmmNotP : cnfOfRows rowsMpmmmNotP = MpmmmNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmmmNotP MpmmmNotPCnf 0 ⟨MpmmmNotPe0, MpmmmNotPe1, MpmmmNotPe2, MpmmmNotPe3, MpmmmNotPe4, MpmmmNotPe5, MpmmmNotPe6, MpmmmNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmmmNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmmmNotP : Minimality.H24.SAT.CoreUnsat rowsMpmmmNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmmmNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmmmNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
