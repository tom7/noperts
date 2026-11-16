module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmzmNotP
public import Minimality.Type24SAT.K24.ChkMpmzmNotP

@[expose] public section

/-!
# Type 24, class mpmzm off `OB1`: core MpmzmNotP, `CoreUnsat rowsMpmzmNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem MpmzmNotPe0 : (MpmzmNotPCnf.drop (0)).take rowsMpmzmNotP0.length = cnfOfRows [rowsMpmzmNotP0] := by decide +kernel
theorem MpmzmNotPe1 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length)).take rowsMpmzmNotP1.length = cnfOfRows [rowsMpmzmNotP1] := by decide +kernel
theorem MpmzmNotPe2 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length)).take rowsMpmzmNotP2.length = cnfOfRows [rowsMpmzmNotP2] := by decide +kernel
theorem MpmzmNotPe3 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length)).take rowsMpmzmNotP3.length = cnfOfRows [rowsMpmzmNotP3] := by decide +kernel
theorem MpmzmNotPe4 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length + rowsMpmzmNotP3.length)).take rowsMpmzmNotP4.length = cnfOfRows [rowsMpmzmNotP4] := by decide +kernel
theorem MpmzmNotPe5 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length + rowsMpmzmNotP3.length + rowsMpmzmNotP4.length)).take rowsMpmzmNotP5.length = cnfOfRows [rowsMpmzmNotP5] := by decide +kernel
theorem MpmzmNotPe6 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length + rowsMpmzmNotP3.length + rowsMpmzmNotP4.length + rowsMpmzmNotP5.length)).take rowsMpmzmNotP6.length = cnfOfRows [rowsMpmzmNotP6] := by decide +kernel
theorem MpmzmNotPe7 : (MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length + rowsMpmzmNotP3.length + rowsMpmzmNotP4.length + rowsMpmzmNotP5.length + rowsMpmzmNotP6.length)).take rowsMpmzmNotP7.length = cnfOfRows [rowsMpmzmNotP7] := by decide +kernel
theorem MpmzmNotPeEnd : MpmzmNotPCnf.drop (0 + rowsMpmzmNotP0.length + rowsMpmzmNotP1.length + rowsMpmzmNotP2.length + rowsMpmzmNotP3.length + rowsMpmzmNotP4.length + rowsMpmzmNotP5.length + rowsMpmzmNotP6.length + rowsMpmzmNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmzmNotP, chunk by chunk. -/
theorem cnf_eqMpmzmNotP : cnfOfRows rowsMpmzmNotP = MpmzmNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmzmNotP MpmzmNotPCnf 0 ⟨MpmzmNotPe0, MpmzmNotPe1, MpmzmNotPe2, MpmzmNotPe3, MpmzmNotPe4, MpmzmNotPe5, MpmzmNotPe6, MpmzmNotPe7, MpmzmNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmzmNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmzmNotP : Minimality.H24.SAT.CoreUnsat rowsMpmzmNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.MpmzmNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqMpmzmNotP] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
