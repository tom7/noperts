module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpmNotP
public import Minimality.Type24SAT.K24.ChkMpmpmNotP

@[expose] public section

/-!
# Type 24, class mpmpm off `OB1`: core MpmpmNotP, `CoreUnsat rowsMpmpmNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmpmNotPe0 : (MpmpmNotPCnf.drop (0)).take rowsMpmpmNotP0.length = cnfOfRows [rowsMpmpmNotP0] := by decide +kernel
theorem MpmpmNotPe1 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length)).take rowsMpmpmNotP1.length = cnfOfRows [rowsMpmpmNotP1] := by decide +kernel
theorem MpmpmNotPe2 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length)).take rowsMpmpmNotP2.length = cnfOfRows [rowsMpmpmNotP2] := by decide +kernel
theorem MpmpmNotPe3 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length)).take rowsMpmpmNotP3.length = cnfOfRows [rowsMpmpmNotP3] := by decide +kernel
theorem MpmpmNotPe4 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length + rowsMpmpmNotP3.length)).take rowsMpmpmNotP4.length = cnfOfRows [rowsMpmpmNotP4] := by decide +kernel
theorem MpmpmNotPe5 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length + rowsMpmpmNotP3.length + rowsMpmpmNotP4.length)).take rowsMpmpmNotP5.length = cnfOfRows [rowsMpmpmNotP5] := by decide +kernel
theorem MpmpmNotPe6 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length + rowsMpmpmNotP3.length + rowsMpmpmNotP4.length + rowsMpmpmNotP5.length)).take rowsMpmpmNotP6.length = cnfOfRows [rowsMpmpmNotP6] := by decide +kernel
theorem MpmpmNotPe7 : (MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length + rowsMpmpmNotP3.length + rowsMpmpmNotP4.length + rowsMpmpmNotP5.length + rowsMpmpmNotP6.length)).take rowsMpmpmNotP7.length = cnfOfRows [rowsMpmpmNotP7] := by decide +kernel
theorem MpmpmNotPeEnd : MpmpmNotPCnf.drop (0 + rowsMpmpmNotP0.length + rowsMpmpmNotP1.length + rowsMpmpmNotP2.length + rowsMpmpmNotP3.length + rowsMpmpmNotP4.length + rowsMpmpmNotP5.length + rowsMpmpmNotP6.length + rowsMpmpmNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmpmNotP, chunk by chunk. -/
theorem cnf_eqMpmpmNotP : cnfOfRows rowsMpmpmNotP = MpmpmNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpmNotP MpmpmNotPCnf 0 ⟨MpmpmNotPe0, MpmpmNotPe1, MpmpmNotPe2, MpmpmNotPe3, MpmpmNotPe4, MpmpmNotPe5, MpmpmNotPe6, MpmpmNotPe7, MpmpmNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmpmNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpmNotP : Minimality.H24.SAT.CoreUnsat rowsMpmpmNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmpmNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmpmNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
