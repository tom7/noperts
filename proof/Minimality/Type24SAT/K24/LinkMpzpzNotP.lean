module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpzpzNotP
public import Minimality.Type24SAT.K24.ChkMpzpzNotP

@[expose] public section

/-!
# Type 24, class mpzpz off `OB1`: core MpzpzNotP, `CoreUnsat rowsMpzpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpzpzNotPe0 : (MpzpzNotPCnf.drop (0)).take rowsMpzpzNotP0.length = cnfOfRows [rowsMpzpzNotP0] := by decide +kernel
theorem MpzpzNotPe1 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length)).take rowsMpzpzNotP1.length = cnfOfRows [rowsMpzpzNotP1] := by decide +kernel
theorem MpzpzNotPe2 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length)).take rowsMpzpzNotP2.length = cnfOfRows [rowsMpzpzNotP2] := by decide +kernel
theorem MpzpzNotPe3 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length + rowsMpzpzNotP2.length)).take rowsMpzpzNotP3.length = cnfOfRows [rowsMpzpzNotP3] := by decide +kernel
theorem MpzpzNotPe4 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length + rowsMpzpzNotP2.length + rowsMpzpzNotP3.length)).take rowsMpzpzNotP4.length = cnfOfRows [rowsMpzpzNotP4] := by decide +kernel
theorem MpzpzNotPe5 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length + rowsMpzpzNotP2.length + rowsMpzpzNotP3.length + rowsMpzpzNotP4.length)).take rowsMpzpzNotP5.length = cnfOfRows [rowsMpzpzNotP5] := by decide +kernel
theorem MpzpzNotPe6 : (MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length + rowsMpzpzNotP2.length + rowsMpzpzNotP3.length + rowsMpzpzNotP4.length + rowsMpzpzNotP5.length)).take rowsMpzpzNotP6.length = cnfOfRows [rowsMpzpzNotP6] := by decide +kernel
theorem MpzpzNotPeEnd : MpzpzNotPCnf.drop (0 + rowsMpzpzNotP0.length + rowsMpzpzNotP1.length + rowsMpzpzNotP2.length + rowsMpzpzNotP3.length + rowsMpzpzNotP4.length + rowsMpzpzNotP5.length + rowsMpzpzNotP6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpzpzNotP, chunk by chunk. -/
theorem cnf_eqMpzpzNotP : cnfOfRows rowsMpzpzNotP = MpzpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsMpzpzNotP MpzpzNotPCnf 0 ⟨MpzpzNotPe0, MpzpzNotPe1, MpzpzNotPe2, MpzpzNotPe3, MpzpzNotPe4, MpzpzNotPe5, MpzpzNotPe6, MpzpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpzpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpzpzNotP : Minimality.H24.SAT.CoreUnsat rowsMpzpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpzpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpzpzNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
