module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpzNotP
public import Minimality.Type24SAT.K24.ChkMpmpzNotP

@[expose] public section

/-!
# Type 24, class mpmpz off `OB1`: core MpmpzNotP, `CoreUnsat rowsMpmpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmpzNotPe0 : (MpmpzNotPCnf.drop (0)).take rowsMpmpzNotP0.length = cnfOfRows [rowsMpmpzNotP0] := by decide +kernel
theorem MpmpzNotPe1 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length)).take rowsMpmpzNotP1.length = cnfOfRows [rowsMpmpzNotP1] := by decide +kernel
theorem MpmpzNotPe2 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length)).take rowsMpmpzNotP2.length = cnfOfRows [rowsMpmpzNotP2] := by decide +kernel
theorem MpmpzNotPe3 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length)).take rowsMpmpzNotP3.length = cnfOfRows [rowsMpmpzNotP3] := by decide +kernel
theorem MpmpzNotPe4 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length + rowsMpmpzNotP3.length)).take rowsMpmpzNotP4.length = cnfOfRows [rowsMpmpzNotP4] := by decide +kernel
theorem MpmpzNotPe5 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length + rowsMpmpzNotP3.length + rowsMpmpzNotP4.length)).take rowsMpmpzNotP5.length = cnfOfRows [rowsMpmpzNotP5] := by decide +kernel
theorem MpmpzNotPe6 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length + rowsMpmpzNotP3.length + rowsMpmpzNotP4.length + rowsMpmpzNotP5.length)).take rowsMpmpzNotP6.length = cnfOfRows [rowsMpmpzNotP6] := by decide +kernel
theorem MpmpzNotPe7 : (MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length + rowsMpmpzNotP3.length + rowsMpmpzNotP4.length + rowsMpmpzNotP5.length + rowsMpmpzNotP6.length)).take rowsMpmpzNotP7.length = cnfOfRows [rowsMpmpzNotP7] := by decide +kernel
theorem MpmpzNotPeEnd : MpmpzNotPCnf.drop (0 + rowsMpmpzNotP0.length + rowsMpmpzNotP1.length + rowsMpmpzNotP2.length + rowsMpmpzNotP3.length + rowsMpmpzNotP4.length + rowsMpmpzNotP5.length + rowsMpmpzNotP6.length + rowsMpmpzNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmpzNotP, chunk by chunk. -/
theorem cnf_eqMpmpzNotP : cnfOfRows rowsMpmpzNotP = MpmpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpzNotP MpmpzNotPCnf 0 ⟨MpmpzNotPe0, MpmpzNotPe1, MpmpzNotPe2, MpmpzNotPe3, MpmpzNotPe4, MpmpzNotPe5, MpmpzNotPe6, MpmpzNotPe7, MpmpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpzNotP : Minimality.H24.SAT.CoreUnsat rowsMpmpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmpzNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
