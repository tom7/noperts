module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpppzNotP
public import Minimality.Type24SAT.K24.ChkPpppzNotP

@[expose] public section

/-!
# Type 24, class ppppz off `OB1`: core PpppzNotP, `CoreUnsat rowsPpppzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PpppzNotPe0 : (PpppzNotPCnf.drop (0)).take rowsPpppzNotP0.length = cnfOfRows [rowsPpppzNotP0] := by decide +kernel
theorem PpppzNotPe1 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length)).take rowsPpppzNotP1.length = cnfOfRows [rowsPpppzNotP1] := by decide +kernel
theorem PpppzNotPe2 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length)).take rowsPpppzNotP2.length = cnfOfRows [rowsPpppzNotP2] := by decide +kernel
theorem PpppzNotPe3 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length)).take rowsPpppzNotP3.length = cnfOfRows [rowsPpppzNotP3] := by decide +kernel
theorem PpppzNotPe4 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length + rowsPpppzNotP3.length)).take rowsPpppzNotP4.length = cnfOfRows [rowsPpppzNotP4] := by decide +kernel
theorem PpppzNotPe5 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length + rowsPpppzNotP3.length + rowsPpppzNotP4.length)).take rowsPpppzNotP5.length = cnfOfRows [rowsPpppzNotP5] := by decide +kernel
theorem PpppzNotPe6 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length + rowsPpppzNotP3.length + rowsPpppzNotP4.length + rowsPpppzNotP5.length)).take rowsPpppzNotP6.length = cnfOfRows [rowsPpppzNotP6] := by decide +kernel
theorem PpppzNotPe7 : (PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length + rowsPpppzNotP3.length + rowsPpppzNotP4.length + rowsPpppzNotP5.length + rowsPpppzNotP6.length)).take rowsPpppzNotP7.length = cnfOfRows [rowsPpppzNotP7] := by decide +kernel
theorem PpppzNotPeEnd : PpppzNotPCnf.drop (0 + rowsPpppzNotP0.length + rowsPpppzNotP1.length + rowsPpppzNotP2.length + rowsPpppzNotP3.length + rowsPpppzNotP4.length + rowsPpppzNotP5.length + rowsPpppzNotP6.length + rowsPpppzNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpppzNotP, chunk by chunk. -/
theorem cnf_eqPpppzNotP : cnfOfRows rowsPpppzNotP = PpppzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPpppzNotP PpppzNotPCnf 0 ⟨PpppzNotPe0, PpppzNotPe1, PpppzNotPe2, PpppzNotPe3, PpppzNotPe4, PpppzNotPe5, PpppzNotPe6, PpppzNotPe7, PpppzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpppzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpppzNotP : Minimality.H24.SAT.CoreUnsat rowsPpppzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PpppzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpppzNotP] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
