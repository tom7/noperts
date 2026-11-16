module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpzpzNotP
public import Minimality.Type24SAT.K24.ChkPpzpzNotP

@[expose] public section

/-!
# Type 24, class ppzpz off `OB1`: core PpzpzNotP, `CoreUnsat rowsPpzpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem PpzpzNotPe0 : (PpzpzNotPCnf.drop (0)).take rowsPpzpzNotP0.length = cnfOfRows [rowsPpzpzNotP0] := by decide +kernel
theorem PpzpzNotPe1 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length)).take rowsPpzpzNotP1.length = cnfOfRows [rowsPpzpzNotP1] := by decide +kernel
theorem PpzpzNotPe2 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length)).take rowsPpzpzNotP2.length = cnfOfRows [rowsPpzpzNotP2] := by decide +kernel
theorem PpzpzNotPe3 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length)).take rowsPpzpzNotP3.length = cnfOfRows [rowsPpzpzNotP3] := by decide +kernel
theorem PpzpzNotPe4 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length + rowsPpzpzNotP3.length)).take rowsPpzpzNotP4.length = cnfOfRows [rowsPpzpzNotP4] := by decide +kernel
theorem PpzpzNotPe5 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length + rowsPpzpzNotP3.length + rowsPpzpzNotP4.length)).take rowsPpzpzNotP5.length = cnfOfRows [rowsPpzpzNotP5] := by decide +kernel
theorem PpzpzNotPe6 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length + rowsPpzpzNotP3.length + rowsPpzpzNotP4.length + rowsPpzpzNotP5.length)).take rowsPpzpzNotP6.length = cnfOfRows [rowsPpzpzNotP6] := by decide +kernel
theorem PpzpzNotPe7 : (PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length + rowsPpzpzNotP3.length + rowsPpzpzNotP4.length + rowsPpzpzNotP5.length + rowsPpzpzNotP6.length)).take rowsPpzpzNotP7.length = cnfOfRows [rowsPpzpzNotP7] := by decide +kernel
theorem PpzpzNotPeEnd : PpzpzNotPCnf.drop (0 + rowsPpzpzNotP0.length + rowsPpzpzNotP1.length + rowsPpzpzNotP2.length + rowsPpzpzNotP3.length + rowsPpzpzNotP4.length + rowsPpzpzNotP5.length + rowsPpzpzNotP6.length + rowsPpzpzNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpzpzNotP, chunk by chunk. -/
theorem cnf_eqPpzpzNotP : cnfOfRows rowsPpzpzNotP = PpzpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPpzpzNotP PpzpzNotPCnf 0 ⟨PpzpzNotPe0, PpzpzNotPe1, PpzpzNotPe2, PpzpzNotPe3, PpzpzNotPe4, PpzpzNotPe5, PpzpzNotPe6, PpzpzNotPe7, PpzpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpzpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpzpzNotP : Minimality.H24.SAT.CoreUnsat rowsPpzpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.PpzpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpzpzNotP] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
