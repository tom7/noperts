module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmpzNotP
public import Minimality.Type24SAT.K24.ChkPpmpzNotP

@[expose] public section

/-!
# Type 24, class ppmpz off `OB1`: core PpmpzNotP, `CoreUnsat rowsPpmpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PpmpzNotPe0 : (PpmpzNotPCnf.drop (0)).take rowsPpmpzNotP0.length = cnfOfRows [rowsPpmpzNotP0] := by decide +kernel
theorem PpmpzNotPe1 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length)).take rowsPpmpzNotP1.length = cnfOfRows [rowsPpmpzNotP1] := by decide +kernel
theorem PpmpzNotPe2 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length)).take rowsPpmpzNotP2.length = cnfOfRows [rowsPpmpzNotP2] := by decide +kernel
theorem PpmpzNotPe3 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length)).take rowsPpmpzNotP3.length = cnfOfRows [rowsPpmpzNotP3] := by decide +kernel
theorem PpmpzNotPe4 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length + rowsPpmpzNotP3.length)).take rowsPpmpzNotP4.length = cnfOfRows [rowsPpmpzNotP4] := by decide +kernel
theorem PpmpzNotPe5 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length + rowsPpmpzNotP3.length + rowsPpmpzNotP4.length)).take rowsPpmpzNotP5.length = cnfOfRows [rowsPpmpzNotP5] := by decide +kernel
theorem PpmpzNotPe6 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length + rowsPpmpzNotP3.length + rowsPpmpzNotP4.length + rowsPpmpzNotP5.length)).take rowsPpmpzNotP6.length = cnfOfRows [rowsPpmpzNotP6] := by decide +kernel
theorem PpmpzNotPe7 : (PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length + rowsPpmpzNotP3.length + rowsPpmpzNotP4.length + rowsPpmpzNotP5.length + rowsPpmpzNotP6.length)).take rowsPpmpzNotP7.length = cnfOfRows [rowsPpmpzNotP7] := by decide +kernel
theorem PpmpzNotPeEnd : PpmpzNotPCnf.drop (0 + rowsPpmpzNotP0.length + rowsPpmpzNotP1.length + rowsPpmpzNotP2.length + rowsPpmpzNotP3.length + rowsPpmpzNotP4.length + rowsPpmpzNotP5.length + rowsPpmpzNotP6.length + rowsPpmpzNotP7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpmpzNotP, chunk by chunk. -/
theorem cnf_eqPpmpzNotP : cnfOfRows rowsPpmpzNotP = PpmpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmpzNotP PpmpzNotPCnf 0 ⟨PpmpzNotPe0, PpmpzNotPe1, PpmpzNotPe2, PpmpzNotPe3, PpmpzNotPe4, PpmpzNotPe5, PpmpzNotPe6, PpmpzNotPe7, PpmpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpmpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmpzNotP : Minimality.H24.SAT.CoreUnsat rowsPpmpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PpmpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpmpzNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
