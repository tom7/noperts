module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmpzNotP
public import Minimality.Type24SAT.K24.ChkZpmpzNotP

@[expose] public section

/-!
# Type 24, class zpmpz off `OB1`: core ZpmpzNotP, `CoreUnsat rowsZpmpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem ZpmpzNotPe0 : (ZpmpzNotPCnf.drop (0)).take rowsZpmpzNotP0.length = cnfOfRows [rowsZpmpzNotP0] := by decide +kernel
theorem ZpmpzNotPe1 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length)).take rowsZpmpzNotP1.length = cnfOfRows [rowsZpmpzNotP1] := by decide +kernel
theorem ZpmpzNotPe2 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length)).take rowsZpmpzNotP2.length = cnfOfRows [rowsZpmpzNotP2] := by decide +kernel
theorem ZpmpzNotPe3 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length)).take rowsZpmpzNotP3.length = cnfOfRows [rowsZpmpzNotP3] := by decide +kernel
theorem ZpmpzNotPe4 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length)).take rowsZpmpzNotP4.length = cnfOfRows [rowsZpmpzNotP4] := by decide +kernel
theorem ZpmpzNotPe5 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length + rowsZpmpzNotP4.length)).take rowsZpmpzNotP5.length = cnfOfRows [rowsZpmpzNotP5] := by decide +kernel
theorem ZpmpzNotPe6 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length + rowsZpmpzNotP4.length + rowsZpmpzNotP5.length)).take rowsZpmpzNotP6.length = cnfOfRows [rowsZpmpzNotP6] := by decide +kernel
theorem ZpmpzNotPe7 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length + rowsZpmpzNotP4.length + rowsZpmpzNotP5.length + rowsZpmpzNotP6.length)).take rowsZpmpzNotP7.length = cnfOfRows [rowsZpmpzNotP7] := by decide +kernel
theorem ZpmpzNotPe8 : (ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length + rowsZpmpzNotP4.length + rowsZpmpzNotP5.length + rowsZpmpzNotP6.length + rowsZpmpzNotP7.length)).take rowsZpmpzNotP8.length = cnfOfRows [rowsZpmpzNotP8] := by decide +kernel
theorem ZpmpzNotPeEnd : ZpmpzNotPCnf.drop (0 + rowsZpmpzNotP0.length + rowsZpmpzNotP1.length + rowsZpmpzNotP2.length + rowsZpmpzNotP3.length + rowsZpmpzNotP4.length + rowsZpmpzNotP5.length + rowsZpmpzNotP6.length + rowsZpmpzNotP7.length + rowsZpmpzNotP8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpmpzNotP, chunk by chunk. -/
theorem cnf_eqZpmpzNotP : cnfOfRows rowsZpmpzNotP = ZpmpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmpzNotP ZpmpzNotPCnf 0 ⟨ZpmpzNotPe0, ZpmpzNotPe1, ZpmpzNotPe2, ZpmpzNotPe3, ZpmpzNotPe4, ZpmpzNotPe5, ZpmpzNotPe6, ZpmpzNotPe7, ZpmpzNotPe8, ZpmpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpmpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmpzNotP : Minimality.H24.SAT.CoreUnsat rowsZpmpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.ZpmpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmpzNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
