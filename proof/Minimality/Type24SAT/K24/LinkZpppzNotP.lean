module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpppzNotP
public import Minimality.Type24SAT.K24.ChkZpppzNotP

@[expose] public section

/-!
# Type 24, class zpppz off `OB1`: core ZpppzNotP, `CoreUnsat rowsZpppzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem ZpppzNotPe0 : (ZpppzNotPCnf.drop (0)).take rowsZpppzNotP0.length = cnfOfRows [rowsZpppzNotP0] := by decide +kernel
theorem ZpppzNotPe1 : (ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length)).take rowsZpppzNotP1.length = cnfOfRows [rowsZpppzNotP1] := by decide +kernel
theorem ZpppzNotPe2 : (ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length + rowsZpppzNotP1.length)).take rowsZpppzNotP2.length = cnfOfRows [rowsZpppzNotP2] := by decide +kernel
theorem ZpppzNotPe3 : (ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length + rowsZpppzNotP1.length + rowsZpppzNotP2.length)).take rowsZpppzNotP3.length = cnfOfRows [rowsZpppzNotP3] := by decide +kernel
theorem ZpppzNotPe4 : (ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length + rowsZpppzNotP1.length + rowsZpppzNotP2.length + rowsZpppzNotP3.length)).take rowsZpppzNotP4.length = cnfOfRows [rowsZpppzNotP4] := by decide +kernel
theorem ZpppzNotPe5 : (ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length + rowsZpppzNotP1.length + rowsZpppzNotP2.length + rowsZpppzNotP3.length + rowsZpppzNotP4.length)).take rowsZpppzNotP5.length = cnfOfRows [rowsZpppzNotP5] := by decide +kernel
theorem ZpppzNotPeEnd : ZpppzNotPCnf.drop (0 + rowsZpppzNotP0.length + rowsZpppzNotP1.length + rowsZpppzNotP2.length + rowsZpppzNotP3.length + rowsZpppzNotP4.length + rowsZpppzNotP5.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpppzNotP, chunk by chunk. -/
theorem cnf_eqZpppzNotP : cnfOfRows rowsZpppzNotP = ZpppzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsZpppzNotP ZpppzNotPCnf 0 ⟨ZpppzNotPe0, ZpppzNotPe1, ZpppzNotPe2, ZpppzNotPe3, ZpppzNotPe4, ZpppzNotPe5, ZpppzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpppzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpppzNotP : Minimality.H24.SAT.CoreUnsat rowsZpppzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.ZpppzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpppzNotP] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
