module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpzpzNotP
public import Minimality.Type24SAT.K24.ChkZpzpzNotP

@[expose] public section

/-!
# Type 24, class zpzpz off `OB1`: core ZpzpzNotP, `CoreUnsat rowsZpzpzNotP` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem ZpzpzNotPe0 : (ZpzpzNotPCnf.drop (0)).take rowsZpzpzNotP0.length = cnfOfRows [rowsZpzpzNotP0] := by decide +kernel
theorem ZpzpzNotPe1 : (ZpzpzNotPCnf.drop (0 + rowsZpzpzNotP0.length)).take rowsZpzpzNotP1.length = cnfOfRows [rowsZpzpzNotP1] := by decide +kernel
theorem ZpzpzNotPe2 : (ZpzpzNotPCnf.drop (0 + rowsZpzpzNotP0.length + rowsZpzpzNotP1.length)).take rowsZpzpzNotP2.length = cnfOfRows [rowsZpzpzNotP2] := by decide +kernel
theorem ZpzpzNotPe3 : (ZpzpzNotPCnf.drop (0 + rowsZpzpzNotP0.length + rowsZpzpzNotP1.length + rowsZpzpzNotP2.length)).take rowsZpzpzNotP3.length = cnfOfRows [rowsZpzpzNotP3] := by decide +kernel
theorem ZpzpzNotPe4 : (ZpzpzNotPCnf.drop (0 + rowsZpzpzNotP0.length + rowsZpzpzNotP1.length + rowsZpzpzNotP2.length + rowsZpzpzNotP3.length)).take rowsZpzpzNotP4.length = cnfOfRows [rowsZpzpzNotP4] := by decide +kernel
theorem ZpzpzNotPeEnd : ZpzpzNotPCnf.drop (0 + rowsZpzpzNotP0.length + rowsZpzpzNotP1.length + rowsZpzpzNotP2.length + rowsZpzpzNotP3.length + rowsZpzpzNotP4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZpzpzNotP, chunk by chunk. -/
theorem cnf_eqZpzpzNotP : cnfOfRows rowsZpzpzNotP = ZpzpzNotPCnf := by
  have h := cnfOfRows_of_chkAt rowsZpzpzNotP ZpzpzNotPCnf 0 ⟨ZpzpzNotPe0, ZpzpzNotPe1, ZpzpzNotPe2, ZpzpzNotPe3, ZpzpzNotPe4, ZpzpzNotPeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core ZpzpzNotP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpzpzNotP : Minimality.H24.SAT.CoreUnsat rowsZpzpzNotP := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.ZpzpzNotPunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqZpzpzNotP] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
