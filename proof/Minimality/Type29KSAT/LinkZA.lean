module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29KSAT.ProofZA
public import Minimality.Type29KSAT.ChkZA

@[expose] public section

/-!
# Type 29, K2a on `Z1`, case A: core ZA, `CoreUnsat rowsZA` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem ZAe0 : (ZACnf.drop (0)).take rowsZA0.length = cnfOfRows [rowsZA0] := by decide +kernel
theorem ZAe1 : (ZACnf.drop (0 + rowsZA0.length)).take rowsZA1.length = cnfOfRows [rowsZA1] := by decide +kernel
theorem ZAe2 : (ZACnf.drop (0 + rowsZA0.length + rowsZA1.length)).take rowsZA2.length = cnfOfRows [rowsZA2] := by decide +kernel
theorem ZAeEnd : ZACnf.drop (0 + rowsZA0.length + rowsZA1.length + rowsZA2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZA, chunk by chunk. -/
theorem cnf_eqZA : cnfOfRows rowsZA = ZACnf := by
  have h := cnfOfRows_of_chkAt rowsZA ZACnf 0 ⟨ZAe0, ZAe1, ZAe2, ZAeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- **The numbered clauses of core ZA are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZA : CoreUnsat rowsZA := by
  intro ρ hρ
  have h := K29.ZAunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqZA] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29K.SAT
