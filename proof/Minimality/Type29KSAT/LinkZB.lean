module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29KSAT.ProofZB
public import Minimality.Type29KSAT.ChkZB

@[expose] public section

/-!
# Type 29, K2a on `Z1`, case B residue: core ZB, `CoreUnsat rowsZB` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem ZBe0 : (ZBCnf.drop (0)).take rowsZB0.length = cnfOfRows [rowsZB0] := by decide +kernel
theorem ZBe1 : (ZBCnf.drop (0 + rowsZB0.length)).take rowsZB1.length = cnfOfRows [rowsZB1] := by decide +kernel
theorem ZBeEnd : ZBCnf.drop (0 + rowsZB0.length + rowsZB1.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZB, chunk by chunk. -/
theorem cnf_eqZB : cnfOfRows rowsZB = ZBCnf := by
  have h := cnfOfRows_of_chkAt rowsZB ZBCnf 0 ⟨ZBe0, ZBe1, ZBeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- **The numbered clauses of core ZB are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZB : CoreUnsat rowsZB := by
  intro ρ hρ
  have h := K29.ZBunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqZB] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29K.SAT
