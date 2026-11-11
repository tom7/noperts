module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29KSAT.ProofK1aL
public import Minimality.Type29KSAT.ChkK1aL

@[expose] public section

/-!
# Type 29, K1a on the corner stratum `Z`: core K1aL, `CoreUnsat rowsK1aL` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem K1aLe0 : (K1aLCnf.drop (0)).take rowsK1aL0.length = cnfOfRows [rowsK1aL0] := by decide +kernel
theorem K1aLe1 : (K1aLCnf.drop (0 + rowsK1aL0.length)).take rowsK1aL1.length = cnfOfRows [rowsK1aL1] := by decide +kernel
theorem K1aLe2 : (K1aLCnf.drop (0 + rowsK1aL0.length + rowsK1aL1.length)).take rowsK1aL2.length = cnfOfRows [rowsK1aL2] := by decide +kernel
theorem K1aLe3 : (K1aLCnf.drop (0 + rowsK1aL0.length + rowsK1aL1.length + rowsK1aL2.length)).take rowsK1aL3.length = cnfOfRows [rowsK1aL3] := by decide +kernel
theorem K1aLe4 : (K1aLCnf.drop (0 + rowsK1aL0.length + rowsK1aL1.length + rowsK1aL2.length + rowsK1aL3.length)).take rowsK1aL4.length = cnfOfRows [rowsK1aL4] := by decide +kernel
theorem K1aLeEnd : K1aLCnf.drop (0 + rowsK1aL0.length + rowsK1aL1.length + rowsK1aL2.length + rowsK1aL3.length + rowsK1aL4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core K1aL, chunk by chunk. -/
theorem cnf_eqK1aL : cnfOfRows rowsK1aL = K1aLCnf := by
  have h := cnfOfRows_of_chkAt rowsK1aL K1aLCnf 0 ⟨K1aLe0, K1aLe1, K1aLe2, K1aLe3, K1aLe4, K1aLeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- **The numbered clauses of core K1aL are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatK1aL : CoreUnsat rowsK1aL := by
  intro ρ hρ
  have h := K29.K1aLunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqK1aL] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29K.SAT
