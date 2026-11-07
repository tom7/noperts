module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29KSAT.ProofK2
public import Minimality.Type29KSAT.ChkK2

@[expose] public section

/-!
# L29T, T11: core K2, `CoreUnsat rowsK2` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT Minimality.H29T.SAT

theorem K2e0 : (K2Cnf.drop (0)).take rowsK20.length = cnfOfRows [rowsK20] := by decide +kernel
theorem K2e1 : (K2Cnf.drop (0 + rowsK20.length)).take rowsK21.length = cnfOfRows [rowsK21] := by decide +kernel
theorem K2e2 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length)).take rowsK22.length = cnfOfRows [rowsK22] := by decide +kernel
theorem K2e3 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length)).take rowsK23.length = cnfOfRows [rowsK23] := by decide +kernel
theorem K2e4 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length)).take rowsK24.length = cnfOfRows [rowsK24] := by decide +kernel
theorem K2e5 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length)).take rowsK25.length = cnfOfRows [rowsK25] := by decide +kernel
theorem K2e6 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length)).take rowsK26.length = cnfOfRows [rowsK26] := by decide +kernel
theorem K2e7 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length)).take rowsK27.length = cnfOfRows [rowsK27] := by decide +kernel
theorem K2e8 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length)).take rowsK28.length = cnfOfRows [rowsK28] := by decide +kernel
theorem K2e9 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length + rowsK28.length)).take rowsK29.length = cnfOfRows [rowsK29] := by decide +kernel
theorem K2e10 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length + rowsK28.length + rowsK29.length)).take rowsK210.length = cnfOfRows [rowsK210] := by decide +kernel
theorem K2e11 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length + rowsK28.length + rowsK29.length + rowsK210.length)).take rowsK211.length = cnfOfRows [rowsK211] := by decide +kernel
theorem K2e12 : (K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length + rowsK28.length + rowsK29.length + rowsK210.length + rowsK211.length)).take rowsK212.length = cnfOfRows [rowsK212] := by decide +kernel
theorem K2eEnd : K2Cnf.drop (0 + rowsK20.length + rowsK21.length + rowsK22.length + rowsK23.length + rowsK24.length + rowsK25.length + rowsK26.length + rowsK27.length + rowsK28.length + rowsK29.length + rowsK210.length + rowsK211.length + rowsK212.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core K2, chunk by chunk. -/
theorem cnf_eqK2 : cnfOfRows rowsK2 = K2Cnf := by
  have h := cnfOfRows_of_chkAt rowsK2 K2Cnf 0 ⟨K2e0, K2e1, K2e2, K2e3, K2e4, K2e5, K2e6, K2e7, K2e8, K2e9, K2e10, K2e11, K2e12, K2eEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

/-- **The numbered clauses of core K2 are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatK2 : CoreUnsat rowsK2 := by
  intro ρ hρ
  have h := K29.K2unsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqK2] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29K.SAT
