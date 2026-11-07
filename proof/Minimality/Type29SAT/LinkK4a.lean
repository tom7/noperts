module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29SAT.ProofK4a
public import Minimality.Type29SAT.ChkK4a

@[expose] public section

/-!
# Type 29, class K4a: `CoreUnsat rowsK4a` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT

theorem K4ae0 : (K4aCnf.drop (0)).take rowsK4a0.length = cnfOfRows [rowsK4a0] := by decide +kernel
theorem K4ae1 : (K4aCnf.drop (0 + rowsK4a0.length)).take rowsK4a1.length = cnfOfRows [rowsK4a1] := by decide +kernel
theorem K4ae2 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length)).take rowsK4a2.length = cnfOfRows [rowsK4a2] := by decide +kernel
theorem K4ae3 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length)).take rowsK4a3.length = cnfOfRows [rowsK4a3] := by decide +kernel
theorem K4ae4 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length)).take rowsK4a4.length = cnfOfRows [rowsK4a4] := by decide +kernel
theorem K4ae5 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length + rowsK4a4.length)).take rowsK4a5.length = cnfOfRows [rowsK4a5] := by decide +kernel
theorem K4ae6 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length + rowsK4a4.length + rowsK4a5.length)).take rowsK4a6.length = cnfOfRows [rowsK4a6] := by decide +kernel
theorem K4ae7 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length + rowsK4a4.length + rowsK4a5.length + rowsK4a6.length)).take rowsK4a7.length = cnfOfRows [rowsK4a7] := by decide +kernel
theorem K4ae8 : (K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length + rowsK4a4.length + rowsK4a5.length + rowsK4a6.length + rowsK4a7.length)).take rowsK4a8.length = cnfOfRows [rowsK4a8] := by decide +kernel
theorem K4aeEnd : K4aCnf.drop (0 + rowsK4a0.length + rowsK4a1.length + rowsK4a2.length + rowsK4a3.length + rowsK4a4.length + rowsK4a5.length + rowsK4a6.length + rowsK4a7.length + rowsK4a8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core K4a, chunk by chunk. -/
theorem cnf_eqK4a : cnfOfRows rowsK4a = K4aCnf := by
  have h := cnfOfRows_of_chkAt rowsK4a K4aCnf 0 ⟨K4ae0, K4ae1, K4ae2, K4ae3, K4ae4, K4ae5, K4ae6, K4ae7, K4ae8, K4aeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29.SAT

/-- **The numbered clauses of core K4a are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatK4a : CoreUnsat rowsK4a := by
  intro ρ hρ
  have h := K29.K4aunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqK4a] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29.SAT
