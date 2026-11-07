module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29SAT.ProofK3a
public import Minimality.Type29SAT.ChkK3a

@[expose] public section

/-!
# Type 29, class K3a: `CoreUnsat rowsK3a` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT

theorem K3ae0 : (K3aCnf.drop (0)).take rowsK3a0.length = cnfOfRows [rowsK3a0] := by decide +kernel
theorem K3ae1 : (K3aCnf.drop (0 + rowsK3a0.length)).take rowsK3a1.length = cnfOfRows [rowsK3a1] := by decide +kernel
theorem K3ae2 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length)).take rowsK3a2.length = cnfOfRows [rowsK3a2] := by decide +kernel
theorem K3ae3 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length)).take rowsK3a3.length = cnfOfRows [rowsK3a3] := by decide +kernel
theorem K3ae4 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length)).take rowsK3a4.length = cnfOfRows [rowsK3a4] := by decide +kernel
theorem K3ae5 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length)).take rowsK3a5.length = cnfOfRows [rowsK3a5] := by decide +kernel
theorem K3ae6 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length)).take rowsK3a6.length = cnfOfRows [rowsK3a6] := by decide +kernel
theorem K3ae7 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length)).take rowsK3a7.length = cnfOfRows [rowsK3a7] := by decide +kernel
theorem K3ae8 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length + rowsK3a7.length)).take rowsK3a8.length = cnfOfRows [rowsK3a8] := by decide +kernel
theorem K3ae9 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length + rowsK3a7.length + rowsK3a8.length)).take rowsK3a9.length = cnfOfRows [rowsK3a9] := by decide +kernel
theorem K3ae10 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length + rowsK3a7.length + rowsK3a8.length + rowsK3a9.length)).take rowsK3a10.length = cnfOfRows [rowsK3a10] := by decide +kernel
theorem K3ae11 : (K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length + rowsK3a7.length + rowsK3a8.length + rowsK3a9.length + rowsK3a10.length)).take rowsK3a11.length = cnfOfRows [rowsK3a11] := by decide +kernel
theorem K3aeEnd : K3aCnf.drop (0 + rowsK3a0.length + rowsK3a1.length + rowsK3a2.length + rowsK3a3.length + rowsK3a4.length + rowsK3a5.length + rowsK3a6.length + rowsK3a7.length + rowsK3a8.length + rowsK3a9.length + rowsK3a10.length + rowsK3a11.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core K3a, chunk by chunk. -/
theorem cnf_eqK3a : cnfOfRows rowsK3a = K3aCnf := by
  have h := cnfOfRows_of_chkAt rowsK3a K3aCnf 0 ⟨K3ae0, K3ae1, K3ae2, K3ae3, K3ae4, K3ae5, K3ae6, K3ae7, K3ae8, K3ae9, K3ae10, K3ae11, K3aeEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29.SAT

/-- **The numbered clauses of core K3a are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatK3a : CoreUnsat rowsK3a := by
  intro ρ hρ
  have h := K29.K3aunsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqK3a] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29.SAT
