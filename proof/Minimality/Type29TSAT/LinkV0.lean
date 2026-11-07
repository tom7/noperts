module

public import Minimality.Type29SAT.LinkBase
public import Minimality.Type29TSAT.ProofV0
public import Minimality.Type29TSAT.ChkV0

@[expose] public section

/-!
# Type 29, class V0: `CoreUnsat rowsV0` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Minimality.H29.SAT.K29

open Minimality.H29.SAT

theorem V0e0 : (V0Cnf.drop (0)).take rowsV00.length = cnfOfRows [rowsV00] := by decide +kernel
theorem V0e1 : (V0Cnf.drop (0 + rowsV00.length)).take rowsV01.length = cnfOfRows [rowsV01] := by decide +kernel
theorem V0e2 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length)).take rowsV02.length = cnfOfRows [rowsV02] := by decide +kernel
theorem V0e3 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length)).take rowsV03.length = cnfOfRows [rowsV03] := by decide +kernel
theorem V0e4 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length)).take rowsV04.length = cnfOfRows [rowsV04] := by decide +kernel
theorem V0e5 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length)).take rowsV05.length = cnfOfRows [rowsV05] := by decide +kernel
theorem V0e6 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length + rowsV05.length)).take rowsV06.length = cnfOfRows [rowsV06] := by decide +kernel
theorem V0e7 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length + rowsV05.length + rowsV06.length)).take rowsV07.length = cnfOfRows [rowsV07] := by decide +kernel
theorem V0e8 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length + rowsV05.length + rowsV06.length + rowsV07.length)).take rowsV08.length = cnfOfRows [rowsV08] := by decide +kernel
theorem V0e9 : (V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length + rowsV05.length + rowsV06.length + rowsV07.length + rowsV08.length)).take rowsV09.length = cnfOfRows [rowsV09] := by decide +kernel
theorem V0eEnd : V0Cnf.drop (0 + rowsV00.length + rowsV01.length + rowsV02.length + rowsV03.length + rowsV04.length + rowsV05.length + rowsV06.length + rowsV07.length + rowsV08.length + rowsV09.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core V0, chunk by chunk. -/
theorem cnf_eqV0 : cnfOfRows rowsV0 = V0Cnf := by
  have h := cnfOfRows_of_chkAt rowsV0 V0Cnf 0 ⟨V0e0, V0e1, V0e2, V0e3, V0e4, V0e5, V0e6, V0e7, V0e8, V0e9, V0eEnd⟩
  simpa using h

end Minimality.H29.SAT.K29

namespace Minimality.H29.SAT

/-- **The numbered clauses of core V0 are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatV0 : CoreUnsat rowsV0 := by
  intro ρ hρ
  have h := K29.V0unsat ρ
  apply h
  intro c hc
  rw [← K29.cnf_eqV0] at hc
  simp only [K29.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H29.SAT
