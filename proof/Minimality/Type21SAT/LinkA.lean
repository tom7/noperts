module

public import Minimality.Type21SAT.LinkBase
public import Minimality.Type21SAT.ProofA
public import Minimality.Type21SAT.Top

@[expose] public section

/-!
# KERNEL3 link: `Minimality.H21.SAT.CoreUnsatA` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Minimality.H21.SAT.K3

open Minimality.H21.SAT

theorem Ae0 : (ACnf.drop (0)).take rowsA0.length = cnfOfRows [rowsA0] := by decide +kernel
theorem Ae1 : (ACnf.drop (0 + rowsA0.length)).take rowsA1.length = cnfOfRows [rowsA1] := by decide +kernel
theorem Ae2 : (ACnf.drop (0 + rowsA0.length + rowsA1.length)).take rowsA2.length = cnfOfRows [rowsA2] := by decide +kernel
theorem Ae3 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length)).take rowsA3.length = cnfOfRows [rowsA3] := by decide +kernel
theorem Ae4 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length)).take rowsA4.length = cnfOfRows [rowsA4] := by decide +kernel
theorem Ae5 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length)).take rowsA5.length = cnfOfRows [rowsA5] := by decide +kernel
theorem Ae6 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length)).take rowsA6.length = cnfOfRows [rowsA6] := by decide +kernel
theorem Ae7 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length)).take rowsA7.length = cnfOfRows [rowsA7] := by decide +kernel
theorem Ae8 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length)).take rowsA8.length = cnfOfRows [rowsA8] := by decide +kernel
theorem Ae9 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length)).take rowsA9.length = cnfOfRows [rowsA9] := by decide +kernel
theorem Ae10 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length + rowsA9.length)).take rowsA10.length = cnfOfRows [rowsA10] := by decide +kernel
theorem Ae11 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length + rowsA9.length + rowsA10.length)).take rowsA11.length = cnfOfRows [rowsA11] := by decide +kernel
theorem Ae12 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length + rowsA9.length + rowsA10.length + rowsA11.length)).take rowsA12.length = cnfOfRows [rowsA12] := by decide +kernel
theorem Ae13 : (ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length + rowsA9.length + rowsA10.length + rowsA11.length + rowsA12.length)).take rowsA13.length = cnfOfRows [rowsA13] := by decide +kernel
theorem AeEnd : ACnf.drop (0 + rowsA0.length + rowsA1.length + rowsA2.length + rowsA3.length + rowsA4.length + rowsA5.length + rowsA6.length + rowsA7.length + rowsA8.length + rowsA9.length + rowsA10.length + rowsA11.length + rowsA12.length + rowsA13.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core A, chunk by chunk. -/
theorem cnf_eqA : cnfOfRows rowsA = ACnf := by
  have h := cnfOfRows_of_chkAt rowsA ACnf 0 ⟨Ae0, Ae1, Ae2, Ae3, Ae4, Ae5, Ae6, Ae7, Ae8, Ae9, Ae10, Ae11, Ae12, Ae13, AeEnd⟩
  simpa using h

end Minimality.H21.SAT.K3

namespace Minimality.H21.SAT

/-- **Core B is unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatA : CoreUnsatA := by
  intro ρ hρ
  have h := K3.Aunsat ρ
  apply h
  intro c hc
  rw [← K3.cnf_eqA] at hc
  simp only [K3.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩


end Minimality.H21.SAT
