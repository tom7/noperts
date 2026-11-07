module

public import Minimality.Type21SAT.LinkBase
public import Minimality.Type21SAT.ProofB
public import Minimality.Type21SAT.TopB

@[expose] public section

/-!
# KERNEL3 link: `Minimality.H21.SAT.CoreUnsatB` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Minimality.H21.SAT.K3

open Minimality.H21.SAT

theorem Be0 : (BCnf.drop (0)).take rowsB0.length = cnfOfRows [rowsB0] := by decide +kernel
theorem Be1 : (BCnf.drop (0 + rowsB0.length)).take rowsB1.length = cnfOfRows [rowsB1] := by decide +kernel
theorem Be2 : (BCnf.drop (0 + rowsB0.length + rowsB1.length)).take rowsB2.length = cnfOfRows [rowsB2] := by decide +kernel
theorem Be3 : (BCnf.drop (0 + rowsB0.length + rowsB1.length + rowsB2.length)).take rowsB3.length = cnfOfRows [rowsB3] := by decide +kernel
theorem Be4 : (BCnf.drop (0 + rowsB0.length + rowsB1.length + rowsB2.length + rowsB3.length)).take rowsB4.length = cnfOfRows [rowsB4] := by decide +kernel
theorem Be5 : (BCnf.drop (0 + rowsB0.length + rowsB1.length + rowsB2.length + rowsB3.length + rowsB4.length)).take rowsB5.length = cnfOfRows [rowsB5] := by decide +kernel
theorem Be6 : (BCnf.drop (0 + rowsB0.length + rowsB1.length + rowsB2.length + rowsB3.length + rowsB4.length + rowsB5.length)).take rowsB6.length = cnfOfRows [rowsB6] := by decide +kernel
theorem BeEnd : BCnf.drop (0 + rowsB0.length + rowsB1.length + rowsB2.length + rowsB3.length + rowsB4.length + rowsB5.length + rowsB6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core B, chunk by chunk. -/
theorem cnf_eqB : cnfOfRows rowsB = BCnf := by
  have h := cnfOfRows_of_chkAt rowsB BCnf 0 ⟨Be0, Be1, Be2, Be3, Be4, Be5, Be6, BeEnd⟩
  simpa using h

end Minimality.H21.SAT.K3

namespace Minimality.H21.SAT

/-- **Core B is unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatB : CoreUnsatB := by
  intro ρ hρ
  have h := K3.Bunsat ρ
  apply h
  intro c hc
  rw [← K3.cnf_eqB] at hc
  simp only [K3.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩


end Minimality.H21.SAT
