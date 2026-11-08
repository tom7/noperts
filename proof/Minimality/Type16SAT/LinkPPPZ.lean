module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPPPZ
public import Minimality.Type16SAT.ChkPPPZ

@[expose] public section

/-!
# Type 16, J7/J8: core PPPZ, `CoreUnsat rowsPPPZ` from the kernel-checked LRAT proof, and `rupert_of_corePPPZ`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PPPZe0 : (PPPZCnf.drop (0)).take rowsPPPZ0.length = cnfOfRows16 [rowsPPPZ0] := by decide +kernel
theorem PPPZe1 : (PPPZCnf.drop (0 + rowsPPPZ0.length)).take rowsPPPZ1.length = cnfOfRows16 [rowsPPPZ1] := by decide +kernel
theorem PPPZe2 : (PPPZCnf.drop (0 + rowsPPPZ0.length + rowsPPPZ1.length)).take rowsPPPZ2.length = cnfOfRows16 [rowsPPPZ2] := by decide +kernel
theorem PPPZeEnd : PPPZCnf.drop (0 + rowsPPPZ0.length + rowsPPPZ1.length + rowsPPPZ2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PPPZ (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPPPZ : cnfOfRows16 rowsPPPZ = PPPZCnf := by
  have h := cnfOfRows16_of_chkAt rowsPPPZ PPPZCnf 0 ⟨PPPZe0, PPPZe1, PPPZe2, PPPZeEnd⟩
  simpa using h

/-- **The numbered clauses of core PPPZ are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPPPZ : Minimality.H16.SAT.CoreUnsat rowsPPPZ := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PPPZunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPPPZ] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+++0` of type 16 is Rupert**: `Core16W 1 1 1 0`. -/
theorem rupert_of_corePPPZ : Minimality.H16.SAT.Core16W 1 1 1 0 := rupert_of_core_dataPPPZ coreUnsatPPPZ

end Minimality.H16K.SAT
