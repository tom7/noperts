module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofZPPP
public import Minimality.Type16SAT.ChkZPPP

@[expose] public section

/-!
# Type 16, J7/J8: core ZPPP, `CoreUnsat rowsZPPP` from the kernel-checked LRAT proof, and `rupert_of_coreZPPP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem ZPPPe0 : (ZPPPCnf.drop (0)).take rowsZPPP0.length = cnfOfRows16 [rowsZPPP0] := by decide +kernel
theorem ZPPPe1 : (ZPPPCnf.drop (0 + rowsZPPP0.length)).take rowsZPPP1.length = cnfOfRows16 [rowsZPPP1] := by decide +kernel
theorem ZPPPe2 : (ZPPPCnf.drop (0 + rowsZPPP0.length + rowsZPPP1.length)).take rowsZPPP2.length = cnfOfRows16 [rowsZPPP2] := by decide +kernel
theorem ZPPPeEnd : ZPPPCnf.drop (0 + rowsZPPP0.length + rowsZPPP1.length + rowsZPPP2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core ZPPP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqZPPP : cnfOfRows16 rowsZPPP = ZPPPCnf := by
  have h := cnfOfRows16_of_chkAt rowsZPPP ZPPPCnf 0 ⟨ZPPPe0, ZPPPe1, ZPPPe2, ZPPPeEnd⟩
  simpa using h

/-- **The numbered clauses of core ZPPP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZPPP : Minimality.H16.SAT.CoreUnsat rowsZPPP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.ZPPPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqZPPP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `0+++` of type 16 is Rupert**: `Core16W 0 1 1 1`. -/
theorem rupert_of_coreZPPP : Minimality.H16.SAT.Core16W 0 1 1 1 := rupert_of_core_dataZPPP coreUnsatZPPP

end Minimality.H16K.SAT
