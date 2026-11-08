module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZPP
public import Minimality.Type16SAT.ChkPZPP

@[expose] public section

/-!
# Type 16, J7/J8: core PZPP, `CoreUnsat rowsPZPP` from the kernel-checked LRAT proof, and `rupert_of_corePZPP`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZPPe0 : (PZPPCnf.drop (0)).take rowsPZPP0.length = cnfOfRows16 [rowsPZPP0] := by decide +kernel
theorem PZPPe1 : (PZPPCnf.drop (0 + rowsPZPP0.length)).take rowsPZPP1.length = cnfOfRows16 [rowsPZPP1] := by decide +kernel
theorem PZPPe2 : (PZPPCnf.drop (0 + rowsPZPP0.length + rowsPZPP1.length)).take rowsPZPP2.length = cnfOfRows16 [rowsPZPP2] := by decide +kernel
theorem PZPPeEnd : PZPPCnf.drop (0 + rowsPZPP0.length + rowsPZPP1.length + rowsPZPP2.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZPP (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZPP : cnfOfRows16 rowsPZPP = PZPPCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZPP PZPPCnf 0 ⟨PZPPe0, PZPPe1, PZPPe2, PZPPeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZPP are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZPP : Minimality.H16.SAT.CoreUnsat rowsPZPP := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZPPunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZPP] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0++` of type 16 is Rupert**: `Core16W 1 0 1 1`. -/
theorem rupert_of_corePZPP : Minimality.H16.SAT.Core16W 1 0 1 1 := rupert_of_core_dataPZPP coreUnsatPZPP

end Minimality.H16K.SAT
