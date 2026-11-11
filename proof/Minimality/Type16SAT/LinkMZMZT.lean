module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofMZMZT
public import Minimality.Type16SAT.ChkMZMZT

@[expose] public section

/-!
# Type 16, J7/J8: core MZMZT, `CoreUnsat rowsMZMZT` from the kernel-checked LRAT proof, and `rupert_of_coreMZMZT`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem MZMZTe0 : (MZMZTCnf.drop (0)).take rowsMZMZT0.length = cnfOfRows16 [rowsMZMZT0] := by decide +kernel
theorem MZMZTe1 : (MZMZTCnf.drop (0 + rowsMZMZT0.length)).take rowsMZMZT1.length = cnfOfRows16 [rowsMZMZT1] := by decide +kernel
theorem MZMZTeEnd : MZMZTCnf.drop (0 + rowsMZMZT0.length + rowsMZMZT1.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MZMZT (type 16 decoder), chunk by chunk. -/
theorem cnf_eqMZMZT : cnfOfRows16 rowsMZMZT = MZMZTCnf := by
  have h := cnfOfRows16_of_chkAt rowsMZMZT MZMZTCnf 0 ⟨MZMZTe0, MZMZTe1, MZMZTeEnd⟩
  simpa using h

/-- **The numbered clauses of core MZMZT are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMZMZT : Minimality.H16.SAT.CoreUnsat rowsMZMZT := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.MZMZTunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqMZMZT] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `-0-0` of type 16 is Rupert**: `Core16ZTW (-1) 0 (-1) 0`. -/
theorem rupert_of_coreMZMZT : Minimality.H16.SAT.Core16ZTW (-1) 0 (-1) 0 := rupert_of_core_dataMZMZT coreUnsatMZMZT

end Minimality.H16K.SAT
