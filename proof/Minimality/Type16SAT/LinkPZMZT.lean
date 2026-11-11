module

public import Minimality.Type16SAT.LinkBase16
public import Minimality.Type16SAT.ProofPZMZT
public import Minimality.Type16SAT.ChkPZMZT

@[expose] public section

/-!
# Type 16, J7/J8: core PZMZT, `CoreUnsat rowsPZMZT` from the kernel-checked LRAT proof, and `rupert_of_corePZMZT`
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT

open Minimality.H29.SAT.K29

theorem PZMZTe0 : (PZMZTCnf.drop (0)).take rowsPZMZT0.length = cnfOfRows16 [rowsPZMZT0] := by decide +kernel
theorem PZMZTeEnd : PZMZTCnf.drop (0 + rowsPZMZT0.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PZMZT (type 16 decoder), chunk by chunk. -/
theorem cnf_eqPZMZT : cnfOfRows16 rowsPZMZT = PZMZTCnf := by
  have h := cnfOfRows16_of_chkAt rowsPZMZT PZMZTCnf 0 ⟨PZMZTe0, PZMZTeEnd⟩
  simpa using h

/-- **The numbered clauses of core PZMZT are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPZMZT : Minimality.H16.SAT.CoreUnsat rowsPZMZT := by
  intro ρ hρ
  have h := Minimality.H29.SAT.K29.PZMZTunsat ρ
  apply h
  intro c hc
  rw [← cnf_eqPZMZT] at hc
  simp only [cnfOfRows16, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  exact hρ ch hch n hn

/-- **Class `+0-0` of type 16 is Rupert**: `Core16ZTW 1 0 (-1) 0`. -/
theorem rupert_of_corePZMZT : Minimality.H16.SAT.Core16ZTW 1 0 (-1) 0 := rupert_of_core_dataPZMZT coreUnsatPZMZT

end Minimality.H16K.SAT
