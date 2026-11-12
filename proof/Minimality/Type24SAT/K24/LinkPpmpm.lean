module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmpm
public import Minimality.Type24SAT.K24.ChkPpmpm

@[expose] public section

/-!
# Type 24, class ppmpm off `OB1`: core Ppmpm, `CoreUnsat rowsPpmpm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Ppmpme0 : (PpmpmCnf.drop (0)).take rowsPpmpm0.length = cnfOfRows [rowsPpmpm0] := by decide +kernel
theorem Ppmpme1 : (PpmpmCnf.drop (0 + rowsPpmpm0.length)).take rowsPpmpm1.length = cnfOfRows [rowsPpmpm1] := by decide +kernel
theorem Ppmpme2 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length)).take rowsPpmpm2.length = cnfOfRows [rowsPpmpm2] := by decide +kernel
theorem Ppmpme3 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length)).take rowsPpmpm3.length = cnfOfRows [rowsPpmpm3] := by decide +kernel
theorem Ppmpme4 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length + rowsPpmpm3.length)).take rowsPpmpm4.length = cnfOfRows [rowsPpmpm4] := by decide +kernel
theorem Ppmpme5 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length + rowsPpmpm3.length + rowsPpmpm4.length)).take rowsPpmpm5.length = cnfOfRows [rowsPpmpm5] := by decide +kernel
theorem Ppmpme6 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length + rowsPpmpm3.length + rowsPpmpm4.length + rowsPpmpm5.length)).take rowsPpmpm6.length = cnfOfRows [rowsPpmpm6] := by decide +kernel
theorem Ppmpme7 : (PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length + rowsPpmpm3.length + rowsPpmpm4.length + rowsPpmpm5.length + rowsPpmpm6.length)).take rowsPpmpm7.length = cnfOfRows [rowsPpmpm7] := by decide +kernel
theorem PpmpmeEnd : PpmpmCnf.drop (0 + rowsPpmpm0.length + rowsPpmpm1.length + rowsPpmpm2.length + rowsPpmpm3.length + rowsPpmpm4.length + rowsPpmpm5.length + rowsPpmpm6.length + rowsPpmpm7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppmpm, chunk by chunk. -/
theorem cnf_eqPpmpm : cnfOfRows rowsPpmpm = PpmpmCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmpm PpmpmCnf 0 ⟨Ppmpme0, Ppmpme1, Ppmpme2, Ppmpme3, Ppmpme4, Ppmpme5, Ppmpme6, Ppmpme7, PpmpmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppmpm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmpm : Minimality.H24.SAT.CoreUnsat rowsPpmpm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Ppmpmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpmpm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
