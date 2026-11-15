module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpzpm
public import Minimality.Type24SAT.K24.ChkMpzpm

@[expose] public section

/-!
# Type 24, class mpzpm off `OB1`: core Mpzpm, `CoreUnsat rowsMpzpm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Mpzpme0 : (MpzpmCnf.drop (0)).take rowsMpzpm0.length = cnfOfRows [rowsMpzpm0] := by decide +kernel
theorem Mpzpme1 : (MpzpmCnf.drop (0 + rowsMpzpm0.length)).take rowsMpzpm1.length = cnfOfRows [rowsMpzpm1] := by decide +kernel
theorem Mpzpme2 : (MpzpmCnf.drop (0 + rowsMpzpm0.length + rowsMpzpm1.length)).take rowsMpzpm2.length = cnfOfRows [rowsMpzpm2] := by decide +kernel
theorem Mpzpme3 : (MpzpmCnf.drop (0 + rowsMpzpm0.length + rowsMpzpm1.length + rowsMpzpm2.length)).take rowsMpzpm3.length = cnfOfRows [rowsMpzpm3] := by decide +kernel
theorem Mpzpme4 : (MpzpmCnf.drop (0 + rowsMpzpm0.length + rowsMpzpm1.length + rowsMpzpm2.length + rowsMpzpm3.length)).take rowsMpzpm4.length = cnfOfRows [rowsMpzpm4] := by decide +kernel
theorem Mpzpme5 : (MpzpmCnf.drop (0 + rowsMpzpm0.length + rowsMpzpm1.length + rowsMpzpm2.length + rowsMpzpm3.length + rowsMpzpm4.length)).take rowsMpzpm5.length = cnfOfRows [rowsMpzpm5] := by decide +kernel
theorem MpzpmeEnd : MpzpmCnf.drop (0 + rowsMpzpm0.length + rowsMpzpm1.length + rowsMpzpm2.length + rowsMpzpm3.length + rowsMpzpm4.length + rowsMpzpm5.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Mpzpm, chunk by chunk. -/
theorem cnf_eqMpzpm : cnfOfRows rowsMpzpm = MpzpmCnf := by
  have h := cnfOfRows_of_chkAt rowsMpzpm MpzpmCnf 0 ⟨Mpzpme0, Mpzpme1, Mpzpme2, Mpzpme3, Mpzpme4, Mpzpme5, MpzpmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Mpzpm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpzpm : Minimality.H24.SAT.CoreUnsat rowsMpzpm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Mpzpmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpzpm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
