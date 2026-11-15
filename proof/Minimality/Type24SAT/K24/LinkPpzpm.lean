module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpzpm
public import Minimality.Type24SAT.K24.ChkPpzpm

@[expose] public section

/-!
# Type 24, class ppzpm off `OB1`: core Ppzpm, `CoreUnsat rowsPpzpm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Ppzpme0 : (PpzpmCnf.drop (0)).take rowsPpzpm0.length = cnfOfRows [rowsPpzpm0] := by decide +kernel
theorem Ppzpme1 : (PpzpmCnf.drop (0 + rowsPpzpm0.length)).take rowsPpzpm1.length = cnfOfRows [rowsPpzpm1] := by decide +kernel
theorem Ppzpme2 : (PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length)).take rowsPpzpm2.length = cnfOfRows [rowsPpzpm2] := by decide +kernel
theorem Ppzpme3 : (PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length + rowsPpzpm2.length)).take rowsPpzpm3.length = cnfOfRows [rowsPpzpm3] := by decide +kernel
theorem Ppzpme4 : (PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length + rowsPpzpm2.length + rowsPpzpm3.length)).take rowsPpzpm4.length = cnfOfRows [rowsPpzpm4] := by decide +kernel
theorem Ppzpme5 : (PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length + rowsPpzpm2.length + rowsPpzpm3.length + rowsPpzpm4.length)).take rowsPpzpm5.length = cnfOfRows [rowsPpzpm5] := by decide +kernel
theorem Ppzpme6 : (PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length + rowsPpzpm2.length + rowsPpzpm3.length + rowsPpzpm4.length + rowsPpzpm5.length)).take rowsPpzpm6.length = cnfOfRows [rowsPpzpm6] := by decide +kernel
theorem PpzpmeEnd : PpzpmCnf.drop (0 + rowsPpzpm0.length + rowsPpzpm1.length + rowsPpzpm2.length + rowsPpzpm3.length + rowsPpzpm4.length + rowsPpzpm5.length + rowsPpzpm6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppzpm, chunk by chunk. -/
theorem cnf_eqPpzpm : cnfOfRows rowsPpzpm = PpzpmCnf := by
  have h := cnfOfRows_of_chkAt rowsPpzpm PpzpmCnf 0 ⟨Ppzpme0, Ppzpme1, Ppzpme2, Ppzpme3, Ppzpme4, Ppzpme5, Ppzpme6, PpzpmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppzpm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpzpm : Minimality.H24.SAT.CoreUnsat rowsPpzpm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Ppzpmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpzpm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
