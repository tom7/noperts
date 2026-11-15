module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpzpm
public import Minimality.Type24SAT.K24.ChkZpzpm

@[expose] public section

/-!
# Type 24, class zpzpm off `OB1`: core Zpzpm, `CoreUnsat rowsZpzpm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zpzpme0 : (ZpzpmCnf.drop (0)).take rowsZpzpm0.length = cnfOfRows [rowsZpzpm0] := by decide +kernel
theorem Zpzpme1 : (ZpzpmCnf.drop (0 + rowsZpzpm0.length)).take rowsZpzpm1.length = cnfOfRows [rowsZpzpm1] := by decide +kernel
theorem Zpzpme2 : (ZpzpmCnf.drop (0 + rowsZpzpm0.length + rowsZpzpm1.length)).take rowsZpzpm2.length = cnfOfRows [rowsZpzpm2] := by decide +kernel
theorem Zpzpme3 : (ZpzpmCnf.drop (0 + rowsZpzpm0.length + rowsZpzpm1.length + rowsZpzpm2.length)).take rowsZpzpm3.length = cnfOfRows [rowsZpzpm3] := by decide +kernel
theorem Zpzpme4 : (ZpzpmCnf.drop (0 + rowsZpzpm0.length + rowsZpzpm1.length + rowsZpzpm2.length + rowsZpzpm3.length)).take rowsZpzpm4.length = cnfOfRows [rowsZpzpm4] := by decide +kernel
theorem ZpzpmeEnd : ZpzpmCnf.drop (0 + rowsZpzpm0.length + rowsZpzpm1.length + rowsZpzpm2.length + rowsZpzpm3.length + rowsZpzpm4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpzpm, chunk by chunk. -/
theorem cnf_eqZpzpm : cnfOfRows rowsZpzpm = ZpzpmCnf := by
  have h := cnfOfRows_of_chkAt rowsZpzpm ZpzpmCnf 0 ⟨Zpzpme0, Zpzpme1, Zpzpme2, Zpzpme3, Zpzpme4, ZpzpmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpzpm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpzpm : Minimality.H24.SAT.CoreUnsat rowsZpzpm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zpzpmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpzpm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
