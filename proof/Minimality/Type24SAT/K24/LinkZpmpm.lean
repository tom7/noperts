module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmpm
public import Minimality.Type24SAT.K24.ChkZpmpm

@[expose] public section

/-!
# Type 24, class zpmpm off `OB1`: core Zpmpm, `CoreUnsat rowsZpmpm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zpmpme0 : (ZpmpmCnf.drop (0)).take rowsZpmpm0.length = cnfOfRows [rowsZpmpm0] := by decide +kernel
theorem Zpmpme1 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length)).take rowsZpmpm1.length = cnfOfRows [rowsZpmpm1] := by decide +kernel
theorem Zpmpme2 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length)).take rowsZpmpm2.length = cnfOfRows [rowsZpmpm2] := by decide +kernel
theorem Zpmpme3 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length)).take rowsZpmpm3.length = cnfOfRows [rowsZpmpm3] := by decide +kernel
theorem Zpmpme4 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length + rowsZpmpm3.length)).take rowsZpmpm4.length = cnfOfRows [rowsZpmpm4] := by decide +kernel
theorem Zpmpme5 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length + rowsZpmpm3.length + rowsZpmpm4.length)).take rowsZpmpm5.length = cnfOfRows [rowsZpmpm5] := by decide +kernel
theorem Zpmpme6 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length + rowsZpmpm3.length + rowsZpmpm4.length + rowsZpmpm5.length)).take rowsZpmpm6.length = cnfOfRows [rowsZpmpm6] := by decide +kernel
theorem Zpmpme7 : (ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length + rowsZpmpm3.length + rowsZpmpm4.length + rowsZpmpm5.length + rowsZpmpm6.length)).take rowsZpmpm7.length = cnfOfRows [rowsZpmpm7] := by decide +kernel
theorem ZpmpmeEnd : ZpmpmCnf.drop (0 + rowsZpmpm0.length + rowsZpmpm1.length + rowsZpmpm2.length + rowsZpmpm3.length + rowsZpmpm4.length + rowsZpmpm5.length + rowsZpmpm6.length + rowsZpmpm7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpmpm, chunk by chunk. -/
theorem cnf_eqZpmpm : cnfOfRows rowsZpmpm = ZpmpmCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmpm ZpmpmCnf 0 ⟨Zpmpme0, Zpmpme1, Zpmpme2, Zpmpme3, Zpmpme4, Zpmpme5, Zpmpme6, Zpmpme7, ZpmpmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpmpm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmpm : Minimality.H24.SAT.CoreUnsat rowsZpmpm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zpmpmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmpm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
