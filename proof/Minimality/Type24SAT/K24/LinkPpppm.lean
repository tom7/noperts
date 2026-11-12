module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpppm
public import Minimality.Type24SAT.K24.ChkPpppm

@[expose] public section

/-!
# Type 24, class ppppm off `OB1`: core Ppppm, `CoreUnsat rowsPpppm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Ppppme0 : (PpppmCnf.drop (0)).take rowsPpppm0.length = cnfOfRows [rowsPpppm0] := by decide +kernel
theorem Ppppme1 : (PpppmCnf.drop (0 + rowsPpppm0.length)).take rowsPpppm1.length = cnfOfRows [rowsPpppm1] := by decide +kernel
theorem Ppppme2 : (PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length)).take rowsPpppm2.length = cnfOfRows [rowsPpppm2] := by decide +kernel
theorem Ppppme3 : (PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length + rowsPpppm2.length)).take rowsPpppm3.length = cnfOfRows [rowsPpppm3] := by decide +kernel
theorem Ppppme4 : (PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length + rowsPpppm2.length + rowsPpppm3.length)).take rowsPpppm4.length = cnfOfRows [rowsPpppm4] := by decide +kernel
theorem Ppppme5 : (PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length + rowsPpppm2.length + rowsPpppm3.length + rowsPpppm4.length)).take rowsPpppm5.length = cnfOfRows [rowsPpppm5] := by decide +kernel
theorem Ppppme6 : (PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length + rowsPpppm2.length + rowsPpppm3.length + rowsPpppm4.length + rowsPpppm5.length)).take rowsPpppm6.length = cnfOfRows [rowsPpppm6] := by decide +kernel
theorem PpppmeEnd : PpppmCnf.drop (0 + rowsPpppm0.length + rowsPpppm1.length + rowsPpppm2.length + rowsPpppm3.length + rowsPpppm4.length + rowsPpppm5.length + rowsPpppm6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppppm, chunk by chunk. -/
theorem cnf_eqPpppm : cnfOfRows rowsPpppm = PpppmCnf := by
  have h := cnfOfRows_of_chkAt rowsPpppm PpppmCnf 0 ⟨Ppppme0, Ppppme1, Ppppme2, Ppppme3, Ppppme4, Ppppme5, Ppppme6, PpppmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppppm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpppm : Minimality.H24.SAT.CoreUnsat rowsPpppm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Ppppmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpppm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
