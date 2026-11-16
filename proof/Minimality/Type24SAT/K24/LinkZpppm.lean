module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpppm
public import Minimality.Type24SAT.K24.ChkZpppm

@[expose] public section

/-!
# Type 24, class zpppm off `OB1`: core Zpppm, `CoreUnsat rowsZpppm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Zpppme0 : (ZpppmCnf.drop (0)).take rowsZpppm0.length = cnfOfRows [rowsZpppm0] := by decide +kernel
theorem Zpppme1 : (ZpppmCnf.drop (0 + rowsZpppm0.length)).take rowsZpppm1.length = cnfOfRows [rowsZpppm1] := by decide +kernel
theorem Zpppme2 : (ZpppmCnf.drop (0 + rowsZpppm0.length + rowsZpppm1.length)).take rowsZpppm2.length = cnfOfRows [rowsZpppm2] := by decide +kernel
theorem Zpppme3 : (ZpppmCnf.drop (0 + rowsZpppm0.length + rowsZpppm1.length + rowsZpppm2.length)).take rowsZpppm3.length = cnfOfRows [rowsZpppm3] := by decide +kernel
theorem Zpppme4 : (ZpppmCnf.drop (0 + rowsZpppm0.length + rowsZpppm1.length + rowsZpppm2.length + rowsZpppm3.length)).take rowsZpppm4.length = cnfOfRows [rowsZpppm4] := by decide +kernel
theorem ZpppmeEnd : ZpppmCnf.drop (0 + rowsZpppm0.length + rowsZpppm1.length + rowsZpppm2.length + rowsZpppm3.length + rowsZpppm4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpppm, chunk by chunk. -/
theorem cnf_eqZpppm : cnfOfRows rowsZpppm = ZpppmCnf := by
  have h := cnfOfRows_of_chkAt rowsZpppm ZpppmCnf 0 ⟨Zpppme0, Zpppme1, Zpppme2, Zpppme3, Zpppme4, ZpppmeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpppm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpppm : Minimality.H24.SAT.CoreUnsat rowsZpppm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Zpppmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqZpppm] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
