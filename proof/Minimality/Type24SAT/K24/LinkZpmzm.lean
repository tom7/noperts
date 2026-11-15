module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmzm
public import Minimality.Type24SAT.K24.ChkZpmzm

@[expose] public section

/-!
# Type 24, class zpmzm off `OB1`: core Zpmzm, `CoreUnsat rowsZpmzm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zpmzme0 : (ZpmzmCnf.drop (0)).take rowsZpmzm0.length = cnfOfRows [rowsZpmzm0] := by decide +kernel
theorem Zpmzme1 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length)).take rowsZpmzm1.length = cnfOfRows [rowsZpmzm1] := by decide +kernel
theorem Zpmzme2 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length)).take rowsZpmzm2.length = cnfOfRows [rowsZpmzm2] := by decide +kernel
theorem Zpmzme3 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length)).take rowsZpmzm3.length = cnfOfRows [rowsZpmzm3] := by decide +kernel
theorem Zpmzme4 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length + rowsZpmzm3.length)).take rowsZpmzm4.length = cnfOfRows [rowsZpmzm4] := by decide +kernel
theorem Zpmzme5 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length + rowsZpmzm3.length + rowsZpmzm4.length)).take rowsZpmzm5.length = cnfOfRows [rowsZpmzm5] := by decide +kernel
theorem Zpmzme6 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length + rowsZpmzm3.length + rowsZpmzm4.length + rowsZpmzm5.length)).take rowsZpmzm6.length = cnfOfRows [rowsZpmzm6] := by decide +kernel
theorem Zpmzme7 : (ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length + rowsZpmzm3.length + rowsZpmzm4.length + rowsZpmzm5.length + rowsZpmzm6.length)).take rowsZpmzm7.length = cnfOfRows [rowsZpmzm7] := by decide +kernel
theorem ZpmzmeEnd : ZpmzmCnf.drop (0 + rowsZpmzm0.length + rowsZpmzm1.length + rowsZpmzm2.length + rowsZpmzm3.length + rowsZpmzm4.length + rowsZpmzm5.length + rowsZpmzm6.length + rowsZpmzm7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpmzm, chunk by chunk. -/
theorem cnf_eqZpmzm : cnfOfRows rowsZpmzm = ZpmzmCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmzm ZpmzmCnf 0 ⟨Zpmzme0, Zpmzme1, Zpmzme2, Zpmzme3, Zpmzme4, Zpmzme5, Zpmzme6, Zpmzme7, ZpmzmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpmzm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmzm : Minimality.H24.SAT.CoreUnsat rowsZpmzm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zpmzmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmzm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
