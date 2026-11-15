module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmmm
public import Minimality.Type24SAT.K24.ChkZpmmm

@[expose] public section

/-!
# Type 24, class zpmmm off `OB1`: core Zpmmm, `CoreUnsat rowsZpmmm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zpmmme0 : (ZpmmmCnf.drop (0)).take rowsZpmmm0.length = cnfOfRows [rowsZpmmm0] := by decide +kernel
theorem Zpmmme1 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length)).take rowsZpmmm1.length = cnfOfRows [rowsZpmmm1] := by decide +kernel
theorem Zpmmme2 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length)).take rowsZpmmm2.length = cnfOfRows [rowsZpmmm2] := by decide +kernel
theorem Zpmmme3 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length)).take rowsZpmmm3.length = cnfOfRows [rowsZpmmm3] := by decide +kernel
theorem Zpmmme4 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length)).take rowsZpmmm4.length = cnfOfRows [rowsZpmmm4] := by decide +kernel
theorem Zpmmme5 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length + rowsZpmmm4.length)).take rowsZpmmm5.length = cnfOfRows [rowsZpmmm5] := by decide +kernel
theorem Zpmmme6 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length + rowsZpmmm4.length + rowsZpmmm5.length)).take rowsZpmmm6.length = cnfOfRows [rowsZpmmm6] := by decide +kernel
theorem Zpmmme7 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length + rowsZpmmm4.length + rowsZpmmm5.length + rowsZpmmm6.length)).take rowsZpmmm7.length = cnfOfRows [rowsZpmmm7] := by decide +kernel
theorem Zpmmme8 : (ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length + rowsZpmmm4.length + rowsZpmmm5.length + rowsZpmmm6.length + rowsZpmmm7.length)).take rowsZpmmm8.length = cnfOfRows [rowsZpmmm8] := by decide +kernel
theorem ZpmmmeEnd : ZpmmmCnf.drop (0 + rowsZpmmm0.length + rowsZpmmm1.length + rowsZpmmm2.length + rowsZpmmm3.length + rowsZpmmm4.length + rowsZpmmm5.length + rowsZpmmm6.length + rowsZpmmm7.length + rowsZpmmm8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpmmm, chunk by chunk. -/
theorem cnf_eqZpmmm : cnfOfRows rowsZpmmm = ZpmmmCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmmm ZpmmmCnf 0 ⟨Zpmmme0, Zpmmme1, Zpmmme2, Zpmmme3, Zpmmme4, Zpmmme5, Zpmmme6, Zpmmme7, Zpmmme8, ZpmmmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpmmm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmmm : Minimality.H24.SAT.CoreUnsat rowsZpmmm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zpmmmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmmm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
