module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmzm
public import Minimality.Type24SAT.K24.ChkPpmzm

@[expose] public section

/-!
# Type 24, class ppmzm off `OB1`: core Ppmzm, `CoreUnsat rowsPpmzm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Ppmzme0 : (PpmzmCnf.drop (0)).take rowsPpmzm0.length = cnfOfRows [rowsPpmzm0] := by decide +kernel
theorem Ppmzme1 : (PpmzmCnf.drop (0 + rowsPpmzm0.length)).take rowsPpmzm1.length = cnfOfRows [rowsPpmzm1] := by decide +kernel
theorem Ppmzme2 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length)).take rowsPpmzm2.length = cnfOfRows [rowsPpmzm2] := by decide +kernel
theorem Ppmzme3 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length)).take rowsPpmzm3.length = cnfOfRows [rowsPpmzm3] := by decide +kernel
theorem Ppmzme4 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length)).take rowsPpmzm4.length = cnfOfRows [rowsPpmzm4] := by decide +kernel
theorem Ppmzme5 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length + rowsPpmzm4.length)).take rowsPpmzm5.length = cnfOfRows [rowsPpmzm5] := by decide +kernel
theorem Ppmzme6 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length + rowsPpmzm4.length + rowsPpmzm5.length)).take rowsPpmzm6.length = cnfOfRows [rowsPpmzm6] := by decide +kernel
theorem Ppmzme7 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length + rowsPpmzm4.length + rowsPpmzm5.length + rowsPpmzm6.length)).take rowsPpmzm7.length = cnfOfRows [rowsPpmzm7] := by decide +kernel
theorem Ppmzme8 : (PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length + rowsPpmzm4.length + rowsPpmzm5.length + rowsPpmzm6.length + rowsPpmzm7.length)).take rowsPpmzm8.length = cnfOfRows [rowsPpmzm8] := by decide +kernel
theorem PpmzmeEnd : PpmzmCnf.drop (0 + rowsPpmzm0.length + rowsPpmzm1.length + rowsPpmzm2.length + rowsPpmzm3.length + rowsPpmzm4.length + rowsPpmzm5.length + rowsPpmzm6.length + rowsPpmzm7.length + rowsPpmzm8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppmzm, chunk by chunk. -/
theorem cnf_eqPpmzm : cnfOfRows rowsPpmzm = PpmzmCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmzm PpmzmCnf 0 ⟨Ppmzme0, Ppmzme1, Ppmzme2, Ppmzme3, Ppmzme4, Ppmzme5, Ppmzme6, Ppmzme7, Ppmzme8, PpmzmeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppmzm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmzm : Minimality.H24.SAT.CoreUnsat rowsPpmzm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Ppmzmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpmzm] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
