module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmmm
public import Minimality.Type24SAT.K24.ChkPpmmm

@[expose] public section

/-!
# Type 24, class ppmmm off `OB1`: core Ppmmm, `CoreUnsat rowsPpmmm` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Ppmmme0 : (PpmmmCnf.drop (0)).take rowsPpmmm0.length = cnfOfRows [rowsPpmmm0] := by decide +kernel
theorem Ppmmme1 : (PpmmmCnf.drop (0 + rowsPpmmm0.length)).take rowsPpmmm1.length = cnfOfRows [rowsPpmmm1] := by decide +kernel
theorem Ppmmme2 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length)).take rowsPpmmm2.length = cnfOfRows [rowsPpmmm2] := by decide +kernel
theorem Ppmmme3 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length)).take rowsPpmmm3.length = cnfOfRows [rowsPpmmm3] := by decide +kernel
theorem Ppmmme4 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length + rowsPpmmm3.length)).take rowsPpmmm4.length = cnfOfRows [rowsPpmmm4] := by decide +kernel
theorem Ppmmme5 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length + rowsPpmmm3.length + rowsPpmmm4.length)).take rowsPpmmm5.length = cnfOfRows [rowsPpmmm5] := by decide +kernel
theorem Ppmmme6 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length + rowsPpmmm3.length + rowsPpmmm4.length + rowsPpmmm5.length)).take rowsPpmmm6.length = cnfOfRows [rowsPpmmm6] := by decide +kernel
theorem Ppmmme7 : (PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length + rowsPpmmm3.length + rowsPpmmm4.length + rowsPpmmm5.length + rowsPpmmm6.length)).take rowsPpmmm7.length = cnfOfRows [rowsPpmmm7] := by decide +kernel
theorem PpmmmeEnd : PpmmmCnf.drop (0 + rowsPpmmm0.length + rowsPpmmm1.length + rowsPpmmm2.length + rowsPpmmm3.length + rowsPpmmm4.length + rowsPpmmm5.length + rowsPpmmm6.length + rowsPpmmm7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppmmm, chunk by chunk. -/
theorem cnf_eqPpmmm : cnfOfRows rowsPpmmm = PpmmmCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmmm PpmmmCnf 0 ⟨Ppmmme0, Ppmmme1, Ppmmme2, Ppmmme3, Ppmmme4, Ppmmme5, Ppmmme6, Ppmmme7, PpmmmeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppmmm are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmmm : Minimality.H24.SAT.CoreUnsat rowsPpmmm := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Ppmmmunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpmmm] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
