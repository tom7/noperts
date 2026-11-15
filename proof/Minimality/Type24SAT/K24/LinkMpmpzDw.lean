module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpzDw
public import Minimality.Type24SAT.K24.ChkMpmpzDw

@[expose] public section

/-!
# Type 24, class mpmpz off `OB1`: core MpmpzDw, `CoreUnsat rowsMpmpzDw` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem MpmpzDwe0 : (MpmpzDwCnf.drop (0)).take rowsMpmpzDw0.length = cnfOfRows [rowsMpmpzDw0] := by decide +kernel
theorem MpmpzDwe1 : (MpmpzDwCnf.drop (0 + rowsMpmpzDw0.length)).take rowsMpmpzDw1.length = cnfOfRows [rowsMpmpzDw1] := by decide +kernel
theorem MpmpzDwe2 : (MpmpzDwCnf.drop (0 + rowsMpmpzDw0.length + rowsMpmpzDw1.length)).take rowsMpmpzDw2.length = cnfOfRows [rowsMpmpzDw2] := by decide +kernel
theorem MpmpzDwe3 : (MpmpzDwCnf.drop (0 + rowsMpmpzDw0.length + rowsMpmpzDw1.length + rowsMpmpzDw2.length)).take rowsMpmpzDw3.length = cnfOfRows [rowsMpmpzDw3] := by decide +kernel
theorem MpmpzDweEnd : MpmpzDwCnf.drop (0 + rowsMpmpzDw0.length + rowsMpmpzDw1.length + rowsMpmpzDw2.length + rowsMpmpzDw3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core MpmpzDw, chunk by chunk. -/
theorem cnf_eqMpmpzDw : cnfOfRows rowsMpmpzDw = MpmpzDwCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpzDw MpmpzDwCnf 0 ⟨MpmpzDwe0, MpmpzDwe1, MpmpzDwe2, MpmpzDwe3, MpmpzDweEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core MpmpzDw are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpzDw : Minimality.H24.SAT.CoreUnsat rowsMpmpzDw := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.MpmpzDwunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmpzDw] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
