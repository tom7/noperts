module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmpzDw
public import Minimality.Type24SAT.K24.ChkPpmpzDw

@[expose] public section

/-!
# Type 24, class ppmpz off `OB1`: core PpmpzDw, `CoreUnsat rowsPpmpzDw` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PpmpzDwe0 : (PpmpzDwCnf.drop (0)).take rowsPpmpzDw0.length = cnfOfRows [rowsPpmpzDw0] := by decide +kernel
theorem PpmpzDwe1 : (PpmpzDwCnf.drop (0 + rowsPpmpzDw0.length)).take rowsPpmpzDw1.length = cnfOfRows [rowsPpmpzDw1] := by decide +kernel
theorem PpmpzDwe2 : (PpmpzDwCnf.drop (0 + rowsPpmpzDw0.length + rowsPpmpzDw1.length)).take rowsPpmpzDw2.length = cnfOfRows [rowsPpmpzDw2] := by decide +kernel
theorem PpmpzDwe3 : (PpmpzDwCnf.drop (0 + rowsPpmpzDw0.length + rowsPpmpzDw1.length + rowsPpmpzDw2.length)).take rowsPpmpzDw3.length = cnfOfRows [rowsPpmpzDw3] := by decide +kernel
theorem PpmpzDweEnd : PpmpzDwCnf.drop (0 + rowsPpmpzDw0.length + rowsPpmpzDw1.length + rowsPpmpzDw2.length + rowsPpmpzDw3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpmpzDw, chunk by chunk. -/
theorem cnf_eqPpmpzDw : cnfOfRows rowsPpmpzDw = PpmpzDwCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmpzDw PpmpzDwCnf 0 ⟨PpmpzDwe0, PpmpzDwe1, PpmpzDwe2, PpmpzDwe3, PpmpzDweEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpmpzDw are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmpzDw : Minimality.H24.SAT.CoreUnsat rowsPpmpzDw := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PpmpzDwunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpmpzDw] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
