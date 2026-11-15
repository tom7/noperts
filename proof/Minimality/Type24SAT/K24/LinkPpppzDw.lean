module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpppzDw
public import Minimality.Type24SAT.K24.ChkPpppzDw

@[expose] public section

/-!
# Type 24, class ppppz off `OB1`: core PpppzDw, `CoreUnsat rowsPpppzDw` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem PpppzDwe0 : (PpppzDwCnf.drop (0)).take rowsPpppzDw0.length = cnfOfRows [rowsPpppzDw0] := by decide +kernel
theorem PpppzDwe1 : (PpppzDwCnf.drop (0 + rowsPpppzDw0.length)).take rowsPpppzDw1.length = cnfOfRows [rowsPpppzDw1] := by decide +kernel
theorem PpppzDwe2 : (PpppzDwCnf.drop (0 + rowsPpppzDw0.length + rowsPpppzDw1.length)).take rowsPpppzDw2.length = cnfOfRows [rowsPpppzDw2] := by decide +kernel
theorem PpppzDwe3 : (PpppzDwCnf.drop (0 + rowsPpppzDw0.length + rowsPpppzDw1.length + rowsPpppzDw2.length)).take rowsPpppzDw3.length = cnfOfRows [rowsPpppzDw3] := by decide +kernel
theorem PpppzDwe4 : (PpppzDwCnf.drop (0 + rowsPpppzDw0.length + rowsPpppzDw1.length + rowsPpppzDw2.length + rowsPpppzDw3.length)).take rowsPpppzDw4.length = cnfOfRows [rowsPpppzDw4] := by decide +kernel
theorem PpppzDweEnd : PpppzDwCnf.drop (0 + rowsPpppzDw0.length + rowsPpppzDw1.length + rowsPpppzDw2.length + rowsPpppzDw3.length + rowsPpppzDw4.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core PpppzDw, chunk by chunk. -/
theorem cnf_eqPpppzDw : cnfOfRows rowsPpppzDw = PpppzDwCnf := by
  have h := cnfOfRows_of_chkAt rowsPpppzDw PpppzDwCnf 0 ⟨PpppzDwe0, PpppzDwe1, PpppzDwe2, PpppzDwe3, PpppzDwe4, PpppzDweEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core PpppzDw are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpppzDw : Minimality.H24.SAT.CoreUnsat rowsPpppzDw := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.PpppzDwunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpppzDw] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
