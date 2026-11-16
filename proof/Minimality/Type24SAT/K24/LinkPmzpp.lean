module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPmzpp
public import Minimality.Type24SAT.K24.ChkPmzpp

@[expose] public section

/-!
# Type 24, class pmzpp off `OB1`: core Pmzpp, `CoreUnsat rowsPmzpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Pmzppe0 : (PmzppCnf.drop (0)).take rowsPmzpp0.length = cnfOfRows [rowsPmzpp0] := by decide +kernel
theorem Pmzppe1 : (PmzppCnf.drop (0 + rowsPmzpp0.length)).take rowsPmzpp1.length = cnfOfRows [rowsPmzpp1] := by decide +kernel
theorem Pmzppe2 : (PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length)).take rowsPmzpp2.length = cnfOfRows [rowsPmzpp2] := by decide +kernel
theorem Pmzppe3 : (PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length + rowsPmzpp2.length)).take rowsPmzpp3.length = cnfOfRows [rowsPmzpp3] := by decide +kernel
theorem Pmzppe4 : (PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length + rowsPmzpp2.length + rowsPmzpp3.length)).take rowsPmzpp4.length = cnfOfRows [rowsPmzpp4] := by decide +kernel
theorem Pmzppe5 : (PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length + rowsPmzpp2.length + rowsPmzpp3.length + rowsPmzpp4.length)).take rowsPmzpp5.length = cnfOfRows [rowsPmzpp5] := by decide +kernel
theorem Pmzppe6 : (PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length + rowsPmzpp2.length + rowsPmzpp3.length + rowsPmzpp4.length + rowsPmzpp5.length)).take rowsPmzpp6.length = cnfOfRows [rowsPmzpp6] := by decide +kernel
theorem PmzppeEnd : PmzppCnf.drop (0 + rowsPmzpp0.length + rowsPmzpp1.length + rowsPmzpp2.length + rowsPmzpp3.length + rowsPmzpp4.length + rowsPmzpp5.length + rowsPmzpp6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Pmzpp, chunk by chunk. -/
theorem cnf_eqPmzpp : cnfOfRows rowsPmzpp = PmzppCnf := by
  have h := cnfOfRows_of_chkAt rowsPmzpp PmzppCnf 0 ⟨Pmzppe0, Pmzppe1, Pmzppe2, Pmzppe3, Pmzppe4, Pmzppe5, Pmzppe6, PmzppeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Pmzpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPmzpp : Minimality.H24.SAT.CoreUnsat rowsPmzpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Pmzppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPmzpp] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
