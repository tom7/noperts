module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpzpp
public import Minimality.Type24SAT.K24.ChkPpzpp

@[expose] public section

/-!
# Type 24, class ppzpp off `OB1`: core Ppzpp, `CoreUnsat rowsPpzpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Ppzppe0 : (PpzppCnf.drop (0)).take rowsPpzpp0.length = cnfOfRows [rowsPpzpp0] := by decide +kernel
theorem Ppzppe1 : (PpzppCnf.drop (0 + rowsPpzpp0.length)).take rowsPpzpp1.length = cnfOfRows [rowsPpzpp1] := by decide +kernel
theorem Ppzppe2 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length)).take rowsPpzpp2.length = cnfOfRows [rowsPpzpp2] := by decide +kernel
theorem Ppzppe3 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length)).take rowsPpzpp3.length = cnfOfRows [rowsPpzpp3] := by decide +kernel
theorem Ppzppe4 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length + rowsPpzpp3.length)).take rowsPpzpp4.length = cnfOfRows [rowsPpzpp4] := by decide +kernel
theorem Ppzppe5 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length + rowsPpzpp3.length + rowsPpzpp4.length)).take rowsPpzpp5.length = cnfOfRows [rowsPpzpp5] := by decide +kernel
theorem Ppzppe6 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length + rowsPpzpp3.length + rowsPpzpp4.length + rowsPpzpp5.length)).take rowsPpzpp6.length = cnfOfRows [rowsPpzpp6] := by decide +kernel
theorem Ppzppe7 : (PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length + rowsPpzpp3.length + rowsPpzpp4.length + rowsPpzpp5.length + rowsPpzpp6.length)).take rowsPpzpp7.length = cnfOfRows [rowsPpzpp7] := by decide +kernel
theorem PpzppeEnd : PpzppCnf.drop (0 + rowsPpzpp0.length + rowsPpzpp1.length + rowsPpzpp2.length + rowsPpzpp3.length + rowsPpzpp4.length + rowsPpzpp5.length + rowsPpzpp6.length + rowsPpzpp7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppzpp, chunk by chunk. -/
theorem cnf_eqPpzpp : cnfOfRows rowsPpzpp = PpzppCnf := by
  have h := cnfOfRows_of_chkAt rowsPpzpp PpzppCnf 0 ⟨Ppzppe0, Ppzppe1, Ppzppe2, Ppzppe3, Ppzppe4, Ppzppe5, Ppzppe6, Ppzppe7, PpzppeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppzpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpzpp : Minimality.H24.SAT.CoreUnsat rowsPpzpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Ppzppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPpzpp] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
