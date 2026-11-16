module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpzpp
public import Minimality.Type24SAT.K24.ChkMpzpp

@[expose] public section

/-!
# Type 24, class mpzpp off `OB1`: core Mpzpp, `CoreUnsat rowsMpzpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Mpzppe0 : (MpzppCnf.drop (0)).take rowsMpzpp0.length = cnfOfRows [rowsMpzpp0] := by decide +kernel
theorem Mpzppe1 : (MpzppCnf.drop (0 + rowsMpzpp0.length)).take rowsMpzpp1.length = cnfOfRows [rowsMpzpp1] := by decide +kernel
theorem Mpzppe2 : (MpzppCnf.drop (0 + rowsMpzpp0.length + rowsMpzpp1.length)).take rowsMpzpp2.length = cnfOfRows [rowsMpzpp2] := by decide +kernel
theorem Mpzppe3 : (MpzppCnf.drop (0 + rowsMpzpp0.length + rowsMpzpp1.length + rowsMpzpp2.length)).take rowsMpzpp3.length = cnfOfRows [rowsMpzpp3] := by decide +kernel
theorem Mpzppe4 : (MpzppCnf.drop (0 + rowsMpzpp0.length + rowsMpzpp1.length + rowsMpzpp2.length + rowsMpzpp3.length)).take rowsMpzpp4.length = cnfOfRows [rowsMpzpp4] := by decide +kernel
theorem Mpzppe5 : (MpzppCnf.drop (0 + rowsMpzpp0.length + rowsMpzpp1.length + rowsMpzpp2.length + rowsMpzpp3.length + rowsMpzpp4.length)).take rowsMpzpp5.length = cnfOfRows [rowsMpzpp5] := by decide +kernel
theorem MpzppeEnd : MpzppCnf.drop (0 + rowsMpzpp0.length + rowsMpzpp1.length + rowsMpzpp2.length + rowsMpzpp3.length + rowsMpzpp4.length + rowsMpzpp5.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Mpzpp, chunk by chunk. -/
theorem cnf_eqMpzpp : cnfOfRows rowsMpzpp = MpzppCnf := by
  have h := cnfOfRows_of_chkAt rowsMpzpp MpzppCnf 0 ⟨Mpzppe0, Mpzppe1, Mpzppe2, Mpzppe3, Mpzppe4, Mpzppe5, MpzppeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Mpzpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpzpp : Minimality.H24.SAT.CoreUnsat rowsMpzpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Mpzppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqMpzpp] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
