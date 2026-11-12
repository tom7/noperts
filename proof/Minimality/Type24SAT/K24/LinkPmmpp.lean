module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPmmpp
public import Minimality.Type24SAT.K24.ChkPmmpp

@[expose] public section

/-!
# Type 24, class pmmpp off `OB1`: core Pmmpp, `CoreUnsat rowsPmmpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Pmmppe0 : (PmmppCnf.drop (0)).take rowsPmmpp0.length = cnfOfRows [rowsPmmpp0] := by decide +kernel
theorem Pmmppe1 : (PmmppCnf.drop (0 + rowsPmmpp0.length)).take rowsPmmpp1.length = cnfOfRows [rowsPmmpp1] := by decide +kernel
theorem Pmmppe2 : (PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length)).take rowsPmmpp2.length = cnfOfRows [rowsPmmpp2] := by decide +kernel
theorem Pmmppe3 : (PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length + rowsPmmpp2.length)).take rowsPmmpp3.length = cnfOfRows [rowsPmmpp3] := by decide +kernel
theorem Pmmppe4 : (PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length + rowsPmmpp2.length + rowsPmmpp3.length)).take rowsPmmpp4.length = cnfOfRows [rowsPmmpp4] := by decide +kernel
theorem Pmmppe5 : (PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length + rowsPmmpp2.length + rowsPmmpp3.length + rowsPmmpp4.length)).take rowsPmmpp5.length = cnfOfRows [rowsPmmpp5] := by decide +kernel
theorem Pmmppe6 : (PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length + rowsPmmpp2.length + rowsPmmpp3.length + rowsPmmpp4.length + rowsPmmpp5.length)).take rowsPmmpp6.length = cnfOfRows [rowsPmmpp6] := by decide +kernel
theorem PmmppeEnd : PmmppCnf.drop (0 + rowsPmmpp0.length + rowsPmmpp1.length + rowsPmmpp2.length + rowsPmmpp3.length + rowsPmmpp4.length + rowsPmmpp5.length + rowsPmmpp6.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Pmmpp, chunk by chunk. -/
theorem cnf_eqPmmpp : cnfOfRows rowsPmmpp = PmmppCnf := by
  have h := cnfOfRows_of_chkAt rowsPmmpp PmmppCnf 0 ⟨Pmmppe0, Pmmppe1, Pmmppe2, Pmmppe3, Pmmppe4, Pmmppe5, Pmmppe6, PmmppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Pmmpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPmmpp : Minimality.H24.SAT.CoreUnsat rowsPmmpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Pmmppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPmmpp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
