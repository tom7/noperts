module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPzzpp
public import Minimality.Type24SAT.K24.ChkPzzpp

@[expose] public section

/-!
# Type 24, class pzzpp off `OB1`: core Pzzpp, `CoreUnsat rowsPzzpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Pzzppe0 : (PzzppCnf.drop (0)).take rowsPzzpp0.length = cnfOfRows [rowsPzzpp0] := by decide +kernel
theorem Pzzppe1 : (PzzppCnf.drop (0 + rowsPzzpp0.length)).take rowsPzzpp1.length = cnfOfRows [rowsPzzpp1] := by decide +kernel
theorem Pzzppe2 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length)).take rowsPzzpp2.length = cnfOfRows [rowsPzzpp2] := by decide +kernel
theorem Pzzppe3 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length)).take rowsPzzpp3.length = cnfOfRows [rowsPzzpp3] := by decide +kernel
theorem Pzzppe4 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length)).take rowsPzzpp4.length = cnfOfRows [rowsPzzpp4] := by decide +kernel
theorem Pzzppe5 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length + rowsPzzpp4.length)).take rowsPzzpp5.length = cnfOfRows [rowsPzzpp5] := by decide +kernel
theorem Pzzppe6 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length + rowsPzzpp4.length + rowsPzzpp5.length)).take rowsPzzpp6.length = cnfOfRows [rowsPzzpp6] := by decide +kernel
theorem Pzzppe7 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length + rowsPzzpp4.length + rowsPzzpp5.length + rowsPzzpp6.length)).take rowsPzzpp7.length = cnfOfRows [rowsPzzpp7] := by decide +kernel
theorem Pzzppe8 : (PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length + rowsPzzpp4.length + rowsPzzpp5.length + rowsPzzpp6.length + rowsPzzpp7.length)).take rowsPzzpp8.length = cnfOfRows [rowsPzzpp8] := by decide +kernel
theorem PzzppeEnd : PzzppCnf.drop (0 + rowsPzzpp0.length + rowsPzzpp1.length + rowsPzzpp2.length + rowsPzzpp3.length + rowsPzzpp4.length + rowsPzzpp5.length + rowsPzzpp6.length + rowsPzzpp7.length + rowsPzzpp8.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Pzzpp, chunk by chunk. -/
theorem cnf_eqPzzpp : cnfOfRows rowsPzzpp = PzzppCnf := by
  have h := cnfOfRows_of_chkAt rowsPzzpp PzzppCnf 0 ⟨Pzzppe0, Pzzppe1, Pzzppe2, Pzzppe3, Pzzppe4, Pzzppe5, Pzzppe6, Pzzppe7, Pzzppe8, PzzppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Pzzpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPzzpp : Minimality.H24.SAT.CoreUnsat rowsPzzpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Pzzppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPzzpp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
