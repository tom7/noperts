module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpmpp
public import Minimality.Type24SAT.K24.ChkZpmpp

@[expose] public section

/-!
# Type 24, class zpmpp off `OB1`: core Zpmpp, `CoreUnsat rowsZpmpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zpmppe0 : (ZpmppCnf.drop (0)).take rowsZpmpp0.length = cnfOfRows [rowsZpmpp0] := by decide +kernel
theorem Zpmppe1 : (ZpmppCnf.drop (0 + rowsZpmpp0.length)).take rowsZpmpp1.length = cnfOfRows [rowsZpmpp1] := by decide +kernel
theorem Zpmppe2 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length)).take rowsZpmpp2.length = cnfOfRows [rowsZpmpp2] := by decide +kernel
theorem Zpmppe3 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length)).take rowsZpmpp3.length = cnfOfRows [rowsZpmpp3] := by decide +kernel
theorem Zpmppe4 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length + rowsZpmpp3.length)).take rowsZpmpp4.length = cnfOfRows [rowsZpmpp4] := by decide +kernel
theorem Zpmppe5 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length + rowsZpmpp3.length + rowsZpmpp4.length)).take rowsZpmpp5.length = cnfOfRows [rowsZpmpp5] := by decide +kernel
theorem Zpmppe6 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length + rowsZpmpp3.length + rowsZpmpp4.length + rowsZpmpp5.length)).take rowsZpmpp6.length = cnfOfRows [rowsZpmpp6] := by decide +kernel
theorem Zpmppe7 : (ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length + rowsZpmpp3.length + rowsZpmpp4.length + rowsZpmpp5.length + rowsZpmpp6.length)).take rowsZpmpp7.length = cnfOfRows [rowsZpmpp7] := by decide +kernel
theorem ZpmppeEnd : ZpmppCnf.drop (0 + rowsZpmpp0.length + rowsZpmpp1.length + rowsZpmpp2.length + rowsZpmpp3.length + rowsZpmpp4.length + rowsZpmpp5.length + rowsZpmpp6.length + rowsZpmpp7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpmpp, chunk by chunk. -/
theorem cnf_eqZpmpp : cnfOfRows rowsZpmpp = ZpmppCnf := by
  have h := cnfOfRows_of_chkAt rowsZpmpp ZpmppCnf 0 ⟨Zpmppe0, Zpmppe1, Zpmppe2, Zpmppe3, Zpmppe4, Zpmppe5, Zpmppe6, Zpmppe7, ZpmppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpmpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpmpp : Minimality.H24.SAT.CoreUnsat rowsZpmpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zpmppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpmpp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
