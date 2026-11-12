module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofMpmpp
public import Minimality.Type24SAT.K24.ChkMpmpp

@[expose] public section

/-!
# Type 24, class mpmpp off `OB1`: core Mpmpp, `CoreUnsat rowsMpmpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Mpmppe0 : (MpmppCnf.drop (0)).take rowsMpmpp0.length = cnfOfRows [rowsMpmpp0] := by decide +kernel
theorem Mpmppe1 : (MpmppCnf.drop (0 + rowsMpmpp0.length)).take rowsMpmpp1.length = cnfOfRows [rowsMpmpp1] := by decide +kernel
theorem Mpmppe2 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length)).take rowsMpmpp2.length = cnfOfRows [rowsMpmpp2] := by decide +kernel
theorem Mpmppe3 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length)).take rowsMpmpp3.length = cnfOfRows [rowsMpmpp3] := by decide +kernel
theorem Mpmppe4 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length + rowsMpmpp3.length)).take rowsMpmpp4.length = cnfOfRows [rowsMpmpp4] := by decide +kernel
theorem Mpmppe5 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length + rowsMpmpp3.length + rowsMpmpp4.length)).take rowsMpmpp5.length = cnfOfRows [rowsMpmpp5] := by decide +kernel
theorem Mpmppe6 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length + rowsMpmpp3.length + rowsMpmpp4.length + rowsMpmpp5.length)).take rowsMpmpp6.length = cnfOfRows [rowsMpmpp6] := by decide +kernel
theorem Mpmppe7 : (MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length + rowsMpmpp3.length + rowsMpmpp4.length + rowsMpmpp5.length + rowsMpmpp6.length)).take rowsMpmpp7.length = cnfOfRows [rowsMpmpp7] := by decide +kernel
theorem MpmppeEnd : MpmppCnf.drop (0 + rowsMpmpp0.length + rowsMpmpp1.length + rowsMpmpp2.length + rowsMpmpp3.length + rowsMpmpp4.length + rowsMpmpp5.length + rowsMpmpp6.length + rowsMpmpp7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Mpmpp, chunk by chunk. -/
theorem cnf_eqMpmpp : cnfOfRows rowsMpmpp = MpmppCnf := by
  have h := cnfOfRows_of_chkAt rowsMpmpp MpmppCnf 0 ⟨Mpmppe0, Mpmppe1, Mpmppe2, Mpmppe3, Mpmppe4, Mpmppe5, Mpmppe6, Mpmppe7, MpmppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Mpmpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatMpmpp : Minimality.H24.SAT.CoreUnsat rowsMpmpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Mpmppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqMpmpp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
