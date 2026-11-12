module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPpmpp
public import Minimality.Type24SAT.K24.ChkPpmpp

@[expose] public section

/-!
# Type 24, class ppmpp off `OB1`: core Ppmpp, `CoreUnsat rowsPpmpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Ppmppe0 : (PpmppCnf.drop (0)).take rowsPpmpp0.length = cnfOfRows [rowsPpmpp0] := by decide +kernel
theorem Ppmppe1 : (PpmppCnf.drop (0 + rowsPpmpp0.length)).take rowsPpmpp1.length = cnfOfRows [rowsPpmpp1] := by decide +kernel
theorem Ppmppe2 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length)).take rowsPpmpp2.length = cnfOfRows [rowsPpmpp2] := by decide +kernel
theorem Ppmppe3 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length)).take rowsPpmpp3.length = cnfOfRows [rowsPpmpp3] := by decide +kernel
theorem Ppmppe4 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length + rowsPpmpp3.length)).take rowsPpmpp4.length = cnfOfRows [rowsPpmpp4] := by decide +kernel
theorem Ppmppe5 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length + rowsPpmpp3.length + rowsPpmpp4.length)).take rowsPpmpp5.length = cnfOfRows [rowsPpmpp5] := by decide +kernel
theorem Ppmppe6 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length + rowsPpmpp3.length + rowsPpmpp4.length + rowsPpmpp5.length)).take rowsPpmpp6.length = cnfOfRows [rowsPpmpp6] := by decide +kernel
theorem Ppmppe7 : (PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length + rowsPpmpp3.length + rowsPpmpp4.length + rowsPpmpp5.length + rowsPpmpp6.length)).take rowsPpmpp7.length = cnfOfRows [rowsPpmpp7] := by decide +kernel
theorem PpmppeEnd : PpmppCnf.drop (0 + rowsPpmpp0.length + rowsPpmpp1.length + rowsPpmpp2.length + rowsPpmpp3.length + rowsPpmpp4.length + rowsPpmpp5.length + rowsPpmpp6.length + rowsPpmpp7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Ppmpp, chunk by chunk. -/
theorem cnf_eqPpmpp : cnfOfRows rowsPpmpp = PpmppCnf := by
  have h := cnfOfRows_of_chkAt rowsPpmpp PpmppCnf 0 ⟨Ppmppe0, Ppmppe1, Ppmppe2, Ppmppe3, Ppmppe4, Ppmppe5, Ppmppe6, Ppmppe7, PpmppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Ppmpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPpmpp : Minimality.H24.SAT.CoreUnsat rowsPpmpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Ppmppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqPpmpp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
