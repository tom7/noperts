module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofPzmpp
public import Minimality.Type24SAT.K24.ChkPzmpp

@[expose] public section

/-!
# Type 24, class pzmpp off `OB1`: core Pzmpp, `CoreUnsat rowsPzmpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Pzmppe0 : (PzmppCnf.drop (0)).take rowsPzmpp0.length = cnfOfRows [rowsPzmpp0] := by decide +kernel
theorem Pzmppe1 : (PzmppCnf.drop (0 + rowsPzmpp0.length)).take rowsPzmpp1.length = cnfOfRows [rowsPzmpp1] := by decide +kernel
theorem Pzmppe2 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length)).take rowsPzmpp2.length = cnfOfRows [rowsPzmpp2] := by decide +kernel
theorem Pzmppe3 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length)).take rowsPzmpp3.length = cnfOfRows [rowsPzmpp3] := by decide +kernel
theorem Pzmppe4 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length + rowsPzmpp3.length)).take rowsPzmpp4.length = cnfOfRows [rowsPzmpp4] := by decide +kernel
theorem Pzmppe5 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length + rowsPzmpp3.length + rowsPzmpp4.length)).take rowsPzmpp5.length = cnfOfRows [rowsPzmpp5] := by decide +kernel
theorem Pzmppe6 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length + rowsPzmpp3.length + rowsPzmpp4.length + rowsPzmpp5.length)).take rowsPzmpp6.length = cnfOfRows [rowsPzmpp6] := by decide +kernel
theorem Pzmppe7 : (PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length + rowsPzmpp3.length + rowsPzmpp4.length + rowsPzmpp5.length + rowsPzmpp6.length)).take rowsPzmpp7.length = cnfOfRows [rowsPzmpp7] := by decide +kernel
theorem PzmppeEnd : PzmppCnf.drop (0 + rowsPzmpp0.length + rowsPzmpp1.length + rowsPzmpp2.length + rowsPzmpp3.length + rowsPzmpp4.length + rowsPzmpp5.length + rowsPzmpp6.length + rowsPzmpp7.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Pzmpp, chunk by chunk. -/
theorem cnf_eqPzmpp : cnfOfRows rowsPzmpp = PzmppCnf := by
  have h := cnfOfRows_of_chkAt rowsPzmpp PzmppCnf 0 ⟨Pzmppe0, Pzmppe1, Pzmppe2, Pzmppe3, Pzmppe4, Pzmppe5, Pzmppe6, Pzmppe7, PzmppeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Pzmpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatPzmpp : Minimality.H24.SAT.CoreUnsat rowsPzmpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Pzmppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqPzmpp] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
