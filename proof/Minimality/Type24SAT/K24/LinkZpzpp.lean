module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpzpp
public import Minimality.Type24SAT.K24.ChkZpzpp

@[expose] public section

/-!
# Type 24, class zpzpp off `OB1`: core Zpzpp, `CoreUnsat rowsZpzpp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.Lrat

open Minimality.H24T.SAT

theorem Zpzppe0 : (ZpzppCnf.drop (0)).take rowsZpzpp0.length = cnfOfRows [rowsZpzpp0] := by decide +kernel
theorem Zpzppe1 : (ZpzppCnf.drop (0 + rowsZpzpp0.length)).take rowsZpzpp1.length = cnfOfRows [rowsZpzpp1] := by decide +kernel
theorem Zpzppe2 : (ZpzppCnf.drop (0 + rowsZpzpp0.length + rowsZpzpp1.length)).take rowsZpzpp2.length = cnfOfRows [rowsZpzpp2] := by decide +kernel
theorem Zpzppe3 : (ZpzppCnf.drop (0 + rowsZpzpp0.length + rowsZpzpp1.length + rowsZpzpp2.length)).take rowsZpzpp3.length = cnfOfRows [rowsZpzpp3] := by decide +kernel
theorem ZpzppeEnd : ZpzppCnf.drop (0 + rowsZpzpp0.length + rowsZpzpp1.length + rowsZpzpp2.length + rowsZpzpp3.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpzpp, chunk by chunk. -/
theorem cnf_eqZpzpp : cnfOfRows rowsZpzpp = ZpzppCnf := by
  have h := cnfOfRows_of_chkAt rowsZpzpp ZpzppCnf 0 ⟨Zpzppe0, Zpzppe1, Zpzppe2, Zpzppe3, ZpzppeEnd⟩
  simpa using h

end Minimality.H24.SAT.Lrat

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpzpp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpzpp : Minimality.H24.SAT.CoreUnsat rowsZpzpp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.Lrat.Zpzppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.Lrat.cnf_eqZpzpp] at hc
  simp only [Minimality.H24.SAT.Lrat.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
