module

public import Minimality.Type24SAT.Geo.LinkBase
public import Minimality.Type24SAT.K24.ProofZpppp
public import Minimality.Type24SAT.K24.ChkZpppp

@[expose] public section

/-!
# Type 24, class zpppp off `OB1`: core Zpppp, `CoreUnsat rowsZpppp` from the kernel-checked LRAT proof
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24.SAT.K24

open Minimality.H24T.SAT

theorem Zppppe0 : (ZppppCnf.drop (0)).take rowsZpppp0.length = cnfOfRows [rowsZpppp0] := by decide +kernel
theorem Zppppe1 : (ZppppCnf.drop (0 + rowsZpppp0.length)).take rowsZpppp1.length = cnfOfRows [rowsZpppp1] := by decide +kernel
theorem Zppppe2 : (ZppppCnf.drop (0 + rowsZpppp0.length + rowsZpppp1.length)).take rowsZpppp2.length = cnfOfRows [rowsZpppp2] := by decide +kernel
theorem Zppppe3 : (ZppppCnf.drop (0 + rowsZpppp0.length + rowsZpppp1.length + rowsZpppp2.length)).take rowsZpppp3.length = cnfOfRows [rowsZpppp3] := by decide +kernel
theorem Zppppe4 : (ZppppCnf.drop (0 + rowsZpppp0.length + rowsZpppp1.length + rowsZpppp2.length + rowsZpppp3.length)).take rowsZpppp4.length = cnfOfRows [rowsZpppp4] := by decide +kernel
theorem Zppppe5 : (ZppppCnf.drop (0 + rowsZpppp0.length + rowsZpppp1.length + rowsZpppp2.length + rowsZpppp3.length + rowsZpppp4.length)).take rowsZpppp5.length = cnfOfRows [rowsZpppp5] := by decide +kernel
theorem ZppppeEnd : ZppppCnf.drop (0 + rowsZpppp0.length + rowsZpppp1.length + rowsZpppp2.length + rowsZpppp3.length + rowsZpppp4.length + rowsZpppp5.length) = [] := by decide +kernel

/-- The checker's input CNF equals the rows of core Zpppp, chunk by chunk. -/
theorem cnf_eqZpppp : cnfOfRows rowsZpppp = ZppppCnf := by
  have h := cnfOfRows_of_chkAt rowsZpppp ZppppCnf 0 ⟨Zppppe0, Zppppe1, Zppppe2, Zppppe3, Zppppe4, Zppppe5, ZppppeEnd⟩
  simpa using h

end Minimality.H24.SAT.K24

namespace Minimality.H24K.SAT
open Minimality.H24T.SAT

/-- **The numbered clauses of core Zpppp are unsatisfiable**, from the kernel-checked LRAT certificate. -/
theorem coreUnsatZpppp : Minimality.H24.SAT.CoreUnsat rowsZpppp := by
  intro ρ hρ
  have h := Minimality.H24.SAT.K24.Zppppunsat ρ
  apply h
  intro c hc
  rw [← Minimality.H24.SAT.K24.cnf_eqZpppp] at hc
  simp only [Minimality.H24.SAT.K24.cnfOfRows, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨ch, hch, n, hn, rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hρ ch hch n hn
  exact ⟨l, hl, hs⟩

end Minimality.H24K.SAT
