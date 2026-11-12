module

public import Minimality.Type24SAT.K24.DataPppppNotP
public import Minimality.Type24SAT.K24.UnitsPppppNotP
public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class ppppp off the obtuse corner `OB1`: the kernel checks of all rows of core PppppNotP (dispatcher `rowK`, class
literals `unitsPppppNotP` and the clause `clauseOB1`)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

/-- The row check of core PppppNotP. -/
def allDPppppNotP (n : Nat) : Bool := rowKs unitsPppppNotP clausesNotP chunksPppppNotP n

/-- Chunk 0 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP0 : (rowsPppppNotP0.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 1 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP1 : (rowsPppppNotP1.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 2 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP2 : (rowsPppppNotP2.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 3 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP3 : (rowsPppppNotP3.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 4 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP4 : (rowsPppppNotP4.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 5 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP5 : (rowsPppppNotP5.all allDPppppNotP) = true := by decide +kernel

/-- Chunk 6 of core PppppNotP: all rows pass. -/
theorem chkPppppNotP6 : (rowsPppppNotP6.all allDPppppNotP) = true := by decide +kernel

/-- Every row of core PppppNotP passes the check. -/
theorem allOKPppppNotP : ∀ ch ∈ rowsPppppNotP, ∀ n ∈ ch, allDPppppNotP n = true := by
  intro ch hch n hn
  simp only [rowsPppppNotP, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp chkPppppNotP0 n hn
  · exact List.all_eq_true.mp chkPppppNotP1 n hn
  · exact List.all_eq_true.mp chkPppppNotP2 n hn
  · exact List.all_eq_true.mp chkPppppNotP3 n hn
  · exact List.all_eq_true.mp chkPppppNotP4 n hn
  · exact List.all_eq_true.mp chkPppppNotP5 n hn
  · exact List.all_eq_true.mp chkPppppNotP6 n hn

variable {x : Fin 7 → ℝ³}

/-- **Core PppppNotP gives Rupert**: if the numbered clauses of core PppppNotP are unsatisfiable, every type 24 shape with the chirality
`[0126] < 0`, the five bracket signs of class pppppnotp and an acute face angle at vertex `1` is Rupert. -/
theorem rupert_of_corePppppNotP (hU : Minimality.H24.SAT.CoreUnsat rowsPppppNotP) (F : S0xFac 9 s0x_S24 x)
    (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (h0 : 0 < det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1))
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : 0 < det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h3 : 0 < det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1))
    (h4 : 0 < det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2))
    (hO : ¬ OB1 x)
    (hP : ¬ (det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  exact hNR (caseKs_of_unsat chunksPppppNotP rowsPppppNotP unitsPppppNotP clausesNotP hU allOKPppppNotP F hchir
    (unitsPppppNotP_true F h0 h1 h2 h3 h4) (clausesNotP_true F hO hP))

end Minimality.H24K.SAT
