module

public import Mathlib
public import Minimality.RimCellClosed
public import Minimality.OrthoView
public import Minimality.OrthoView2
public import Minimality.OrthoView3
public import Minimality.OrthoCorner
public import Minimality.QuadCross
public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.Geo.Top

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.T24.TheoremP

variable {x : Fin 7 → ℝ³}

/-- Whether a vertex of Type 24 is one of the three ends `0, 2, 6` of the obtuse corner at `1`. -/
def isEnd (v : Fin 7) : Bool :=
  v == 0 || v == 2 || v == 6

/-- Number of transitions from non-end to end along a cycle `c : ZMod k → Fin 7`. -/
def countEndTransitions {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : ℕ :=
  (Finset.univ : Finset (ZMod k)).filter (fun i => !isEnd (c i) && isEnd (c (i + 1))) |>.card

/-- The ends are contiguous along the rim cycle `c` (at most one transition from non-end to end). -/
def isContiguousEnds {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) : Bool :=
  countEndTransitions c ≤ 1

-- ----------------------------------------------------------------------------
-- Canonical Rim Cycles in C (the Orthocentre Silhouette Chamber)
-- ----------------------------------------------------------------------------

/-- Rim 0435 (EVVV): quad diagonal crossing. -/
def c0435 : ZMod 4 → Fin 7 := ![0, 4, 3, 5]
def U0435 : Finset (Fin 9) := {3}
def D0435 : Finset (Fin 9) := {0, 1, 2, 4, 5, 6, 7, 8}

/-- Rim 0234 (EEVV). -/
def c0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
def U0234 : Finset (Fin 9) := {2, 3, 6}
def D0234 : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}

/-- Rim 0235 (EEVV). -/
def c0235 : ZMod 4 → Fin 7 := ![0, 2, 3, 5]
def U0235 : Finset (Fin 9) := {2, 6}
def D0235 : Finset (Fin 9) := {0, 1, 3, 4, 5, 7, 8}

/-- Rim 6043 (EEVV, rotation of 0436). -/
def c6043 : ZMod 4 → Fin 7 := ![6, 0, 4, 3]
def U6043 : Finset (Fin 9) := {4, 8}
def D6043 : Finset (Fin 9) := {0, 1, 2, 3, 5, 6, 7}

/-- Rim 6053 (EEVV, rotation of 0536). -/
def c6053 : ZMod 4 → Fin 7 := ![6, 0, 5, 3]
def U6053 : Finset (Fin 9) := {3, 4, 7}
def D6053 : Finset (Fin 9) := {0, 1, 2, 5, 6, 8}

/-- Rim 6253 (EEVV, rotation of 2536). -/
def c6253 : ZMod 4 → Fin 7 := ![6, 2, 5, 3]
def U6253 : Finset (Fin 9) := {6, 7}
def D6253 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 8}

/-- Rim 6234 (EEVV, rotation of 2346). -/
def c6234 : ZMod 4 → Fin 7 := ![6, 2, 3, 4]
def U6234 : Finset (Fin 9) := {7, 8}
def D6234 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 6}

/-- Rim 0526 (EEEV). -/
def c0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def U0526 : Finset (Fin 9) := {2, 4, 7}
def D0526 : Finset (Fin 9) := {0, 1, 3, 5, 6, 8}

/-- Rim 6402 (EEEV, rotation of 0264). -/
def c6402 : ZMod 4 → Fin 7 := ![6, 4, 0, 2]
def U6402 : Finset (Fin 9) := {2, 4, 7}
def D6402 : Finset (Fin 9) := {0, 1, 3, 5, 6, 8}

/-- Rim 2360 (EEEV, rotation of 0236). -/
def c2360 : ZMod 4 → Fin 7 := ![2, 3, 6, 0]
def U2360 : Finset (Fin 9) := {2, 4, 7}
def D2360 : Finset (Fin 9) := {0, 1, 3, 5, 6, 8}

/-- Rim 26053 (5-rim EEEVV, rotation of 05326). -/
def c26053 : ZMod 5 → Fin 7 := ![2, 6, 0, 5, 3]
def U26053 : Finset (Fin 9) := {1, 2, 5, 6}
def D26053 : Finset (Fin 9) := {3, 4, 7}

/-- Rim 26043 (5-rim EEEVV, rotation of 04326). -/
def c26043 : ZMod 5 → Fin 7 := ![2, 6, 0, 4, 3]
def U26043 : Finset (Fin 9) := {4, 7, 8}
def D26043 : Finset (Fin 9) := {0, 1, 2, 3, 5, 6}

/-- Rim 60234 (5-rim EEEVV, rotation of 02346). -/
def c60234 : ZMod 5 → Fin 7 := ![6, 0, 2, 3, 4]
def U60234 : Finset (Fin 9) := {2, 3, 4, 6}
def D60234 : Finset (Fin 9) := {0, 1, 5, 7, 8}

/-- Rim 02635 (5-rim EEEVV). -/
def c02635 : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 5]
def U02635 : Finset (Fin 9) := {2, 6, 7}
def D02635 : Finset (Fin 9) := {0, 1, 3, 4, 5, 8}

/-- Rim 02634 (5-rim EEEVV). -/
def c02634 : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 4]
def U02634 : Finset (Fin 9) := {2, 3, 7}
def D02634 : Finset (Fin 9) := {0, 1, 4, 5, 6, 8}

/-- Rim 60253 (5-rim EEEVV, rotation of 02536). -/
def c60253 : ZMod 5 → Fin 7 := ![6, 0, 2, 5, 3]
def U60253 : Finset (Fin 9) := {2, 3, 4, 7}
def D60253 : Finset (Fin 9) := {0, 1, 5, 6, 8}

/-- Rim 60534 (5-rim EEVVV, rotation of 05346). -/
def c60534 : ZMod 5 → Fin 7 := ![6, 0, 5, 3, 4]
def U60534 : Finset (Fin 9) := {3, 4}
def D60534 : Finset (Fin 9) := {0, 1, 2, 5, 6, 7, 8}

/-- Rim 62534 (5-rim EEVVV, rotation of 25346). -/
def c62534 : ZMod 5 → Fin 7 := ![6, 2, 5, 3, 4]
def U62534 : Finset (Fin 9) := {6, 7, 8}
def D62534 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5}

/-- Rim 02534 (5-rim EEVVV). -/
def c02534 : ZMod 5 → Fin 7 := ![0, 2, 5, 3, 4]
def U02534 : Finset (Fin 9) := {2, 3}
def D02534 : Finset (Fin 9) := {0, 1, 4, 5, 6, 7, 8}

/-- Rim 026435 (6-rim EEEVVV). -/
def c026435 : ZMod 6 → Fin 7 := ![0, 2, 6, 4, 3, 5]
def U026435 : Finset (Fin 9) := {2, 6, 7, 8}
def D026435 : Finset (Fin 9) := {0, 1, 3, 4, 5}

/-- Rim 602534 (6-rim EEEVVV, rotation of 025346). -/
def c602534 : ZMod 6 → Fin 7 := ![6, 0, 2, 5, 3, 4]
def U602534 : Finset (Fin 9) := {2, 3, 4}
def D602534 : Finset (Fin 9) := {0, 1, 5, 6, 7, 8}

/-- Rim 260435 (6-rim EEEVVV, rotation of 043526). -/
def c260435 : ZMod 6 → Fin 7 := ![2, 6, 0, 4, 3, 5]
def U260435 : Finset (Fin 9) := {4, 6, 7, 8}
def D260435 : Finset (Fin 9) := {0, 1, 2, 3, 5}

-- ----------------------------------------------------------------------------
-- S0xCycUD Certificates and Injective Rims (All by kernel decision)
-- ----------------------------------------------------------------------------

theorem cyc0435 : S0xCycUD s0x_S24 c0435 U0435 D0435 := by decide
theorem cyc0234 : S0xCycUD s0x_S24 c0234 U0234 D0234 := by decide
theorem cyc0235 : S0xCycUD s0x_S24 c0235 U0235 D0235 := by decide
theorem cyc6043 : S0xCycUD s0x_S24 c6043 U6043 D6043 := by decide
theorem cyc6053 : S0xCycUD s0x_S24 c6053 U6053 D6053 := by decide
theorem cyc6253 : S0xCycUD s0x_S24 c6253 U6253 D6253 := by decide
theorem cyc6234 : S0xCycUD s0x_S24 c6234 U6234 D6234 := by decide
theorem cyc0526 : S0xCycUD s0x_S24 c0526 U0526 D0526 := by decide
theorem cyc6402 : S0xCycUD s0x_S24 c6402 U6402 D6402 := by decide
theorem cyc2360 : S0xCycUD s0x_S24 c2360 U2360 D2360 := by decide
theorem cyc26053 : S0xCycUD s0x_S24 c26053 U26053 D26053 := by decide
theorem cyc26043 : S0xCycUD s0x_S24 c26043 U26043 D26043 := by decide
theorem cyc60234 : S0xCycUD s0x_S24 c60234 U60234 D60234 := by decide
theorem cyc02635 : S0xCycUD s0x_S24 c02635 U02635 D02635 := by decide
theorem cyc02634 : S0xCycUD s0x_S24 c02634 U02634 D02634 := by decide
theorem cyc60253 : S0xCycUD s0x_S24 c60253 U60253 D60253 := by decide
theorem cyc60534 : S0xCycUD s0x_S24 c60534 U60534 D60534 := by decide
theorem cyc62534 : S0xCycUD s0x_S24 c62534 U62534 D62534 := by decide
theorem cyc02534 : S0xCycUD s0x_S24 c02534 U02534 D02534 := by decide
theorem cyc026435 : S0xCycUD s0x_S24 c026435 U026435 D026435 := by decide
theorem cyc602534 : S0xCycUD s0x_S24 c602534 U602534 D602534 := by decide
theorem cyc260435 : S0xCycUD s0x_S24 c260435 U260435 D260435 := by decide

theorem inj_c0435 : Function.Injective c0435 := by decide
theorem inj_c0234 : Function.Injective c0234 := by decide
theorem inj_c0235 : Function.Injective c0235 := by decide
theorem inj_c6043 : Function.Injective c6043 := by decide
theorem inj_c6053 : Function.Injective c6053 := by decide
theorem inj_c6253 : Function.Injective c6253 := by decide
theorem inj_c6234 : Function.Injective c6234 := by decide
theorem inj_c0526 : Function.Injective c0526 := by decide
theorem inj_c6402 : Function.Injective c6402 := by decide
theorem inj_c2360 : Function.Injective c2360 := by decide
theorem inj_c26053 : Function.Injective c26053 := by decide
theorem inj_c26043 : Function.Injective c26043 := by decide
theorem inj_c60234 : Function.Injective c60234 := by decide
theorem inj_c02635 : Function.Injective c02635 := by decide
theorem inj_c02634 : Function.Injective c02634 := by decide
theorem inj_c60253 : Function.Injective c60253 := by decide
theorem inj_c60534 : Function.Injective c60534 := by decide
theorem inj_c62534 : Function.Injective c62534 := by decide
theorem inj_c02534 : Function.Injective c02534 := by decide
theorem inj_c026435 : Function.Injective c026435 := by decide
theorem inj_c602534 : Function.Injective c602534 := by decide
theorem inj_c260435 : Function.Injective c260435 := by decide

-- ----------------------------------------------------------------------------
-- Contiguous Ends Verification
-- ----------------------------------------------------------------------------

theorem cont_c0435 : isContiguousEnds c0435 = true := by decide
theorem cont_c0234 : isContiguousEnds c0234 = true := by decide
theorem cont_c0235 : isContiguousEnds c0235 = true := by decide
theorem cont_c6043 : isContiguousEnds c6043 = true := by decide
theorem cont_c6053 : isContiguousEnds c6053 = true := by decide
theorem cont_c6253 : isContiguousEnds c6253 = true := by decide
theorem cont_c6234 : isContiguousEnds c6234 = true := by decide
theorem cont_c0526 : isContiguousEnds c0526 = true := by decide
theorem cont_c6402 : isContiguousEnds c6402 = true := by decide
theorem cont_c2360 : isContiguousEnds c2360 = true := by decide
theorem cont_c26053 : isContiguousEnds c26053 = true := by decide
theorem cont_c26043 : isContiguousEnds c26043 = true := by decide
theorem cont_c60234 : isContiguousEnds c60234 = true := by decide
theorem cont_c02635 : isContiguousEnds c02635 = true := by decide
theorem cont_c02634 : isContiguousEnds c02634 = true := by decide
theorem cont_c60253 : isContiguousEnds c60253 = true := by decide
theorem cont_c60534 : isContiguousEnds c60534 = true := by decide
theorem cont_c62534 : isContiguousEnds c62534 = true := by decide
theorem cont_c02534 : isContiguousEnds c02534 = true := by decide
theorem cont_c026435 : isContiguousEnds c026435 = true := by decide
theorem cont_c602534 : isContiguousEnds c602534 = true := by decide
theorem cont_c260435 : isContiguousEnds c260435 = true := by decide

-- ----------------------------------------------------------------------------
-- Feasible Cell Enumeration in C
-- ----------------------------------------------------------------------------

/-- The feasible rim cells occurring in the orthocentre silhouette chamber `C`. -/
inductive FeasibleCellC where
  | c0435 : FeasibleCellC
  | c0234 : FeasibleCellC
  | c0235 : FeasibleCellC
  | c6043 : FeasibleCellC
  | c6053 : FeasibleCellC
  | c6253 : FeasibleCellC
  | c6234 : FeasibleCellC
  | c0526 : FeasibleCellC
  | c6402 : FeasibleCellC
  | c2360 : FeasibleCellC
  | c26053 : FeasibleCellC
  | c26043 : FeasibleCellC
  | c60234 : FeasibleCellC
  | c02635 : FeasibleCellC
  | c02634 : FeasibleCellC
  | c60253 : FeasibleCellC
  | c60534 : FeasibleCellC
  | c62534 : FeasibleCellC
  | c02534 : FeasibleCellC
  | c026435 : FeasibleCellC
  | c602534 : FeasibleCellC
  | c260435 : FeasibleCellC

/-- A view `u` lies in candidate cell `c`. -/
def InFeasibleCell (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : FeasibleCellC → Prop
  | FeasibleCellC.c0435 => CellAt F U0435 D0435 u
  | FeasibleCellC.c0234 => CellAt F U0234 D0234 u
  | FeasibleCellC.c0235 => CellAt F U0235 D0235 u
  | FeasibleCellC.c6043 => CellAt F U6043 D6043 u
  | FeasibleCellC.c6053 => CellAt F U6053 D6053 u
  | FeasibleCellC.c6253 => CellAt F U6253 D6253 u
  | FeasibleCellC.c6234 => CellAt F U6234 D6234 u
  | FeasibleCellC.c0526 => CellAt F U0526 D0526 u
  | FeasibleCellC.c6402 => CellAt F U6402 D6402 u
  | FeasibleCellC.c2360 => CellAt F U2360 D2360 u
  | FeasibleCellC.c26053 => CellAt F U26053 D26053 u
  | FeasibleCellC.c26043 => CellAt F U26043 D26043 u
  | FeasibleCellC.c60234 => CellAt F U60234 D60234 u
  | FeasibleCellC.c02635 => CellAt F U02635 D02635 u
  | FeasibleCellC.c02634 => CellAt F U02634 D02634 u
  | FeasibleCellC.c60253 => CellAt F U60253 D60253 u
  | FeasibleCellC.c60534 => CellAt F U60534 D60534 u
  | FeasibleCellC.c62534 => CellAt F U62534 D62534 u
  | FeasibleCellC.c02534 => CellAt F U02534 D02534 u
  | FeasibleCellC.c026435 => CellAt F U026435 D026435 u
  | FeasibleCellC.c602534 => CellAt F U602534 D602534 u
  | FeasibleCellC.c260435 => CellAt F U260435 D260435 u

-- ----------------------------------------------------------------------------
-- The Dispatches: Per-Cell Leaves of Theorem P
-- ----------------------------------------------------------------------------

/-- Theorem P dispatch for `c0435` (EVVV / QuadCross). -/
theorem isRupert_of_c0435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0435 D0435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e)
    (d : ℝ³)
    (d1 : (∑ e, y 3 e) = ∑ e, y 4 e → 0 < ⟪x 3 - x 4, d⟫)
    (d3 : (∑ e, y 3 e) = ∑ e, y 5 e → 0 < ⟪x 3 - x 5, d⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_evvv_t24 F (Minimality.H24.SAT.inj_of_fac F) cyc0435 hu p v y hxy hv
    (by linarith) (by linarith) d d1 d3

/-- Theorem P dispatch for EEVV cell `c0234`. -/
theorem isRupert_of_c0234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0234 D0234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c0234 cyc0234 hu p v y hxy hv
    hE0 hE2 hV3 hV4

/-- Theorem P dispatch for EEVV cell `c0235`. -/
theorem isRupert_of_c0235 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0235 D0235 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c0235 cyc0235 hu p v y hxy hv
    hE0 hE2 hV3 hV5

/-- Theorem P dispatch for EEVV cell `c6043`. -/
theorem isRupert_of_c6043 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6043 D6043 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6043 cyc6043 hu p v y hxy hv
    hE6 hE0 hV4 hV3

/-- Theorem P dispatch for EEVV cell `c6053`. -/
theorem isRupert_of_c6053 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6053 D6053 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6053 cyc6053 hu p v y hxy hv
    hE6 hE0 hV5 hV3

/-- Theorem P dispatch for EEVV cell `c6253`. -/
theorem isRupert_of_c6253 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6253 D6253 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6253 cyc6253 hu p v y hxy hv
    hE6 hE2 hV5 hV3

/-- Theorem P dispatch for EEVV cell `c6234`. -/
theorem isRupert_of_c6234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6234 D6234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eevv F (Minimality.H24.SAT.inj_of_fac F) inj_c6234 cyc6234 hu p v y hxy hv
    hE6 hE2 hV3 hV4

/-- Theorem P dispatch for EEEV cell `c0526`. -/
theorem isRupert_of_c0526 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U0526 D0526 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c0526 cyc0526 hu p v y hxy hv
    (show (∑ e, y (c0526 0) e) < ∑ e, y (c0526 1) e by change (∑ e, y 0 e) < ∑ e, y 5 e; linarith)
    (show (∑ e, y (c0526 0) e) = ∑ e, y (c0526 3) e by change (∑ e, y 0 e) = ∑ e, y 6 e; linarith)

/-- Theorem P dispatch for EEEV cell `c6402`. -/
theorem isRupert_of_c6402 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U6402 D6402 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c6402 cyc6402 hu p v y hxy hv
    (show (∑ e, y (c6402 0) e) < ∑ e, y (c6402 1) e by change (∑ e, y 6 e) < ∑ e, y 4 e; linarith)
    (show (∑ e, y (c6402 0) e) = ∑ e, y (c6402 3) e by change (∑ e, y 6 e) = ∑ e, y 2 e; linarith)

/-- Theorem P dispatch for EEEV cell `c2360`. -/
theorem isRupert_of_c2360 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U2360 D2360 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_eeev' F (Minimality.H24.SAT.inj_of_fac F) inj_c2360 cyc2360 hu p v y hxy hv
    (show (∑ e, y (c2360 0) e) < ∑ e, y (c2360 1) e by change (∑ e, y 2 e) < ∑ e, y 3 e; linarith)
    (show (∑ e, y (c2360 0) e) = ∑ e, y (c2360 3) e by change (∑ e, y 2 e) = ∑ e, y 0 e; linarith)

/-- Theorem P dispatch for 5-rim EEEVV cell `c26053`. -/
theorem isRupert_of_c26053 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U26053 D26053 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c26053 cyc26053 hu p v y hxy hv
    hE2 hE6 hE0 hV5 hV3

/-- Theorem P dispatch for 6-rim EEEVVV cell `c026435`. -/
theorem isRupert_of_c026435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U026435 D026435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e)
    (d : ℝ³) (hd10 : 0 < ⟪x 0 - x 2, d⟫) (hd12 : 0 < ⟪x 6 - x 2, d⟫)
    (h34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d⟫))
    (h54 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_6rim F (Minimality.H24.SAT.inj_of_fac F) inj_c026435 cyc026435 hu p v y hxy hv
    hE0 hE2 hE6 hV4 hV5 d hd10 hd12 h34 h54

/-- Theorem P dispatch for 5-rim EEEVV cell `c26043`. -/
theorem isRupert_of_c26043 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U26043 D26043 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c26043 cyc26043 hu p v y hxy hv
    hE2 hE6 hE0 hV4 hV3

/-- Theorem P dispatch for 5-rim EEEVV cell `c60234`. -/
theorem isRupert_of_c60234 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60234 D60234 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c60234 cyc60234 hu p v y hxy hv
    hE6 hE0 hE2 hV3 hV4

/-- Theorem P dispatch for 5-rim EEEVV cell `c02635`. -/
theorem isRupert_of_c02635 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02635 D02635 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV5 : 1 < ∑ e, y 5 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c02635 cyc02635 hu p v y hxy hv
    hE0 hE2 hE6 hV3 hV5

/-- Theorem P dispatch for 5-rim EEEVV cell `c02634`. -/
theorem isRupert_of_c02634 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02634 D02634 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c02634 cyc02634 hu p v y hxy hv
    hE0 hE2 hE6 hV3 hV4

/-- Theorem P dispatch for 5-rim EEEVV cell `c60253`. -/
theorem isRupert_of_c60253 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60253 D60253 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV3 : 1 < ∑ e, y 3 e) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eeevv F (Minimality.H24.SAT.inj_of_fac F) inj_c60253 cyc60253 hu p v y hxy hv
    hE6 hE0 hE2 hV5 hV3

/-- Theorem P dispatch for 5-rim EEVVV cell `c60534`. -/
theorem isRupert_of_c60534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U60534 D60534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e)
    (d : ℝ³) (hd : 0 < ⟪x 6 - x 0, d⟫)
    (h35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eevvv F (Minimality.H24.SAT.inj_of_fac F) inj_c60534 cyc60534 hu p v y hxy hv
    hE6 hE0 hV4 d hd h35

/-- Theorem P dispatch for 5-rim EEVVV cell `c62534`. -/
theorem isRupert_of_c62534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U62534 D62534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e)
    (d : ℝ³) (hd : 0 < ⟪x 6 - x 2, d⟫)
    (h35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eevvv F (Minimality.H24.SAT.inj_of_fac F) inj_c62534 cyc62534 hu p v y hxy hv
    hE6 hE2 hV4 d hd h35

/-- Theorem P dispatch for 5-rim EEVVV cell `c02534`. -/
theorem isRupert_of_c02534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U02534 D02534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e)
    (d : ℝ³) (hd : 0 < ⟪x 0 - x 2, d⟫)
    (h35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_5rim_eevvv F (Minimality.H24.SAT.inj_of_fac F) inj_c02534 cyc02534 hu p v y hxy hv
    hE0 hE2 hV4 d hd h35

/-- Theorem P dispatch for 6-rim EEEVVV cell `c602534`. -/
theorem isRupert_of_c602534 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U602534 D602534 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1)
    (hV5 : 1 < ∑ e, y 5 e) (hV4 : 1 < ∑ e, y 4 e)
    (d : ℝ³) (hd10 : 0 < ⟪x 6 - x 0, d⟫) (hd12 : 0 < ⟪x 2 - x 0, d⟫)
    (h35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫))
    (h34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_6rim F (Minimality.H24.SAT.inj_of_fac F) inj_c602534 cyc602534 hu p v y hxy hv
    hE6 hE0 hE2 hV5 hV4 d hd10 hd12 h35 h34

/-- Theorem P dispatch for 6-rim EEEVVV cell `c260435`. -/
theorem isRupert_of_c260435 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hu : CellAt F U260435 D260435 u) (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1) (hE0 : (∑ e, y 0 e) = 1)
    (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e)
    (d : ℝ³) (hd10 : 0 < ⟪x 2 - x 6, d⟫) (hd12 : 0 < ⟪x 0 - x 6, d⟫)
    (h34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d⟫))
    (h35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_orthocentre_6rim F (Minimality.H24.SAT.inj_of_fac F) inj_c260435 cyc260435 hu p v y hxy hv
    hE2 hE6 hE0 hV4 hV5 d hd10 hd12 h34 h35

-- ----------------------------------------------------------------------------
-- Theorem P (Type 24 End-to-End Dispatch)
-- ----------------------------------------------------------------------------

/-- **Theorem P for Type 24.**
For any solid of Type 24 (`F : S0xFac 9 s0x_S24 x`), with an obtuse corner at vertex 1
represented by edge coordinates `y`, and `u` the orthocentre view (`⟪v e, u⟫ = 1`)
lying in any of the candidate cells of `C` with contiguous ends: `IsRupert (univ.image x)`. -/
theorem theoremP24_of_candidateCell (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (cell : FeasibleCellC) (hcell : InFeasibleCell F u cell)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hv : ∀ e, ⟪v e, u⟫ = 1)
    (hE0 : (∑ e, y 0 e) = 1) (hE2 : (∑ e, y 2 e) = 1) (hE6 : (∑ e, y 6 e) = 1)
    (hV3 : 1 < ∑ e, y 3 e) (hV4 : 1 < ∑ e, y 4 e) (hV5 : 1 < ∑ e, y 5 e)
    (d_0435 : ℝ³)
    (hd_0435_1 : (∑ e, y 3 e) = ∑ e, y 4 e → 0 < ⟪x 3 - x 4, d_0435⟫)
    (hd_0435_3 : (∑ e, y 3 e) = ∑ e, y 5 e → 0 < ⟪x 3 - x 5, d_0435⟫)
    (d_60534 : ℝ³) (hd_60534_01 : 0 < ⟪x 6 - x 0, d_60534⟫)
    (hd_60534_35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_60534⟫))
    (d_62534 : ℝ³) (hd_62534_01 : 0 < ⟪x 6 - x 2, d_62534⟫)
    (hd_62534_35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_62534⟫))
    (d_02534 : ℝ³) (hd_02534_01 : 0 < ⟪x 0 - x 2, d_02534⟫)
    (hd_02534_35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_02534⟫))
    (d_026435 : ℝ³) (hd_026435_10 : 0 < ⟪x 0 - x 2, d_026435⟫) (hd_026435_12 : 0 < ⟪x 6 - x 2, d_026435⟫)
    (hd_026435_34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d_026435⟫))
    (hd_026435_54 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_026435⟫))
    (d_602534 : ℝ³) (hd_602534_10 : 0 < ⟪x 6 - x 0, d_602534⟫) (hd_602534_12 : 0 < ⟪x 2 - x 0, d_602534⟫)
    (hd_602534_35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_602534⟫))
    (hd_602534_34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d_602534⟫))
    (d_260435 : ℝ³) (hd_260435_10 : 0 < ⟪x 2 - x 6, d_260435⟫) (hd_260435_12 : 0 < ⟪x 0 - x 6, d_260435⟫)
    (hd_260435_34 : 0 < ⟪x 3 - x 4, u⟫ ∨ (⟪x 3 - x 4, u⟫ = 0 ∧ 0 < ⟪x 3 - x 4, d_260435⟫))
    (hd_260435_35 : 0 < ⟪x 3 - x 5, u⟫ ∨ (⟪x 3 - x 5, u⟫ = 0 ∧ 0 < ⟪x 3 - x 5, d_260435⟫)) :
    IsRupert (univ.image x) := by
  cases cell with
  | c0435 => exact isRupert_of_c0435 F hcell p v y hxy hv hE0 hV4 hV5 d_0435 hd_0435_1 hd_0435_3
  | c0234 => exact isRupert_of_c0234 F hcell p v y hxy hv hE0 hE2 hV3 hV4
  | c0235 => exact isRupert_of_c0235 F hcell p v y hxy hv hE0 hE2 hV3 hV5
  | c6043 => exact isRupert_of_c6043 F hcell p v y hxy hv hE6 hE0 hV4 hV3
  | c6053 => exact isRupert_of_c6053 F hcell p v y hxy hv hE6 hE0 hV5 hV3
  | c6253 => exact isRupert_of_c6253 F hcell p v y hxy hv hE6 hE2 hV5 hV3
  | c6234 => exact isRupert_of_c6234 F hcell p v y hxy hv hE6 hE2 hV3 hV4
  | c0526 => exact isRupert_of_c0526 F hcell p v y hxy hv hE0 hE6 hV5
  | c6402 => exact isRupert_of_c6402 F hcell p v y hxy hv hE6 hE2 hV4
  | c2360 => exact isRupert_of_c2360 F hcell p v y hxy hv hE2 hE0 hV3
  | c26053 => exact isRupert_of_c26053 F hcell p v y hxy hv hE2 hE6 hE0 hV5 hV3
  | c26043 => exact isRupert_of_c26043 F hcell p v y hxy hv hE2 hE6 hE0 hV4 hV3
  | c60234 => exact isRupert_of_c60234 F hcell p v y hxy hv hE6 hE0 hE2 hV3 hV4
  | c02635 => exact isRupert_of_c02635 F hcell p v y hxy hv hE0 hE2 hE6 hV3 hV5
  | c02634 => exact isRupert_of_c02634 F hcell p v y hxy hv hE0 hE2 hE6 hV3 hV4
  | c60253 => exact isRupert_of_c60253 F hcell p v y hxy hv hE6 hE0 hE2 hV5 hV3
  | c60534 => exact isRupert_of_c60534 F hcell p v y hxy hv hE6 hE0 hV4 d_60534 hd_60534_01 hd_60534_35
  | c62534 => exact isRupert_of_c62534 F hcell p v y hxy hv hE6 hE2 hV4 d_62534 hd_62534_01 hd_62534_35
  | c02534 => exact isRupert_of_c02534 F hcell p v y hxy hv hE0 hE2 hV4 d_02534 hd_02534_01 hd_02534_35
  | c026435 => exact isRupert_of_c026435 F hcell p v y hxy hv hE0 hE2 hE6 hV4 hV5 d_026435 hd_026435_10 hd_026435_12 hd_026435_34 hd_026435_54
  | c602534 => exact isRupert_of_c602534 F hcell p v y hxy hv hE6 hE0 hE2 hV5 hV4 d_602534 hd_602534_10 hd_602534_12 hd_602534_35 hd_602534_34
  | c260435 => exact isRupert_of_c260435 F hcell p v y hxy hv hE2 hE6 hE0 hV4 hV5 d_260435 hd_260435_10 hd_260435_12 hd_260435_34 hd_260435_35

end Minimality.T24.TheoremP
