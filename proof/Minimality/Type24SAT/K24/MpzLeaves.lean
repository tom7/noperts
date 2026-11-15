module

public import Minimality.Type24SAT.K24.ParLeaves

@[expose] public section

/-!
# Type 24, `mpppz` sub-class (`[2456] = 0`): three more Q4 leaves

Closed-cell Q4 leaves on rims `0 5 2 6`, `2 5 3 6`, `0 1 6 4` of the type 24 facet structure
(`S0xFac 9 s0x_S24 x`), in the form of `leaf_P0234` / `leaf_P0536` (`ParLeaves.lean`).
Only the facets of the rim edges are constrained.  Together with `P0536`, `P0264`, `P0234` they are the
6-leaf menu of the `mpppz` census (`p4/sat/MPPPZLEM.md`): `P0526` closes the 95.6 % level, `P2536` the
walk endpoints, `P0164` the 13 census solids without the first four.
No hypothesis on the shape (`[2456] = 0`, parallelograms, OB1) is used: those only decide which leaf applies.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

/-- Rim `0 5 2 6`: edges `05` (C, D), `52` (C, G), `26` (F, H), `60` (B, E). -/
def c0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
/-- Rim `2 5 3 6`: edges `25` (C, G), `53` (G, D), `36` (H, I), `62` (F, H). -/
def c2536 : ZMod 4 → Fin 7 := ![2, 5, 3, 6]
/-- Rim `0 1 6 4`: edges `01` (A, B), `16` (B, F), `64` (E, I), `40` (E, D). -/
def c0164 : ZMod 4 → Fin 7 := ![0, 1, 6, 4]

def U0526 : Finset (Fin 9) := {1, 2, 5}
def D0526 : Finset (Fin 9) := {3, 4, 6, 7}
def U2536 : Finset (Fin 9) := {6, 7}
def D2536 : Finset (Fin 9) := {2, 3, 5, 8}
def U0164 : Finset (Fin 9) := {1, 4}
def D0164 : Finset (Fin 9) := {0, 3, 5, 8}

theorem cyc0526 : S0xCycUD s0x_S24 c0526 U0526 D0526 := by decide
theorem cyc2536 : S0xCycUD s0x_S24 c2536 U2536 D2536 := by decide
theorem cyc0164 : S0xCycUD s0x_S24 c0164 U0164 D0164 := by decide

open Minimality.RimCell in
/-- **Leaf P0526** (Q4). -/
theorem leaf_P0526 (F : S0xFac 9 s0x_S24 x) {a g g' : ℝ³} (ha : CellAt F U0526 D0526 a)
    (hg : CellLe F U0526 D0526 g) (hg' : CellLe F U0526 D0526 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0526 p.1) - x (c0526 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0526 p.1) - x (c0526 p.2), g'⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc0526 ha hg hg' hn hp

open Minimality.RimCell in
/-- **Leaf P2536** (Q4). -/
theorem leaf_P2536 (F : S0xFac 9 s0x_S24 x) {a g g' : ℝ³} (ha : CellAt F U2536 D2536 a)
    (hg : CellLe F U2536 D2536 g) (hg' : CellLe F U2536 D2536 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c2536 p.1) - x (c2536 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c2536 p.1) - x (c2536 p.2), g'⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc2536 ha hg hg' hn hp

open Minimality.RimCell in
/-- **Leaf P0164** (Q4). -/
theorem leaf_P0164 (F : S0xFac 9 s0x_S24 x) {a g g' : ℝ³} (ha : CellAt F U0164 D0164 a)
    (hg : CellLe F U0164 D0164 g) (hg' : CellLe F U0164 D0164 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0164 p.1) - x (c0164 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0164 p.1) - x (c0164 p.2), g'⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc0164 ha hg hg' hn hp

end Minimality.T24.Par
