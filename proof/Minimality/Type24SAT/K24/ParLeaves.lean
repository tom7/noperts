module

public import Minimality.RimCellClosed
public import Minimality.Type24SAT.Geo.Top

@[expose] public section

/-!
# Type 24, parallelogram stratum, obtuse half: the leaves of the cover

Facets `A … I` = indices `0 … 8` of `s0x_S24` (`012, 016, 025, 0345, 046, 126, 235, 236, 346`).
Each leaf is a rim cycle with its up facets `U` and down facets `Dn` (only the facets of the rim edges;
the others are free), stated on any 7 points with the type 24 facet structure (`S0xFac 9 s0x_S24 x`).
No parallelogram, `E ∥ G` / `C ∥ I`, obtuse or off-OB1 hypothesis is used: those only decide *which*
leaf applies.
* `leaf_P0234`, `leaf_P0536`: Q4 leaves (4-rim; `D1` fails at one closed-cell point, `D2` at another).
* `leaf_V04625`, `leaf_V01635`, `leaf_V01234`: vertex leaves (5-rim; robustly unimodal depths at one
  closed-cell point).  The cover's rays are `E^H`, `C^H` (V04625), `G^H`, `A^C` (V01635), `E^I`
  (V01234).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

/-- Rim `0 2 3 4`: edges `02` (A up, C down), `23` (H, G), `34` (I, D), `40` (E, D). -/
def c0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
/-- Rim `0 5 3 6`: edges `05` (C, D), `53` (G, D), `36` (H, I), `60` (B, E). -/
def c0536 : ZMod 4 → Fin 7 := ![0, 5, 3, 6]
/-- Rim `0 4 6 2 5`: edges `04` (E, D), `46` (E, I), `62` (F, H), `25` (C, G), `50` (C, D). -/
def c04625 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
/-- Rim `0 1 6 3 5`: edges `01` (A, B), `16` (F, B), `63` (H, I), `35` (G, D), `50` (C, D). -/
def c01635 : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
/-- Rim `0 1 2 3 4`: edges `01` (A, B), `12` (A, F), `23` (G, H), `34` (D, I), `40` (D, E). -/
def c01234 : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 4]
/-- Rim `0 5 3 2 6`: edges `05` (C, D), `53` (G, D), `32` (G, H), `26` (F, H), `60` (B, E). -/
def c05326 : ZMod 5 → Fin 7 := ![0, 5, 3, 2, 6]

def U0234 : Finset (Fin 9) := {0, 4, 7, 8}
def D0234 : Finset (Fin 9) := {2, 3, 6}
def U0536 : Finset (Fin 9) := {1, 2, 6, 7}
def D0536 : Finset (Fin 9) := {3, 4, 8}
def U04625 : Finset (Fin 9) := {2, 4, 5}
def D04625 : Finset (Fin 9) := {3, 6, 7, 8}
def U01635 : Finset (Fin 9) := {0, 2, 5, 6, 7}
def D01635 : Finset (Fin 9) := {1, 3, 8}
def U01234 : Finset (Fin 9) := {0, 3, 6}
def D01234 : Finset (Fin 9) := {1, 4, 5, 7, 8}
def U05326 : Finset (Fin 9) := {1, 2, 5, 6}
def D05326 : Finset (Fin 9) := {3, 4, 7}

theorem cyc0234 : S0xCycUD s0x_S24 c0234 U0234 D0234 := by decide
theorem cyc0536 : S0xCycUD s0x_S24 c0536 U0536 D0536 := by decide
theorem cyc04625 : S0xCycUD s0x_S24 c04625 U04625 D04625 := by decide
theorem cyc01635 : S0xCycUD s0x_S24 c01635 U01635 D01635 := by decide
theorem cyc01234 : S0xCycUD s0x_S24 c01234 U01234 D01234 := by decide
theorem cyc05326 : S0xCycUD s0x_S24 c05326 U05326 D05326 := by decide

open Minimality.RimCell in
/-- **Leaf P0234** (Q4). -/
theorem leaf_P0234 (F : S0xFac 9 s0x_S24 x) {a g g' : ℝ³} (ha : CellAt F U0234 D0234 a)
    (hg : CellLe F U0234 D0234 g) (hg' : CellLe F U0234 D0234 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0234 p.1) - x (c0234 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0234 p.1) - x (c0234 p.2), g'⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc0234 ha hg hg' hn hp

open Minimality.RimCell in
/-- **Leaf P0536** (Q4). -/
theorem leaf_P0536 (F : S0xFac 9 s0x_S24 x) {a g g' : ℝ³} (ha : CellAt F U0536 D0536 a)
    (hg : CellLe F U0536 D0536 g) (hg' : CellLe F U0536 D0536 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0536 p.1) - x (c0536 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0536 p.1) - x (c0536 p.2), g'⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell_q4 F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc0536 ha hg hg' hn hp

/-- **Leaf V04625** (vertex; rays `E^H` in `E ∥ G`, `C^H` in `C ∥ I`). -/
theorem leaf_V04625 (F : S0xFac 9 s0x_S24 x) {a u : ℝ³} (ha : CellAt F U04625 D04625 a)
    (hu : CellLe F U04625 D04625 u) (hR : RobUni fun i => ⟪x (c04625 i), u⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell (by norm_num) F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc04625 ha hu hR

/-- **Leaf V01635** (vertex; rays `G^H` and `A^C` in `C ∥ I`). -/
theorem leaf_V01635 (F : S0xFac 9 s0x_S24 x) {a u : ℝ³} (ha : CellAt F U01635 D01635 a)
    (hu : CellLe F U01635 D01635 u) (hR : RobUni fun i => ⟪x (c01635 i), u⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell (by norm_num) F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc01635 ha hu hR

/-- **Leaf V01234** (vertex; ray `E^I` in `E ∥ G`). -/
theorem leaf_V01234 (F : S0xFac 9 s0x_S24 x) {a u : ℝ³} (ha : CellAt F U01234 D01234 a)
    (hu : CellLe F U01234 D01234 u) (hR : RobUni fun i => ⟪x (c01234 i), u⟫) :
    IsRupert (univ.image x) :=
  isRupert_of_closedCell (by norm_num) F (Minimality.H24.SAT.inj_of_fac F) (by decide) cyc01234 ha hu hR

end Minimality.T24.Par
