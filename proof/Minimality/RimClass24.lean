module

public import Mathlib
public import Minimality.TheoremP24
public import Minimality.TriangleT

@[expose] public section

/-!
# Rim Class Case Split for Type 24 OB1 Orthocentre Views (Task K)

This module formalizes the exhaustive case split of the canonical orthocentre view
`u* = apexView v 1` for Type 24 OB1 polyhedra (`F : S0xFac 9 s0x_S24 x`, `hli`, `h网`).

## Setting & Geometry
At the orthocentre view `u*`, apex `1` is hidden and all three corner facets `012, 016, 126`
(facets 0, 1, 5) are strictly back (`corner_facets_back`). When no facet is edge-on, the rim
is determined by the facing signs of the other six facets `025, 0345, 046, 235, 236, 346`
(facets 2, 3, 4, 6, 7, 8).

## Exhaustive Classification (64 Sign Patterns)
There are `2^6 = 64` possible sign patterns for the 6 variable facets:
* **Case (a): Contiguous ends or 3-rim cell (28 patterns)**
  - 22 contiguous-end cells (`FeasibleCellC`, from `TheoremP24.lean`)
  - 5 lateral/cap 3-rim cells (one facet front: 2, 4, 6, 7, 8)
  - 1 waist 3-rim cell (`c026 = ![0, 2, 6]`, front set `{2, 3, 4, 6, 7, 8}`)
* **Case (b): Single-isolated end (7 patterns, `LEAFB24.md`)**
  - Rim has exactly 1 isolated end `E`, with two neighbours `V, W` and adjacent ends `E', E''`.
  - `B_0` (isolated end 0): `c04625`, `c043625`, `c046235`
  - `B_2` (isolated end 2): `c05236`, `c052346`
  - `B_6` (isolated end 6): `c02364`, `c025364`
* **Case (c): Multi-isolated ends (4 patterns, `MULTIISO24.md`)**
  - `c046325` (hexagon: `U = {3, 6, 8}`)
  - `c04325` (`U = {3, 6}`)
  - `c04635` (`U = {3, 8}`)
  - `c0435` (`U = {3}`, EVVV 4-rim, also in `FeasibleCellC`)
  - On all four, the three waist/cap facets `025, 046, 236` (facets 2, 4, 7) are strictly back.
* **Unrealizable / Non-simple patterns (26 patterns)**
  - 1 empty pattern (`U = ∅`), impossible on a compact convex polyhedron
  - 20 disconnected front facet sets (e.g. `{2, 4}`, `{6, 8}`)
  - 5 pinched front facet sets with degree 4 vertices (figure-8 self-intersection)

All rim cycles have verified `S0xCycUD` certificates in Lean kernel via `decide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Matrix Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.TheoremP

variable {x : Fin 7 → ℝ³}

-- ----------------------------------------------------------------------------
-- Corner Facets Backness at Orthocentre View
-- ----------------------------------------------------------------------------

/-- The three corner facets `0: {0, 1, 2}`, `1: {0, 1, 6}`, `5: {1, 2, 6}` meeting at apex `1`
are strictly back at the canonical orthocentre view `apexView v 1`. -/
theorem corner_facets_back (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0) :
    let v := ![x 0 - x 1, x 2 - x 1, x 6 - x 1]
    let u := Minimality.NCone.apexView v 1
    ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 5, u⟫ < 0 := by
  intro v u
  have hwpos : ∀ a : Fin 3, 0 < (1 : Fin 3 → ℝ) a := fun _ => by norm_num
  have hcpos : ∀ a, 0 < ((Minimality.NCone.gram3 v)⁻¹ *ᵥ (1 : Fin 3 → ℝ)) a :=
    Minimality.NCone.Hw_pos hli hobt hwpos
  have hu_def : u = ∑ a, ((Minimality.NCone.gram3 v)⁻¹ *ᵥ 1) a • v a := rfl
  rw [hu_def]
  refine ⟨?_, ?_, ?_⟩
  · exact Minimality.T24.Hexagon.facet0_back F v rfl rfl rfl _ (hcpos 2)
  · exact Minimality.T24.Hexagon.facet1_back F v rfl rfl rfl _ (hcpos 1)
  · exact Minimality.T24.Hexagon.facet5_back F v rfl rfl rfl _ (hcpos 0)

-- ----------------------------------------------------------------------------
-- Variable Facets and Facing Pattern
-- ----------------------------------------------------------------------------

/-- The six non-corner facets of Type 24 (`s0x_S24`):
* `0: 2 = {0, 2, 5}` (lateral triangle)
* `1: 3 = {0, 3, 4, 5}` (planar quadrilateral quad G)
* `2: 4 = {0, 4, 6}` (lateral triangle)
* `3: 6 = {2, 3, 5}` (lateral triangle)
* `4: 7 = {2, 3, 6}` (lateral triangle)
* `5: 8 = {3, 4, 6}` (lateral triangle) -/
def varFacets : Fin 6 → Fin 9 := ![2, 3, 4, 6, 7, 8]

/-- The boolean facing signs of the six non-corner facets from viewpoint `u`. -/
noncomputable def facingPattern (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Fin 6 → Bool :=
  fun i => decide (0 < ⟪F.N (varFacets i), u⟫)

theorem facingPattern_true_iff (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (i : Fin 6) :
    facingPattern F u i = true ↔ 0 < ⟪F.N (varFacets i), u⟫ := by
  unfold facingPattern
  exact decide_eq_true_iff

theorem facingPattern_false_iff (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (i : Fin 6)
    (hne : ⟪F.N (varFacets i), u⟫ ≠ 0) :
    facingPattern F u i = false ↔ ⟪F.N (varFacets i), u⟫ < 0 := by
  unfold facingPattern
  rw [decide_eq_false_iff_not]
  constructor
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) hne
  · intro h; exact not_lt.mpr h.le

/-- Given facing signs `b : Fin 6 → Bool`, the set of front facets in `Fin 9`. -/
def bitsToU (b : Fin 6 → Bool) : Finset (Fin 9) :=
  Finset.univ.filter (fun t =>
    (t = 2 ∧ b 0 = true) ∨ (t = 3 ∧ b 1 = true) ∨ (t = 4 ∧ b 2 = true) ∨
    (t = 6 ∧ b 3 = true) ∨ (t = 7 ∧ b 4 = true) ∨ (t = 8 ∧ b 5 = true))

/-- Given facing signs `b : Fin 6 → Bool`, the set of back facets in `Fin 9` (including corner facets 0, 1, 5). -/
def bitsToDn (b : Fin 6 → Bool) : Finset (Fin 9) :=
  Finset.univ \ bitsToU b

theorem bits_partition (b : Fin 6 → Bool) :
    bitsToDn b = Finset.univ \ bitsToU b := rfl

theorem mem_bitsToU_2 (b : Fin 6 → Bool) (h : b 0 = true) : (2 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_2 (b : Fin 6 → Bool) (h : (2 : Fin 9) ∉ bitsToU b) : b 0 = false := by
  cases hb : b 0
  · rfl
  · exfalso; exact h (mem_bitsToU_2 b hb)

theorem mem_bitsToU_3 (b : Fin 6 → Bool) (h : b 1 = true) : (3 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_3 (b : Fin 6 → Bool) (h : (3 : Fin 9) ∉ bitsToU b) : b 1 = false := by
  cases hb : b 1
  · rfl
  · exfalso; exact h (mem_bitsToU_3 b hb)

theorem mem_bitsToU_4 (b : Fin 6 → Bool) (h : b 2 = true) : (4 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_4 (b : Fin 6 → Bool) (h : (4 : Fin 9) ∉ bitsToU b) : b 2 = false := by
  cases hb : b 2
  · rfl
  · exfalso; exact h (mem_bitsToU_4 b hb)

theorem mem_bitsToU_6 (b : Fin 6 → Bool) (h : b 3 = true) : (6 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_6 (b : Fin 6 → Bool) (h : (6 : Fin 9) ∉ bitsToU b) : b 3 = false := by
  cases hb : b 3
  · rfl
  · exfalso; exact h (mem_bitsToU_6 b hb)

theorem mem_bitsToU_7 (b : Fin 6 → Bool) (h : b 4 = true) : (7 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_7 (b : Fin 6 → Bool) (h : (7 : Fin 9) ∉ bitsToU b) : b 4 = false := by
  cases hb : b 4
  · rfl
  · exfalso; exact h (mem_bitsToU_7 b hb)

theorem mem_bitsToU_8 (b : Fin 6 → Bool) (h : b 5 = true) : (8 : Fin 9) ∈ bitsToU b := by
  simp [bitsToU, h]

theorem false_of_not_mem_8 (b : Fin 6 → Bool) (h : (8 : Fin 9) ∉ bitsToU b) : b 5 = false := by
  cases hb : b 5
  · rfl
  · exfalso; exact h (mem_bitsToU_8 b hb)

-- ----------------------------------------------------------------------------
-- Fintype and DecidableEq on FeasibleCellC
-- ----------------------------------------------------------------------------

deriving instance DecidableEq for FeasibleCellC

instance : Fintype FeasibleCellC where
  elems := { .c0435, .c0234, .c0235, .c6043, .c6053, .c6253, .c6234, .c0526,
             .c6402, .c2360, .c26053, .c26043, .c60234, .c02635, .c02634,
             .c60253, .c60534, .c62534, .c02534, .c026435, .c602534, .c260435 }
  complete := by intro x; cases x <;> simp

-- ----------------------------------------------------------------------------
-- Single-Isolated Rims (LEAFB24)
-- ----------------------------------------------------------------------------

/-- The seven single-isolated-end rim classes of Type 24 OB1 (`LEAFB24.md`). -/
inductive SingleIsoRim where
  | c04625   : SingleIsoRim  -- B0: isolated 0, V=4, W=5, E'=6, E''=2, U={3, 6, 7, 8}
  | c043625  : SingleIsoRim  -- B0: isolated 0, V=4, W=5, E'=6, E''=2, U={3, 6, 7}
  | c046235  : SingleIsoRim  -- B0: isolated 0, V=4, W=5, E'=6, E''=2, U={3, 7, 8}
  | c05236   : SingleIsoRim  -- B2: isolated 2, V=5, W=3, E'=0, E''=6, U={3, 4, 6, 8}
  | c052346  : SingleIsoRim  -- B2: isolated 2, V=5, W=3, E'=0, E''=6, U={3, 4, 6}
  | c02364   : SingleIsoRim  -- B6: isolated 6, V=3, W=4, E'=2, E''=0, U={2, 3, 6, 8}
  | c025364  : SingleIsoRim  -- B6: isolated 6, V=3, W=4, E'=2, E''=0, U={2, 3, 8}
deriving DecidableEq

instance : Fintype SingleIsoRim where
  elems := { .c04625, .c043625, .c046235, .c05236, .c052346, .c02364, .c025364 }
  complete := by intro x; cases x <;> simp

/-- Front facet set for each single-isolated rim. -/
def singleIsoU : SingleIsoRim → Finset (Fin 9)
  | .c04625  => {3, 6, 7, 8}
  | .c043625 => {3, 6, 7}
  | .c046235 => {3, 7, 8}
  | .c05236  => {3, 4, 6, 8}
  | .c052346 => {3, 4, 6}
  | .c02364  => {2, 3, 6, 8}
  | .c025364 => {2, 3, 8}

/-- The isolated end vertex E for each single-isolated rim. -/
def singleIsoEnd : SingleIsoRim → Fin 7
  | .c04625 | .c043625 | .c046235 => 0
  | .c05236 | .c052346             => 2
  | .c02364 | .c025364             => 6

/-- The two adjacent ends (E', E'') on the rim. -/
def singleIsoAdjacentEnds : SingleIsoRim → Fin 7 × Fin 7
  | .c04625 | .c043625 | .c046235 => (6, 2)
  | .c05236 | .c052346             => (0, 6)
  | .c02364 | .c025364             => (2, 0)

/-- The two neighbours (V, W) of the isolated end along the rim. -/
def singleIsoNeighbours : SingleIsoRim → Fin 7 × Fin 7
  | .c04625 | .c043625 | .c046235 => (4, 5)
  | .c05236 | .c052346             => (5, 3)
  | .c02364 | .c025364             => (3, 4)

-- Rim cycles:
def c04625   : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
def c043625  : ZMod 6 → Fin 7 := ![0, 4, 3, 6, 2, 5]
def c046235  : ZMod 6 → Fin 7 := ![0, 4, 6, 2, 3, 5]
def c05236   : ZMod 5 → Fin 7 := ![0, 5, 2, 3, 6]
def c052346  : ZMod 6 → Fin 7 := ![0, 5, 2, 3, 4, 6]
def c02364   : ZMod 5 → Fin 7 := ![0, 2, 3, 6, 4]
def c025364  : ZMod 6 → Fin 7 := ![0, 2, 5, 3, 6, 4]

theorem cyc04625  : S0xCycUD s0x_S24 c04625 (singleIsoU .c04625) (Finset.univ \ singleIsoU .c04625) := by decide
theorem cyc043625 : S0xCycUD s0x_S24 c043625 (singleIsoU .c043625) (Finset.univ \ singleIsoU .c043625) := by decide
theorem cyc046235 : S0xCycUD s0x_S24 c046235 (singleIsoU .c046235) (Finset.univ \ singleIsoU .c046235) := by decide
theorem cyc05236  : S0xCycUD s0x_S24 c05236 (singleIsoU .c05236) (Finset.univ \ singleIsoU .c05236) := by decide
theorem cyc052346 : S0xCycUD s0x_S24 c052346 (singleIsoU .c052346) (Finset.univ \ singleIsoU .c052346) := by decide
theorem cyc02364  : S0xCycUD s0x_S24 c02364 (singleIsoU .c02364) (Finset.univ \ singleIsoU .c02364) := by decide
theorem cyc025364 : S0xCycUD s0x_S24 c025364 (singleIsoU .c025364) (Finset.univ \ singleIsoU .c025364) := by decide

theorem inj_c04625  : Function.Injective c04625 := by decide
theorem inj_c043625 : Function.Injective c043625 := by decide
theorem inj_c046235 : Function.Injective c046235 := by decide
theorem inj_c05236  : Function.Injective c05236 := by decide
theorem inj_c052346 : Function.Injective c052346 := by decide
theorem inj_c02364  : Function.Injective c02364 := by decide
theorem inj_c025364 : Function.Injective c025364 := by decide

-- ----------------------------------------------------------------------------
-- Multi-Isolated Rims (MULTIISO24)
-- ----------------------------------------------------------------------------

/-- The four multi-isolated-end rim classes of Type 24 OB1 (`MULTIISO24.md`). -/
inductive MultiIsoRim where
  | c046325 : MultiIsoRim  -- hexagon: U={3, 6, 8}
  | c04325  : MultiIsoRim  -- U={3, 6}
  | c04635  : MultiIsoRim  -- U={3, 8}
  | c0435   : MultiIsoRim  -- U={3} (EVVV, also in FeasibleCellC)
deriving DecidableEq

instance : Fintype MultiIsoRim where
  elems := { .c046325, .c04325, .c04635, .c0435 }
  complete := by intro x; cases x <;> simp

def multiIsoU : MultiIsoRim → Finset (Fin 9)
  | .c046325 => {3, 6, 8}
  | .c04325  => {3, 6}
  | .c04635  => {3, 8}
  | .c0435   => {3}

def c046325 : ZMod 6 → Fin 7 := ![0, 4, 6, 3, 2, 5]
def c04325  : ZMod 5 → Fin 7 := ![0, 4, 3, 2, 5]
def c04635  : ZMod 5 → Fin 7 := ![0, 4, 6, 3, 5]

theorem cyc046325 : S0xCycUD s0x_S24 c046325 (multiIsoU .c046325) (Finset.univ \ multiIsoU .c046325) := by decide
theorem cyc04325  : S0xCycUD s0x_S24 c04325 (multiIsoU .c04325) (Finset.univ \ multiIsoU .c04325) := by decide
theorem cyc04635  : S0xCycUD s0x_S24 c04635 (multiIsoU .c04635) (Finset.univ \ multiIsoU .c04635) := by decide

theorem inj_c046325 : Function.Injective c046325 := by decide
theorem inj_c04325  : Function.Injective c04325 := by decide
theorem inj_c04635  : Function.Injective c04635 := by decide

/-- On all multi-isolated rims, the three waist/cap side facets `025`, `046`, `236`
(facets `2, 4, 7`) are strictly back (`MULTIISO24.md`). -/
theorem multiIso_side_facets_back (r : MultiIsoRim) :
    2 ∉ multiIsoU r ∧ 4 ∉ multiIsoU r ∧ 7 ∉ multiIsoU r := by
  cases r <;> decide

-- ----------------------------------------------------------------------------
-- 3-Rim Cells and Class Predicates
-- ----------------------------------------------------------------------------

/-- A 3-rim cell: one facet front among the 5 lateral/cap triangles, or the waist 3-rim cell `c026`. -/
def Is3RimCell (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  CellAt F {2} (Finset.univ \ {2}) u ∨
  CellAt F {4} (Finset.univ \ {4}) u ∨
  CellAt F {6} (Finset.univ \ {6}) u ∨
  CellAt F {7} (Finset.univ \ {7}) u ∨
  CellAt F {8} (Finset.univ \ {8}) u ∨
  CellAt F {2, 3, 4, 6, 7, 8} (Finset.univ \ {2, 3, 4, 6, 7, 8}) u

/-- Case (a): `u` is in one of the 22 `FeasibleCellC` cells (contiguous ends) of `TheoremP24`,
or in a 3-rim cell. -/
def IsContiguousEndsOrTri (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  (∃ cell : FeasibleCellC, InFeasibleCell F u cell) ∨ Is3RimCell F u

/-- Case (b): `u` is in one of the 7 single-isolated-end rim cells (`LEAFB24.md`). -/
def InSingleIsoCell (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (r : SingleIsoRim) : Prop :=
  CellAt F (singleIsoU r) (Finset.univ \ singleIsoU r) u

def IsSingleIsolated (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ∃ r : SingleIsoRim, InSingleIsoCell F u r

/-- Case (c): `u` is in one of the multi-isolated-end rim cells (`MULTIISO24.md`). -/
def InMultiIsoCell (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (r : MultiIsoRim) : Prop :=
  CellAt F (multiIsoU r) (Finset.univ \ multiIsoU r) u

def IsMultiIsolated (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ∃ r : MultiIsoRim, InMultiIsoCell F u r

-- ----------------------------------------------------------------------------
-- The 64 Sign Vector Enumeration
-- ----------------------------------------------------------------------------

/-- Classification of each of the 64 sign vectors of the 6 non-corner facets. -/
inductive RimClass24 where
  | feasibleC (cell : FeasibleCellC) : RimClass24
  | triFacet  (t : Fin 9)            : RimClass24
  | triWaist                         : RimClass24
  | singleIso (r : SingleIsoRim)     : RimClass24
  | multiIso  (r : MultiIsoRim)      : RimClass24
  | nonSimple                        : RimClass24
deriving DecidableEq

/-- Explicit decision table mapping each of the 64 sign combinations to its rim class. -/
def classifyBits : Bool → Bool → Bool → Bool → Bool → Bool → RimClass24
  | false, false, false, false, false, false => .nonSimple
  | true, false, false, false, false, false => .triFacet 2
  | false, true, false, false, false, false => .feasibleC .c0435
  | true, true, false, false, false, false => .feasibleC .c02534
  | false, false, true, false, false, false => .triFacet 4
  | true, false, true, false, false, false => .nonSimple
  | false, true, true, false, false, false => .feasibleC .c60534
  | true, true, true, false, false, false => .feasibleC .c602534
  | false, false, false, true, false, false => .triFacet 6
  | true, false, false, true, false, false => .feasibleC .c0235
  | false, true, false, true, false, false => .multiIso .c04325
  | true, true, false, true, false, false => .feasibleC .c0234
  | false, false, true, true, false, false => .nonSimple
  | true, false, true, true, false, false => .nonSimple
  | false, true, true, true, false, false => .singleIso .c052346
  | true, true, true, true, false, false => .feasibleC .c60234
  | false, false, false, false, true, false => .triFacet 7
  | true, false, false, false, true, false => .nonSimple
  | false, true, false, false, true, false => .nonSimple
  | true, true, false, false, true, false => .nonSimple
  | false, false, true, false, true, false => .nonSimple
  | true, false, true, false, true, false => .nonSimple
  | false, true, true, false, true, false => .nonSimple
  | true, true, true, false, true, false => .nonSimple
  | false, false, false, true, true, false => .feasibleC .c6253
  | true, false, false, true, true, false => .feasibleC .c02635
  | false, true, false, true, true, false => .singleIso .c043625
  | true, true, false, true, true, false => .feasibleC .c02634
  | false, false, true, true, true, false => .nonSimple
  | true, false, true, true, true, false => .nonSimple
  | false, true, true, true, true, false => .nonSimple
  | true, true, true, true, true, false => .nonSimple
  | false, false, false, false, false, true => .triFacet 8
  | true, false, false, false, false, true => .nonSimple
  | false, true, false, false, false, true => .multiIso .c04635
  | true, true, false, false, false, true => .singleIso .c025364
  | false, false, true, false, false, true => .feasibleC .c6043
  | true, false, true, false, false, true => .nonSimple
  | false, true, true, false, false, true => .feasibleC .c6053
  | true, true, true, false, false, true => .feasibleC .c60253
  | false, false, false, true, false, true => .nonSimple
  | true, false, false, true, false, true => .nonSimple
  | false, true, false, true, false, true => .multiIso .c046325
  | true, true, false, true, false, true => .singleIso .c02364
  | false, false, true, true, false, true => .nonSimple
  | true, false, true, true, false, true => .nonSimple
  | false, true, true, true, false, true => .singleIso .c05236
  | true, true, true, true, false, true => .feasibleC .c2360
  | false, false, false, false, true, true => .feasibleC .c6234
  | true, false, false, false, true, true => .nonSimple
  | false, true, false, false, true, true => .singleIso .c046235
  | true, true, false, false, true, true => .nonSimple
  | false, false, true, false, true, true => .feasibleC .c26043
  | true, false, true, false, true, true => .nonSimple
  | false, true, true, false, true, true => .feasibleC .c26053
  | true, true, true, false, true, true => .nonSimple
  | false, false, false, true, true, true => .feasibleC .c62534
  | true, false, false, true, true, true => .feasibleC .c026435
  | false, true, false, true, true, true => .singleIso .c04625
  | true, true, false, true, true, true => .feasibleC .c6402
  | false, false, true, true, true, true => .feasibleC .c260435
  | true, false, true, true, true, true => .nonSimple
  | false, true, true, true, true, true => .feasibleC .c0526
  | true, true, true, true, true, true => .triWaist

/-- Classification of a facing sign vector `s : Fin 6 → Bool`. -/
def classifyPattern (s : Fin 6 → Bool) : RimClass24 :=
  classifyBits (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)

/-- A pattern is geometrically realizable (simple silhouette cycle) if it is not non-simple. -/
def isRealizablePattern (s : Fin 6 → Bool) : Bool :=
  match classifyPattern s with
  | .nonSimple => false
  | _ => true

theorem classifyBits_exhaustive (b0 b1 b2 b3 b4 b5 : Bool) :
    (∃ cell : FeasibleCellC, classifyBits b0 b1 b2 b3 b4 b5 = .feasibleC cell) ∨
    (∃ t : Fin 9, classifyBits b0 b1 b2 b3 b4 b5 = .triFacet t) ∨
    (classifyBits b0 b1 b2 b3 b4 b5 = .triWaist) ∨
    (∃ r : SingleIsoRim, classifyBits b0 b1 b2 b3 b4 b5 = .singleIso r) ∨
    (∃ r : MultiIsoRim, classifyBits b0 b1 b2 b3 b4 b5 = .multiIso r) ∨
    (classifyBits b0 b1 b2 b3 b4 b5 = .nonSimple) := by
  revert b0 b1 b2 b3 b4 b5
  decide

theorem classifyPattern_exhaustive (s : Fin 6 → Bool) :
    (∃ cell : FeasibleCellC, classifyPattern s = .feasibleC cell) ∨
    (∃ t : Fin 9, classifyPattern s = .triFacet t) ∨
    (classifyPattern s = .triWaist) ∨
    (∃ r : SingleIsoRim, classifyPattern s = .singleIso r) ∨
    (∃ r : MultiIsoRim, classifyPattern s = .multiIso r) ∨
    (classifyPattern s = .nonSimple) := by
  exact classifyBits_exhaustive (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)

theorem classifyPattern_of_realizable (s : Fin 6 → Bool)
    (h_real : isRealizablePattern s = true) :
    (∃ cell : FeasibleCellC, classifyPattern s = .feasibleC cell) ∨
    (∃ t : Fin 9, classifyPattern s = .triFacet t) ∨
    (classifyPattern s = .triWaist) ∨
    (∃ r : SingleIsoRim, classifyPattern s = .singleIso r) ∨
    (∃ r : MultiIsoRim, classifyPattern s = .multiIso r) := by
  revert s h_real
  decide

-- ----------------------------------------------------------------------------
-- Bridge Equivalence between Bit Patterns and Cell Definitions
-- ----------------------------------------------------------------------------

/-- Canonical front facet set `U` for each `FeasibleCellC`. -/
def feasibleCU : FeasibleCellC → Finset (Fin 9)
  | .c0435 => {3}
  | .c0234 => {2, 3, 6}
  | .c0235 => {2, 6}
  | .c6043 => {4, 8}
  | .c6053 => {3, 4, 8}
  | .c6253 => {6, 7}
  | .c6234 => {7, 8}
  | .c0526 => {3, 4, 6, 7, 8}
  | .c6402 => {2, 3, 6, 7, 8}
  | .c2360 => {2, 3, 4, 6, 8}
  | .c26053 => {3, 4, 7, 8}
  | .c26043 => {4, 7, 8}
  | .c60234 => {2, 3, 4, 6}
  | .c02635 => {2, 6, 7}
  | .c02634 => {2, 3, 6, 7}
  | .c60253 => {2, 3, 4, 8}
  | .c60534 => {3, 4}
  | .c62534 => {6, 7, 8}
  | .c02534 => {2, 3}
  | .c026435 => {2, 6, 7, 8}
  | .c602534 => {2, 3, 4}
  | .c260435 => {4, 6, 7, 8}

theorem feasibleC_U_eq (s : Fin 6 → Bool) (cell : FeasibleCellC) :
    classifyPattern s = .feasibleC cell → bitsToU s = feasibleCU cell := by
  revert s cell
  decide

theorem feasibleC_InFeasibleCell_iff (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (cell : FeasibleCellC) :
    CellAt F (feasibleCU cell) (Finset.univ \ feasibleCU cell) u ↔ InFeasibleCell F u cell := by
  cases cell <;> rfl

theorem singleIso_U_eq (s : Fin 6 → Bool) (r : SingleIsoRim) :
    classifyPattern s = .singleIso r → bitsToU s = singleIsoU r := by
  revert s r
  decide

theorem multiIso_U_eq (s : Fin 6 → Bool) (r : MultiIsoRim) :
    classifyPattern s = .multiIso r → bitsToU s = multiIsoU r := by
  revert s r
  decide

theorem triFacet_U_eq (s : Fin 6 → Bool) (t : Fin 9) :
    classifyPattern s = .triFacet t → bitsToU s = {t} := by
  revert s t
  decide

theorem triWaist_U_eq (s : Fin 6 → Bool) :
    classifyPattern s = .triWaist → bitsToU s = {2, 3, 4, 6, 7, 8} := by
  revert s
  decide

theorem triFacet_valid (s : Fin 6 → Bool) (t : Fin 9) :
    classifyPattern s = .triFacet t → t = 2 ∨ t = 4 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by
  revert s t
  decide

theorem cellAt_triWaist_back_eq :
    (Finset.univ \ ({2, 3, 4, 6, 7, 8} : Finset (Fin 9)) : Finset (Fin 9)) = {0, 1, 5} := by decide

-- ----------------------------------------------------------------------------
-- The General Facing Cell Lemma
-- ----------------------------------------------------------------------------

/-- The facing sign pattern of any viewpoint `u` with strict facings defines a valid `CellAt`. -/
theorem cellAt_bits (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h0 : ⟪F.N 0, u⟫ < 0) (h1 : ⟪F.N 1, u⟫ < 0) (h5 : ⟪F.N 5, u⟫ < 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0) :
    CellAt F (bitsToU (facingPattern F u)) (Finset.univ \ bitsToU (facingPattern F u)) u := by
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [bitsToU, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · exact (facingPattern_true_iff F u 0).mp hb
    · exact (facingPattern_true_iff F u 1).mp hb
    · exact (facingPattern_true_iff F u 2).mp hb
    · exact (facingPattern_true_iff F u 3).mp hb
    · exact (facingPattern_true_iff F u 4).mp hb
    · exact (facingPattern_true_iff F u 5).mp hb
  · intro t ht
    rw [Finset.mem_sdiff] at ht
    have ht_not := ht.2
    fin_cases t
    · exact h0
    · exact h1
    · have hf0 := false_of_not_mem_2 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 0 (h_no_edge_on 2)).mp hf0
    · have hf1 := false_of_not_mem_3 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 1 (h_no_edge_on 3)).mp hf1
    · have hf2 := false_of_not_mem_4 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 2 (h_no_edge_on 4)).mp hf2
    · exact h5
    · have hf3 := false_of_not_mem_6 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 3 (h_no_edge_on 6)).mp hf3
    · have hf4 := false_of_not_mem_7 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 4 (h_no_edge_on 7)).mp hf4
    · have hf5 := false_of_not_mem_8 (facingPattern F u) ht_not
      exact (facingPattern_false_iff F u 5 (h_no_edge_on 8)).mp hf5

-- ----------------------------------------------------------------------------
-- Main Theorems (Task K)
-- ----------------------------------------------------------------------------

/-- **Theorem: Complete Case Split of Orthocentre View by Rim Class.**
For any Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), at the canonical orthocentre view
`u* = apexView v 1`, if no facet is edge-on:
either `u*` lies in one of the 22 contiguous-end `FeasibleCellC` cells of `TheoremP24`
or a 3-rim cell, or `u*` lies in one of the 7 single-isolated rim cells,
or `u*` lies in one of the multi-isolated rim cells (with `025, 046, 236` back),
or `facingPattern F u*` is one of the 26 non-simple/unrealizable sign patterns. -/
theorem orthocentre_sign_vector_split (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    IsContiguousEndsOrTri F u ∨
    IsSingleIsolated F u ∨
    IsMultiIsolated F u ∨
    classifyPattern (facingPattern F u) = .nonSimple := by
  set u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
  have ⟨h0, h1, h5⟩ := corner_facets_back F hli hobt
  set s := facingPattern F u
  have hcell : CellAt F (bitsToU s) (Finset.univ \ bitsToU s) u := cellAt_bits F u h0 h1 h5 h_no_edge_on
  rcases classifyPattern_exhaustive s with ⟨cell, hc⟩ | ⟨t, ht⟩ | hw | ⟨r, hr⟩ | ⟨r, hr⟩ | hns
  · have hu := feasibleC_U_eq s cell hc
    rw [hu] at hcell
    have hinf := (feasibleC_InFeasibleCell_iff F u cell).mp hcell
    exact Or.inl (Or.inl ⟨cell, hinf⟩)
  · have hu := triFacet_U_eq s t ht
    rw [hu] at hcell
    have htv := triFacet_valid s t ht
    rcases htv with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inr (Or.inl hcell))
    · exact Or.inl (Or.inr (Or.inr (Or.inl hcell)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hcell))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcell)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcell))))))
  · have hu := triWaist_U_eq s hw
    rw [hu] at hcell
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcell))))))
  · have hu := singleIso_U_eq s r hr
    rw [hu] at hcell
    exact Or.inr (Or.inl ⟨r, hcell⟩)
  · have hu := multiIso_U_eq s r hr
    rw [hu] at hcell
    exact Or.inr (Or.inr (Or.inl ⟨r, hcell⟩))
  · exact Or.inr (Or.inr (Or.inr hns))

/-- **Theorem: Orthocentre View Rim Class Disjunction (Realizable Case).**
Assuming the facing pattern at `u*` is geometrically realizable (i.e. not one of the 26
non-simple/pinched sign patterns):
`u*` is in `IsContiguousEndsOrTri` (contiguous ends or 3-rim),
or `IsSingleIsolated` (single isolated end),
or `IsMultiIsolated` (multi-isolated ends with `025, 046, 236` back). -/
theorem orthocentre_rim_class_split (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0)
    (h_real : isRealizablePattern (facingPattern F (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1)) = true) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    IsContiguousEndsOrTri F u ∨
    IsSingleIsolated F u ∨
    IsMultiIsolated F u := by
  set u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
  have hsplit := orthocentre_sign_vector_split F hli hobt h_no_edge_on
  rcases hsplit with h | h | h | hns
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · unfold isRealizablePattern at h_real
    rw [hns] at h_real
    contradiction

end
