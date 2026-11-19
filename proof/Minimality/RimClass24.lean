module

public import Mathlib
public import Minimality.TheoremP24
public import Minimality.TriangleT
public import Minimality.FrontConnected24

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
open Minimality.T24.FrontConn

namespace Minimality.T24.RimClass

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

theorem mem_bitsToU_iff (b : Fin 6 → Bool) (t : Fin 9) :
    t ∈ bitsToU b ↔
      (t = 2 ∧ b 0 = true) ∨ (t = 3 ∧ b 1 = true) ∨ (t = 4 ∧ b 2 = true) ∨
      (t = 6 ∧ b 3 = true) ∨ (t = 7 ∧ b 4 = true) ∨ (t = 8 ∧ b 5 = true) := by
  simp [bitsToU]

theorem mem_bitsToU_2_iff (b : Fin 6 → Bool) : (2 : Fin 9) ∈ bitsToU b ↔ b 0 = true := by
  simp [mem_bitsToU_iff]

theorem mem_bitsToU_3_iff (b : Fin 6 → Bool) : (3 : Fin 9) ∈ bitsToU b ↔ b 1 = true := by
  simp [mem_bitsToU_iff]

theorem mem_bitsToU_4_iff (b : Fin 6 → Bool) : (4 : Fin 9) ∈ bitsToU b ↔ b 2 = true := by
  simp [mem_bitsToU_iff]

theorem mem_bitsToU_6_iff (b : Fin 6 → Bool) : (6 : Fin 9) ∈ bitsToU b ↔ b 3 = true := by
  simp [mem_bitsToU_iff]

theorem mem_bitsToU_7_iff (b : Fin 6 → Bool) : (7 : Fin 9) ∈ bitsToU b ↔ b 4 = true := by
  simp [mem_bitsToU_iff]

theorem mem_bitsToU_8_iff (b : Fin 6 → Bool) : (8 : Fin 9) ∈ bitsToU b ↔ b 5 = true := by
  simp [mem_bitsToU_iff]

theorem not_mem_bitsToU_2_iff (b : Fin 6 → Bool) : (2 : Fin 9) ∉ bitsToU b ↔ b 0 = false := by
  rw [mem_bitsToU_2_iff, Bool.not_eq_true]

theorem not_mem_bitsToU_3_iff (b : Fin 6 → Bool) : (3 : Fin 9) ∉ bitsToU b ↔ b 1 = false := by
  rw [mem_bitsToU_3_iff, Bool.not_eq_true]

theorem not_mem_bitsToU_4_iff (b : Fin 6 → Bool) : (4 : Fin 9) ∉ bitsToU b ↔ b 2 = false := by
  rw [mem_bitsToU_4_iff, Bool.not_eq_true]

theorem not_mem_bitsToU_6_iff (b : Fin 6 → Bool) : (6 : Fin 9) ∉ bitsToU b ↔ b 3 = false := by
  rw [mem_bitsToU_6_iff, Bool.not_eq_true]

theorem not_mem_bitsToU_7_iff (b : Fin 6 → Bool) : (7 : Fin 9) ∉ bitsToU b ↔ b 4 = false := by
  rw [mem_bitsToU_7_iff, Bool.not_eq_true]

theorem not_mem_bitsToU_8_iff (b : Fin 6 → Bool) : (8 : Fin 9) ∉ bitsToU b ↔ b 5 = false := by
  rw [mem_bitsToU_8_iff, Bool.not_eq_true]

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

-- ----------------------------------------------------------------------------
-- Task L: Elimination of Non-Simple Facing Patterns via Polyhedral Convexity
-- ----------------------------------------------------------------------------

/-- **Exhaustive Decomposition of Non-Simple Facing Patterns (Task L).**
Every non-simple sign pattern  falls into one of 8 geometric cases:
1. Empty front set  (1 pattern: idx 0)
2. Alternates at Vertex 3 with (3, 7) front, (6, 8) back (4 patterns: 18, 19, 22, 23)
3. Alternates at Vertex 3 with (6, 8) front, (3, 7) back (4 patterns: 40, 41, 44, 45)
4. Alternates at Vertex 0 with (2, 4) front, 3 back (7 patterns: 5, 13, 21, 29, 37, 53, 61)
5. Alternates at Vertex 2 with (2, 7) front, 6 back (4 patterns: 17, 49, 51, 55)
6. Alternates at Vertex 6 with (4, 7) front, 8 back (4 patterns: 20, 28, 30, 31)
7. Disjoint triangles {4, 6} = {046, 235} (1 pattern: idx 12)
8. Disjoint triangles {2, 8} = {025, 346} (1 pattern: idx 33)
Total: 1 + 4 + 4 + 7 + 4 + 4 + 1 + 1 = 26 patterns. -/
theorem nonSimple_exhaustive (s : Fin 6 → Bool) (hns : classifyPattern s = .nonSimple) :
    (bitsToU s = ∅) ∨
    (3 ∈ bitsToU s ∧ 7 ∈ bitsToU s ∧ 6 ∉ bitsToU s ∧ 8 ∉ bitsToU s) ∨
    (6 ∈ bitsToU s ∧ 8 ∈ bitsToU s ∧ 3 ∉ bitsToU s ∧ 7 ∉ bitsToU s) ∨
    (2 ∈ bitsToU s ∧ 4 ∈ bitsToU s ∧ 3 ∉ bitsToU s) ∨
    (2 ∈ bitsToU s ∧ 7 ∈ bitsToU s ∧ 6 ∉ bitsToU s) ∨
    (4 ∈ bitsToU s ∧ 7 ∈ bitsToU s ∧ 8 ∉ bitsToU s) ∨
    (bitsToU s = {4, 6}) ∨
    (bitsToU s = {2, 8}) := by
  revert s hns
  decide

-- ----------------------------------------------------------------------------
-- Task M: Derivation of Vertex Quad Relations and Complete Rim Class Split
-- ----------------------------------------------------------------------------

theorem ip_expand (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

def dt3 (a b c : ℝ³) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- **Lemma V3** (Generic vertex figure relation at a 4-valent vertex):
Four outward facet normals `A, B, C, D` in cyclic order around a vertex, with edges
`e₁ = A ∩ B`, `e₂ = B ∩ C`, `e₃ = C ∩ D` strictly beneath the other facets,
satisfy the diagonals crossing relation `k₁ A + k₃ C = k₂ B + k₄ D` with all `kᵢ > 0`. -/
theorem v_quad_3d {A B C D e1 e2 e3 : ℝ³} (h1A : ⟪A, e1⟫ = 0) (h1B : ⟪B, e1⟫ = 0)
    (h1C : ⟪C, e1⟫ < 0) (h1D : ⟪D, e1⟫ < 0) (h2B : ⟪B, e2⟫ = 0) (h2C : ⟪C, e2⟫ = 0)
    (h2A : ⟪A, e2⟫ < 0) (h2D : ⟪D, e2⟫ < 0) (h3C : ⟪C, e3⟫ = 0) (h3D : ⟪D, e3⟫ = 0)
    (h3A : ⟪A, e3⟫ < 0) (h3B : ⟪B, e3⟫ < 0) :
    ∃ k1 k2 k3 k4 : ℝ, 0 < k1 ∧ 0 < k2 ∧ 0 < k3 ∧ 0 < k4 ∧
      ∀ w : ℝ³, k1 * ⟪A, w⟫ + k3 * ⟪C, w⟫ = k2 * ⟪B, w⟫ + k4 * ⟪D, w⟫ := by
  set lA := dt3 B C D
  set lB := -dt3 A C D
  set lC := dt3 A B D
  set lD := -dt3 A B C
  have rel : ∀ w : ℝ³, lA * ⟪A, w⟫ + lB * ⟪B, w⟫ + lC * ⟪C, w⟫ + lD * ⟪D, w⟫ = 0 := by
    intro w; simp only [lA, lB, lC, lD, ip_expand, dt3]; ring
  have cb : lA * dt3 e2 e3 e1 =
      ⟪B, e2⟫ * (⟪C, e3⟫ * ⟪D, e1⟫ - ⟪C, e1⟫ * ⟪D, e3⟫) -
        ⟪B, e3⟫ * (⟪C, e2⟫ * ⟪D, e1⟫ - ⟪C, e1⟫ * ⟪D, e2⟫) +
        ⟪B, e1⟫ * (⟪C, e2⟫ * ⟪D, e3⟫ - ⟪C, e3⟫ * ⟪D, e2⟫) := by
    simp only [lA, ip_expand, dt3]; ring
  rw [h2B, h2C, h3C, h3D, h1B] at cb
  have hneg : lA * dt3 e2 e3 e1 < 0 := by
    rw [cb]; nlinarith [mul_pos (mul_pos_of_neg_of_neg h3B h1C) (neg_pos.2 h2D)]
  have hlA : lA ≠ 0 := by rintro h; rw [h, zero_mul] at hneg; exact lt_irrefl _ hneg
  have r1 := rel e1
  have r2 := rel e2
  have r3 := rel e3
  rw [h1A, h1B] at r1
  rw [h2B, h2C] at r2
  rw [h3C, h3D] at r3
  rcases lt_or_gt_of_ne hlA with h | h
  · have hD : 0 < lD := by nlinarith
    have hB : 0 < lB := by nlinarith
    have hC : lC < 0 := by nlinarith
    refine ⟨-lA, lB, -lC, lD, by linarith, hB, by linarith, hD, fun w => ?_⟩
    linear_combination -(rel w)
  · have hD : lD < 0 := by nlinarith
    have hB : lB < 0 := by nlinarith
    have hC : 0 < lC := by nlinarith
    refine ⟨lA, -lB, lC, -lD, h, by linarith, hC, by linarith, fun w => ?_⟩
    linear_combination rel w

/-- **Vertex 3 Quad Relation (Task M).**
At quad vertex 3, the outward facet normals of 3, 6, 7, 8 satisfy
`a₃ N₃ + a₇ N₇ = a₆ N₆ + a₈ N₈` with all `aᵢ > 0`. -/
theorem vertex3_quad_relation (F : S0xFac 9 s0x_S24 x) :
    ∃ (a₃ a₆ a₇ a₈ : ℝ), 0 < a₃ ∧ 0 < a₆ ∧ 0 < a₇ ∧ 0 < a₈ ∧
      ∀ w, a₃ * ⟪F.N 3, w⟫ + a₇ * ⟪F.N 7, w⟫ = a₆ * ⟪F.N 6, w⟫ + a₈ * ⟪F.N 8, w⟫ := by
  have z : ∀ t : Fin 9, ∀ i j : Fin 7, i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 :=
    fun t i j hi hj => perp24 F t i j hi hj
  have ng : ∀ t : Fin 9, ∀ i : Fin 7, i ∉ s0x_S24 t → (3 : Fin 7) ∈ s0x_S24 t →
      ⟪F.N t, x i - x 3⟫ < 0 := by
    intro t i hi h3; rw [F.inner_sub, F.zero t 3 h3]; linarith [F.neg t i hi]
  obtain ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩ := v_quad_3d (A := F.N 3) (B := F.N 6) (C := F.N 7)
    (D := F.N 8) (e1 := x 5 - x 3) (e2 := x 2 - x 3) (e3 := x 6 - x 3)
    (z 3 5 3 (by decide) (by decide)) (z 6 5 3 (by decide) (by decide)) (ng 7 5 (by decide) (by decide))
    (ng 8 5 (by decide) (by decide)) (z 6 2 3 (by decide) (by decide)) (z 7 2 3 (by decide) (by decide))
    (ng 3 2 (by decide) (by decide)) (ng 8 2 (by decide) (by decide)) (z 7 6 3 (by decide) (by decide))
    (z 8 6 3 (by decide) (by decide)) (ng 3 6 (by decide) (by decide)) (ng 6 6 (by decide) (by decide))
  exact ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩

/-- **Vertex 0 Quad Relation (Task M).**
At degree-5 vertex 0, dropping facet 0 gives the cyclic 4-tuple 1, 4, 3, 2, satisfying
`b₁ N₁ + b₃ N₃ = b₂ N₂ + b₄ N₄` with all `bᵢ > 0`. -/
theorem vertex0_quad_relation (F : S0xFac 9 s0x_S24 x) :
    ∃ (b₁ b₂ b₃ b₄ : ℝ), 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧ 0 < b₄ ∧
      ∀ w, b₁ * ⟪F.N 1, w⟫ + b₃ * ⟪F.N 3, w⟫ = b₂ * ⟪F.N 2, w⟫ + b₄ * ⟪F.N 4, w⟫ := by
  have z : ∀ t : Fin 9, ∀ i j : Fin 7, i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 :=
    fun t i j hi hj => perp24 F t i j hi hj
  have ng : ∀ t : Fin 9, ∀ i : Fin 7, i ∉ s0x_S24 t → (0 : Fin 7) ∈ s0x_S24 t →
      ⟪F.N t, x i - x 0⟫ < 0 := by
    intro t i hi h0; rw [F.inner_sub, F.zero t 0 h0]; linarith [F.neg t i hi]
  obtain ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩ := v_quad_3d (A := F.N 1) (B := F.N 4) (C := F.N 3)
    (D := F.N 2) (e1 := x 6 - x 0) (e2 := x 4 - x 0) (e3 := x 5 - x 0)
    (z 1 6 0 (by decide) (by decide)) (z 4 6 0 (by decide) (by decide)) (ng 3 6 (by decide) (by decide))
    (ng 2 6 (by decide) (by decide)) (z 4 4 0 (by decide) (by decide)) (z 3 4 0 (by decide) (by decide))
    (ng 1 4 (by decide) (by decide)) (ng 2 4 (by decide) (by decide)) (z 3 5 0 (by decide) (by decide))
    (z 2 5 0 (by decide) (by decide)) (ng 1 5 (by decide) (by decide)) (ng 4 5 (by decide) (by decide))
  refine ⟨K1, K4, K3, K2, hK1, hK4, hK3, hK2, fun w => ?_⟩
  have h := hrel w
  linarith

/-- **Vertex 2 Quad Relation (Task M).**
At degree-5 vertex 2, dropping facet 5 gives the cyclic 4-tuple 0, 2, 6, 7, satisfying
`c₀ N₀ + c₆ N₆ = c₂ N₂ + c₇ N₇` with all `cᵢ > 0`. -/
theorem vertex2_quad_relation (F : S0xFac 9 s0x_S24 x) :
    ∃ (c₀ c₂ c₆ c₇ : ℝ), 0 < c₀ ∧ 0 < c₂ ∧ 0 < c₆ ∧ 0 < c₇ ∧
      ∀ w, c₀ * ⟪F.N 0, w⟫ + c₆ * ⟪F.N 6, w⟫ = c₂ * ⟪F.N 2, w⟫ + c₇ * ⟪F.N 7, w⟫ := by
  have z : ∀ t : Fin 9, ∀ i j : Fin 7, i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 :=
    fun t i j hi hj => perp24 F t i j hi hj
  have ng : ∀ t : Fin 9, ∀ i : Fin 7, i ∉ s0x_S24 t → (2 : Fin 7) ∈ s0x_S24 t →
      ⟪F.N t, x i - x 2⟫ < 0 := by
    intro t i hi h2; rw [F.inner_sub, F.zero t 2 h2]; linarith [F.neg t i hi]
  obtain ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩ := v_quad_3d (A := F.N 0) (B := F.N 2) (C := F.N 6)
    (D := F.N 7) (e1 := x 0 - x 2) (e2 := x 5 - x 2) (e3 := x 3 - x 2)
    (z 0 0 2 (by decide) (by decide)) (z 2 0 2 (by decide) (by decide)) (ng 6 0 (by decide) (by decide))
    (ng 7 0 (by decide) (by decide)) (z 2 5 2 (by decide) (by decide)) (z 6 5 2 (by decide) (by decide))
    (ng 0 5 (by decide) (by decide)) (ng 7 5 (by decide) (by decide)) (z 6 3 2 (by decide) (by decide))
    (z 7 3 2 (by decide) (by decide)) (ng 0 3 (by decide) (by decide)) (ng 2 3 (by decide) (by decide))
  exact ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩

/-- **Vertex 6 Quad Relation (Task M).**
At degree-5 vertex 6, dropping facet 5 gives the cyclic 4-tuple 1, 4, 8, 7, satisfying
`d₁ N₁ + d₈ N₈ = d₄ N₄ + d₇ N₇` with all `dᵢ > 0`. -/
theorem vertex6_quad_relation (F : S0xFac 9 s0x_S24 x) :
    ∃ (d₁ d₄ d₇ d₈ : ℝ), 0 < d₁ ∧ 0 < d₄ ∧ 0 < d₇ ∧ 0 < d₈ ∧
      ∀ w, d₁ * ⟪F.N 1, w⟫ + d₈ * ⟪F.N 8, w⟫ = d₄ * ⟪F.N 4, w⟫ + d₇ * ⟪F.N 7, w⟫ := by
  have z : ∀ t : Fin 9, ∀ i j : Fin 7, i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 :=
    fun t i j hi hj => perp24 F t i j hi hj
  have ng : ∀ t : Fin 9, ∀ i : Fin 7, i ∉ s0x_S24 t → (6 : Fin 7) ∈ s0x_S24 t →
      ⟪F.N t, x i - x 6⟫ < 0 := by
    intro t i hi h6; rw [F.inner_sub, F.zero t 6 h6]; linarith [F.neg t i hi]
  obtain ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩ := v_quad_3d (A := F.N 1) (B := F.N 4) (C := F.N 8)
    (D := F.N 7) (e1 := x 0 - x 6) (e2 := x 4 - x 6) (e3 := x 3 - x 6)
    (z 1 0 6 (by decide) (by decide)) (z 4 0 6 (by decide) (by decide)) (ng 8 0 (by decide) (by decide))
    (ng 7 0 (by decide) (by decide)) (z 4 4 6 (by decide) (by decide)) (z 8 4 6 (by decide) (by decide))
    (ng 1 4 (by decide) (by decide)) (ng 7 4 (by decide) (by decide)) (z 8 3 6 (by decide) (by decide))
    (z 7 3 6 (by decide) (by decide)) (ng 1 3 (by decide) (by decide)) (ng 4 3 (by decide) (by decide))
  exact ⟨K1, K2, K4, K3, hK1, hK2, hK4, hK3, hrel⟩

/-- **Local Vertex Cone Convexity Relations (Task M).**
Every Type 24 polyhedron unconditionally satisfies positive quad balance relations
at vertices 3, 0, 2, 6. -/
def VertexConvexity (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ a₃ a₆ a₇ a₈ : ℝ, 0 < a₃ ∧ 0 < a₆ ∧ 0 < a₇ ∧ 0 < a₈ ∧
    ∀ w, a₃ * ⟪F.N 3, w⟫ + a₇ * ⟪F.N 7, w⟫ = a₆ * ⟪F.N 6, w⟫ + a₈ * ⟪F.N 8, w⟫) ∧
  (∃ b₁ b₂ b₃ b₄ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧ 0 < b₄ ∧
    ∀ w, b₁ * ⟪F.N 1, w⟫ + b₃ * ⟪F.N 3, w⟫ = b₂ * ⟪F.N 2, w⟫ + b₄ * ⟪F.N 4, w⟫) ∧
  (∃ c₀ c₂ c₆ c₇ : ℝ, 0 < c₀ ∧ 0 < c₂ ∧ 0 < c₆ ∧ 0 < c₇ ∧
    ∀ w, c₀ * ⟪F.N 0, w⟫ + c₆ * ⟪F.N 6, w⟫ = c₂ * ⟪F.N 2, w⟫ + c₇ * ⟪F.N 7, w⟫) ∧
  (∃ d₁ d₄ d₇ d₈ : ℝ, 0 < d₁ ∧ 0 < d₄ ∧ 0 < d₇ ∧ 0 < d₈ ∧
    ∀ w, d₁ * ⟪F.N 1, w⟫ + d₈ * ⟪F.N 8, w⟫ = d₄ * ⟪F.N 4, w⟫ + d₇ * ⟪F.N 7, w⟫)

/-- **Theorem: Vertex Convexity Holds for All Type 24 Polyhedra (Task M).** -/
theorem vertexConvexity (F : S0xFac 9 s0x_S24 x) : VertexConvexity F :=
  ⟨vertex3_quad_relation F, vertex0_quad_relation F, vertex2_quad_relation F, vertex6_quad_relation F⟩

/-- **Vertex-Quad Alternation Lemma (Generic Diagonals Cross Relation).**
If four outward facet normals satisfy `a₁ N₁ + a₃ N₃ = a₂ N₂ + a₄ N₄` with all `aᵢ > 0`,
the facing signs cannot alternate (1, 3 front and 2, 4 back, or vice versa). -/
theorem quad_no_alternate (u : ℝ³) {n₁ n₂ n₃ n₄ : ℝ³} {a₁ a₂ a₃ a₄ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄)
    (h_rel : ∀ w, a₁ * ⟪n₁, w⟫ + a₃ * ⟪n₃, w⟫ = a₂ * ⟪n₂, w⟫ + a₄ * ⟪n₄, w⟫) :
    ¬ (0 < ⟪n₁, u⟫ ∧ ⟪n₂, u⟫ < 0 ∧ 0 < ⟪n₃, u⟫ ∧ ⟪n₄, u⟫ < 0) ∧
    ¬ (⟪n₁, u⟫ < 0 ∧ 0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ < 0 ∧ 0 < ⟪n₄, u⟫) := by
  have hdot := h_rel u
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hpos : 0 < a₁ * ⟪n₁, u⟫ + a₃ * ⟪n₃, u⟫ :=
      add_pos (mul_pos ha₁ h1) (mul_pos ha₃ h3)
    have hneg : a₂ * ⟪n₂, u⟫ + a₄ * ⟪n₄, u⟫ < 0 :=
      add_neg (mul_neg_of_pos_of_neg ha₂ h2) (mul_neg_of_pos_of_neg ha₄ h4)
    linarith
  · rintro ⟨h1, h2, h3, h4⟩
    have hneg : a₁ * ⟪n₁, u⟫ + a₃ * ⟪n₃, u⟫ < 0 :=
      add_neg (mul_neg_of_pos_of_neg ha₁ h1) (mul_neg_of_pos_of_neg ha₃ h3)
    have hpos : 0 < a₂ * ⟪n₂, u⟫ + a₄ * ⟪n₄, u⟫ :=
      add_pos (mul_pos ha₂ h2) (mul_pos ha₄ h4)
    linarith

/-- **Quad Alternation Lemma with Corner Facet Back.**
If `b₁ N₁ + b₃ N₃ = b₂ N₂ + b₄ N₄` with all `bᵢ > 0`, and corner facet `n₁` is back (`⟪n₁, u⟫ ≤ 0`),
then `n₂` and `n₄` front while `n₃` back is impossible. -/
theorem quad_corner_no_alternate (u : ℝ³) {n₁ n₂ n₃ n₄ : ℝ³} {b₁ b₂ b₃ b₄ : ℝ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) (hb₄ : 0 < b₄)
    (h_rel : ∀ w, b₁ * ⟪n₁, w⟫ + b₃ * ⟪n₃, w⟫ = b₂ * ⟪n₂, w⟫ + b₄ * ⟪n₄, w⟫)
    (h₁ : ⟪n₁, u⟫ ≤ 0) :
    ¬ (0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ < 0 ∧ 0 < ⟪n₄, u⟫) := by
  intro ⟨h2, h3, h4⟩
  have hdot := h_rel u
  have hrhs : 0 < b₂ * ⟪n₂, u⟫ + b₄ * ⟪n₄, u⟫ :=
    add_pos (mul_pos hb₂ h2) (mul_pos hb₄ h4)
  have hlhs : b₁ * ⟪n₁, u⟫ + b₃ * ⟪n₃, u⟫ < 0 := by
    have hneg3 := mul_neg_of_pos_of_neg hb₃ h3
    have hnonpos1 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb₁) h₁
    linarith
  linarith

lemma not_nonSimple_empty (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_empty : bitsToU (facingPattern F u) = ∅) : False := by
  have h_ne : ∃ t : Fin 9, 0 < ⟪F.N t, u⟫ := exists_front F u ⟨0, h_no_edge_on 0⟩
  rcases h_ne with ⟨t, ht⟩
  set s := facingPattern F u
  fin_cases t
  · have h0_pos : 0 < ⟪F.N 0, u⟫ := ht; linarith
  · have h1_pos : 0 < ⟪F.N 1, u⟫ := ht; linarith
  · have hm : (2 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_2_iff]
      exact (facingPattern_true_iff F u 0).mpr ht
    rw [h_empty] at hm; cases hm
  · have hm : (3 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_3_iff]
      exact (facingPattern_true_iff F u 1).mpr ht
    rw [h_empty] at hm; cases hm
  · have hm : (4 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_4_iff]
      exact (facingPattern_true_iff F u 2).mpr ht
    rw [h_empty] at hm; cases hm
  · have h5_pos : 0 < ⟪F.N 5, u⟫ := ht; linarith
  · have hm : (6 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_6_iff]
      exact (facingPattern_true_iff F u 3).mpr ht
    rw [h_empty] at hm; cases hm
  · have hm : (7 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_7_iff]
      exact (facingPattern_true_iff F u 4).mpr ht
    rw [h_empty] at hm; cases hm
  · have hm : (8 : Fin 9) ∈ bitsToU s := by
      rw [mem_bitsToU_8_iff]
      exact (facingPattern_true_iff F u 5).mpr ht
    rw [h_empty] at hm; cases hm

/-- **Theorem: All 26 Non-Simple Patterns Are Unrealizable for Any Type 24 Polyhedron.**
For any Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), at any view `u` with no edge-on facets
and corner facets back (e.g. the canonical orthocentre view `u* = apexView v 1`),
the facing pattern is never `.nonSimple`.
- The empty pattern is refuted by Minkowski equilibrium (`exists_front`).
- The 22 alternating patterns are refuted by the local vertex quad relations at vertices 3, 0, 2, 6.
- The two disjoint pairs `{4, 6}` and `{2, 8}` are refuted by isolated front triangles (`not_front46`, `not_front28`).
No compactness, vertex convexity, or disjoint pair hypotheses are assumed. -/
theorem not_nonSimple (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0) :
    classifyPattern (facingPattern F u) ≠ .nonSimple := by
  intro hns
  set s := facingPattern F u
  have hexh := nonSimple_exhaustive s hns
  obtain ⟨a₃, a₆, a₇, a₈, ha₃, ha₆, ha₇, ha₈, h_v3⟩ := vertex3_quad_relation F
  obtain ⟨b₁, b₂, b₃, b₄, hb₁, hb₂, hb₃, hb₄, h_v0⟩ := vertex0_quad_relation F
  obtain ⟨c₀, c₂, c₆, c₇, hc₀, hc₂, hc₆, hc₇, h_v2⟩ := vertex2_quad_relation F
  obtain ⟨d₁, d₄, d₇, d₈, hd₁, hd₄, hd₇, hd₈, h_v6⟩ := vertex6_quad_relation F
  have hpos2 : (2 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 2, u⟫ := by
    intro hm; rw [mem_bitsToU_2_iff] at hm
    exact (facingPattern_true_iff F u 0).mp hm
  have hpos3 : (3 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 3, u⟫ := by
    intro hm; rw [mem_bitsToU_3_iff] at hm
    exact (facingPattern_true_iff F u 1).mp hm
  have hpos4 : (4 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 4, u⟫ := by
    intro hm; rw [mem_bitsToU_4_iff] at hm
    exact (facingPattern_true_iff F u 2).mp hm
  have hpos6 : (6 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 6, u⟫ := by
    intro hm; rw [mem_bitsToU_6_iff] at hm
    exact (facingPattern_true_iff F u 3).mp hm
  have hpos7 : (7 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 7, u⟫ := by
    intro hm; rw [mem_bitsToU_7_iff] at hm
    exact (facingPattern_true_iff F u 4).mp hm
  have hpos8 : (8 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 8, u⟫ := by
    intro hm; rw [mem_bitsToU_8_iff] at hm
    exact (facingPattern_true_iff F u 5).mp hm

  have hneg2 : (2 : Fin 9) ∉ bitsToU s → ⟪F.N 2, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_2_iff] at hm
    exact (facingPattern_false_iff F u 0 (h_no_edge_on 2)).mp hm
  have hneg3 : (3 : Fin 9) ∉ bitsToU s → ⟪F.N 3, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_3_iff] at hm
    exact (facingPattern_false_iff F u 1 (h_no_edge_on 3)).mp hm
  have hneg4 : (4 : Fin 9) ∉ bitsToU s → ⟪F.N 4, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_4_iff] at hm
    exact (facingPattern_false_iff F u 2 (h_no_edge_on 4)).mp hm
  have hneg6 : (6 : Fin 9) ∉ bitsToU s → ⟪F.N 6, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_6_iff] at hm
    exact (facingPattern_false_iff F u 3 (h_no_edge_on 6)).mp hm
  have hneg7 : (7 : Fin 9) ∉ bitsToU s → ⟪F.N 7, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_7_iff] at hm
    exact (facingPattern_false_iff F u 4 (h_no_edge_on 7)).mp hm
  have hneg8 : (8 : Fin 9) ∉ bitsToU s → ⟪F.N 8, u⟫ < 0 := by
    intro hm; rw [not_mem_bitsToU_8_iff] at hm
    exact (facingPattern_false_iff F u 5 (h_no_edge_on 8)).mp hm

  rcases hexh with h_empty | h_v3a | h_v3b | h_v0 | h_v2 | h_v6 | h_p46 | h_p28
  · exact not_nonSimple_empty F u h_no_edge_on h0 h1 h5 h_empty
  · rcases h_v3a with ⟨m3, m7, n6, n8⟩
    have h_obs := (quad_no_alternate u ha₃ ha₆ ha₇ ha₈ h_v3).1
    exact h_obs ⟨hpos3 m3, hneg6 n6, hpos7 m7, hneg8 n8⟩
  · rcases h_v3b with ⟨m6, m8, n3, n7⟩
    have h_obs := (quad_no_alternate u ha₃ ha₆ ha₇ ha₈ h_v3).2
    exact h_obs ⟨hneg3 n3, hpos6 m6, hneg7 n7, hpos8 m8⟩
  · rcases h_v0 with ⟨m2, m4, n3⟩
    have h_obs := quad_corner_no_alternate u hb₁ hb₂ hb₃ hb₄ h_v0 h1
    exact h_obs ⟨hpos2 m2, hneg3 n3, hpos4 m4⟩
  · rcases h_v2 with ⟨m2, m7, n6⟩
    have h_obs := quad_corner_no_alternate u hc₀ hc₂ hc₆ hc₇ h_v2 h0
    exact h_obs ⟨hpos2 m2, hneg6 n6, hpos7 m7⟩
  · rcases h_v6 with ⟨m4, m7, n8⟩
    have h_obs := quad_corner_no_alternate u hd₁ hd₄ hd₈ hd₇ h_v6 h1
    exact h_obs ⟨hpos4 m4, hneg8 n8, hpos7 m7⟩
  · have hm4 : (4 : Fin 9) ∈ bitsToU s := by rw [h_p46]; decide
    have hm6 : (6 : Fin 9) ∈ bitsToU s := by rw [h_p46]; decide
    have hn2 : (2 : Fin 9) ∉ bitsToU s := by rw [h_p46]; decide
    have hn3 : (3 : Fin 9) ∉ bitsToU s := by rw [h_p46]; decide
    have hn7 : (7 : Fin 9) ∉ bitsToU s := by rw [h_p46]; decide
    exact not_front46 F (hpos4 hm4) (hpos6 hm6) (hneg2 hn2) (hneg3 hn3) (hneg7 hn7)
  · have hm2 : (2 : Fin 9) ∈ bitsToU s := by rw [h_p28]; decide
    have hm8 : (8 : Fin 9) ∈ bitsToU s := by rw [h_p28]; decide
    have hn3 : (3 : Fin 9) ∉ bitsToU s := by rw [h_p28]; decide
    have hn6 : (6 : Fin 9) ∉ bitsToU s := by rw [h_p28]; decide
    have h0_neg : ⟪F.N 0, u⟫ < 0 := lt_of_le_of_ne h0 (h_no_edge_on 0)
    exact not_front28 F (hpos2 hm2) (hpos8 hm8) h0_neg (hneg3 hn3) (hneg6 hn6)

/-- Backward-compatible form of `not_nonSimple_of_vertexConvexity`. -/
theorem not_nonSimple_of_vertexConvexity (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (_h_conv : VertexConvexity F)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0)
    (hns : classifyPattern (facingPattern F u) = .nonSimple) : False :=
  not_nonSimple F u h0 h1 h5 h_no_edge_on hns

/-- Backward-compatible form of `not_nonSimple_of_vertexConvexity_closed`. -/
theorem not_nonSimple_of_vertexConvexity_closed (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0) :
    classifyPattern (facingPattern F u) ≠ .nonSimple :=
  not_nonSimple F u h0 h1 h5 h_no_edge_on

/-- **Theorem: Complete Unconditional 3-Way Rim Class Split of Orthocentre View (Task M).**
For any Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), at the canonical orthocentre view
`u* = apexView v 1`, if no facet is edge-on:
`u*` unconditionally falls into one of the three geometric rim classes:
`IsContiguousEndsOrTri F u*` (contiguous ends or 3-rim),
or `IsSingleIsolated F u*` (single isolated end),
or `IsMultiIsolated F u*` (multi-isolated ends with `025, 046, 236` back).
No convexity, FQ, or disjoint pair hypotheses are assumed. -/
theorem orthocentre_rim_class_split_closed (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0) :
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
  · have ⟨h0, h1, h5⟩ := corner_facets_back F hli hobt
    have hnot := not_nonSimple F u h0.le h1.le h5.le h_no_edge_on
    contradiction

/-- Backward-compatible alias for the local rim class split (Task M). -/
theorem orthocentre_rim_class_split_local (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0) :
    let u := Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1
    IsContiguousEndsOrTri F u ∨
    IsSingleIsolated F u ∨
    IsMultiIsolated F u :=
  orthocentre_rim_class_split_closed F hli hobt h_no_edge_on

#print axioms vertex3_quad_relation
#print axioms vertex0_quad_relation
#print axioms vertex2_quad_relation
#print axioms vertex6_quad_relation
#print axioms vertexConvexity
#print axioms not_nonSimple
#print axioms orthocentre_rim_class_split_local
#print axioms orthocentre_rim_class_split_closed

end Minimality.T24.RimClass

end
