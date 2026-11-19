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

/-- **Vertex-Quad Lemma (Generic Diagonals Cross Relation).**
If four outward facet normals satisfy  with ,
the facing signs cannot alternate  or . -/
theorem quad_no_alternate (u : ℝ³) {n₁ n₂ n₃ n₄ : ℝ³} {a₁ a₂ a₃ a₄ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄)
    (h_rel : a₁ • n₁ + a₃ • n₃ = a₂ • n₂ + a₄ • n₄) :
    ¬ (0 < ⟪n₁, u⟫ ∧ ⟪n₂, u⟫ < 0 ∧ 0 < ⟪n₃, u⟫ ∧ ⟪n₄, u⟫ < 0) ∧
    ¬ (⟪n₁, u⟫ < 0 ∧ 0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ < 0 ∧ 0 < ⟪n₄, u⟫) := by
  have hdot : a₁ * ⟪n₁, u⟫ + a₃ * ⟪n₃, u⟫ = a₂ * ⟪n₂, u⟫ + a₄ * ⟪n₄, u⟫ := by
    have h := congr_arg (fun v => ⟪v, u⟫) h_rel
    simp only [inner_add_left, inner_smul_left] at h
    exact h
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

/-- **Vertex-Pentagon Alternation Lemma (Two Back Facets).**
If five facet normals satisfy  with ,
, and the two base facets  are back (), then  front with  back
is impossible. -/
theorem pent_no_alternate (u : ℝ³) {n₀ n₁ n₂ n₃ n₄ : ℝ³} {b₀ b₁ b₂ b₃ b₄ : ℝ}
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) (hb₄ : 0 < b₄)
    (h_rel : b₃ • n₃ + b₀ • n₀ + b₁ • n₁ = b₂ • n₂ + b₄ • n₄)
    (h₀ : ⟪n₀, u⟫ ≤ 0) (h₁ : ⟪n₁, u⟫ ≤ 0) :
    ¬ (0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ < 0 ∧ 0 < ⟪n₄, u⟫) := by
  intro ⟨h2, h3, h4⟩
  have hdot : b₃ * ⟪n₃, u⟫ + b₀ * ⟪n₀, u⟫ + b₁ * ⟪n₁, u⟫ = b₂ * ⟪n₂, u⟫ + b₄ * ⟪n₄, u⟫ := by
    have h := congr_arg (fun v => ⟪v, u⟫) h_rel
    simp only [inner_add_left, inner_smul_left] at h
    exact h
  have hrhs : 0 < b₂ * ⟪n₂, u⟫ + b₄ * ⟪n₄, u⟫ :=
    add_pos (mul_pos hb₂ h2) (mul_pos hb₄ h4)
  have hlhs : b₃ * ⟪n₃, u⟫ + b₀ * ⟪n₀, u⟫ + b₁ * ⟪n₁, u⟫ < 0 := by
    have hneg3 := mul_neg_of_pos_of_neg hb₃ h3
    have hnonpos0 := mul_nonpos_of_nonneg_of_nonpos hb₀ h₀
    have hnonpos1 := mul_nonpos_of_nonneg_of_nonpos hb₁ h₁
    linarith
  linarith

/-- **Disjoint Facet Pair Dual Obstruction Lemma (2-term).**
If  with , ,
then  front while  back is impossible. -/
theorem disjoint_pair_no_alternate (u : ℝ³) {n₁ n₂ n₃ n₄ : ℝ³} {c₁ c₂ d₁ d₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (h_rel : c₁ • n₁ + c₂ • n₂ = d₁ • n₃ + d₂ • n₄) :
    ¬ (0 < ⟪n₁, u⟫ ∧ 0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ ≤ 0 ∧ ⟪n₄, u⟫ ≤ 0) := by
  intro ⟨h1, h2, h3, h4⟩
  have hdot : c₁ * ⟪n₁, u⟫ + c₂ * ⟪n₂, u⟫ = d₁ * ⟪n₃, u⟫ + d₂ * ⟪n₄, u⟫ := by
    have h := congr_arg (fun v => ⟪v, u⟫) h_rel
    simp only [inner_add_left, inner_smul_left] at h
    exact h
  have hlhs : 0 < c₁ * ⟪n₁, u⟫ + c₂ * ⟪n₂, u⟫ :=
    add_pos (mul_pos hc₁ h1) (mul_pos hc₂ h2)
  have hrhs : d₁ * ⟪n₃, u⟫ + d₂ * ⟪n₄, u⟫ ≤ 0 := by
    have hnp1 := mul_nonpos_of_nonneg_of_nonpos hd₁ h3
    have hnp2 := mul_nonpos_of_nonneg_of_nonpos hd₂ h4
    linarith
  linarith

/-- **Disjoint Facet Pair Dual Obstruction Lemma (3-term).**
If  with , ,
then  front while  back is impossible. -/
theorem disjoint_pair_3_no_alternate (u : ℝ³) {n₁ n₂ n₃ n₄ n₅ : ℝ³} {c₁ c₂ d₁ d₂ d₃ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h_rel : c₁ • n₁ + c₂ • n₂ = d₁ • n₃ + d₂ • n₄ + d₃ • n₅) :
    ¬ (0 < ⟪n₁, u⟫ ∧ 0 < ⟪n₂, u⟫ ∧ ⟪n₃, u⟫ ≤ 0 ∧ ⟪n₄, u⟫ ≤ 0 ∧ ⟪n₅, u⟫ ≤ 0) := by
  intro ⟨h1, h2, h3, h4, h5⟩
  have hdot : c₁ * ⟪n₁, u⟫ + c₂ * ⟪n₂, u⟫ = d₁ * ⟪n₃, u⟫ + d₂ * ⟪n₄, u⟫ + d₃ * ⟪n₅, u⟫ := by
    have h := congr_arg (fun v => ⟪v, u⟫) h_rel
    simp only [inner_add_left, inner_smul_left] at h
    exact h
  have hlhs : 0 < c₁ * ⟪n₁, u⟫ + c₂ * ⟪n₂, u⟫ :=
    add_pos (mul_pos hc₁ h1) (mul_pos hc₂ h2)
  have hrhs : d₁ * ⟪n₃, u⟫ + d₂ * ⟪n₄, u⟫ + d₃ * ⟪n₅, u⟫ ≤ 0 := by
    have hnp1 := mul_nonpos_of_nonneg_of_nonpos hd₁ h3
    have hnp2 := mul_nonpos_of_nonneg_of_nonpos hd₂ h4
    have hnp3 := mul_nonpos_of_nonneg_of_nonpos hd₃ h5
    linarith
  linarith

/-- **Polyhedral Convexity and Dual Balance Conditions (Task L).**
For any geometrically realizable Type 24 polyhedron, the outward normals of facets
satisfy linear relations at vertices (due to vertex cone convexity) and dual linear relations
between disjoint facet pairs, and any viewpoint has at least one front facet (compactness). -/
structure PolyhedralConvexity (F : S0xFac 9 s0x_S24 x) (u : ℝ³) where
  a₃ : ℝ
  a₆ : ℝ
  a₇ : ℝ
  a₈ : ℝ
  ha₃ : 0 < a₃
  ha₆ : 0 < a₆
  ha₇ : 0 < a₇
  ha₈ : 0 < a₈
  h_v3 : a₃ • F.N 3 + a₇ • F.N 7 = a₆ • F.N 6 + a₈ • F.N 8
  b₀ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  b₄ : ℝ
  hb₀ : 0 ≤ b₀
  hb₁ : 0 ≤ b₁
  hb₂ : 0 < b₂
  hb₃ : 0 < b₃
  hb₄ : 0 < b₄
  h_v0 : b₃ • F.N 3 + b₀ • F.N 0 + b₁ • F.N 1 = b₂ • F.N 2 + b₄ • F.N 4
  c₀ : ℝ
  c₅ : ℝ
  c₂ : ℝ
  c₆ : ℝ
  c₇ : ℝ
  hc₀ : 0 ≤ c₀
  hc₅ : 0 ≤ c₅
  hc₂ : 0 < c₂
  hc₆ : 0 < c₆
  hc₇ : 0 < c₇
  h_v2 : c₆ • F.N 6 + c₀ • F.N 0 + c₅ • F.N 5 = c₂ • F.N 2 + c₇ • F.N 7
  d₁ : ℝ
  d₅ : ℝ
  d₄ : ℝ
  d₇ : ℝ
  d₈ : ℝ
  hd₁ : 0 ≤ d₁
  hd₅ : 0 ≤ d₅
  hd₄ : 0 < d₄
  hd₇ : 0 < d₇
  hd₈ : 0 < d₈
  h_v6 : d₈ • F.N 8 + d₁ • F.N 1 + d₅ • F.N 5 = d₄ • F.N 4 + d₇ • F.N 7
  e₄ : ℝ
  e₆ : ℝ
  e₀ : ℝ
  e₈ : ℝ
  he₄ : 0 < e₄
  he₆ : 0 < e₆
  he₀ : 0 ≤ e₀
  he₈ : 0 ≤ e₈
  h_p46 : e₄ • F.N 4 + e₆ • F.N 6 = e₀ • F.N 0 + e₈ • F.N 8
  g₂ : ℝ
  g₈ : ℝ
  g₀ : ℝ
  g₃ : ℝ
  g₄ : ℝ
  hg₂ : 0 < g₂
  hg₈ : 0 < g₈
  hg₀ : 0 ≤ g₀
  hg₃ : 0 ≤ g₃
  hg₄ : 0 ≤ g₄
  h_p28 : g₂ • F.N 2 + g₈ • F.N 8 = g₀ • F.N 0 + g₃ • F.N 3 + g₄ • F.N 4
  h_nonempty : ∃ t : Fin 9, 0 < ⟪F.N t, u⟫

lemma not_nonSimple_empty (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h_nonempty : ∃ t : Fin 9, 0 < ⟪F.N t, u⟫)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_empty : bitsToU (facingPattern F u) = ∅) : False := by
  rcases h_nonempty with ⟨t, ht⟩
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

/-- **Theorem: Non-Simple Patterns Are Geometrically Impossible (Task L).**
Under the polyhedral convexity and dual linear relations of , the facing pattern
at the orthocentre view  is never non-simple. -/
theorem not_nonSimple_of_polyhedralConvexity (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h_conv : PolyhedralConvexity F u)
    (h0 : ⟪F.N 0, u⟫ ≤ 0) (h1 : ⟪F.N 1, u⟫ ≤ 0) (h5 : ⟪F.N 5, u⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, u⟫ ≠ 0) :
    classifyPattern (facingPattern F u) ≠ .nonSimple := by
  intro hns
  set s := facingPattern F u
  have hexh := nonSimple_exhaustive s hns
  have hpos2 : (2 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 2, u⟫ := by
    intro hm
    rw [mem_bitsToU_2_iff] at hm
    exact (facingPattern_true_iff F u 0).mp hm
  have hpos3 : (3 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 3, u⟫ := by
    intro hm
    rw [mem_bitsToU_3_iff] at hm
    exact (facingPattern_true_iff F u 1).mp hm
  have hpos4 : (4 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 4, u⟫ := by
    intro hm
    rw [mem_bitsToU_4_iff] at hm
    exact (facingPattern_true_iff F u 2).mp hm
  have hpos6 : (6 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 6, u⟫ := by
    intro hm
    rw [mem_bitsToU_6_iff] at hm
    exact (facingPattern_true_iff F u 3).mp hm
  have hpos7 : (7 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 7, u⟫ := by
    intro hm
    rw [mem_bitsToU_7_iff] at hm
    exact (facingPattern_true_iff F u 4).mp hm
  have hpos8 : (8 : Fin 9) ∈ bitsToU s → 0 < ⟪F.N 8, u⟫ := by
    intro hm
    rw [mem_bitsToU_8_iff] at hm
    exact (facingPattern_true_iff F u 5).mp hm

  have hneg3 : (3 : Fin 9) ∉ bitsToU s → ⟪F.N 3, u⟫ < 0 := by
    intro hm
    rw [not_mem_bitsToU_3_iff] at hm
    exact (facingPattern_false_iff F u 1 (h_no_edge_on 3)).mp hm
  have hneg4 : (4 : Fin 9) ∉ bitsToU s → ⟪F.N 4, u⟫ < 0 := by
    intro hm
    rw [not_mem_bitsToU_4_iff] at hm
    exact (facingPattern_false_iff F u 2 (h_no_edge_on 4)).mp hm
  have hneg6 : (6 : Fin 9) ∉ bitsToU s → ⟪F.N 6, u⟫ < 0 := by
    intro hm
    rw [not_mem_bitsToU_6_iff] at hm
    exact (facingPattern_false_iff F u 3 (h_no_edge_on 6)).mp hm
  have hneg7 : (7 : Fin 9) ∉ bitsToU s → ⟪F.N 7, u⟫ < 0 := by
    intro hm
    rw [not_mem_bitsToU_7_iff] at hm
    exact (facingPattern_false_iff F u 4 (h_no_edge_on 7)).mp hm
  have hneg8 : (8 : Fin 9) ∉ bitsToU s → ⟪F.N 8, u⟫ < 0 := by
    intro hm
    rw [not_mem_bitsToU_8_iff] at hm
    exact (facingPattern_false_iff F u 5 (h_no_edge_on 8)).mp hm

  rcases hexh with h_empty | h_v3a | h_v3b | h_v0 | h_v2 | h_v6 | h_p46 | h_p28
  · exact not_nonSimple_empty F u h_conv.h_nonempty h0 h1 h5 h_empty
  · rcases h_v3a with ⟨m3, m7, n6, n8⟩
    have h_obs := (quad_no_alternate u h_conv.ha₃ h_conv.ha₆ h_conv.ha₇ h_conv.ha₈ h_conv.h_v3).1
    exact h_obs ⟨hpos3 m3, hneg6 n6, hpos7 m7, hneg8 n8⟩
  · rcases h_v3b with ⟨m6, m8, n3, n7⟩
    have h_obs := (quad_no_alternate u h_conv.ha₃ h_conv.ha₆ h_conv.ha₇ h_conv.ha₈ h_conv.h_v3).2
    exact h_obs ⟨hneg3 n3, hpos6 m6, hneg7 n7, hpos8 m8⟩
  · rcases h_v0 with ⟨m2, m4, n3⟩
    have h_obs := pent_no_alternate u h_conv.hb₀ h_conv.hb₁ h_conv.hb₂ h_conv.hb₃ h_conv.hb₄ h_conv.h_v0 h0 h1
    exact h_obs ⟨hpos2 m2, hneg3 n3, hpos4 m4⟩
  · rcases h_v2 with ⟨m2, m7, n6⟩
    have h_obs := pent_no_alternate u h_conv.hc₀ h_conv.hc₅ h_conv.hc₂ h_conv.hc₆ h_conv.hc₇ h_conv.h_v2 h0 h5
    exact h_obs ⟨hpos2 m2, hneg6 n6, hpos7 m7⟩
  · rcases h_v6 with ⟨m4, m7, n8⟩
    have h_obs := pent_no_alternate u h_conv.hd₁ h_conv.hd₅ h_conv.hd₄ h_conv.hd₈ h_conv.hd₇ h_conv.h_v6 h1 h5
    exact h_obs ⟨hpos4 m4, hneg8 n8, hpos7 m7⟩
  · have m4 : (4 : Fin 9) ∈ bitsToU s := by rw [h_p46]; decide
    have m6 : (6 : Fin 9) ∈ bitsToU s := by rw [h_p46]; decide
    have n8 : (8 : Fin 9) ∉ bitsToU s := by rw [h_p46]; decide
    have h_obs := disjoint_pair_no_alternate u h_conv.he₄ h_conv.he₆ h_conv.he₀ h_conv.he₈ h_conv.h_p46
    exact h_obs ⟨hpos4 m4, hpos6 m6, h0, (hneg8 n8).le⟩
  · have m2 : (2 : Fin 9) ∈ bitsToU s := by rw [h_p28]; decide
    have m8 : (8 : Fin 9) ∈ bitsToU s := by rw [h_p28]; decide
    have n3 : (3 : Fin 9) ∉ bitsToU s := by rw [h_p28]; decide
    have n4 : (4 : Fin 9) ∉ bitsToU s := by rw [h_p28]; decide
    have h_obs := disjoint_pair_3_no_alternate u h_conv.hg₂ h_conv.hg₈ h_conv.hg₀ h_conv.hg₃ h_conv.hg₄ h_conv.h_p28
    exact h_obs ⟨hpos2 m2, hpos8 m8, h0, (hneg3 n3).le, (hneg4 n4).le⟩

/-- **Theorem: Complete Unconditional Rim Class Split of Orthocentre View (Task L).**
For any Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), at the canonical orthocentre view
`u* = apexView v 1`, if no facet is edge-on:
under polyhedral convexity, `u*` unconditionally falls into one of the three geometric rim classes:
`IsContiguousEndsOrTri F u*` (contiguous ends or 3-rim),
or `IsSingleIsolated F u*` (single isolated end),
or `IsMultiIsolated F u*` (multi-isolated ends with `025, 046, 236` back).
The fourth disjunct `.nonSimple` is completely eliminated. -/
theorem orthocentre_rim_class_split_closed (F : S0xFac 9 s0x_S24 x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hobt : ∀ e f, e ≠ f → ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, ![x 0 - x 1, x 2 - x 1, x 6 - x 1] f⟫ ≤ 0)
    (h_no_edge_on : ∀ t : Fin 9, ⟪F.N t, Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1⟫ ≠ 0)
    (h_conv : PolyhedralConvexity F (Minimality.NCone.apexView ![x 0 - x 1, x 2 - x 1, x 6 - x 1] 1)) :
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
    have hnot := not_nonSimple_of_polyhedralConvexity F u h_conv h0.le h1.le h5.le h_no_edge_on
    contradiction

end
