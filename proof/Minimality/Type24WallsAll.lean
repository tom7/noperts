module

public import Minimality.Type24CellWallGen

/-!
# Type24WallsAll: all feasible edge-on walls of `cells28` (Task GB)

Mechanically constructed via `cellWallOf` and `wall_cert_or_E` across all 15 cells of `cells28`,
filtered to shared-vertex candidate segments (`a0 = a1 ∨ b0 = b1`) that are `SegLet`-feasible
on the `q82` witness pool (`140` walls total).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic rim-sign scalar and `cert_or_E` helper -/

/-- Canonical rim-sign scalar for cell `c` from a rim-vertex facet `(i, j, t_rim, qv)`. -/
noncomputable def cellRimScalar (c : Cell24) (i j : ZMod c.k) (t_rim : Fin 9) (qv : Fin 7)
    (x : Fin 7 → ℝ³) : ℝ :=
  if t_rim ∈ c.U then
    -Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) (x qv - x (c.r i))
  else
    Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) (x qv - x (c.r i))

/-- **Generic rim sign:** on the open cell `c`, `0 < ρ * cellRimScalar c i j t_rim qv x`. -/
theorem cellRhoOf (F : S0xFac 9 s0x_S24 x) (c : Cell24) (i j : ZMod c.k) (t_rim : Fin 9) (qv : Fin 7)
    (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hi : c.r i ∈ s0x_S24 t_rim) (hi1 : c.r (i + 1) ∈ s0x_S24 t_rim) (hj : c.r j ∈ s0x_S24 t_rim)
    (hqv : qv ∉ s0x_S24 t_rim)
    {w : ℝ³} (hcell : CellAt F c.U (univ \ c.U) w) {ρ : ℝ}
    (hrim : ∀ i' j' : ZMod c.k, j' ≠ i' → j' ≠ i' + 1 →
      0 < ρ * Split.det3 (x (c.r (i' + 1)) - x (c.r i')) (x (c.r j') - x (c.r i')) w) :
    0 < ρ * cellRimScalar c i j t_rim qv x := by
  have hl := hrim i j hji hji1
  have ha : ⟪F.N t_rim, x (c.r (i + 1)) - x (c.r i)⟫ = 0 := by
    rw [F.inner_sub, F.zero t_rim _ hi1, F.zero t_rim _ hi, sub_self]
  have hb : ⟪F.N t_rim, x (c.r j) - x (c.r i)⟫ = 0 := by
    rw [F.inner_sub, F.zero t_rim _ hj, F.zero t_rim _ hi, sub_self]
  have hq : ⟪F.N t_rim, x qv - x (c.r i)⟫ < 0 := by
    rw [F.inner_sub, F.zero t_rim _ hi, sub_zero]
    exact F.neg t_rim qv hqv
  by_cases ht : t_rim ∈ c.U
  · simp only [cellRimScalar, ht, ↓reduceIte, mul_neg]
    have hw : 0 < ⟪F.N t_rim, w⟫ := hcell.1 t_rim ht
    have hneg := rho_of_perp_neg ha hb hl (mul_neg_of_pos_of_neg hw hq)
    linarith
  · simp only [cellRimScalar, ht, ↓reduceIte]
    have hw : ⟪F.N t_rim, w⟫ < 0 := hcell.2 t_rim (mem_sdiff.2 ⟨mem_univ _, ht⟩)
    exact rho_of_perp ha hb hl (mul_pos_of_neg_of_neg hw hq)

/-- **Generic wall cert-or-E** combining `wall_cert_or_E` and `cellRhoOf`. -/
theorem cellWall_cert_or_E (F : S0xFac 9 s0x_S24 x) (c : Cell24)
    (i j : ZMod c.k) (t_rim : Fin 9) (qv : Fin 7)
    (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hi : c.r i ∈ s0x_S24 t_rim) (hi1 : c.r (i + 1) ∈ s0x_S24 t_rim) (hj : c.r j ∈ s0x_S24 t_rim)
    (hqv : qv ∉ s0x_S24 t_rim)
    (W : CellWall F c) :
    Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE F c W (cellRimScalar c i j t_rim qv x) :=
  wall_cert_or_E F c W (fun _ hc _ _ hrim => cellRhoOf F c i j t_rim qv hji hji1 hi hi1 hj hqv hc hrim)

/-! ## All 140 walls of `cells28` -/

noncomputable def wall_cellC_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 1 [(2, false), (3, true), (6, true), (7, false), (8, true)] 0 1 6 1 2 0 (by decide)

def WallE_cellC_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t1_01_61 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t1_01_61 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t1_01_61 F)

noncomputable def wall_cellC_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 2 [(1, false), (4, true), (5, false), (7, false), (8, true)] 5 0 5 2 1 0 (by decide)

def WallE_cellC_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t2_50_52 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t2_50_52 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t2_50_52 F)

noncomputable def wall_cellC_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 4 [(0, false), (2, false), (5, false), (6, true), (7, false)] 4 0 4 6 0 1 (by decide)

def WallE_cellC_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t4_40_46 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t4_40_46 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t4_40_46 F)

noncomputable def wall_cellC_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 6 [(1, false), (4, true), (8, true)] 3 2 5 2 2 0 (by decide)

def WallE_cellC_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t6_32_52 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t6_32_52 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t6_32_52 F)

noncomputable def wall_cellC_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 7 [(0, false), (1, false), (2, false), (4, true)] 3 2 3 6 0 2 (by decide)

def WallE_cellC_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t7_32_36 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t7_32_36 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t7_32_36 F)

noncomputable def wall_cellC_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 8 [(0, false), (1, false), (2, false), (5, false), (6, true)] 4 3 4 6 3 0 (by decide)

def WallE_cellC_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t8_43_46 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t8_43_46 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t8_43_46 F)

noncomputable def wall_cellD_t0_10_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 0 [(3, false), (4, false), (6, false), (7, true), (8, false)] 1 0 1 2 3 0 (by decide)

def WallE_cellD_t0_10_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t0_10_12 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t0_10_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t0_10_12 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t0_10_12 F)

noncomputable def wall_cellD_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 1 [(6, false), (7, true), (8, false)] 1 0 6 0 0 2 (by decide)

def WallE_cellD_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t1_10_60 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t1_10_60 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t1_10_60 F)

noncomputable def wall_cellD_t4_04_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 4 [(0, false), (2, false), (5, true), (6, false), (7, true)] 0 4 6 4 1 0 (by decide)

def WallE_cellD_t4_04_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t4_04_64 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t4_04_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t4_04_64 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t4_04_64 F)

noncomputable def wall_cellD_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 6 [(0, false), (1, true), (4, false), (5, true), (8, false)] 2 5 3 5 0 2 (by decide)

def WallE_cellD_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t6_25_35 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t6_25_35 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t6_25_35 F)

noncomputable def wall_cellD_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 8 [(0, false), (1, true), (2, false), (5, true), (6, false)] 3 4 6 4 0 3 (by decide)

def WallE_cellD_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t8_34_64 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t8_34_64 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t8_34_64 F)

noncomputable def wall_cellD6_t0_10_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 0 [(3, false), (4, false), (6, false), (7, true), (8, true)] 1 0 1 2 3 0 (by decide)

def WallE_cellD6_t0_10_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t0_10_12 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t0_10_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t0_10_12 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t0_10_12 F)

noncomputable def wall_cellD6_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 1 [(6, false), (7, true), (8, true)] 1 0 6 0 0 2 (by decide)

def WallE_cellD6_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t1_10_60 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t1_10_60 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t1_10_60 F)

noncomputable def wall_cellD6_t4_60_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 4 [(0, false), (2, false), (6, false)] 6 0 6 4 1 0 (by decide)

def WallE_cellD6_t4_60_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t4_60_64 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t4_60_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t4_60_64 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t4_60_64 F)

noncomputable def wall_cellD6_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 6 [(0, false), (1, true), (4, false), (5, true), (8, true)] 2 5 3 5 0 2 (by decide)

def WallE_cellD6_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t6_25_35 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t6_25_35 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t6_25_35 F)

noncomputable def wall_cellD6_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 8 [(0, false), (1, true), (2, false), (5, true), (6, false)] 3 4 6 4 3 0 (by decide)

def WallE_cellD6_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t8_34_64 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t8_34_64 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t8_34_64 F)

noncomputable def wall_cellA2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 0 [(3, true), (4, true), (8, true)] 0 2 1 2 3 0 (by decide)

def WallE_cellA2_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t0_02_12 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t0_02_12 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t0_02_12 F)

noncomputable def wall_cellA2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 1 [(2, false), (3, true), (6, false), (7, false), (8, true)] 0 1 6 1 0 2 (by decide)

def WallE_cellA2_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t1_01_61 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t1_01_61 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t1_01_61 F)

noncomputable def wall_cellA2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 2 [(1, true), (4, true), (8, true)] 0 2 5 2 1 0 (by decide)

def WallE_cellA2_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t2_02_52 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t2_02_52 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t2_02_52 F)

noncomputable def wall_cellA2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, true)] 0 5 3 5 0 1 (by decide)

def WallE_cellA2_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_35 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_35 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_35 F)

noncomputable def wall_cellA2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (5, false), (7, false), (8, true)] 0 5 4 5 0 1 (by decide)

def WallE_cellA2_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_45 F)

noncomputable def wall_cellA2_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (7, false)] 3 5 4 5 0 1 (by decide)

def WallE_cellA2_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_35_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_35_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_35_45 F)

noncomputable def wall_cellA2_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 4 0 4 3 0 1 (by decide)

def WallE_cellA2_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_40_43 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_40_43 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_40_43 F)

noncomputable def wall_cellA2_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (5, false), (6, false), (7, false)] 4 0 4 5 0 1 (by decide)

def WallE_cellA2_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_40_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_40_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_40_45 F)

noncomputable def wall_cellA2_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (7, false)] 4 3 4 5 0 1 (by decide)

def WallE_cellA2_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_43_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_43_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_43_45 F)

noncomputable def wall_cellA2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 5 [(3, true), (4, true), (8, true)] 1 2 6 2 0 1 (by decide)

def WallE_cellA2_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t5_12_62 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t5_12_62 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t5_12_62 F)

noncomputable def wall_cellA2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 6 [(1, true), (4, true), (8, true)] 3 2 5 2 0 2 (by decide)

def WallE_cellA2_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t6_32_52 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t6_32_52 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t6_32_52 F)

noncomputable def wall_cellA2_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 7 [(1, true), (3, true), (4, true)] 3 2 6 2 0 2 (by decide)

def WallE_cellA2_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t7_32_62 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t7_32_62 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t7_32_62 F)

noncomputable def wall_cellA2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 8 [(0, false), (1, true), (2, false), (5, false), (6, false)] 4 3 4 6 3 0 (by decide)

def WallE_cellA2_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t8_43_46 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t8_43_46 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t8_43_46 F)

noncomputable def wall_cellB2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 0 [(3, true), (4, true), (8, false)] 0 2 1 2 3 0 (by decide)

def WallE_cellB2_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t0_02_12 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t0_02_12 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t0_02_12 F)

noncomputable def wall_cellB2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 1 [(2, false), (3, true), (6, false), (7, false), (8, false)] 0 1 6 1 0 2 (by decide)

def WallE_cellB2_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t1_01_61 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t1_01_61 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t1_01_61 F)

noncomputable def wall_cellB2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 2 [(1, true), (4, true), (8, false)] 0 2 5 2 1 0 (by decide)

def WallE_cellB2_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t2_02_52 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t2_02_52 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t2_02_52 F)

noncomputable def wall_cellB2_t3_03_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false)] 0 3 4 3 0 1 (by decide)

def WallE_cellB2_t3_03_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_03_43 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_03_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_03_43 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_03_43 F)

noncomputable def wall_cellB2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, false)] 0 5 3 5 0 1 (by decide)

def WallE_cellB2_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_35 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_35 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_35 F)

noncomputable def wall_cellB2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (5, false), (7, false), (8, false)] 0 5 4 5 0 1 (by decide)

def WallE_cellB2_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_45 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_45 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_45 F)

noncomputable def wall_cellB2_t3_43_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false)] 4 3 5 3 0 1 (by decide)

def WallE_cellB2_t3_43_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_43_53 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_43_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_43_53 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_43_53 F)

noncomputable def wall_cellB2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 5 [(3, true), (4, true), (8, false)] 1 2 6 2 0 1 (by decide)

def WallE_cellB2_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t5_12_62 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t5_12_62 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t5_12_62 F)

noncomputable def wall_cellB2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 6 [(1, true), (4, true), (8, false)] 3 2 5 2 0 2 (by decide)

def WallE_cellB2_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t6_32_52 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t6_32_52 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t6_32_52 F)

noncomputable def wall_cellB2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 8 [(0, false), (1, true), (2, false), (5, false), (6, false)] 4 3 4 6 0 3 (by decide)

def WallE_cellB2_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t8_43_46 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t8_43_46 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t8_43_46 F)

noncomputable def wall_cellA0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 0 [(6, true), (7, true), (8, false)] 1 0 2 0 3 0 (by decide)

def WallE_cellA0_t0_10_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t0_10_20 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t0_10_20 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t0_10_20 F)

noncomputable def wall_cellA0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 1 [(6, true), (7, true), (8, false)] 1 0 6 0 2 0 (by decide)

def WallE_cellA0_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t1_10_60 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t1_10_60 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t1_10_60 F)

noncomputable def wall_cellA0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 2 [(5, true), (7, true), (8, false)] 2 0 5 0 1 0 (by decide)

def WallE_cellA0_t2_20_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t2_20_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t2_20_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t2_20_50 F)

noncomputable def wall_cellA0_t3_04_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true)] 0 4 3 4 1 0 (by decide)

def WallE_cellA0_t3_04_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_04_34 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_04_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_04_34 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_04_34 F)

noncomputable def wall_cellA0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(5, true), (7, true), (8, false)] 3 0 5 0 1 0 (by decide)

def WallE_cellA0_t3_30_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_30_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_30_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_30_50 F)

noncomputable def wall_cellA0_t3_34_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (7, true)] 3 4 5 4 1 0 (by decide)

def WallE_cellA0_t3_34_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_34_54 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_34_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_34_54 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_34_54 F)

noncomputable def wall_cellA0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(5, true), (6, true), (7, true), (8, false)] 4 0 5 0 1 0 (by decide)

def WallE_cellA0_t3_40_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_40_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_40_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_40_50 F)

noncomputable def wall_cellA0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 5 [(2, false), (3, false), (4, false), (6, true), (8, false)] 2 1 6 1 1 0 (by decide)

def WallE_cellA0_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t5_21_61 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t5_21_61 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t5_21_61 F)

noncomputable def wall_cellA0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 6 [(0, false), (1, false), (4, false), (5, true), (8, false)] 2 5 3 5 2 0 (by decide)

def WallE_cellA0_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t6_25_35 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t6_25_35 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t6_25_35 F)

noncomputable def wall_cellA0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 8 [(0, false), (1, false), (2, false), (5, true), (6, true)] 3 4 6 4 0 3 (by decide)

def WallE_cellA0_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t8_34_64 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t8_34_64 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t8_34_64 F)

noncomputable def wall_cellB0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 0 [(6, true), (7, true), (8, true)] 1 0 2 0 3 0 (by decide)

def WallE_cellB0_t0_10_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t0_10_20 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t0_10_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t0_10_20 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t0_10_20 F)

noncomputable def wall_cellB0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 1 [(6, true), (7, true), (8, true)] 1 0 6 0 2 0 (by decide)

def WallE_cellB0_t1_10_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t1_10_60 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t1_10_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t1_10_60 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t1_10_60 F)

noncomputable def wall_cellB0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 2 [(5, true), (7, true), (8, true)] 2 0 5 0 1 0 (by decide)

def WallE_cellB0_t2_20_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t2_20_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t2_20_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t2_20_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t2_20_50 F)

noncomputable def wall_cellB0_t3_30_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true)] 3 0 3 4 1 0 (by decide)

def WallE_cellB0_t3_30_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_34 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_34 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_34 F)

noncomputable def wall_cellB0_t3_30_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true)] 3 0 3 5 1 0 (by decide)

def WallE_cellB0_t3_30_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_35 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_35 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_35 F)

noncomputable def wall_cellB0_t3_30_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(5, true), (6, true), (7, true)] 3 0 4 0 1 0 (by decide)

def WallE_cellB0_t3_30_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_40 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_40 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_40 F)

noncomputable def wall_cellB0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(5, true), (7, true), (8, true)] 3 0 5 0 1 0 (by decide)

def WallE_cellB0_t3_30_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_50 F)

noncomputable def wall_cellB0_t3_34_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true)] 3 4 3 5 1 0 (by decide)

def WallE_cellB0_t3_34_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_34_35 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_34_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_34_35 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_34_35 F)

noncomputable def wall_cellB0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(5, true), (6, true), (7, true), (8, true)] 4 0 5 0 1 0 (by decide)

def WallE_cellB0_t3_40_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_40_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_40_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_40_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_40_50 F)

noncomputable def wall_cellB0_t4_40_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 4 [(5, true), (6, true), (7, true)] 4 0 6 0 1 0 (by decide)

def WallE_cellB0_t4_40_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t4_40_60 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t4_40_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t4_40_60 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t4_40_60 F)

noncomputable def wall_cellB0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 5 [(2, false), (3, false), (4, false), (6, true), (8, true)] 2 1 6 1 1 0 (by decide)

def WallE_cellB0_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t5_21_61 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t5_21_61 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t5_21_61 F)

noncomputable def wall_cellB0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 6 [(0, false), (1, false), (4, false), (5, true), (8, true)] 2 5 3 5 2 0 (by decide)

def WallE_cellB0_t6_25_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t6_25_35 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t6_25_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t6_25_35 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t6_25_35 F)

noncomputable def wall_cellB0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 8 [(0, false), (1, false), (2, false), (5, true), (6, true)] 3 4 6 4 3 0 (by decide)

def WallE_cellB0_t8_34_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t8_34_64 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t8_34_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t8_34_64 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t8_34_64 F)

noncomputable def wall_cellCp_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 1 [(2, false), (3, true), (6, true), (7, true), (8, true)] 0 1 6 1 2 0 (by decide)

def WallE_cellCp_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t1_01_61 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t1_01_61 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t1_01_61 F)

noncomputable def wall_cellCp_t3_30_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false)] 3 0 3 5 0 1 (by decide)

def WallE_cellCp_t3_30_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_30_35 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_30_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_30_35 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_30_35 F)

noncomputable def wall_cellCp_t3_34_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false)] 3 4 3 5 0 1 (by decide)

def WallE_cellCp_t3_34_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_34_35 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_34_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_34_35 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_34_35 F)

noncomputable def wall_cellCp_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true)] 4 0 4 3 0 1 (by decide)

def WallE_cellCp_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_40_43 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_40_43 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_40_43 F)

noncomputable def wall_cellCp_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (5, false), (6, true), (7, true)] 4 0 4 5 0 1 (by decide)

def WallE_cellCp_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_40_45 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_40_45 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_40_45 F)

noncomputable def wall_cellCp_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 4 [(0, false), (2, false), (5, false), (6, true), (7, true)] 4 0 4 6 0 1 (by decide)

def WallE_cellCp_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t4_40_46 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t4_40_46 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t4_40_46 F)

noncomputable def wall_cellCp_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 5 [(2, false), (3, true), (4, true), (6, true), (8, true)] 2 1 6 1 0 1 (by decide)

def WallE_cellCp_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t5_21_61 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t5_21_61 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t5_21_61 F)

noncomputable def wall_cellCp_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 6 [(0, false), (1, false), (4, true), (5, false)] 3 2 3 5 2 0 (by decide)

def WallE_cellCp_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t6_32_35 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t6_32_35 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t6_32_35 F)

noncomputable def wall_cellCp_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 7 [(0, false), (1, false), (2, false), (4, true)] 3 2 3 6 2 0 (by decide)

def WallE_cellCp_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t7_32_36 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t7_32_36 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t7_32_36 F)

noncomputable def wall_cell0236_t0_01_21 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 0 [(3, true), (4, true), (6, true), (7, false), (8, true)] 0 1 2 1 3 0 (by decide)

def WallE_cell0236_t0_01_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t0_01_21 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t0_01_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t0_01_21 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t0_01_21 F)

noncomputable def wall_cell0236_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 1 [(2, true), (3, true), (6, true), (7, false), (8, true)] 0 1 6 1 2 0 (by decide)

def WallE_cell0236_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t1_01_61 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t1_01_61 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t1_01_61 F)

noncomputable def wall_cell0236_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 2 [(1, false), (4, true), (5, false), (7, false), (8, true)] 5 0 5 2 0 1 (by decide)

def WallE_cell0236_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t2_50_52 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t2_50_52 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t2_50_52 F)

noncomputable def wall_cell0236_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 4 [(0, false), (2, true), (5, false), (6, true), (7, false)] 4 0 4 6 0 1 (by decide)

def WallE_cell0236_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t4_40_46 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t4_40_46 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t4_40_46 F)

noncomputable def wall_cell0236_t6_52_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 6 [(0, false), (1, false), (4, true), (5, false), (8, true)] 5 2 5 3 2 0 (by decide)

def WallE_cell0236_t6_52_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t6_52_53 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t6_52_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t6_52_53 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t6_52_53 F)

noncomputable def wall_cell0236_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 8 [(0, false), (1, false), (2, true), (5, false), (6, true)] 4 3 4 6 3 0 (by decide)

def WallE_cell0236_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t8_43_46 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t8_43_46 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t8_43_46 F)

noncomputable def wall_cell0536_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 1 [(2, false), (3, true), (6, false), (7, false), (8, true)] 0 1 6 1 2 0 (by decide)

def WallE_cell0536_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t1_01_61 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t1_01_61 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t1_01_61 F)

noncomputable def wall_cell0536_t2_02_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 2 [(1, false), (4, true), (8, true)] 0 2 5 2 1 0 (by decide)

def WallE_cell0536_t2_02_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t2_02_52 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t2_02_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t2_02_52 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t2_02_52 F)

noncomputable def wall_cell0536_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 0 5 3 5 0 1 (by decide)

def WallE_cell0536_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_35 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_35 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_35 F)

noncomputable def wall_cell0536_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (5, false), (7, false), (8, true)] 0 5 4 5 0 1 (by decide)

def WallE_cell0536_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_45 F)

noncomputable def wall_cell0536_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (7, false)] 3 5 4 5 0 1 (by decide)

def WallE_cell0536_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_35_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_35_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_35_45 F)

noncomputable def wall_cell0536_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, false)] 4 0 4 3 0 1 (by decide)

def WallE_cell0536_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_40_43 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_40_43 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_40_43 F)

noncomputable def wall_cell0536_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (5, false), (6, false), (7, false)] 4 0 4 5 0 1 (by decide)

def WallE_cell0536_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_40_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_40_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_40_45 F)

noncomputable def wall_cell0536_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (7, false)] 4 3 4 5 0 1 (by decide)

def WallE_cell0536_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_43_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_43_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_43_45 F)

noncomputable def wall_cell0536_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 4 [(0, false), (2, false), (5, false), (6, false), (7, false)] 4 0 4 6 0 1 (by decide)

def WallE_cell0536_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t4_40_46 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t4_40_46 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t4_40_46 F)

noncomputable def wall_cell0536_t6_32_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 6 [(1, false), (4, true), (8, true)] 3 2 5 2 0 2 (by decide)

def WallE_cell0536_t6_32_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t6_32_52 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t6_32_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t6_32_52 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t6_32_52 F)

noncomputable def wall_cell0536_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 7 [(1, false), (3, true), (4, true)] 3 2 6 2 0 2 (by decide)

def WallE_cell0536_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t7_32_62 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t7_32_62 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t7_32_62 F)

noncomputable def wall_cell0536_t8_43_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 8 [(0, false), (1, false), (2, false), (5, false), (6, false)] 4 3 4 6 3 0 (by decide)

def WallE_cell0536_t8_43_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t8_43_46 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t8_43_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t8_43_46 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t8_43_46 F)

noncomputable def wall_cellP_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 2 [(1, false), (4, false), (5, false), (7, true), (8, true)] 5 0 5 2 1 0 (by decide)

def WallE_cellP_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t2_50_52 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t2_50_52 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t2_50_52 F)

noncomputable def wall_cellP_t3_30_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false)] 3 0 3 4 0 1 (by decide)

def WallE_cellP_t3_30_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_34 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_34 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_34 F)

noncomputable def wall_cellP_t3_30_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false)] 3 0 3 5 0 1 (by decide)

def WallE_cellP_t3_30_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_35 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_35 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_35 F)

noncomputable def wall_cellP_t3_30_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(5, false), (6, true), (7, true)] 3 0 4 0 0 1 (by decide)

def WallE_cellP_t3_30_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_40 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_40 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_40 F)

noncomputable def wall_cellP_t3_30_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(5, false), (7, true), (8, true)] 3 0 5 0 0 1 (by decide)

def WallE_cellP_t3_30_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_50 F)

noncomputable def wall_cellP_t3_34_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false)] 3 4 3 5 0 1 (by decide)

def WallE_cellP_t3_34_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_34_35 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_34_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_34_35 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_34_35 F)

noncomputable def wall_cellP_t3_40_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(5, false), (6, true), (7, true), (8, true)] 4 0 5 0 0 1 (by decide)

def WallE_cellP_t3_40_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_40_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_40_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_40_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_40_50 F)

noncomputable def wall_cellP_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 4 [(0, false), (2, false), (5, false), (6, true), (7, true)] 4 0 4 6 1 0 (by decide)

def WallE_cellP_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t4_40_46 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t4_40_46 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t4_40_46 F)

noncomputable def wall_cellP_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 5 [(2, false), (3, true), (4, false), (6, true), (8, true)] 2 1 6 1 0 1 (by decide)

def WallE_cellP_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t5_21_61 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t5_21_61 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t5_21_61 F)

noncomputable def wall_cellP_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 6 [(0, false), (1, false), (4, false), (5, false)] 3 2 3 5 2 0 (by decide)

def WallE_cellP_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t6_32_35 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t6_32_35 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t6_32_35 F)

noncomputable def wall_cellP_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 7 [(0, false), (1, false), (2, false), (4, false)] 3 2 3 6 2 0 (by decide)

def WallE_cellP_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t7_32_36 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t7_32_36 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t7_32_36 F)

noncomputable def wall_cellP_t8_34_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 8 [(0, false), (1, false), (2, false), (5, false)] 3 4 3 6 3 0 (by decide)

def WallE_cellP_t8_34_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t8_34_36 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t8_34_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t8_34_36 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t8_34_36 F)

noncomputable def wall_cell0164_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 0 [(3, false), (4, true), (8, false)] 0 2 1 2 3 0 (by decide)

def WallE_cell0164_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t0_02_12 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t0_02_12 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t0_02_12 F)

noncomputable def wall_cell0164_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 1 [(2, false), (3, false), (6, false), (7, false), (8, false)] 0 1 6 1 0 2 (by decide)

def WallE_cell0164_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t1_01_61 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t1_01_61 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t1_01_61 F)

noncomputable def wall_cell0164_t3_03_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false)] 0 3 4 3 1 0 (by decide)

def WallE_cell0164_t3_03_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_03_43 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_03_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_03_43 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_03_43 F)

noncomputable def wall_cell0164_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, false)] 0 5 3 5 1 0 (by decide)

def WallE_cell0164_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_35 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_35 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_35 F)

noncomputable def wall_cell0164_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (5, false), (7, false), (8, false)] 0 5 4 5 1 0 (by decide)

def WallE_cell0164_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_45 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_45 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_45 F)

noncomputable def wall_cell0164_t3_43_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false)] 4 3 5 3 1 0 (by decide)

def WallE_cell0164_t3_43_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_43_53 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_43_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_43_53 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_43_53 F)

noncomputable def wall_cell0164_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 5 [(3, false), (4, true), (8, false)] 1 2 6 2 0 1 (by decide)

def WallE_cell0164_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t5_12_62 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t5_12_62 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t5_12_62 F)

noncomputable def wall_cell0164_t8_43_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 8 [(0, false), (1, true), (2, false), (5, false)] 4 3 6 3 0 3 (by decide)

def WallE_cell0164_t8_43_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t8_43_63 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t8_43_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t8_43_63 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t8_43_63 F)

noncomputable def wall_cell01634_t0_02_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 0 [(3, false), (4, true), (8, true)] 0 2 1 2 3 0 (by decide)

def WallE_cell01634_t0_02_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t0_02_12 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t0_02_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t0_02_12 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t0_02_12 F)

noncomputable def wall_cell01634_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 1 [(2, false), (3, false), (6, false), (7, false), (8, true)] 0 1 6 1 0 2 (by decide)

def WallE_cell01634_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t1_01_61 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t1_01_61 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t1_01_61 F)

noncomputable def wall_cell01634_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, true)] 0 5 3 5 1 0 (by decide)

def WallE_cell01634_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_35 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_35 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_35 F)

noncomputable def wall_cell01634_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (5, false), (7, false), (8, true)] 0 5 4 5 1 0 (by decide)

def WallE_cell01634_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_45 F)

noncomputable def wall_cell01634_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (7, false)] 3 5 4 5 1 0 (by decide)

def WallE_cell01634_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_35_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_35_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_35_45 F)

noncomputable def wall_cell01634_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 4 0 4 3 1 0 (by decide)

def WallE_cell01634_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_40_43 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_40_43 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_40_43 F)

noncomputable def wall_cell01634_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (5, false), (6, false), (7, false)] 4 0 4 5 1 0 (by decide)

def WallE_cell01634_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_40_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_40_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_40_45 F)

noncomputable def wall_cell01634_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (7, false)] 4 3 4 5 1 0 (by decide)

def WallE_cell01634_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_43_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_43_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_43_45 F)

noncomputable def wall_cell01634_t5_12_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 5 [(3, false), (4, true), (8, true)] 1 2 6 2 0 1 (by decide)

def WallE_cell01634_t5_12_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t5_12_62 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t5_12_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t5_12_62 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t5_12_62 F)

noncomputable def wall_cell01634_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 7 [(1, true), (3, false), (4, true)] 3 2 6 2 0 2 (by decide)

def WallE_cell01634_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t7_32_62 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t7_32_62 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t7_32_62 F)

noncomputable def wall_cell01634_t8_43_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 8 [(0, false), (1, true), (2, false), (5, false)] 4 3 6 3 3 0 (by decide)

def WallE_cell01634_t8_43_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t8_43_63 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t8_43_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t8_43_63 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t8_43_63 F)

noncomputable def wall_cell05326_t1_01_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 1 [(2, false), (3, true), (6, false), (7, true), (8, true)] 0 1 6 1 2 0 (by decide)

def WallE_cell05326_t1_01_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t1_01_61 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t1_01_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t1_01_61 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t1_01_61 F)

noncomputable def wall_cell05326_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (7, true), (8, true)] 0 5 3 5 0 1 (by decide)

def WallE_cell05326_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_35 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_35 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_35 F)

noncomputable def wall_cell05326_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (7, true)] 3 5 4 5 0 1 (by decide)

def WallE_cell05326_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_35_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_35_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_35_45 F)

noncomputable def wall_cell05326_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, true)] 4 0 4 3 0 1 (by decide)

def WallE_cell05326_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_40_43 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_40_43 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_40_43 F)

noncomputable def wall_cell05326_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (5, false), (6, false), (7, true)] 4 0 4 5 0 1 (by decide)

def WallE_cell05326_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_40_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_40_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_40_45 F)

noncomputable def wall_cell05326_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 4 [(0, false), (2, false), (5, false), (6, false), (7, true)] 4 0 4 6 0 1 (by decide)

def WallE_cell05326_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t4_40_46 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t4_40_46 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t4_40_46 F)

noncomputable def wall_cell05326_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 5 [(2, false), (3, true), (4, true), (6, false), (8, true)] 2 1 6 1 0 1 (by decide)

def WallE_cell05326_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t5_21_61 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t5_21_61 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t5_21_61 F)

noncomputable def wall_cell05326_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 6 [(0, false), (1, false), (4, true), (5, false)] 3 2 3 5 0 2 (by decide)

def WallE_cell05326_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t6_32_35 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t6_32_35 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t6_32_35 F)

noncomputable def wall_cell05326_t7_32_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 7 [(1, false), (3, true), (4, true)] 3 2 6 2 2 0 (by decide)

def WallE_cell05326_t7_32_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t7_32_62 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t7_32_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t7_32_62 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t7_32_62 F)

noncomputable def wall_cell046125_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 2 [(1, false), (4, false), (5, true), (7, true), (8, true)] 5 0 5 2 1 0 (by decide)

def WallE_cell046125_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t2_50_52 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t2_50_52 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t2_50_52 F)

noncomputable def wall_cell046125_t3_30_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true)] 3 0 3 4 0 1 (by decide)

def WallE_cell046125_t3_30_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_34 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_34 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_34 F)

noncomputable def wall_cell046125_t3_30_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true)] 3 0 3 5 0 1 (by decide)

def WallE_cell046125_t3_30_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_35 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_35 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_35 F)

noncomputable def wall_cell046125_t3_30_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(5, true), (6, true), (7, true)] 3 0 4 0 0 1 (by decide)

def WallE_cell046125_t3_30_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_40 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_40 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_40 F)

noncomputable def wall_cell046125_t3_30_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(5, true), (7, true), (8, true)] 3 0 5 0 0 1 (by decide)

def WallE_cell046125_t3_30_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_50 F)

noncomputable def wall_cell046125_t3_34_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true)] 3 4 3 5 0 1 (by decide)

def WallE_cell046125_t3_34_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_34_35 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_34_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_34_35 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_34_35 F)

noncomputable def wall_cell046125_t3_40_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(5, true), (6, true), (7, true), (8, true)] 4 0 5 0 0 1 (by decide)

def WallE_cell046125_t3_40_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_40_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_40_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_40_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_40_50 F)

noncomputable def wall_cell046125_t4_40_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 4 [(0, false), (2, false), (5, true), (6, true), (7, true)] 4 0 4 6 1 0 (by decide)

def WallE_cell046125_t4_40_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t4_40_46 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t4_40_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t4_40_46 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t4_40_46 F)

noncomputable def wall_cell046125_t5_21_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 5 [(2, false), (3, true), (4, false), (6, true), (8, true)] 2 1 6 1 1 0 (by decide)

def WallE_cell046125_t5_21_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t5_21_61 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t5_21_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t5_21_61 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t5_21_61 F)

noncomputable def wall_cell046125_t6_32_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 6 [(0, false), (1, false), (4, false), (5, true)] 3 2 3 5 2 0 (by decide)

def WallE_cell046125_t6_32_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t6_32_35 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t6_32_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t6_32_35 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t6_32_35 F)

noncomputable def wall_cell046125_t8_34_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 8 [(0, false), (1, false), (2, false), (5, true)] 3 4 3 6 3 0 (by decide)

def WallE_cell046125_t8_34_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t8_34_36 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t8_34_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t8_34_36 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t8_34_36 F)

/-! ## Conjunction `AllWallE` and `CellCoverEmptyAll` -/

/-- Conjunction of `WallE` across all 140 `cells28` walls on `(x, F)`. -/
def AllWallE (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellC_t1_01_61 x F ∧
  WallE_cellC_t2_50_52 x F ∧
  WallE_cellC_t4_40_46 x F ∧
  WallE_cellC_t6_32_52 x F ∧
  WallE_cellC_t7_32_36 x F ∧
  WallE_cellC_t8_43_46 x F ∧
  WallE_cellD_t0_10_12 x F ∧
  WallE_cellD_t1_10_60 x F ∧
  WallE_cellD_t4_04_64 x F ∧
  WallE_cellD_t6_25_35 x F ∧
  WallE_cellD_t8_34_64 x F ∧
  WallE_cellD6_t0_10_12 x F ∧
  WallE_cellD6_t1_10_60 x F ∧
  WallE_cellD6_t4_60_64 x F ∧
  WallE_cellD6_t6_25_35 x F ∧
  WallE_cellD6_t8_34_64 x F ∧
  WallE_cellA2_t0_02_12 x F ∧
  WallE_cellA2_t1_01_61 x F ∧
  WallE_cellA2_t2_02_52 x F ∧
  WallE_cellA2_t3_05_35 x F ∧
  WallE_cellA2_t3_05_45 x F ∧
  WallE_cellA2_t3_35_45 x F ∧
  WallE_cellA2_t3_40_43 x F ∧
  WallE_cellA2_t3_40_45 x F ∧
  WallE_cellA2_t3_43_45 x F ∧
  WallE_cellA2_t5_12_62 x F ∧
  WallE_cellA2_t6_32_52 x F ∧
  WallE_cellA2_t7_32_62 x F ∧
  WallE_cellA2_t8_43_46 x F ∧
  WallE_cellB2_t0_02_12 x F ∧
  WallE_cellB2_t1_01_61 x F ∧
  WallE_cellB2_t2_02_52 x F ∧
  WallE_cellB2_t3_03_43 x F ∧
  WallE_cellB2_t3_05_35 x F ∧
  WallE_cellB2_t3_05_45 x F ∧
  WallE_cellB2_t3_43_53 x F ∧
  WallE_cellB2_t5_12_62 x F ∧
  WallE_cellB2_t6_32_52 x F ∧
  WallE_cellB2_t8_43_46 x F ∧
  WallE_cellA0_t0_10_20 x F ∧
  WallE_cellA0_t1_10_60 x F ∧
  WallE_cellA0_t2_20_50 x F ∧
  WallE_cellA0_t3_04_34 x F ∧
  WallE_cellA0_t3_30_50 x F ∧
  WallE_cellA0_t3_34_54 x F ∧
  WallE_cellA0_t3_40_50 x F ∧
  WallE_cellA0_t5_21_61 x F ∧
  WallE_cellA0_t6_25_35 x F ∧
  WallE_cellA0_t8_34_64 x F ∧
  WallE_cellB0_t0_10_20 x F ∧
  WallE_cellB0_t1_10_60 x F ∧
  WallE_cellB0_t2_20_50 x F ∧
  WallE_cellB0_t3_30_34 x F ∧
  WallE_cellB0_t3_30_35 x F ∧
  WallE_cellB0_t3_30_40 x F ∧
  WallE_cellB0_t3_30_50 x F ∧
  WallE_cellB0_t3_34_35 x F ∧
  WallE_cellB0_t3_40_50 x F ∧
  WallE_cellB0_t4_40_60 x F ∧
  WallE_cellB0_t5_21_61 x F ∧
  WallE_cellB0_t6_25_35 x F ∧
  WallE_cellB0_t8_34_64 x F ∧
  WallE_cellCp_t1_01_61 x F ∧
  WallE_cellCp_t3_30_35 x F ∧
  WallE_cellCp_t3_34_35 x F ∧
  WallE_cellCp_t3_40_43 x F ∧
  WallE_cellCp_t3_40_45 x F ∧
  WallE_cellCp_t4_40_46 x F ∧
  WallE_cellCp_t5_21_61 x F ∧
  WallE_cellCp_t6_32_35 x F ∧
  WallE_cellCp_t7_32_36 x F ∧
  WallE_cell0236_t0_01_21 x F ∧
  WallE_cell0236_t1_01_61 x F ∧
  WallE_cell0236_t2_50_52 x F ∧
  WallE_cell0236_t4_40_46 x F ∧
  WallE_cell0236_t6_52_53 x F ∧
  WallE_cell0236_t8_43_46 x F ∧
  WallE_cell0536_t1_01_61 x F ∧
  WallE_cell0536_t2_02_52 x F ∧
  WallE_cell0536_t3_05_35 x F ∧
  WallE_cell0536_t3_05_45 x F ∧
  WallE_cell0536_t3_35_45 x F ∧
  WallE_cell0536_t3_40_43 x F ∧
  WallE_cell0536_t3_40_45 x F ∧
  WallE_cell0536_t3_43_45 x F ∧
  WallE_cell0536_t4_40_46 x F ∧
  WallE_cell0536_t6_32_52 x F ∧
  WallE_cell0536_t7_32_62 x F ∧
  WallE_cell0536_t8_43_46 x F ∧
  WallE_cellP_t2_50_52 x F ∧
  WallE_cellP_t3_30_34 x F ∧
  WallE_cellP_t3_30_35 x F ∧
  WallE_cellP_t3_30_40 x F ∧
  WallE_cellP_t3_30_50 x F ∧
  WallE_cellP_t3_34_35 x F ∧
  WallE_cellP_t3_40_50 x F ∧
  WallE_cellP_t4_40_46 x F ∧
  WallE_cellP_t5_21_61 x F ∧
  WallE_cellP_t6_32_35 x F ∧
  WallE_cellP_t7_32_36 x F ∧
  WallE_cellP_t8_34_36 x F ∧
  WallE_cell0164_t0_02_12 x F ∧
  WallE_cell0164_t1_01_61 x F ∧
  WallE_cell0164_t3_03_43 x F ∧
  WallE_cell0164_t3_05_35 x F ∧
  WallE_cell0164_t3_05_45 x F ∧
  WallE_cell0164_t3_43_53 x F ∧
  WallE_cell0164_t5_12_62 x F ∧
  WallE_cell0164_t8_43_63 x F ∧
  WallE_cell01634_t0_02_12 x F ∧
  WallE_cell01634_t1_01_61 x F ∧
  WallE_cell01634_t3_05_35 x F ∧
  WallE_cell01634_t3_05_45 x F ∧
  WallE_cell01634_t3_35_45 x F ∧
  WallE_cell01634_t3_40_43 x F ∧
  WallE_cell01634_t3_40_45 x F ∧
  WallE_cell01634_t3_43_45 x F ∧
  WallE_cell01634_t5_12_62 x F ∧
  WallE_cell01634_t7_32_62 x F ∧
  WallE_cell01634_t8_43_63 x F ∧
  WallE_cell05326_t1_01_61 x F ∧
  WallE_cell05326_t3_05_35 x F ∧
  WallE_cell05326_t3_35_45 x F ∧
  WallE_cell05326_t3_40_43 x F ∧
  WallE_cell05326_t3_40_45 x F ∧
  WallE_cell05326_t4_40_46 x F ∧
  WallE_cell05326_t5_21_61 x F ∧
  WallE_cell05326_t6_32_35 x F ∧
  WallE_cell05326_t7_32_62 x F ∧
  WallE_cell046125_t2_50_52 x F ∧
  WallE_cell046125_t3_30_34 x F ∧
  WallE_cell046125_t3_30_35 x F ∧
  WallE_cell046125_t3_30_40 x F ∧
  WallE_cell046125_t3_30_50 x F ∧
  WallE_cell046125_t3_34_35 x F ∧
  WallE_cell046125_t3_40_50 x F ∧
  WallE_cell046125_t4_40_46 x F ∧
  WallE_cell046125_t5_21_61 x F ∧
  WallE_cell046125_t6_32_35 x F ∧
  WallE_cell046125_t8_34_36 x F

private lemma holeLeaf_of_cert {F : S0xFac 9 s0x_S24 x} {P : Prop}
    (h : Gen.LexAny F ∨ Gen.SplitAny F ∨ P) (hF : HoleLeaf x F) : P :=
  (h.resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

private lemma holeLeaf_of_cert_twin {F : S0xFac 9 s0x_S24 x} {P : Prop}
    (h : Gen.LexAny (Sym.sym24 F) ∨ Gen.SplitAny (Sym.sym24 F) ∨ P) (hF : HoleLeaf x F) : P :=
  (h.resolve_left (fun hL => hF.2.2.2.1 (Sym.lexAny_sym F hL))).resolve_left
    (fun hS => hF.2.2.2.2.1 (Sym.splitAny24_sym F hS))

/-- **Hole fact:** at a `HoleLeaf`, `AllWallE x F` holds. -/
theorem holeLeaf_allWallE {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert (cert_cellC_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cellC_t2_50_52 F) hF
  · exact holeLeaf_of_cert (cert_cellC_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cellC_t6_32_52 F) hF
  · exact holeLeaf_of_cert (cert_cellC_t7_32_36 F) hF
  · exact holeLeaf_of_cert (cert_cellC_t8_43_46 F) hF
  · exact holeLeaf_of_cert (cert_cellD_t0_10_12 F) hF
  · exact holeLeaf_of_cert (cert_cellD_t1_10_60 F) hF
  · exact holeLeaf_of_cert (cert_cellD_t4_04_64 F) hF
  · exact holeLeaf_of_cert (cert_cellD_t6_25_35 F) hF
  · exact holeLeaf_of_cert (cert_cellD_t8_34_64 F) hF
  · exact holeLeaf_of_cert (cert_cellD6_t0_10_12 F) hF
  · exact holeLeaf_of_cert (cert_cellD6_t1_10_60 F) hF
  · exact holeLeaf_of_cert (cert_cellD6_t4_60_64 F) hF
  · exact holeLeaf_of_cert (cert_cellD6_t6_25_35 F) hF
  · exact holeLeaf_of_cert (cert_cellD6_t8_34_64 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t0_02_12 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t2_02_52 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_05_45 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_35_45 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_40_43 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_40_45 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t3_43_45 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t5_12_62 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t6_32_52 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t7_32_62 F) hF
  · exact holeLeaf_of_cert (cert_cellA2_t8_43_46 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t0_02_12 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t2_02_52 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t3_03_43 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t3_05_45 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t3_43_53 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t5_12_62 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t6_32_52 F) hF
  · exact holeLeaf_of_cert (cert_cellB2_t8_43_46 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t0_10_20 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t1_10_60 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t2_20_50 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t3_04_34 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t3_30_50 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t3_34_54 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t3_40_50 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t6_25_35 F) hF
  · exact holeLeaf_of_cert (cert_cellA0_t8_34_64 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t0_10_20 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t1_10_60 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t2_20_50 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_30_34 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_30_35 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_30_40 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_30_50 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_34_35 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t3_40_50 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t4_40_60 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t6_25_35 F) hF
  · exact holeLeaf_of_cert (cert_cellB0_t8_34_64 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t3_30_35 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t3_34_35 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t3_40_43 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t3_40_45 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t6_32_35 F) hF
  · exact holeLeaf_of_cert (cert_cellCp_t7_32_36 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t0_01_21 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t2_50_52 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t6_52_53 F) hF
  · exact holeLeaf_of_cert (cert_cell0236_t8_43_46 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t2_02_52 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_05_45 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_35_45 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_40_43 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_40_45 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t3_43_45 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t6_32_52 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t7_32_62 F) hF
  · exact holeLeaf_of_cert (cert_cell0536_t8_43_46 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t2_50_52 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_30_34 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_30_35 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_30_40 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_30_50 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_34_35 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t3_40_50 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t6_32_35 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t7_32_36 F) hF
  · exact holeLeaf_of_cert (cert_cellP_t8_34_36 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t0_02_12 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t3_03_43 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t3_05_45 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t3_43_53 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t5_12_62 F) hF
  · exact holeLeaf_of_cert (cert_cell0164_t8_43_63 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t0_02_12 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_05_45 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_35_45 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_40_43 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_40_45 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t3_43_45 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t5_12_62 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t7_32_62 F) hF
  · exact holeLeaf_of_cert (cert_cell01634_t8_43_63 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t1_01_61 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t3_05_35 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t3_35_45 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t3_40_43 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t3_40_45 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t6_32_35 F) hF
  · exact holeLeaf_of_cert (cert_cell05326_t7_32_62 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t2_50_52 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_30_34 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_30_35 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_30_40 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_30_50 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_34_35 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t3_40_50 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t4_40_46 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t5_21_61 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t6_32_35 F) hF
  · exact holeLeaf_of_cert (cert_cell046125_t8_34_36 F) hF

/-- **Twin hole fact:** at a `HoleLeaf`, `AllWallE (x ∘ Sym.pi24) (Sym.sym24 F)` holds. -/
theorem holeLeaf_allWallE_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert_twin (cert_cellC_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellC_t2_50_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellC_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellC_t6_32_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellC_t7_32_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellC_t8_43_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD_t0_10_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD_t1_10_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD_t4_04_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD_t6_25_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD_t8_34_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD6_t0_10_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD6_t1_10_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD6_t4_60_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD6_t6_25_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellD6_t8_34_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t0_02_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t2_02_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_35_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t3_43_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t5_12_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t6_32_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t7_32_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA2_t8_43_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t0_02_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t2_02_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t3_03_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t3_43_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t5_12_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t6_32_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB2_t8_43_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t0_10_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t1_10_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t2_20_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t3_04_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t3_30_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t3_34_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t3_40_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t6_25_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellA0_t8_34_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t0_10_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t1_10_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t2_20_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_30_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_30_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_30_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_30_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_34_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t3_40_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t4_40_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t6_25_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellB0_t8_34_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t3_30_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t3_34_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t6_32_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellCp_t7_32_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t0_01_21 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t2_50_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t6_52_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0236_t8_43_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t2_02_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_35_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t3_43_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t6_32_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t7_32_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0536_t8_43_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t2_50_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_30_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_30_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_30_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_30_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_34_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t3_40_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t6_32_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t7_32_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cellP_t8_34_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t0_02_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t3_03_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t3_43_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t5_12_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell0164_t8_43_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t0_02_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_35_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t3_43_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t5_12_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t7_32_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell01634_t8_43_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t1_01_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t3_35_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t6_32_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell05326_t7_32_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t2_50_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_30_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_30_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_30_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_30_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_34_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t3_40_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t4_40_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t5_21_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t6_32_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert_twin (cert_cell046125_t8_34_36 (Sym.sym24 F)) hF

/-- **[OPEN] `CellCoverEmptyAll L`**: on `CbarIn`, `OB1`, with `AllWallE` on `x` and on the twin, the point
is not in the cell-cover residue of `L`. -/
def CellCoverEmptyAll (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → AllWallE x F →
    AllWallE (x ∘ Sym.pi24) (Sym.sym24 F) → ¬ CellCoverResidue L x F

/-- `CellCoverEmpty L` implies `CellCoverEmptyAll L`. -/
theorem cellCoverEmptyAll_of_cellCoverEmpty {L : List Cell24} (h : CellCoverEmpty L) :
    CellCoverEmptyAll L :=
  fun x F hC hO _ _ => h x F hC hO

/-- `CellCoverEmptyAll L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyAll {L : List Cell24} (hN : CellCoverEmptyAll L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_allWallE h) (holeLeaf_allWallE_twin h) (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyAll L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyAll {L : List Cell24} (hN : CellCoverEmptyAll L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyAll hN x F hO (holeLeaf_of_holeFull hF)

end Minimality.T24.Cell
