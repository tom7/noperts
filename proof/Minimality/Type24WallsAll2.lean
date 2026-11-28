module

public import Minimality.Type24WallsAll

/-!
# Type24WallsAll2: complete `wallOK` wall list across `cells28` (Task GC)

Extends `Type24WallsAll` (`140` feasible shared-vertex walls) with all remaining `454`
deduplicated `wallOK`-accepted walls whose open segment is not provably empty by
antiparallel endpoints (`E0 = -E1`) or a single `forms` facet being `≤ 0` on both endpoints
(`594` walls total).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

private lemma holeLeaf_of_cert2 {F : S0xFac 9 s0x_S24 x} {P : Prop}
    (h : Gen.LexAny F ∨ Gen.SplitAny F ∨ P) (hF : HoleLeaf x F) : P :=
  (h.resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

private lemma holeLeaf_of_cert2_twin {F : S0xFac 9 s0x_S24 x} {P : Prop}
    (h : Gen.LexAny (Sym.sym24 F) ∨ Gen.SplitAny (Sym.sym24 F) ∨ P) (hF : HoleLeaf x F) : P :=
  (h.resolve_left (fun hL => hF.2.2.2.1 (Sym.lexAny_sym F hL))).resolve_left
    (fun hS => hF.2.2.2.2.1 (Sym.splitAny24_sym F hS))

/-! ## Additional 454 walls of `cells28` -/

noncomputable def wall_cellC_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 1 [(2, false), (3, true), (5, false), (6, true), (7, false), (8, true)] 0 1 6 0 2 0 (by decide)

def WallE_cellC_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t1_01_60 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t1_01_60 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t1_01_60 F)

noncomputable def wall_cellC_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 1 [(0, false), (2, false), (3, true), (6, true), (7, false), (8, true)] 0 6 6 1 2 0 (by decide)

def WallE_cellC_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t1_06_61 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t1_06_61 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t1_06_61 F)

noncomputable def wall_cellC_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 2 [(1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cellC_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t2_02_50 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t2_02_50 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t2_02_50 F)

noncomputable def wall_cellC_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 2 [(1, false), (3, true), (4, true), (5, false), (7, false), (8, true)] 2 0 5 2 1 0 (by decide)

def WallE_cellC_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t2_20_52 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t2_20_52 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t2_20_52 F)

noncomputable def wall_cellC_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, false), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cellC_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_03_40 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_03_40 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_03_40 F)

noncomputable def wall_cellC_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cellC_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_04_35 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_04_35 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_04_35 F)

noncomputable def wall_cellC_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, false), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cellC_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_04_45 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_04_45 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_04_45 F)

noncomputable def wall_cellC_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cellC_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_05_30 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_05_30 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_05_30 F)

noncomputable def wall_cellC_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cellC_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_05_34 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_05_34 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_05_34 F)

noncomputable def wall_cellC_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (5, false), (6, true), (7, false), (8, true)] 0 5 4 0 0 1 (by decide)

def WallE_cellC_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_05_40 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_05_40 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_05_40 F)

noncomputable def wall_cellC_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false)] 3 0 4 3 0 1 (by decide)

def WallE_cellC_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_30_43 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_30_43 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_30_43 F)

noncomputable def wall_cellC_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false)] 3 0 4 5 0 1 (by decide)

def WallE_cellC_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_30_45 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_30_45 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_30_45 F)

noncomputable def wall_cellC_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, false), (8, true)] 3 0 5 3 0 1 (by decide)

def WallE_cellC_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_30_53 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_30_53 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_30_53 F)

noncomputable def wall_cellC_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false)] 3 4 4 5 0 1 (by decide)

def WallE_cellC_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_34_45 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_34_45 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_34_45 F)

noncomputable def wall_cellC_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false)] 3 5 4 0 0 1 (by decide)

def WallE_cellC_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_35_40 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_35_40 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_35_40 F)

noncomputable def wall_cellC_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 3 5 5 0 0 1 (by decide)

def WallE_cellC_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_35_50 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_35_50 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_35_50 F)

noncomputable def wall_cellC_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, false), (8, true)] 3 5 5 4 0 1 (by decide)

def WallE_cellC_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_35_54 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_35_54 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_35_54 F)

noncomputable def wall_cellC_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, false)] 4 0 4 3 0 1 (by decide)

def WallE_cellC_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_40_43 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_40_43 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_40_43 F)

noncomputable def wall_cellC_t3_40_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (5, false), (6, true), (7, false)] 4 0 4 5 0 1 (by decide)

def WallE_cellC_t3_40_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_40_45 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_40_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_40_45 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_40_45 F)

noncomputable def wall_cellC_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cellC_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_40_53 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_40_53 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_40_53 F)

noncomputable def wall_cellC_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cellC_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_43_50 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_43_50 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_43_50 F)

noncomputable def wall_cellC_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cellC_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t3_45_50 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t3_45_50 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t3_45_50 F)

noncomputable def wall_cellC_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 4 [(0, false), (2, false), (5, false), (6, true), (7, false), (8, true)] 0 6 4 0 0 1 (by decide)

def WallE_cellC_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t4_06_40 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t4_06_40 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t4_06_40 F)

noncomputable def wall_cellC_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 4 [(0, false), (2, false), (3, true), (5, false), (6, true), (7, false)] 4 6 6 0 0 1 (by decide)

def WallE_cellC_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t4_46_60 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t4_46_60 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t4_46_60 F)

noncomputable def wall_cellC_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 6 [(0, false), (1, false), (2, false), (4, true), (5, false), (8, true)] 3 2 5 3 2 0 (by decide)

def WallE_cellC_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t6_32_53 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t6_32_53 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t6_32_53 F)

noncomputable def wall_cellC_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 6 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 3 5 5 2 2 0 (by decide)

def WallE_cellC_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t6_35_52 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t6_35_52 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t6_35_52 F)

noncomputable def wall_cellC_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (8, true)] 2 6 3 2 0 2 (by decide)

def WallE_cellC_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t7_26_32 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t7_26_32 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t7_26_32 F)

noncomputable def wall_cellC_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (6, true)] 3 6 6 2 0 2 (by decide)

def WallE_cellC_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t7_36_62 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t7_36_62 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t7_36_62 F)

noncomputable def wall_cellC_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 8 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true)] 3 6 4 3 3 0 (by decide)

def WallE_cellC_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t8_36_43 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t8_36_43 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t8_36_43 F)

noncomputable def wall_cellC_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC :=
  cellWallOf F cellC 8 [(0, false), (1, false), (2, false), (3, true), (5, false), (6, true)] 4 6 6 3 3 0 (by decide)

def WallE_cellC_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC (wall_cellC_t8_46_63 F) (cellRimScalar cellC 0 2 2 1 x)

theorem cert_cellC_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellC_t8_46_63 x F :=
  cellWall_cert_or_E F cellC 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellC_t8_46_63 F)

noncomputable def wall_cellD_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 0 [(3, false), (4, false), (5, true), (6, false), (7, true), (8, false)] 0 2 1 0 3 0 (by decide)

def WallE_cellD_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t0_02_10 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t0_02_10 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t0_02_10 F)

noncomputable def wall_cellD_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 0 [(1, true), (3, false), (4, false), (6, false), (7, true), (8, false)] 1 2 2 0 3 0 (by decide)

def WallE_cellD_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t0_12_20 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t0_12_20 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t0_12_20 F)

noncomputable def wall_cellD_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 1 [(2, false), (3, false), (4, false), (6, false), (7, true), (8, false)] 1 0 6 1 0 2 (by decide)

def WallE_cellD_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t1_10_61 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t1_10_61 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t1_10_61 F)

noncomputable def wall_cellD_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 1 [(0, false), (2, false), (3, false), (6, false), (7, true), (8, false)] 1 6 6 0 0 2 (by decide)

def WallE_cellD_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t1_16_60 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t1_16_60 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t1_16_60 F)

noncomputable def wall_cellD_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true)] 0 3 3 4 1 0 (by decide)

def WallE_cellD_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_03_34 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_03_34 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_03_34 F)

noncomputable def wall_cellD_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (7, true), (8, false)] 0 3 3 5 1 0 (by decide)

def WallE_cellD_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_03_35 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_03_35 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_03_35 F)

noncomputable def wall_cellD_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true), (8, false)] 0 4 3 0 1 0 (by decide)

def WallE_cellD_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_04_30 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_04_30 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_04_30 F)

noncomputable def wall_cellD_t3_04_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true)] 0 4 3 4 1 0 (by decide)

def WallE_cellD_t3_04_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_04_34 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_04_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_04_34 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_04_34 F)

noncomputable def wall_cellD_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, false)] 0 4 3 5 1 0 (by decide)

def WallE_cellD_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_04_35 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_04_35 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_04_35 F)

noncomputable def wall_cellD_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true), (8, false)] 0 5 3 0 1 0 (by decide)

def WallE_cellD_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_05_30 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_05_30 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_05_30 F)

noncomputable def wall_cellD_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, false)] 0 5 3 4 1 0 (by decide)

def WallE_cellD_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_05_34 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_05_34 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_05_34 F)

noncomputable def wall_cellD_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (4, false), (5, true), (7, true), (8, false)] 0 5 3 5 1 0 (by decide)

def WallE_cellD_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_05_35 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_05_35 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_05_35 F)

noncomputable def wall_cellD_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, false)] 4 0 5 3 1 0 (by decide)

def WallE_cellD_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_40_53 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_40_53 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_40_53 F)

noncomputable def wall_cellD_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true), (8, false)] 4 0 5 4 1 0 (by decide)

def WallE_cellD_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_40_54 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_40_54 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_40_54 F)

noncomputable def wall_cellD_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, false)] 4 3 5 0 1 0 (by decide)

def WallE_cellD_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_43_50 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_43_50 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_43_50 F)

noncomputable def wall_cellD_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true)] 4 3 5 4 1 0 (by decide)

def WallE_cellD_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_43_54 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_43_54 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_43_54 F)

noncomputable def wall_cellD_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true), (8, false)] 4 5 5 0 1 0 (by decide)

def WallE_cellD_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_45_50 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_45_50 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_45_50 F)

noncomputable def wall_cellD_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (7, true), (8, false)] 4 5 5 3 1 0 (by decide)

def WallE_cellD_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t3_45_53 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t3_45_53 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t3_45_53 F)

noncomputable def wall_cellD_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 4 [(0, false), (2, false), (5, true), (6, false), (7, true), (8, false)] 0 4 6 0 1 0 (by decide)

def WallE_cellD_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t4_04_60 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t4_04_60 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t4_04_60 F)

noncomputable def wall_cellD_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 4 [(0, false), (2, false), (3, false), (5, true), (6, false), (7, true)] 0 6 6 4 1 0 (by decide)

def WallE_cellD_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t4_06_64 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t4_06_64 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t4_06_64 F)

noncomputable def wall_cellD_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 5 [(2, false), (3, false), (4, false), (6, false), (7, true), (8, false)] 1 2 6 1 1 0 (by decide)

def WallE_cellD_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t5_12_61 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t5_12_61 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t5_12_61 F)

noncomputable def wall_cellD_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 5 [(1, true), (2, false), (3, false), (4, false), (6, false), (8, false)] 2 1 6 2 1 0 (by decide)

def WallE_cellD_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t5_21_62 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t5_21_62 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t5_21_62 F)

noncomputable def wall_cellD_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 6 [(0, false), (1, true), (2, false), (4, false), (5, true), (8, false)] 2 3 3 5 0 2 (by decide)

def WallE_cellD_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t6_23_35 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t6_23_35 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t6_23_35 F)

noncomputable def wall_cellD_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 6 [(0, false), (1, true), (3, false), (4, false), (5, true), (8, false)] 2 5 3 2 0 2 (by decide)

def WallE_cellD_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t6_25_32 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t6_25_32 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t6_25_32 F)

noncomputable def wall_cellD_t7_23_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 7 [(0, false), (1, true), (2, false), (3, false), (4, false), (8, false)] 2 3 6 2 2 0 (by decide)

def WallE_cellD_t7_23_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t7_23_62 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t7_23_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t7_23_62 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t7_23_62 F)

noncomputable def wall_cellD_t7_23_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 7 [(0, false), (1, true), (2, false), (4, false)] 2 3 6 3 2 0 (by decide)

def WallE_cellD_t7_23_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t7_23_63 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t7_23_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t7_23_63 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t7_23_63 F)

noncomputable def wall_cellD_t7_26_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 7 [(0, false), (1, true), (2, false), (3, false), (4, false), (6, false)] 2 6 6 3 2 0 (by decide)

def WallE_cellD_t7_26_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t7_26_63 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t7_26_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t7_26_63 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t7_26_63 F)

noncomputable def wall_cellD_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 8 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false)] 3 4 6 3 0 3 (by decide)

def WallE_cellD_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t8_34_63 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t8_34_63 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t8_34_63 F)

noncomputable def wall_cellD_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD :=
  cellWallOf F cellD 8 [(0, false), (1, true), (2, false), (3, false), (5, true), (6, false)] 3 6 6 4 0 3 (by decide)

def WallE_cellD_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD (wall_cellD_t8_36_64 F) (cellRimScalar cellD 0 2 0 3 x)

theorem cert_cellD_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD_t8_36_64 x F :=
  cellWall_cert_or_E F cellD 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD_t8_36_64 F)

noncomputable def wall_cellD6_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 0 [(3, false), (4, false), (5, true), (6, false), (7, true), (8, true)] 0 2 1 0 3 0 (by decide)

def WallE_cellD6_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t0_02_10 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t0_02_10 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t0_02_10 F)

noncomputable def wall_cellD6_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 0 [(1, true), (3, false), (4, false), (6, false), (7, true), (8, true)] 1 2 2 0 3 0 (by decide)

def WallE_cellD6_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t0_12_20 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t0_12_20 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t0_12_20 F)

noncomputable def wall_cellD6_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 1 [(2, false), (3, false), (4, false), (6, false), (7, true), (8, true)] 1 0 6 1 0 2 (by decide)

def WallE_cellD6_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t1_10_61 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t1_10_61 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t1_10_61 F)

noncomputable def wall_cellD6_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 1 [(0, false), (2, false), (3, false), (6, false), (7, true), (8, true)] 1 6 6 0 0 2 (by decide)

def WallE_cellD6_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t1_16_60 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t1_16_60 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t1_16_60 F)

noncomputable def wall_cellD6_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (7, true), (8, true)] 0 3 3 5 1 0 (by decide)

def WallE_cellD6_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_03_35 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_03_35 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_03_35 F)

noncomputable def wall_cellD6_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true), (8, true)] 0 4 3 0 1 0 (by decide)

def WallE_cellD6_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_04_30 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_04_30 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_04_30 F)

noncomputable def wall_cellD6_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, true)] 0 4 3 5 1 0 (by decide)

def WallE_cellD6_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_04_35 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_04_35 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_04_35 F)

noncomputable def wall_cellD6_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true), (8, true)] 0 5 3 0 1 0 (by decide)

def WallE_cellD6_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_05_30 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_05_30 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_05_30 F)

noncomputable def wall_cellD6_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, true)] 0 5 3 4 1 0 (by decide)

def WallE_cellD6_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_05_34 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_05_34 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_05_34 F)

noncomputable def wall_cellD6_t3_05_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (7, true), (8, true)] 0 5 3 5 1 0 (by decide)

def WallE_cellD6_t3_05_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_05_35 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_05_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_05_35 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_05_35 F)

noncomputable def wall_cellD6_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true)] 3 0 4 3 1 0 (by decide)

def WallE_cellD6_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_30_43 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_30_43 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_30_43 F)

noncomputable def wall_cellD6_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true)] 3 0 4 5 1 0 (by decide)

def WallE_cellD6_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_30_45 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_30_45 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_30_45 F)

noncomputable def wall_cellD6_t3_34_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true)] 3 4 4 0 1 0 (by decide)

def WallE_cellD6_t3_34_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_34_40 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_34_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_34_40 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_34_40 F)

noncomputable def wall_cellD6_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true)] 3 4 4 5 1 0 (by decide)

def WallE_cellD6_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_34_45 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_34_45 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_34_45 F)

noncomputable def wall_cellD6_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true)] 3 5 4 0 1 0 (by decide)

def WallE_cellD6_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_35_40 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_35_40 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_35_40 F)

noncomputable def wall_cellD6_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (7, true)] 3 5 4 3 1 0 (by decide)

def WallE_cellD6_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_35_43 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_35_43 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_35_43 F)

noncomputable def wall_cellD6_t3_35_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (7, true)] 3 5 4 5 1 0 (by decide)

def WallE_cellD6_t3_35_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_35_45 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_35_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_35_45 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_35_45 F)

noncomputable def wall_cellD6_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, true)] 4 0 5 3 1 0 (by decide)

def WallE_cellD6_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_40_53 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_40_53 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_40_53 F)

noncomputable def wall_cellD6_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true), (8, true)] 4 0 5 4 1 0 (by decide)

def WallE_cellD6_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_40_54 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_40_54 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_40_54 F)

noncomputable def wall_cellD6_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false), (7, true), (8, true)] 4 3 5 0 1 0 (by decide)

def WallE_cellD6_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_43_50 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_43_50 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_43_50 F)

noncomputable def wall_cellD6_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (4, false), (5, true), (6, false), (7, true), (8, true)] 4 5 5 0 1 0 (by decide)

def WallE_cellD6_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_45_50 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_45_50 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_45_50 F)

noncomputable def wall_cellD6_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 3 [(0, false), (1, true), (2, false), (4, false), (5, true), (7, true), (8, true)] 4 5 5 3 1 0 (by decide)

def WallE_cellD6_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t3_45_53 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t3_45_53 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t3_45_53 F)

noncomputable def wall_cellD6_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 4 [(0, false), (2, false), (5, true), (6, false), (7, true), (8, true)] 0 4 6 0 1 0 (by decide)

def WallE_cellD6_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t4_04_60 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t4_04_60 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t4_04_60 F)

noncomputable def wall_cellD6_t4_40_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 4 [(0, false), (1, true), (2, false), (5, true), (6, false), (7, true)] 4 0 6 4 1 0 (by decide)

def WallE_cellD6_t4_40_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t4_40_64 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t4_40_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t4_40_64 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t4_40_64 F)

noncomputable def wall_cellD6_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 5 [(2, false), (3, false), (4, false), (6, false), (7, true), (8, true)] 1 2 6 1 1 0 (by decide)

def WallE_cellD6_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t5_12_61 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t5_12_61 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t5_12_61 F)

noncomputable def wall_cellD6_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 5 [(1, true), (2, false), (3, false), (4, false), (6, false), (8, true)] 2 1 6 2 1 0 (by decide)

def WallE_cellD6_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t5_21_62 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t5_21_62 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t5_21_62 F)

noncomputable def wall_cellD6_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 6 [(0, false), (1, true), (2, false), (4, false), (5, true), (8, true)] 2 3 3 5 0 2 (by decide)

def WallE_cellD6_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t6_23_35 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t6_23_35 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t6_23_35 F)

noncomputable def wall_cellD6_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 6 [(0, false), (1, true), (3, false), (4, false), (5, true), (8, true)] 2 5 3 2 0 2 (by decide)

def WallE_cellD6_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t6_25_32 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t6_25_32 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t6_25_32 F)

noncomputable def wall_cellD6_t7_23_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 7 [(0, false), (1, true), (2, false), (3, false), (4, false), (8, true)] 2 3 6 2 2 0 (by decide)

def WallE_cellD6_t7_23_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t7_23_62 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t7_23_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t7_23_62 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t7_23_62 F)

noncomputable def wall_cellD6_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 7 [(0, false), (1, true), (2, false), (3, false), (4, false), (5, true)] 3 2 6 3 2 0 (by decide)

def WallE_cellD6_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t7_32_63 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t7_32_63 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t7_32_63 F)

noncomputable def wall_cellD6_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 8 [(0, false), (1, true), (2, false), (4, false), (5, true), (6, false)] 3 4 6 3 3 0 (by decide)

def WallE_cellD6_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t8_34_63 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t8_34_63 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t8_34_63 F)

noncomputable def wall_cellD6_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellD6 :=
  cellWallOf F cellD6 8 [(0, false), (1, true), (2, false), (3, false), (5, true), (6, false)] 3 6 6 4 3 0 (by decide)

def WallE_cellD6_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellD6 (wall_cellD6_t8_36_64 F) (cellRimScalar cellD6 0 2 0 3 x)

theorem cert_cellD6_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellD6_t8_36_64 x F :=
  cellWall_cert_or_E F cellD6 0 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellD6_t8_36_64 F)

noncomputable def wall_cellA2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 0 [(2, false), (3, true), (4, true), (6, false), (7, false), (8, true)] 0 1 1 2 3 0 (by decide)

def WallE_cellA2_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t0_01_12 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t0_01_12 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t0_01_12 F)

noncomputable def wall_cellA2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 0 [(3, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 2 1 0 3 0 (by decide)

def WallE_cellA2_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t0_02_10 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t0_02_10 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t0_02_10 F)

noncomputable def wall_cellA2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 1 [(2, false), (3, true), (5, false), (6, false), (7, false), (8, true)] 0 1 6 0 0 2 (by decide)

def WallE_cellA2_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t1_01_60 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t1_01_60 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t1_01_60 F)

noncomputable def wall_cellA2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 1 [(0, false), (2, false), (3, true), (6, false), (7, false), (8, true)] 0 6 6 1 0 2 (by decide)

def WallE_cellA2_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t1_06_61 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t1_06_61 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t1_06_61 F)

noncomputable def wall_cellA2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 2 [(1, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cellA2_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t2_02_50 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t2_02_50 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t2_02_50 F)

noncomputable def wall_cellA2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 2 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, true)] 0 5 5 2 1 0 (by decide)

def WallE_cellA2_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t2_05_52 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t2_05_52 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t2_05_52 F)

noncomputable def wall_cellA2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, true)] 0 3 3 5 0 1 (by decide)

def WallE_cellA2_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_03_35 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_03_35 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_03_35 F)

noncomputable def wall_cellA2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cellA2_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_03_40 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_03_40 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_03_40 F)

noncomputable def wall_cellA2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, true)] 0 3 4 5 0 1 (by decide)

def WallE_cellA2_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_03_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_03_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_03_45 F)

noncomputable def wall_cellA2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cellA2_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_04_35 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_04_35 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_04_35 F)

noncomputable def wall_cellA2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cellA2_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_04_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_04_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_04_45 F)

noncomputable def wall_cellA2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cellA2_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_30 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_30 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_30 F)

noncomputable def wall_cellA2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cellA2_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_34 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_34 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_34 F)

noncomputable def wall_cellA2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (5, false), (6, false), (7, false), (8, true)] 0 5 4 0 0 1 (by decide)

def WallE_cellA2_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_40 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_40 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_40 F)

noncomputable def wall_cellA2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, true)] 0 5 4 3 0 1 (by decide)

def WallE_cellA2_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_05_43 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_05_43 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_05_43 F)

noncomputable def wall_cellA2_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 0 4 3 0 1 (by decide)

def WallE_cellA2_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_30_43 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_30_43 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_30_43 F)

noncomputable def wall_cellA2_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false)] 3 0 4 5 0 1 (by decide)

def WallE_cellA2_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_30_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_30_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_30_45 F)

noncomputable def wall_cellA2_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 4 4 5 0 1 (by decide)

def WallE_cellA2_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_34_45 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_34_45 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_34_45 F)

noncomputable def wall_cellA2_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false)] 3 5 4 0 0 1 (by decide)

def WallE_cellA2_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_35_40 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_35_40 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_35_40 F)

noncomputable def wall_cellA2_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false)] 3 5 4 3 0 1 (by decide)

def WallE_cellA2_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_35_43 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_35_43 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_35_43 F)

noncomputable def wall_cellA2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cellA2_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_40_53 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_40_53 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_40_53 F)

noncomputable def wall_cellA2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cellA2_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_43_50 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_43_50 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_43_50 F)

noncomputable def wall_cellA2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cellA2_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_45_50 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_45_50 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_45_50 F)

noncomputable def wall_cellA2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, true)] 4 5 5 3 0 1 (by decide)

def WallE_cellA2_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t3_45_53 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t3_45_53 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t3_45_53 F)

noncomputable def wall_cellA2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 5 [(2, false), (3, true), (4, true), (6, false), (7, false), (8, true)] 1 2 6 1 0 1 (by decide)

def WallE_cellA2_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t5_12_61 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t5_12_61 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t5_12_61 F)

noncomputable def wall_cellA2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 5 [(0, false), (2, false), (3, true), (4, true), (6, false), (8, true)] 1 6 6 2 0 1 (by decide)

def WallE_cellA2_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t5_16_62 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t5_16_62 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t5_16_62 F)

noncomputable def wall_cellA2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 6 [(0, false), (1, true), (2, false), (4, true), (5, false), (8, true)] 3 2 5 3 0 2 (by decide)

def WallE_cellA2_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t6_32_53 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t6_32_53 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t6_32_53 F)

noncomputable def wall_cellA2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 6 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, true)] 3 5 5 2 0 2 (by decide)

def WallE_cellA2_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t6_35_52 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t6_35_52 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t6_35_52 F)

noncomputable def wall_cellA2_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 7 [(0, false), (1, true), (2, false), (3, true), (4, true), (5, false)] 3 2 6 3 0 2 (by decide)

def WallE_cellA2_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t7_32_63 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t7_32_63 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t7_32_63 F)

noncomputable def wall_cellA2_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 7 [(0, false), (1, true), (2, false), (3, true), (4, true), (6, false)] 3 6 6 2 0 2 (by decide)

def WallE_cellA2_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t7_36_62 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t7_36_62 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t7_36_62 F)

noncomputable def wall_cellA2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 8 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false)] 3 6 4 3 3 0 (by decide)

def WallE_cellA2_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t8_36_43 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t8_36_43 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t8_36_43 F)

noncomputable def wall_cellA2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA2 :=
  cellWallOf F cellA2 8 [(0, false), (1, true), (2, false), (3, true), (5, false), (6, false)] 4 6 6 3 3 0 (by decide)

def WallE_cellA2_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA2 (wall_cellA2_t8_46_63 F) (cellRimScalar cellA2 0 2 3 1 x)

theorem cert_cellA2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA2_t8_46_63 x F :=
  cellWall_cert_or_E F cellA2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA2_t8_46_63 F)

noncomputable def wall_cellB2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 0 [(2, false), (3, true), (4, true), (6, false), (7, false), (8, false)] 0 1 1 2 3 0 (by decide)

def WallE_cellB2_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t0_01_12 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t0_01_12 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t0_01_12 F)

noncomputable def wall_cellB2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 0 [(3, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 2 1 0 3 0 (by decide)

def WallE_cellB2_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t0_02_10 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t0_02_10 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t0_02_10 F)

noncomputable def wall_cellB2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 1 [(2, false), (3, true), (5, false), (6, false), (7, false), (8, false)] 0 1 6 0 0 2 (by decide)

def WallE_cellB2_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t1_01_60 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t1_01_60 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t1_01_60 F)

noncomputable def wall_cellB2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 1 [(0, false), (2, false), (3, true), (6, false), (7, false), (8, false)] 0 6 6 1 0 2 (by decide)

def WallE_cellB2_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t1_06_61 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t1_06_61 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t1_06_61 F)

noncomputable def wall_cellB2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 2 [(1, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 2 5 0 1 0 (by decide)

def WallE_cellB2_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t2_02_50 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t2_02_50 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t2_02_50 F)

noncomputable def wall_cellB2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 2 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, false)] 0 5 5 2 1 0 (by decide)

def WallE_cellB2_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t2_05_52 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t2_05_52 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t2_05_52 F)

noncomputable def wall_cellB2_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 0 3 3 4 0 1 (by decide)

def WallE_cellB2_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_03_34 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_03_34 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_03_34 F)

noncomputable def wall_cellB2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, false)] 0 3 3 5 0 1 (by decide)

def WallE_cellB2_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_03_35 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_03_35 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_03_35 F)

noncomputable def wall_cellB2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, false)] 0 3 4 0 0 1 (by decide)

def WallE_cellB2_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_03_40 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_03_40 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_03_40 F)

noncomputable def wall_cellB2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, false)] 0 3 4 5 0 1 (by decide)

def WallE_cellB2_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_03_45 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_03_45 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_03_45 F)

noncomputable def wall_cellB2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 4 3 5 0 1 (by decide)

def WallE_cellB2_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_04_35 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_04_35 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_04_35 F)

noncomputable def wall_cellB2_t3_04_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 0 4 4 3 0 1 (by decide)

def WallE_cellB2_t3_04_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_04_43 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_04_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_04_43 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_04_43 F)

noncomputable def wall_cellB2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, false)] 0 4 4 5 0 1 (by decide)

def WallE_cellB2_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_04_45 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_04_45 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_04_45 F)

noncomputable def wall_cellB2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 5 3 0 0 1 (by decide)

def WallE_cellB2_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_30 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_30 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_30 F)

noncomputable def wall_cellB2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 5 3 4 0 1 (by decide)

def WallE_cellB2_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_34 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_34 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_34 F)

noncomputable def wall_cellB2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (5, false), (6, false), (7, false), (8, false)] 0 5 4 0 0 1 (by decide)

def WallE_cellB2_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_40 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_40 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_40 F)

noncomputable def wall_cellB2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, false)] 0 5 4 3 0 1 (by decide)

def WallE_cellB2_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_05_43 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_05_43 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_05_43 F)

noncomputable def wall_cellB2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 0 5 3 0 1 (by decide)

def WallE_cellB2_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_40_53 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_40_53 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_40_53 F)

noncomputable def wall_cellB2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 3 5 0 0 1 (by decide)

def WallE_cellB2_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_43_50 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_43_50 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_43_50 F)

noncomputable def wall_cellB2_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 4 3 5 4 0 1 (by decide)

def WallE_cellB2_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_43_54 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_43_54 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_43_54 F)

noncomputable def wall_cellB2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 5 5 0 0 1 (by decide)

def WallE_cellB2_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_45_50 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_45_50 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_45_50 F)

noncomputable def wall_cellB2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, false)] 4 5 5 3 0 1 (by decide)

def WallE_cellB2_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t3_45_53 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t3_45_53 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t3_45_53 F)

noncomputable def wall_cellB2_t4_04_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 4 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 0 4 4 6 0 1 (by decide)

def WallE_cellB2_t4_04_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t4_04_46 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t4_04_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t4_04_46 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t4_04_46 F)

noncomputable def wall_cellB2_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 4 [(0, false), (2, false), (3, true), (5, false), (6, false), (7, false)] 0 6 6 4 0 1 (by decide)

def WallE_cellB2_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t4_06_64 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t4_06_64 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t4_06_64 F)

noncomputable def wall_cellB2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 5 [(2, false), (3, true), (4, true), (6, false), (7, false), (8, false)] 1 2 6 1 0 1 (by decide)

def WallE_cellB2_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t5_12_61 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t5_12_61 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t5_12_61 F)

noncomputable def wall_cellB2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 5 [(0, false), (2, false), (3, true), (4, true), (6, false), (8, false)] 1 6 6 2 0 1 (by decide)

def WallE_cellB2_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t5_16_62 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t5_16_62 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t5_16_62 F)

noncomputable def wall_cellB2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 6 [(0, false), (1, true), (2, false), (4, true), (5, false), (8, false)] 3 2 5 3 0 2 (by decide)

def WallE_cellB2_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t6_32_53 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t6_32_53 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t6_32_53 F)

noncomputable def wall_cellB2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 6 [(0, false), (1, true), (4, true), (5, false), (7, false), (8, false)] 3 5 5 2 0 2 (by decide)

def WallE_cellB2_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t6_35_52 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t6_35_52 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t6_35_52 F)

noncomputable def wall_cellB2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 8 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false)] 3 6 4 3 0 3 (by decide)

def WallE_cellB2_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t8_36_43 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t8_36_43 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t8_36_43 F)

noncomputable def wall_cellB2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB2 :=
  cellWallOf F cellB2 8 [(0, false), (1, true), (2, false), (3, true), (5, false), (6, false)] 4 6 6 3 0 3 (by decide)

def WallE_cellB2_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB2 (wall_cellB2_t8_46_63 F) (cellRimScalar cellB2 0 2 3 1 x)

theorem cert_cellB2_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB2_t8_46_63 x F :=
  cellWall_cert_or_E F cellB2 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB2_t8_46_63 F)

noncomputable def wall_cellA0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 0 [(2, false), (3, false), (4, false), (6, true), (7, true), (8, false)] 1 0 2 1 3 0 (by decide)

def WallE_cellA0_t0_10_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t0_10_21 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t0_10_21 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t0_10_21 F)

noncomputable def wall_cellA0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 0 [(1, false), (3, false), (4, false), (6, true), (7, true), (8, false)] 1 2 2 0 3 0 (by decide)

def WallE_cellA0_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t0_12_20 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t0_12_20 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t0_12_20 F)

noncomputable def wall_cellA0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 1 [(2, false), (3, false), (4, false), (6, true), (7, true), (8, false)] 1 0 6 1 2 0 (by decide)

def WallE_cellA0_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t1_10_61 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t1_10_61 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t1_10_61 F)

noncomputable def wall_cellA0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 1 [(0, false), (2, false), (3, false), (6, true), (7, true), (8, false)] 1 6 6 0 2 0 (by decide)

def WallE_cellA0_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t1_16_60 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t1_16_60 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t1_16_60 F)

noncomputable def wall_cellA0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 2 [(1, false), (3, false), (4, false), (5, true), (7, true), (8, false)] 2 0 5 2 1 0 (by decide)

def WallE_cellA0_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t2_20_52 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t2_20_52 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t2_20_52 F)

noncomputable def wall_cellA0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 2 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, false)] 2 5 5 0 1 0 (by decide)

def WallE_cellA0_t2_25_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t2_25_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t2_25_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t2_25_50 F)

noncomputable def wall_cellA0_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 0 3 3 4 1 0 (by decide)

def WallE_cellA0_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_03_34 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_03_34 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_03_34 F)

noncomputable def wall_cellA0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, false)] 0 4 3 0 1 0 (by decide)

def WallE_cellA0_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_04_30 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_04_30 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_04_30 F)

noncomputable def wall_cellA0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 0 4 3 5 1 0 (by decide)

def WallE_cellA0_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_04_35 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_04_35 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_04_35 F)

noncomputable def wall_cellA0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 0 5 3 0 1 0 (by decide)

def WallE_cellA0_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_05_30 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_05_30 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_05_30 F)

noncomputable def wall_cellA0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 0 5 3 4 1 0 (by decide)

def WallE_cellA0_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_05_34 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_05_34 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_05_34 F)

noncomputable def wall_cellA0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, false)] 3 0 5 3 1 0 (by decide)

def WallE_cellA0_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_30_53 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_30_53 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_30_53 F)

noncomputable def wall_cellA0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, false)] 3 0 5 4 1 0 (by decide)

def WallE_cellA0_t3_30_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_30_54 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_30_54 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_30_54 F)

noncomputable def wall_cellA0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, false)] 3 4 5 0 1 0 (by decide)

def WallE_cellA0_t3_34_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_34_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_34_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_34_50 F)

noncomputable def wall_cellA0_t3_34_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true)] 3 4 5 3 1 0 (by decide)

def WallE_cellA0_t3_34_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_34_53 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_34_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_34_53 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_34_53 F)

noncomputable def wall_cellA0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, false)] 3 5 5 0 1 0 (by decide)

def WallE_cellA0_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_35_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_35_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_35_50 F)

noncomputable def wall_cellA0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, false)] 3 5 5 4 1 0 (by decide)

def WallE_cellA0_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_35_54 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_35_54 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_35_54 F)

noncomputable def wall_cellA0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 4 0 5 3 1 0 (by decide)

def WallE_cellA0_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_40_53 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_40_53 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_40_53 F)

noncomputable def wall_cellA0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, false)] 4 0 5 4 1 0 (by decide)

def WallE_cellA0_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_40_54 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_40_54 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_40_54 F)

noncomputable def wall_cellA0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 4 3 5 0 1 0 (by decide)

def WallE_cellA0_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_43_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_43_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_43_50 F)

noncomputable def wall_cellA0_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 4 3 5 4 1 0 (by decide)

def WallE_cellA0_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_43_54 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_43_54 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_43_54 F)

noncomputable def wall_cellA0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, false)] 4 5 5 0 1 0 (by decide)

def WallE_cellA0_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t3_45_50 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t3_45_50 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t3_45_50 F)

noncomputable def wall_cellA0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 5 [(1, false), (2, false), (3, false), (4, false), (6, true), (8, false)] 2 1 6 2 1 0 (by decide)

def WallE_cellA0_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t5_21_62 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t5_21_62 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t5_21_62 F)

noncomputable def wall_cellA0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 5 [(0, false), (2, false), (3, false), (4, false), (6, true), (8, false)] 2 6 6 1 1 0 (by decide)

def WallE_cellA0_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t5_26_61 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t5_26_61 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t5_26_61 F)

noncomputable def wall_cellA0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 6 [(0, false), (1, false), (2, false), (4, false), (5, true), (8, false)] 2 3 3 5 2 0 (by decide)

def WallE_cellA0_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t6_23_35 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t6_23_35 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t6_23_35 F)

noncomputable def wall_cellA0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 6 [(0, false), (1, false), (3, false), (4, false), (5, true), (8, false)] 2 5 3 2 2 0 (by decide)

def WallE_cellA0_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t6_25_32 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t6_25_32 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t6_25_32 F)

noncomputable def wall_cellA0_t7_23_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 7 [(0, false), (1, false), (2, false), (3, false), (4, false), (5, true)] 2 3 3 6 2 0 (by decide)

def WallE_cellA0_t7_23_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t7_23_36 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t7_23_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t7_23_36 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t7_23_36 F)

noncomputable def wall_cellA0_t7_26_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 7 [(0, false), (1, false), (2, false), (3, false), (4, false), (6, true)] 2 6 6 3 2 0 (by decide)

def WallE_cellA0_t7_26_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t7_26_63 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t7_26_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t7_26_63 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t7_26_63 F)

noncomputable def wall_cellA0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 8 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true)] 3 4 6 3 0 3 (by decide)

def WallE_cellA0_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t8_34_63 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t8_34_63 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t8_34_63 F)

noncomputable def wall_cellA0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellA0 :=
  cellWallOf F cellA0 8 [(0, false), (1, false), (2, false), (3, false), (5, true), (6, true)] 3 6 6 4 0 3 (by decide)

def WallE_cellA0_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellA0 (wall_cellA0_t8_36_64 F) (cellRimScalar cellA0 0 4 5 0 x)

theorem cert_cellA0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellA0_t8_36_64 x F :=
  cellWall_cert_or_E F cellA0 0 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellA0_t8_36_64 F)

noncomputable def wall_cellB0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 0 [(2, false), (3, false), (4, false), (6, true), (7, true), (8, true)] 1 0 2 1 3 0 (by decide)

def WallE_cellB0_t0_10_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t0_10_21 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t0_10_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t0_10_21 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t0_10_21 F)

noncomputable def wall_cellB0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 0 [(1, false), (3, false), (4, false), (6, true), (7, true), (8, true)] 1 2 2 0 3 0 (by decide)

def WallE_cellB0_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t0_12_20 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t0_12_20 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t0_12_20 F)

noncomputable def wall_cellB0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 1 [(2, false), (3, false), (4, false), (6, true), (7, true), (8, true)] 1 0 6 1 2 0 (by decide)

def WallE_cellB0_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t1_10_61 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t1_10_61 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t1_10_61 F)

noncomputable def wall_cellB0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 1 [(0, false), (2, false), (3, false), (6, true), (7, true), (8, true)] 1 6 6 0 2 0 (by decide)

def WallE_cellB0_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t1_16_60 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t1_16_60 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t1_16_60 F)

noncomputable def wall_cellB0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 2 [(1, false), (3, false), (4, false), (5, true), (7, true), (8, true)] 2 0 5 2 1 0 (by decide)

def WallE_cellB0_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t2_20_52 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t2_20_52 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t2_20_52 F)

noncomputable def wall_cellB0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 2 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, true)] 2 5 5 0 1 0 (by decide)

def WallE_cellB0_t2_25_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t2_25_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t2_25_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t2_25_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t2_25_50 F)

noncomputable def wall_cellB0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, true)] 0 4 3 0 1 0 (by decide)

def WallE_cellB0_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_04_30 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_04_30 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_04_30 F)

noncomputable def wall_cellB0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 4 3 5 1 0 (by decide)

def WallE_cellB0_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_04_35 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_04_35 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_04_35 F)

noncomputable def wall_cellB0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 5 3 0 1 0 (by decide)

def WallE_cellB0_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_05_30 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_05_30 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_05_30 F)

noncomputable def wall_cellB0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 5 3 4 1 0 (by decide)

def WallE_cellB0_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_05_34 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_05_34 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_05_34 F)

noncomputable def wall_cellB0_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 3 0 4 3 1 0 (by decide)

def WallE_cellB0_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_43 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_43 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_43 F)

noncomputable def wall_cellB0_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true)] 3 0 4 5 1 0 (by decide)

def WallE_cellB0_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_45 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_45 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_45 F)

noncomputable def wall_cellB0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, true)] 3 0 5 3 1 0 (by decide)

def WallE_cellB0_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_53 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_53 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_53 F)

noncomputable def wall_cellB0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, true)] 3 0 5 4 1 0 (by decide)

def WallE_cellB0_t3_30_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_30_54 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_30_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_30_54 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_30_54 F)

noncomputable def wall_cellB0_t3_34_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true)] 3 4 4 0 1 0 (by decide)

def WallE_cellB0_t3_34_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_34_40 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_34_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_34_40 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_34_40 F)

noncomputable def wall_cellB0_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 3 4 4 5 1 0 (by decide)

def WallE_cellB0_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_34_45 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_34_45 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_34_45 F)

noncomputable def wall_cellB0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, true)] 3 4 5 0 1 0 (by decide)

def WallE_cellB0_t3_34_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_34_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_34_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_34_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_34_50 F)

noncomputable def wall_cellB0_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true)] 3 5 4 0 1 0 (by decide)

def WallE_cellB0_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_35_40 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_35_40 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_35_40 F)

noncomputable def wall_cellB0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, true)] 3 5 5 0 1 0 (by decide)

def WallE_cellB0_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_35_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_35_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_35_50 F)

noncomputable def wall_cellB0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, true)] 3 5 5 4 1 0 (by decide)

def WallE_cellB0_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_35_54 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_35_54 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_35_54 F)

noncomputable def wall_cellB0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 0 5 3 1 0 (by decide)

def WallE_cellB0_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_40_53 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_40_53 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_40_53 F)

noncomputable def wall_cellB0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, true)] 4 0 5 4 1 0 (by decide)

def WallE_cellB0_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_40_54 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_40_54 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_40_54 F)

noncomputable def wall_cellB0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 3 5 0 1 0 (by decide)

def WallE_cellB0_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_43_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_43_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_43_50 F)

noncomputable def wall_cellB0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 5 5 0 1 0 (by decide)

def WallE_cellB0_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t3_45_50 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t3_45_50 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t3_45_50 F)

noncomputable def wall_cellB0_t4_40_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 4 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true)] 4 0 6 4 1 0 (by decide)

def WallE_cellB0_t4_40_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t4_40_64 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t4_40_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t4_40_64 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t4_40_64 F)

noncomputable def wall_cellB0_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 4 [(0, false), (2, false), (3, false), (5, true), (6, true), (7, true)] 4 6 6 0 1 0 (by decide)

def WallE_cellB0_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t4_46_60 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t4_46_60 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t4_46_60 F)

noncomputable def wall_cellB0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 5 [(1, false), (2, false), (3, false), (4, false), (6, true), (8, true)] 2 1 6 2 1 0 (by decide)

def WallE_cellB0_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t5_21_62 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t5_21_62 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t5_21_62 F)

noncomputable def wall_cellB0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 5 [(0, false), (2, false), (3, false), (4, false), (6, true), (8, true)] 2 6 6 1 1 0 (by decide)

def WallE_cellB0_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t5_26_61 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t5_26_61 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t5_26_61 F)

noncomputable def wall_cellB0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 6 [(0, false), (1, false), (2, false), (4, false), (5, true), (8, true)] 2 3 3 5 2 0 (by decide)

def WallE_cellB0_t6_23_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t6_23_35 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t6_23_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t6_23_35 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t6_23_35 F)

noncomputable def wall_cellB0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 6 [(0, false), (1, false), (3, false), (4, false), (5, true), (8, true)] 2 5 3 2 2 0 (by decide)

def WallE_cellB0_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t6_25_32 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t6_25_32 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t6_25_32 F)

noncomputable def wall_cellB0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 8 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true)] 3 4 6 3 3 0 (by decide)

def WallE_cellB0_t8_34_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t8_34_63 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t8_34_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t8_34_63 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t8_34_63 F)

noncomputable def wall_cellB0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellB0 :=
  cellWallOf F cellB0 8 [(0, false), (1, false), (2, false), (3, false), (5, true), (6, true)] 3 6 6 4 3 0 (by decide)

def WallE_cellB0_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellB0 (wall_cellB0_t8_36_64 F) (cellRimScalar cellB0 0 5 5 0 x)

theorem cert_cellB0_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellB0_t8_36_64 x F :=
  cellWall_cert_or_E F cellB0 0 5 5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellB0_t8_36_64 F)

noncomputable def wall_cellCp_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 1 [(2, false), (3, true), (5, false), (6, true), (7, true), (8, true)] 0 1 6 0 2 0 (by decide)

def WallE_cellCp_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t1_01_60 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t1_01_60 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t1_01_60 F)

noncomputable def wall_cellCp_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 1 [(0, false), (2, false), (3, true), (6, true), (7, true), (8, true)] 0 6 6 1 2 0 (by decide)

def WallE_cellCp_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t1_06_61 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t1_06_61 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t1_06_61 F)

noncomputable def wall_cellCp_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 2 [(1, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cellCp_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t2_02_50 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t2_02_50 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t2_02_50 F)

noncomputable def wall_cellCp_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 2 [(1, false), (3, true), (4, true), (5, false), (7, true), (8, true)] 2 0 5 2 1 0 (by decide)

def WallE_cellCp_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t2_20_52 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t2_20_52 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t2_20_52 F)

noncomputable def wall_cellCp_t2_50_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 2 [(1, false), (4, true), (5, false), (7, true), (8, true)] 5 0 5 2 1 0 (by decide)

def WallE_cellCp_t2_50_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t2_50_52 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t2_50_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t2_50_52 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t2_50_52 F)

noncomputable def wall_cellCp_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cellCp_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_03_40 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_03_40 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_03_40 F)

noncomputable def wall_cellCp_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cellCp_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_04_35 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_04_35 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_04_35 F)

noncomputable def wall_cellCp_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cellCp_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_04_45 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_04_45 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_04_45 F)

noncomputable def wall_cellCp_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cellCp_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_05_30 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_05_30 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_05_30 F)

noncomputable def wall_cellCp_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cellCp_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_05_34 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_05_34 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_05_34 F)

noncomputable def wall_cellCp_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (5, false), (6, true), (7, true), (8, true)] 0 5 4 0 0 1 (by decide)

def WallE_cellCp_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_05_40 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_05_40 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_05_40 F)

noncomputable def wall_cellCp_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true)] 3 0 4 3 0 1 (by decide)

def WallE_cellCp_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_30_43 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_30_43 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_30_43 F)

noncomputable def wall_cellCp_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, true)] 3 0 4 5 0 1 (by decide)

def WallE_cellCp_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_30_45 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_30_45 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_30_45 F)

noncomputable def wall_cellCp_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, true), (8, true)] 3 0 5 3 0 1 (by decide)

def WallE_cellCp_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_30_53 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_30_53 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_30_53 F)

noncomputable def wall_cellCp_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true)] 3 4 4 5 0 1 (by decide)

def WallE_cellCp_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_34_45 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_34_45 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_34_45 F)

noncomputable def wall_cellCp_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, true)] 3 5 4 0 0 1 (by decide)

def WallE_cellCp_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_35_40 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_35_40 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_35_40 F)

noncomputable def wall_cellCp_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false), (7, true), (8, true)] 3 5 5 0 0 1 (by decide)

def WallE_cellCp_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_35_50 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_35_50 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_35_50 F)

noncomputable def wall_cellCp_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, true), (8, true)] 3 5 5 4 0 1 (by decide)

def WallE_cellCp_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_35_54 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_35_54 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_35_54 F)

noncomputable def wall_cellCp_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cellCp_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_40_53 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_40_53 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_40_53 F)

noncomputable def wall_cellCp_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cellCp_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_43_50 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_43_50 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_43_50 F)

noncomputable def wall_cellCp_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, true), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cellCp_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t3_45_50 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t3_45_50 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t3_45_50 F)

noncomputable def wall_cellCp_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 4 [(0, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 0 6 4 0 0 1 (by decide)

def WallE_cellCp_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t4_06_40 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t4_06_40 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t4_06_40 F)

noncomputable def wall_cellCp_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 4 [(0, false), (2, false), (3, true), (5, false), (6, true), (7, true)] 4 6 6 0 0 1 (by decide)

def WallE_cellCp_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t4_46_60 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t4_46_60 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t4_46_60 F)

noncomputable def wall_cellCp_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 5 [(1, false), (2, false), (3, true), (4, true), (6, true), (8, true)] 2 1 6 2 0 1 (by decide)

def WallE_cellCp_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t5_21_62 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t5_21_62 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t5_21_62 F)

noncomputable def wall_cellCp_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 5 [(0, false), (2, false), (3, true), (4, true), (6, true), (8, true)] 2 6 6 1 0 1 (by decide)

def WallE_cellCp_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t5_26_61 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t5_26_61 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t5_26_61 F)

noncomputable def wall_cellCp_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 6 [(0, false), (1, false), (3, true), (4, true), (5, false), (8, true)] 2 5 3 2 2 0 (by decide)

def WallE_cellCp_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t6_25_32 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t6_25_32 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t6_25_32 F)

noncomputable def wall_cellCp_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 6 [(0, false), (1, false), (4, true), (5, false), (7, true), (8, true)] 3 5 5 2 2 0 (by decide)

def WallE_cellCp_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t6_35_52 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t6_35_52 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t6_35_52 F)

noncomputable def wall_cellCp_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (8, true)] 2 6 3 2 2 0 (by decide)

def WallE_cellCp_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t7_26_32 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t7_26_32 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t7_26_32 F)

noncomputable def wall_cellCp_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellC' :=
  cellWallOf F cellC' 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (6, true)] 3 6 6 2 2 0 (by decide)

def WallE_cellCp_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellC' (wall_cellCp_t7_36_62 F) (cellRimScalar cellC' 0 2 2 1 x)

theorem cert_cellCp_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellCp_t7_36_62 x F :=
  cellWall_cert_or_E F cellC' 0 2 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellCp_t7_36_62 F)

noncomputable def wall_cell0236_t0_01_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 0 [(3, true), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 1 2 0 3 0 (by decide)

def WallE_cell0236_t0_01_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t0_01_20 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t0_01_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t0_01_20 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t0_01_20 F)

noncomputable def wall_cell0236_t0_02_21 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 0 [(1, false), (3, true), (4, true), (6, true), (7, false), (8, true)] 0 2 2 1 3 0 (by decide)

def WallE_cell0236_t0_02_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t0_02_21 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t0_02_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t0_02_21 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t0_02_21 F)

noncomputable def wall_cell0236_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 1 [(2, true), (3, true), (5, false), (6, true), (7, false), (8, true)] 0 1 6 0 2 0 (by decide)

def WallE_cell0236_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t1_01_60 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t1_01_60 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t1_01_60 F)

noncomputable def wall_cell0236_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 1 [(0, false), (2, true), (3, true), (6, true), (7, false), (8, true)] 0 6 6 1 2 0 (by decide)

def WallE_cell0236_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t1_06_61 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t1_06_61 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t1_06_61 F)

noncomputable def wall_cell0236_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 2 [(1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 2 5 0 0 1 (by decide)

def WallE_cell0236_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t2_02_50 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t2_02_50 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t2_02_50 F)

noncomputable def wall_cell0236_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 2 [(1, false), (3, true), (4, true), (5, false), (7, false), (8, true)] 2 0 5 2 0 1 (by decide)

def WallE_cell0236_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t2_20_52 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t2_20_52 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t2_20_52 F)

noncomputable def wall_cell0236_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (5, false), (6, true), (7, false), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cell0236_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_03_40 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_03_40 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_03_40 F)

noncomputable def wall_cell0236_t3_03_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 3 5 0 0 1 (by decide)

def WallE_cell0236_t3_03_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_03_50 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_03_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_03_50 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_03_50 F)

noncomputable def wall_cell0236_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cell0236_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_04_35 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_04_35 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_04_35 F)

noncomputable def wall_cell0236_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (5, false), (6, true), (7, false), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cell0236_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_04_45 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_04_45 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_04_45 F)

noncomputable def wall_cell0236_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cell0236_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_05_34 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_05_34 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_05_34 F)

noncomputable def wall_cell0236_t3_05_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (4, true), (5, false), (6, true), (7, false), (8, true)] 0 5 5 4 0 1 (by decide)

def WallE_cell0236_t3_05_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_05_54 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_05_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_05_54 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_05_54 F)

noncomputable def wall_cell0236_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false)] 3 0 4 3 0 1 (by decide)

def WallE_cell0236_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_30_43 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_30_43 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_30_43 F)

noncomputable def wall_cell0236_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (7, false), (8, true)] 3 0 5 3 0 1 (by decide)

def WallE_cell0236_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_30_53 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_30_53 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_30_53 F)

noncomputable def wall_cell0236_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false)] 3 4 4 5 0 1 (by decide)

def WallE_cell0236_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_34_45 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_34_45 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_34_45 F)

noncomputable def wall_cell0236_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (7, false), (8, true)] 3 5 5 4 0 1 (by decide)

def WallE_cell0236_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_35_54 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_35_54 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_35_54 F)

noncomputable def wall_cell0236_t3_40_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (5, false), (6, true), (7, false)] 4 0 4 3 0 1 (by decide)

def WallE_cell0236_t3_40_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_40_43 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_40_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_40_43 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_40_43 F)

noncomputable def wall_cell0236_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cell0236_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_40_53 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_40_53 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_40_53 F)

noncomputable def wall_cell0236_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true), (7, false), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cell0236_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_43_50 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_43_50 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_43_50 F)

noncomputable def wall_cell0236_t3_50_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 3 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 5 0 5 3 0 1 (by decide)

def WallE_cell0236_t3_50_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t3_50_53 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t3_50_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t3_50_53 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t3_50_53 F)

noncomputable def wall_cell0236_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 4 [(0, false), (2, true), (5, false), (6, true), (7, false), (8, true)] 0 6 4 0 0 1 (by decide)

def WallE_cell0236_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t4_06_40 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t4_06_40 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t4_06_40 F)

noncomputable def wall_cell0236_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 4 [(0, false), (2, true), (3, true), (5, false), (6, true), (7, false)] 4 6 6 0 0 1 (by decide)

def WallE_cell0236_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t4_46_60 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t4_46_60 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t4_46_60 F)

noncomputable def wall_cell0236_t6_23_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 6 [(0, false), (1, false), (3, true), (4, true), (5, false), (8, true)] 2 3 5 2 2 0 (by decide)

def WallE_cell0236_t6_23_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t6_23_52 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t6_23_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t6_23_52 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t6_23_52 F)

noncomputable def wall_cell0236_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 6 [(0, false), (1, false), (2, true), (4, true), (5, false), (8, true)] 3 2 5 3 2 0 (by decide)

def WallE_cell0236_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t6_32_53 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t6_32_53 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t6_32_53 F)

noncomputable def wall_cell0236_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 7 [(0, false), (1, false), (2, true), (3, true), (4, true), (8, true)] 2 6 3 2 0 2 (by decide)

def WallE_cell0236_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t7_26_32 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t7_26_32 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t7_26_32 F)

noncomputable def wall_cell0236_t7_32_36 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 7 [(0, false), (1, false), (2, true), (4, true)] 3 2 3 6 0 2 (by decide)

def WallE_cell0236_t7_32_36 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t7_32_36 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t7_32_36 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t7_32_36 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t7_32_36 F)

noncomputable def wall_cell0236_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 7 [(0, false), (1, false), (2, true), (3, true), (4, true), (6, true)] 3 6 6 2 0 2 (by decide)

def WallE_cell0236_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t7_36_62 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t7_36_62 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t7_36_62 F)

noncomputable def wall_cell0236_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 8 [(0, false), (1, false), (2, true), (4, true), (5, false), (6, true)] 3 6 4 3 3 0 (by decide)

def WallE_cell0236_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t8_36_43 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t8_36_43 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t8_36_43 F)

noncomputable def wall_cell0236_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0236 :=
  cellWallOf F cell0236 8 [(0, false), (1, false), (2, true), (3, true), (5, false), (6, true)] 4 6 6 3 3 0 (by decide)

def WallE_cell0236_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0236 (wall_cell0236_t8_46_63 F) (cellRimScalar cell0236 1 3 7 0 x)

theorem cert_cell0236_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0236_t8_46_63 x F :=
  cellWall_cert_or_E F cell0236 1 3 7 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0236_t8_46_63 F)

noncomputable def wall_cell0536_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 1 [(2, false), (3, true), (5, false), (6, false), (7, false), (8, true)] 0 1 6 0 2 0 (by decide)

def WallE_cell0536_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t1_01_60 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t1_01_60 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t1_01_60 F)

noncomputable def wall_cell0536_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 1 [(0, false), (2, false), (3, true), (6, false), (7, false), (8, true)] 0 6 6 1 2 0 (by decide)

def WallE_cell0536_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t1_06_61 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t1_06_61 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t1_06_61 F)

noncomputable def wall_cell0536_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 2 [(1, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cell0536_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t2_02_50 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t2_02_50 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t2_02_50 F)

noncomputable def wall_cell0536_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 2 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 0 5 5 2 1 0 (by decide)

def WallE_cell0536_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t2_05_52 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t2_05_52 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t2_05_52 F)

noncomputable def wall_cell0536_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, false), (8, true)] 0 3 3 5 0 1 (by decide)

def WallE_cell0536_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_03_35 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_03_35 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_03_35 F)

noncomputable def wall_cell0536_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cell0536_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_03_40 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_03_40 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_03_40 F)

noncomputable def wall_cell0536_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (7, false), (8, true)] 0 3 4 5 0 1 (by decide)

def WallE_cell0536_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_03_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_03_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_03_45 F)

noncomputable def wall_cell0536_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cell0536_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_04_35 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_04_35 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_04_35 F)

noncomputable def wall_cell0536_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cell0536_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_04_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_04_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_04_45 F)

noncomputable def wall_cell0536_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cell0536_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_30 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_30 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_30 F)

noncomputable def wall_cell0536_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cell0536_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_34 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_34 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_34 F)

noncomputable def wall_cell0536_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (5, false), (6, false), (7, false), (8, true)] 0 5 4 0 0 1 (by decide)

def WallE_cell0536_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_40 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_40 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_40 F)

noncomputable def wall_cell0536_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (5, false), (7, false), (8, true)] 0 5 4 3 0 1 (by decide)

def WallE_cell0536_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_05_43 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_05_43 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_05_43 F)

noncomputable def wall_cell0536_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 0 4 3 0 1 (by decide)

def WallE_cell0536_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_30_43 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_30_43 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_30_43 F)

noncomputable def wall_cell0536_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, false)] 3 0 4 5 0 1 (by decide)

def WallE_cell0536_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_30_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_30_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_30_45 F)

noncomputable def wall_cell0536_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 4 4 5 0 1 (by decide)

def WallE_cell0536_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_34_45 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_34_45 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_34_45 F)

noncomputable def wall_cell0536_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, false)] 3 5 4 0 0 1 (by decide)

def WallE_cell0536_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_35_40 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_35_40 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_35_40 F)

noncomputable def wall_cell0536_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, false)] 3 5 4 3 0 1 (by decide)

def WallE_cell0536_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_35_43 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_35_43 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_35_43 F)

noncomputable def wall_cell0536_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cell0536_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_40_53 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_40_53 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_40_53 F)

noncomputable def wall_cell0536_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cell0536_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_43_50 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_43_50 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_43_50 F)

noncomputable def wall_cell0536_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cell0536_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_45_50 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_45_50 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_45_50 F)

noncomputable def wall_cell0536_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, false), (8, true)] 4 5 5 3 0 1 (by decide)

def WallE_cell0536_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t3_45_53 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t3_45_53 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t3_45_53 F)

noncomputable def wall_cell0536_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 4 [(0, false), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 6 4 0 0 1 (by decide)

def WallE_cell0536_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t4_06_40 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t4_06_40 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t4_06_40 F)

noncomputable def wall_cell0536_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 4 [(0, false), (2, false), (3, true), (5, false), (6, false), (7, false)] 4 6 6 0 0 1 (by decide)

def WallE_cell0536_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t4_46_60 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t4_46_60 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t4_46_60 F)

noncomputable def wall_cell0536_t6_32_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 6 [(0, false), (1, false), (2, false), (4, true), (5, false), (8, true)] 3 2 5 3 0 2 (by decide)

def WallE_cell0536_t6_32_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t6_32_53 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t6_32_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t6_32_53 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t6_32_53 F)

noncomputable def wall_cell0536_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 6 [(0, false), (1, false), (4, true), (5, false), (7, false), (8, true)] 3 5 5 2 0 2 (by decide)

def WallE_cell0536_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t6_35_52 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t6_35_52 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t6_35_52 F)

noncomputable def wall_cell0536_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (5, false)] 3 2 6 3 0 2 (by decide)

def WallE_cell0536_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t7_32_63 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t7_32_63 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t7_32_63 F)

noncomputable def wall_cell0536_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (6, false)] 3 6 6 2 0 2 (by decide)

def WallE_cell0536_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t7_36_62 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t7_36_62 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t7_36_62 F)

noncomputable def wall_cell0536_t8_36_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 8 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false)] 3 6 4 3 3 0 (by decide)

def WallE_cell0536_t8_36_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t8_36_43 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t8_36_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t8_36_43 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t8_36_43 F)

noncomputable def wall_cell0536_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0536 :=
  cellWallOf F cell0536 8 [(0, false), (1, false), (2, false), (3, true), (5, false), (6, false)] 4 6 6 3 3 0 (by decide)

def WallE_cell0536_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0536 (wall_cell0536_t8_46_63 F) (cellRimScalar cell0536 2 0 3 1 x)

theorem cert_cell0536_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0536_t8_46_63 x F :=
  cellWall_cert_or_E F cell0536 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0536_t8_46_63 F)

noncomputable def wall_cellP_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 2 [(1, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cellP_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t2_02_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t2_02_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t2_02_50 F)

noncomputable def wall_cellP_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 2 [(1, false), (3, true), (4, false), (5, false), (7, true), (8, true)] 2 0 5 2 1 0 (by decide)

def WallE_cellP_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t2_20_52 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t2_20_52 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t2_20_52 F)

noncomputable def wall_cellP_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 0 4 3 0 0 1 (by decide)

def WallE_cellP_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_04_30 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_04_30 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_04_30 F)

noncomputable def wall_cellP_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cellP_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_04_35 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_04_35 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_04_35 F)

noncomputable def wall_cellP_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cellP_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_05_30 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_05_30 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_05_30 F)

noncomputable def wall_cellP_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cellP_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_05_34 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_05_34 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_05_34 F)

noncomputable def wall_cellP_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true)] 3 0 4 3 0 1 (by decide)

def WallE_cellP_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_43 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_43 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_43 F)

noncomputable def wall_cellP_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false), (6, true), (7, true)] 3 0 4 5 0 1 (by decide)

def WallE_cellP_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_45 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_45 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_45 F)

noncomputable def wall_cellP_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (7, true), (8, true)] 3 0 5 3 0 1 (by decide)

def WallE_cellP_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_53 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_53 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_53 F)

noncomputable def wall_cellP_t3_30_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false), (7, true), (8, true)] 3 0 5 4 0 1 (by decide)

def WallE_cellP_t3_30_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_30_54 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_30_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_30_54 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_30_54 F)

noncomputable def wall_cellP_t3_34_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true)] 3 4 4 0 0 1 (by decide)

def WallE_cellP_t3_34_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_34_40 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_34_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_34_40 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_34_40 F)

noncomputable def wall_cellP_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true)] 3 4 4 5 0 1 (by decide)

def WallE_cellP_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_34_45 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_34_45 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_34_45 F)

noncomputable def wall_cellP_t3_34_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false), (7, true), (8, true)] 3 4 5 0 0 1 (by decide)

def WallE_cellP_t3_34_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_34_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_34_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_34_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_34_50 F)

noncomputable def wall_cellP_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false), (6, true), (7, true)] 3 5 4 0 0 1 (by decide)

def WallE_cellP_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_35_40 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_35_40 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_35_40 F)

noncomputable def wall_cellP_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false), (7, true), (8, true)] 3 5 5 0 0 1 (by decide)

def WallE_cellP_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_35_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_35_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_35_50 F)

noncomputable def wall_cellP_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (7, true), (8, true)] 3 5 5 4 0 1 (by decide)

def WallE_cellP_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_35_54 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_35_54 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_35_54 F)

noncomputable def wall_cellP_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cellP_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_40_53 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_40_53 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_40_53 F)

noncomputable def wall_cellP_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 4 0 5 4 0 1 (by decide)

def WallE_cellP_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_40_54 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_40_54 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_40_54 F)

noncomputable def wall_cellP_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (2, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cellP_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_43_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_43_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_43_50 F)

noncomputable def wall_cellP_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 3 [(0, false), (1, false), (4, false), (5, false), (6, true), (7, true), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cellP_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t3_45_50 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t3_45_50 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t3_45_50 F)

noncomputable def wall_cellP_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 4 [(0, false), (2, false), (5, false), (6, true), (7, true), (8, true)] 0 6 4 0 1 0 (by decide)

def WallE_cellP_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t4_06_40 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t4_06_40 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t4_06_40 F)

noncomputable def wall_cellP_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 4 [(0, false), (2, false), (3, true), (5, false), (6, true), (7, true)] 4 6 6 0 1 0 (by decide)

def WallE_cellP_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t4_46_60 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t4_46_60 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t4_46_60 F)

noncomputable def wall_cellP_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 5 [(1, false), (2, false), (3, true), (4, false), (6, true), (8, true)] 2 1 6 2 0 1 (by decide)

def WallE_cellP_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t5_21_62 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t5_21_62 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t5_21_62 F)

noncomputable def wall_cellP_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 5 [(0, false), (2, false), (3, true), (4, false), (6, true), (8, true)] 2 6 6 1 0 1 (by decide)

def WallE_cellP_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t5_26_61 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t5_26_61 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t5_26_61 F)

noncomputable def wall_cellP_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 6 [(0, false), (1, false), (3, true), (4, false), (5, false), (8, true)] 2 5 3 2 2 0 (by decide)

def WallE_cellP_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t6_25_32 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t6_25_32 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t6_25_32 F)

noncomputable def wall_cellP_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 6 [(0, false), (1, false), (4, false), (5, false), (7, true), (8, true)] 3 5 5 2 2 0 (by decide)

def WallE_cellP_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t6_35_52 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t6_35_52 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t6_35_52 F)

noncomputable def wall_cellP_t7_26_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 7 [(0, false), (1, false), (2, false), (3, true), (4, false), (8, true)] 2 6 3 2 2 0 (by decide)

def WallE_cellP_t7_26_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t7_26_32 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t7_26_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t7_26_32 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t7_26_32 F)

noncomputable def wall_cellP_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 7 [(0, false), (1, false), (2, false), (3, true), (4, false), (6, true)] 3 6 6 2 2 0 (by decide)

def WallE_cellP_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t7_36_62 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t7_36_62 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t7_36_62 F)

noncomputable def wall_cellP_t8_34_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 8 [(0, false), (1, false), (2, false), (5, false), (6, true), (7, true)] 3 4 4 6 3 0 (by decide)

def WallE_cellP_t8_34_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t8_34_46 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t8_34_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t8_34_46 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t8_34_46 F)

noncomputable def wall_cellP_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cellP :=
  cellWallOf F cellP 8 [(0, false), (1, false), (2, false), (3, true), (5, false), (6, true)] 3 6 6 4 3 0 (by decide)

def WallE_cellP_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cellP (wall_cellP_t8_36_64 F) (cellRimScalar cellP 0 2 4 1 x)

theorem cert_cellP_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cellP_t8_36_64 x F :=
  cellWall_cert_or_E F cellP 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cellP_t8_36_64 F)

noncomputable def wall_cell0164_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 0 [(2, false), (3, false), (4, true), (6, false), (7, false), (8, false)] 0 1 1 2 3 0 (by decide)

def WallE_cell0164_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t0_01_12 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t0_01_12 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t0_01_12 F)

noncomputable def wall_cell0164_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 0 [(3, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 2 1 0 3 0 (by decide)

def WallE_cell0164_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t0_02_10 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t0_02_10 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t0_02_10 F)

noncomputable def wall_cell0164_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 1 [(2, false), (3, false), (5, false), (6, false), (7, false), (8, false)] 0 1 6 0 0 2 (by decide)

def WallE_cell0164_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t1_01_60 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t1_01_60 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t1_01_60 F)

noncomputable def wall_cell0164_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 1 [(0, false), (2, false), (3, false), (6, false), (7, false), (8, false)] 0 6 6 1 0 2 (by decide)

def WallE_cell0164_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t1_06_61 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t1_06_61 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t1_06_61 F)

noncomputable def wall_cell0164_t3_03_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 0 3 3 4 1 0 (by decide)

def WallE_cell0164_t3_03_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_03_34 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_03_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_03_34 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_03_34 F)

noncomputable def wall_cell0164_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, false)] 0 3 3 5 1 0 (by decide)

def WallE_cell0164_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_03_35 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_03_35 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_03_35 F)

noncomputable def wall_cell0164_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, false)] 0 3 4 0 1 0 (by decide)

def WallE_cell0164_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_03_40 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_03_40 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_03_40 F)

noncomputable def wall_cell0164_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, false)] 0 3 4 5 1 0 (by decide)

def WallE_cell0164_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_03_45 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_03_45 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_03_45 F)

noncomputable def wall_cell0164_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 4 3 5 1 0 (by decide)

def WallE_cell0164_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_04_35 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_04_35 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_04_35 F)

noncomputable def wall_cell0164_t3_04_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 0 4 4 3 1 0 (by decide)

def WallE_cell0164_t3_04_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_04_43 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_04_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_04_43 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_04_43 F)

noncomputable def wall_cell0164_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, false)] 0 4 4 5 1 0 (by decide)

def WallE_cell0164_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_04_45 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_04_45 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_04_45 F)

noncomputable def wall_cell0164_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 5 3 0 1 0 (by decide)

def WallE_cell0164_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_30 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_30 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_30 F)

noncomputable def wall_cell0164_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 0 5 3 4 1 0 (by decide)

def WallE_cell0164_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_34 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_34 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_34 F)

noncomputable def wall_cell0164_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (5, false), (6, false), (7, false), (8, false)] 0 5 4 0 1 0 (by decide)

def WallE_cell0164_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_40 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_40 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_40 F)

noncomputable def wall_cell0164_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, false)] 0 5 4 3 1 0 (by decide)

def WallE_cell0164_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_05_43 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_05_43 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_05_43 F)

noncomputable def wall_cell0164_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 0 5 3 1 0 (by decide)

def WallE_cell0164_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_40_53 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_40_53 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_40_53 F)

noncomputable def wall_cell0164_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 3 5 0 1 0 (by decide)

def WallE_cell0164_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_43_50 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_43_50 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_43_50 F)

noncomputable def wall_cell0164_t3_43_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 4 3 5 4 1 0 (by decide)

def WallE_cell0164_t3_43_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_43_54 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_43_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_43_54 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_43_54 F)

noncomputable def wall_cell0164_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, false)] 4 5 5 0 1 0 (by decide)

def WallE_cell0164_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_45_50 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_45_50 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_45_50 F)

noncomputable def wall_cell0164_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, false)] 4 5 5 3 1 0 (by decide)

def WallE_cell0164_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t3_45_53 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t3_45_53 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t3_45_53 F)

noncomputable def wall_cell0164_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 4 [(0, false), (2, false), (5, false), (6, false), (7, false), (8, false)] 0 4 6 0 0 1 (by decide)

def WallE_cell0164_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t4_04_60 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t4_04_60 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t4_04_60 F)

noncomputable def wall_cell0164_t4_04_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 4 [(0, false), (2, false), (5, false), (6, false), (7, false)] 0 4 6 4 0 1 (by decide)

def WallE_cell0164_t4_04_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t4_04_64 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t4_04_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t4_04_64 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t4_04_64 F)

noncomputable def wall_cell0164_t4_06_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 4 [(0, false), (2, false), (3, false), (5, false), (6, false), (7, false)] 0 6 6 4 0 1 (by decide)

def WallE_cell0164_t4_06_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t4_06_64 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t4_06_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t4_06_64 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t4_06_64 F)

noncomputable def wall_cell0164_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 5 [(2, false), (3, false), (4, true), (6, false), (7, false), (8, false)] 1 2 6 1 0 1 (by decide)

def WallE_cell0164_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t5_12_61 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t5_12_61 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t5_12_61 F)

noncomputable def wall_cell0164_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 5 [(0, false), (2, false), (3, false), (4, true), (6, false), (8, false)] 1 6 6 2 0 1 (by decide)

def WallE_cell0164_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t5_16_62 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t5_16_62 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t5_16_62 F)

noncomputable def wall_cell0164_t8_43_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 8 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 4 3 6 4 0 3 (by decide)

def WallE_cell0164_t8_43_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t8_43_64 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t8_43_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t8_43_64 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t8_43_64 F)

noncomputable def wall_cell0164_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell0164 :=
  cellWallOf F cell0164 8 [(0, false), (1, true), (2, false), (3, false), (5, false), (6, false)] 4 6 6 3 0 3 (by decide)

def WallE_cell0164_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell0164 (wall_cell0164_t8_46_63 F) (cellRimScalar cell0164 0 2 1 2 x)

theorem cert_cell0164_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell0164_t8_46_63 x F :=
  cellWall_cert_or_E F cell0164 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell0164_t8_46_63 F)

noncomputable def wall_cell01634_t0_01_12 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 0 [(2, false), (3, false), (4, true), (6, false), (7, false), (8, true)] 0 1 1 2 3 0 (by decide)

def WallE_cell01634_t0_01_12 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t0_01_12 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t0_01_12 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t0_01_12 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t0_01_12 F)

noncomputable def wall_cell01634_t0_02_10 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 0 [(3, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 2 1 0 3 0 (by decide)

def WallE_cell01634_t0_02_10 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t0_02_10 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t0_02_10 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t0_02_10 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t0_02_10 F)

noncomputable def wall_cell01634_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 1 [(2, false), (3, false), (5, false), (6, false), (7, false), (8, true)] 0 1 6 0 0 2 (by decide)

def WallE_cell01634_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t1_01_60 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t1_01_60 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t1_01_60 F)

noncomputable def wall_cell01634_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 1 [(0, false), (2, false), (3, false), (6, false), (7, false), (8, true)] 0 6 6 1 0 2 (by decide)

def WallE_cell01634_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t1_06_61 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t1_06_61 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t1_06_61 F)

noncomputable def wall_cell01634_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, true)] 0 3 3 5 1 0 (by decide)

def WallE_cell01634_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_03_35 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_03_35 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_03_35 F)

noncomputable def wall_cell01634_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 3 4 0 1 0 (by decide)

def WallE_cell01634_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_03_40 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_03_40 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_03_40 F)

noncomputable def wall_cell01634_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, true)] 0 3 4 5 1 0 (by decide)

def WallE_cell01634_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_03_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_03_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_03_45 F)

noncomputable def wall_cell01634_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 4 3 5 1 0 (by decide)

def WallE_cell01634_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_04_35 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_04_35 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_04_35 F)

noncomputable def wall_cell01634_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 4 4 5 1 0 (by decide)

def WallE_cell01634_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_04_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_04_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_04_45 F)

noncomputable def wall_cell01634_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 0 1 0 (by decide)

def WallE_cell01634_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_30 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_30 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_30 F)

noncomputable def wall_cell01634_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 0 5 3 4 1 0 (by decide)

def WallE_cell01634_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_34 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_34 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_34 F)

noncomputable def wall_cell01634_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (5, false), (6, false), (7, false), (8, true)] 0 5 4 0 1 0 (by decide)

def WallE_cell01634_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_40 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_40 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_40 F)

noncomputable def wall_cell01634_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (5, false), (7, false), (8, true)] 0 5 4 3 1 0 (by decide)

def WallE_cell01634_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_05_43 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_05_43 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_05_43 F)

noncomputable def wall_cell01634_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 0 4 3 1 0 (by decide)

def WallE_cell01634_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_30_43 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_30_43 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_30_43 F)

noncomputable def wall_cell01634_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false)] 3 0 4 5 1 0 (by decide)

def WallE_cell01634_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_30_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_30_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_30_45 F)

noncomputable def wall_cell01634_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false)] 3 4 4 5 1 0 (by decide)

def WallE_cell01634_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_34_45 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_34_45 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_34_45 F)

noncomputable def wall_cell01634_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false)] 3 5 4 0 1 0 (by decide)

def WallE_cell01634_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_35_40 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_35_40 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_35_40 F)

noncomputable def wall_cell01634_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false)] 3 5 4 3 1 0 (by decide)

def WallE_cell01634_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_35_43 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_35_43 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_35_43 F)

noncomputable def wall_cell01634_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 0 5 3 1 0 (by decide)

def WallE_cell01634_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_40_53 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_40_53 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_40_53 F)

noncomputable def wall_cell01634_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 3 5 0 1 0 (by decide)

def WallE_cell01634_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_43_50 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_43_50 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_43_50 F)

noncomputable def wall_cell01634_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (4, true), (5, false), (6, false), (7, false), (8, true)] 4 5 5 0 1 0 (by decide)

def WallE_cell01634_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_45_50 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_45_50 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_45_50 F)

noncomputable def wall_cell01634_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 3 [(0, false), (1, true), (2, false), (4, true), (5, false), (7, false), (8, true)] 4 5 5 3 1 0 (by decide)

def WallE_cell01634_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t3_45_53 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t3_45_53 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t3_45_53 F)

noncomputable def wall_cell01634_t4_04_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 4 [(0, false), (2, false), (5, false), (6, false), (7, false), (8, true)] 0 4 6 0 0 1 (by decide)

def WallE_cell01634_t4_04_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t4_04_60 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t4_04_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t4_04_60 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t4_04_60 F)

noncomputable def wall_cell01634_t4_40_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 4 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 4 0 6 4 0 1 (by decide)

def WallE_cell01634_t4_40_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t4_40_64 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t4_40_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t4_40_64 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t4_40_64 F)

noncomputable def wall_cell01634_t5_12_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 5 [(2, false), (3, false), (4, true), (6, false), (7, false), (8, true)] 1 2 6 1 0 1 (by decide)

def WallE_cell01634_t5_12_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t5_12_61 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t5_12_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t5_12_61 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t5_12_61 F)

noncomputable def wall_cell01634_t5_16_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 5 [(0, false), (2, false), (3, false), (4, true), (6, false), (8, true)] 1 6 6 2 0 1 (by decide)

def WallE_cell01634_t5_16_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t5_16_62 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t5_16_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t5_16_62 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t5_16_62 F)

noncomputable def wall_cell01634_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 7 [(0, false), (1, true), (2, false), (3, false), (4, true), (5, false)] 3 2 6 3 0 2 (by decide)

def WallE_cell01634_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t7_32_63 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t7_32_63 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t7_32_63 F)

noncomputable def wall_cell01634_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 7 [(0, false), (1, true), (2, false), (3, false), (4, true), (6, false)] 3 6 6 2 0 2 (by decide)

def WallE_cell01634_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t7_36_62 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t7_36_62 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t7_36_62 F)

noncomputable def wall_cell01634_t8_43_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 8 [(0, false), (1, true), (2, false), (5, false), (6, false), (7, false)] 4 3 6 4 3 0 (by decide)

def WallE_cell01634_t8_43_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t8_43_64 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t8_43_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t8_43_64 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t8_43_64 F)

noncomputable def wall_cell01634_t8_46_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell01634 :=
  cellWallOf F cell01634 8 [(0, false), (1, true), (2, false), (3, false), (5, false), (6, false)] 4 6 6 3 3 0 (by decide)

def WallE_cell01634_t8_46_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell01634 (wall_cell01634_t8_46_63 F) (cellRimScalar cell01634 0 2 1 2 x)

theorem cert_cell01634_t8_46_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell01634_t8_46_63 x F :=
  cellWall_cert_or_E F cell01634 0 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell01634_t8_46_63 F)

noncomputable def wall_cell05326_t1_01_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 1 [(2, false), (3, true), (5, false), (6, false), (7, true), (8, true)] 0 1 6 0 2 0 (by decide)

def WallE_cell05326_t1_01_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t1_01_60 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t1_01_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t1_01_60 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t1_01_60 F)

noncomputable def wall_cell05326_t1_06_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 1 [(0, false), (2, false), (3, true), (6, false), (7, true), (8, true)] 0 6 6 1 2 0 (by decide)

def WallE_cell05326_t1_06_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t1_06_61 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t1_06_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t1_06_61 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t1_06_61 F)

noncomputable def wall_cell05326_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 2 [(1, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cell05326_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t2_02_50 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t2_02_50 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t2_02_50 F)

noncomputable def wall_cell05326_t2_05_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 2 [(0, false), (1, false), (4, true), (5, false), (7, true), (8, true)] 0 5 5 2 1 0 (by decide)

def WallE_cell05326_t2_05_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t2_05_52 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t2_05_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t2_05_52 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t2_05_52 F)

noncomputable def wall_cell05326_t3_03_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, true), (8, true)] 0 3 3 5 0 1 (by decide)

def WallE_cell05326_t3_03_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_03_35 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_03_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_03_35 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_03_35 F)

noncomputable def wall_cell05326_t3_03_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, true), (8, true)] 0 3 4 0 0 1 (by decide)

def WallE_cell05326_t3_03_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_03_40 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_03_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_03_40 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_03_40 F)

noncomputable def wall_cell05326_t3_03_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (7, true), (8, true)] 0 3 4 5 0 1 (by decide)

def WallE_cell05326_t3_03_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_03_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_03_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_03_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_03_45 F)

noncomputable def wall_cell05326_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cell05326_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_04_35 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_04_35 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_04_35 F)

noncomputable def wall_cell05326_t3_04_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (6, false), (7, true), (8, true)] 0 4 4 5 0 1 (by decide)

def WallE_cell05326_t3_04_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_04_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_04_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_04_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_04_45 F)

noncomputable def wall_cell05326_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cell05326_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_30 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_30 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_30 F)

noncomputable def wall_cell05326_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cell05326_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_34 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_34 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_34 F)

noncomputable def wall_cell05326_t3_05_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (5, false), (6, false), (7, true), (8, true)] 0 5 4 0 0 1 (by decide)

def WallE_cell05326_t3_05_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_40 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_40 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_40 F)

noncomputable def wall_cell05326_t3_05_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (7, true), (8, true)] 0 5 4 3 0 1 (by decide)

def WallE_cell05326_t3_05_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_43 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_43 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_43 F)

noncomputable def wall_cell05326_t3_05_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (5, false), (7, true), (8, true)] 0 5 4 5 0 1 (by decide)

def WallE_cell05326_t3_05_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_05_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_05_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_05_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_05_45 F)

noncomputable def wall_cell05326_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true)] 3 0 4 3 0 1 (by decide)

def WallE_cell05326_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_30_43 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_30_43 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_30_43 F)

noncomputable def wall_cell05326_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, true)] 3 0 4 5 0 1 (by decide)

def WallE_cell05326_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_30_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_30_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_30_45 F)

noncomputable def wall_cell05326_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true)] 3 4 4 5 0 1 (by decide)

def WallE_cell05326_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_34_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_34_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_34_45 F)

noncomputable def wall_cell05326_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, true)] 3 5 4 0 0 1 (by decide)

def WallE_cell05326_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_35_40 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_35_40 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_35_40 F)

noncomputable def wall_cell05326_t3_35_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, true)] 3 5 4 3 0 1 (by decide)

def WallE_cell05326_t3_35_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_35_43 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_35_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_35_43 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_35_43 F)

noncomputable def wall_cell05326_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cell05326_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_40_53 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_40_53 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_40_53 F)

noncomputable def wall_cell05326_t3_43_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (5, false), (7, true)] 4 3 4 5 0 1 (by decide)

def WallE_cell05326_t3_43_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_43_45 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_43_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_43_45 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_43_45 F)

noncomputable def wall_cell05326_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cell05326_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_43_50 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_43_50 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_43_50 F)

noncomputable def wall_cell05326_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (4, true), (5, false), (6, false), (7, true), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cell05326_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_45_50 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_45_50 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_45_50 F)

noncomputable def wall_cell05326_t3_45_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 3 [(0, false), (1, false), (2, false), (4, true), (5, false), (7, true), (8, true)] 4 5 5 3 0 1 (by decide)

def WallE_cell05326_t3_45_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t3_45_53 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t3_45_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t3_45_53 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t3_45_53 F)

noncomputable def wall_cell05326_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 4 [(0, false), (2, false), (5, false), (6, false), (7, true), (8, true)] 0 6 4 0 0 1 (by decide)

def WallE_cell05326_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t4_06_40 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t4_06_40 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t4_06_40 F)

noncomputable def wall_cell05326_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 4 [(0, false), (2, false), (3, true), (5, false), (6, false), (7, true)] 4 6 6 0 0 1 (by decide)

def WallE_cell05326_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t4_46_60 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t4_46_60 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t4_46_60 F)

noncomputable def wall_cell05326_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 5 [(1, false), (2, false), (3, true), (4, true), (6, false), (8, true)] 2 1 6 2 0 1 (by decide)

def WallE_cell05326_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t5_21_62 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t5_21_62 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t5_21_62 F)

noncomputable def wall_cell05326_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 5 [(0, false), (2, false), (3, true), (4, true), (6, false), (8, true)] 2 6 6 1 0 1 (by decide)

def WallE_cell05326_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t5_26_61 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t5_26_61 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t5_26_61 F)

noncomputable def wall_cell05326_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 6 [(0, false), (1, false), (3, true), (4, true), (5, false), (8, true)] 2 5 3 2 0 2 (by decide)

def WallE_cell05326_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t6_25_32 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t6_25_32 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t6_25_32 F)

noncomputable def wall_cell05326_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 6 [(0, false), (1, false), (4, true), (5, false), (7, true), (8, true)] 3 5 5 2 0 2 (by decide)

def WallE_cell05326_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t6_35_52 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t6_35_52 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t6_35_52 F)

noncomputable def wall_cell05326_t7_32_63 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (5, false)] 3 2 6 3 2 0 (by decide)

def WallE_cell05326_t7_32_63 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t7_32_63 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t7_32_63 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t7_32_63 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t7_32_63 F)

noncomputable def wall_cell05326_t7_36_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell05326 :=
  cellWallOf F cell05326 7 [(0, false), (1, false), (2, false), (3, true), (4, true), (6, false)] 3 6 6 2 2 0 (by decide)

def WallE_cell05326_t7_36_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell05326 (wall_cell05326_t7_36_62 F) (cellRimScalar cell05326 0 2 3 1 x)

theorem cert_cell05326_t7_36_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell05326_t7_36_62 x F :=
  cellWall_cert_or_E F cell05326 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell05326_t7_36_62 F)

noncomputable def wall_cell046125_t0_10_21 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 0 [(2, false), (3, true), (4, false), (6, true), (7, true), (8, true)] 1 0 2 1 3 0 (by decide)

def WallE_cell046125_t0_10_21 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t0_10_21 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t0_10_21 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t0_10_21 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t0_10_21 F)

noncomputable def wall_cell046125_t0_12_20 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 0 [(1, false), (3, true), (4, false), (6, true), (7, true), (8, true)] 1 2 2 0 3 0 (by decide)

def WallE_cell046125_t0_12_20 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t0_12_20 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t0_12_20 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t0_12_20 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t0_12_20 F)

noncomputable def wall_cell046125_t1_10_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 1 [(2, false), (3, true), (4, false), (6, true), (7, true), (8, true)] 1 0 6 1 2 0 (by decide)

def WallE_cell046125_t1_10_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t1_10_61 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t1_10_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t1_10_61 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t1_10_61 F)

noncomputable def wall_cell046125_t1_16_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 1 [(0, false), (2, false), (3, true), (6, true), (7, true), (8, true)] 1 6 6 0 2 0 (by decide)

def WallE_cell046125_t1_16_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t1_16_60 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t1_16_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t1_16_60 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t1_16_60 F)

noncomputable def wall_cell046125_t2_02_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 2 [(1, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 2 5 0 1 0 (by decide)

def WallE_cell046125_t2_02_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t2_02_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t2_02_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t2_02_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t2_02_50 F)

noncomputable def wall_cell046125_t2_20_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 2 [(1, false), (3, true), (4, false), (5, true), (7, true), (8, true)] 2 0 5 2 1 0 (by decide)

def WallE_cell046125_t2_20_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t2_20_52 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t2_20_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t2_20_52 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t2_20_52 F)

noncomputable def wall_cell046125_t3_04_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, true)] 0 4 3 0 0 1 (by decide)

def WallE_cell046125_t3_04_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_04_30 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_04_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_04_30 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_04_30 F)

noncomputable def wall_cell046125_t3_04_35 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 4 3 5 0 1 (by decide)

def WallE_cell046125_t3_04_35 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_04_35 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_04_35 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_04_35 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_04_35 F)

noncomputable def wall_cell046125_t3_05_30 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 5 3 0 0 1 (by decide)

def WallE_cell046125_t3_05_30 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_05_30 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_05_30 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_05_30 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_05_30 F)

noncomputable def wall_cell046125_t3_05_34 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 0 5 3 4 0 1 (by decide)

def WallE_cell046125_t3_05_34 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_05_34 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_05_34 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_05_34 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_05_34 F)

noncomputable def wall_cell046125_t3_30_43 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 3 0 4 3 0 1 (by decide)

def WallE_cell046125_t3_30_43 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_43 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_43 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_43 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_43 F)

noncomputable def wall_cell046125_t3_30_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true)] 3 0 4 5 0 1 (by decide)

def WallE_cell046125_t3_30_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_45 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_45 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_45 F)

noncomputable def wall_cell046125_t3_30_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, true)] 3 0 5 3 0 1 (by decide)

def WallE_cell046125_t3_30_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_53 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_53 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_53 F)

noncomputable def wall_cell046125_t3_30_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, true)] 3 0 5 4 0 1 (by decide)

def WallE_cell046125_t3_30_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_30_54 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_30_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_30_54 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_30_54 F)

noncomputable def wall_cell046125_t3_34_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true)] 3 4 4 0 0 1 (by decide)

def WallE_cell046125_t3_34_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_34_40 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_34_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_34_40 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_34_40 F)

noncomputable def wall_cell046125_t3_34_45 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true)] 3 4 4 5 0 1 (by decide)

def WallE_cell046125_t3_34_45 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_34_45 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_34_45 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_34_45 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_34_45 F)

noncomputable def wall_cell046125_t3_34_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true), (7, true), (8, true)] 3 4 5 0 0 1 (by decide)

def WallE_cell046125_t3_34_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_34_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_34_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_34_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_34_50 F)

noncomputable def wall_cell046125_t3_35_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true)] 3 5 4 0 0 1 (by decide)

def WallE_cell046125_t3_35_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_35_40 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_35_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_35_40 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_35_40 F)

noncomputable def wall_cell046125_t3_35_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, true)] 3 5 5 0 0 1 (by decide)

def WallE_cell046125_t3_35_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_35_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_35_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_35_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_35_50 F)

noncomputable def wall_cell046125_t3_35_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (7, true), (8, true)] 3 5 5 4 0 1 (by decide)

def WallE_cell046125_t3_35_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_35_54 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_35_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_35_54 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_35_54 F)

noncomputable def wall_cell046125_t3_40_53 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 0 5 3 0 1 (by decide)

def WallE_cell046125_t3_40_53 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_40_53 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_40_53 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_40_53 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_40_53 F)

noncomputable def wall_cell046125_t3_40_54 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true), (8, true)] 4 0 5 4 0 1 (by decide)

def WallE_cell046125_t3_40_54 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_40_54 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_40_54 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_40_54 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_40_54 F)

noncomputable def wall_cell046125_t3_43_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (2, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 3 5 0 0 1 (by decide)

def WallE_cell046125_t3_43_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_43_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_43_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_43_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_43_50 F)

noncomputable def wall_cell046125_t3_45_50 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 3 [(0, false), (1, false), (4, false), (5, true), (6, true), (7, true), (8, true)] 4 5 5 0 0 1 (by decide)

def WallE_cell046125_t3_45_50 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t3_45_50 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t3_45_50 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t3_45_50 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t3_45_50 F)

noncomputable def wall_cell046125_t4_06_40 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 4 [(0, false), (2, false), (5, true), (6, true), (7, true), (8, true)] 0 6 4 0 1 0 (by decide)

def WallE_cell046125_t4_06_40 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t4_06_40 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t4_06_40 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t4_06_40 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t4_06_40 F)

noncomputable def wall_cell046125_t4_46_60 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 4 [(0, false), (2, false), (3, true), (5, true), (6, true), (7, true)] 4 6 6 0 1 0 (by decide)

def WallE_cell046125_t4_46_60 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t4_46_60 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t4_46_60 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t4_46_60 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t4_46_60 F)

noncomputable def wall_cell046125_t5_21_62 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 5 [(1, false), (2, false), (3, true), (4, false), (6, true), (8, true)] 2 1 6 2 1 0 (by decide)

def WallE_cell046125_t5_21_62 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t5_21_62 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t5_21_62 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t5_21_62 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t5_21_62 F)

noncomputable def wall_cell046125_t5_26_61 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 5 [(0, false), (2, false), (3, true), (4, false), (6, true), (8, true)] 2 6 6 1 1 0 (by decide)

def WallE_cell046125_t5_26_61 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t5_26_61 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t5_26_61 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t5_26_61 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t5_26_61 F)

noncomputable def wall_cell046125_t6_25_32 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 6 [(0, false), (1, false), (3, true), (4, false), (5, true), (8, true)] 2 5 3 2 2 0 (by decide)

def WallE_cell046125_t6_25_32 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t6_25_32 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t6_25_32 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t6_25_32 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t6_25_32 F)

noncomputable def wall_cell046125_t6_35_52 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 6 [(0, false), (1, false), (4, false), (5, true), (7, true), (8, true)] 3 5 5 2 2 0 (by decide)

def WallE_cell046125_t6_35_52 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t6_35_52 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t6_35_52 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t6_35_52 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t6_35_52 F)

noncomputable def wall_cell046125_t8_34_46 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 8 [(0, false), (1, false), (2, false), (5, true), (6, true), (7, true)] 3 4 4 6 3 0 (by decide)

def WallE_cell046125_t8_34_46 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t8_34_46 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t8_34_46 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t8_34_46 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t8_34_46 F)

noncomputable def wall_cell046125_t8_36_64 (F : S0xFac 9 s0x_S24 x) : CellWall F cell046125 :=
  cellWallOf F cell046125 8 [(0, false), (1, false), (2, false), (3, true), (5, true), (6, true)] 3 6 6 4 3 0 (by decide)

def WallE_cell046125_t8_36_64 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE F cell046125 (wall_cell046125_t8_36_64 F) (cellRimScalar cell046125 0 2 4 1 x)

theorem cert_cell046125_t8_36_64 (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE_cell046125_t8_36_64 x F :=
  cellWall_cert_or_E F cell046125 0 2 4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (wall_cell046125_t8_36_64 F)

/-! ## Per-cell conjunctions and `AllWallE2` / `CellCoverEmptyAll2` -/

def AllWallE2_cellC (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellC_t1_01_60 x F ∧
  WallE_cellC_t1_06_61 x F ∧
  WallE_cellC_t2_02_50 x F ∧
  WallE_cellC_t2_20_52 x F ∧
  WallE_cellC_t3_03_40 x F ∧
  WallE_cellC_t3_04_35 x F ∧
  WallE_cellC_t3_04_45 x F ∧
  WallE_cellC_t3_05_30 x F ∧
  WallE_cellC_t3_05_34 x F ∧
  WallE_cellC_t3_05_40 x F ∧
  WallE_cellC_t3_30_43 x F ∧
  WallE_cellC_t3_30_45 x F ∧
  WallE_cellC_t3_30_53 x F ∧
  WallE_cellC_t3_34_45 x F ∧
  WallE_cellC_t3_35_40 x F ∧
  WallE_cellC_t3_35_50 x F ∧
  WallE_cellC_t3_35_54 x F ∧
  WallE_cellC_t3_40_43 x F ∧
  WallE_cellC_t3_40_45 x F ∧
  WallE_cellC_t3_40_53 x F ∧
  WallE_cellC_t3_43_50 x F ∧
  WallE_cellC_t3_45_50 x F ∧
  WallE_cellC_t4_06_40 x F ∧
  WallE_cellC_t4_46_60 x F ∧
  WallE_cellC_t6_32_53 x F ∧
  WallE_cellC_t6_35_52 x F ∧
  WallE_cellC_t7_26_32 x F ∧
  WallE_cellC_t7_36_62 x F ∧
  WallE_cellC_t8_36_43 x F ∧
  WallE_cellC_t8_46_63 x F

private lemma holeLeaf_allWallE2_cellC {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellC x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellC_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_40_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_40_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t6_32_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t7_26_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t8_36_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellC_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cellC_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellC (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellC_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_40_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t6_32_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t7_26_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t8_36_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellC_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cellD (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellD_t0_02_10 x F ∧
  WallE_cellD_t0_12_20 x F ∧
  WallE_cellD_t1_10_61 x F ∧
  WallE_cellD_t1_16_60 x F ∧
  WallE_cellD_t3_03_34 x F ∧
  WallE_cellD_t3_03_35 x F ∧
  WallE_cellD_t3_04_30 x F ∧
  WallE_cellD_t3_04_34 x F ∧
  WallE_cellD_t3_04_35 x F ∧
  WallE_cellD_t3_05_30 x F ∧
  WallE_cellD_t3_05_34 x F ∧
  WallE_cellD_t3_05_35 x F ∧
  WallE_cellD_t3_40_53 x F ∧
  WallE_cellD_t3_40_54 x F ∧
  WallE_cellD_t3_43_50 x F ∧
  WallE_cellD_t3_43_54 x F ∧
  WallE_cellD_t3_45_50 x F ∧
  WallE_cellD_t3_45_53 x F ∧
  WallE_cellD_t4_04_60 x F ∧
  WallE_cellD_t4_06_64 x F ∧
  WallE_cellD_t5_12_61 x F ∧
  WallE_cellD_t5_21_62 x F ∧
  WallE_cellD_t6_23_35 x F ∧
  WallE_cellD_t6_25_32 x F ∧
  WallE_cellD_t7_23_62 x F ∧
  WallE_cellD_t7_23_63 x F ∧
  WallE_cellD_t7_26_63 x F ∧
  WallE_cellD_t8_34_63 x F ∧
  WallE_cellD_t8_36_64 x F

private lemma holeLeaf_allWallE2_cellD {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellD x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellD_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t0_12_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t1_10_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t1_16_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_03_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_04_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_05_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_43_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t4_04_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t4_06_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t6_23_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t7_23_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t7_23_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t7_26_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t8_34_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cellD_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellD (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellD_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t0_12_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t1_10_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t1_16_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_03_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_04_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_43_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t4_04_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t4_06_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t6_23_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t7_23_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t7_23_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t7_26_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t8_34_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD_t8_36_64 (Sym.sym24 F)) hF

def AllWallE2_cellD6 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellD6_t0_02_10 x F ∧
  WallE_cellD6_t0_12_20 x F ∧
  WallE_cellD6_t1_10_61 x F ∧
  WallE_cellD6_t1_16_60 x F ∧
  WallE_cellD6_t3_03_35 x F ∧
  WallE_cellD6_t3_04_30 x F ∧
  WallE_cellD6_t3_04_35 x F ∧
  WallE_cellD6_t3_05_30 x F ∧
  WallE_cellD6_t3_05_34 x F ∧
  WallE_cellD6_t3_05_35 x F ∧
  WallE_cellD6_t3_30_43 x F ∧
  WallE_cellD6_t3_30_45 x F ∧
  WallE_cellD6_t3_34_40 x F ∧
  WallE_cellD6_t3_34_45 x F ∧
  WallE_cellD6_t3_35_40 x F ∧
  WallE_cellD6_t3_35_43 x F ∧
  WallE_cellD6_t3_35_45 x F ∧
  WallE_cellD6_t3_40_53 x F ∧
  WallE_cellD6_t3_40_54 x F ∧
  WallE_cellD6_t3_43_50 x F ∧
  WallE_cellD6_t3_45_50 x F ∧
  WallE_cellD6_t3_45_53 x F ∧
  WallE_cellD6_t4_04_60 x F ∧
  WallE_cellD6_t4_40_64 x F ∧
  WallE_cellD6_t5_12_61 x F ∧
  WallE_cellD6_t5_21_62 x F ∧
  WallE_cellD6_t6_23_35 x F ∧
  WallE_cellD6_t6_25_32 x F ∧
  WallE_cellD6_t7_23_62 x F ∧
  WallE_cellD6_t7_32_63 x F ∧
  WallE_cellD6_t8_34_63 x F ∧
  WallE_cellD6_t8_36_64 x F

private lemma holeLeaf_allWallE2_cellD6 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellD6 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellD6_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t0_12_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t1_10_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t1_16_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_05_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_34_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_35_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_35_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t4_04_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t4_40_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t6_23_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t7_23_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t7_32_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t8_34_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellD6_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cellD6_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellD6 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t0_12_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t1_10_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t1_16_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_05_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_34_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_35_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_35_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t4_04_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t4_40_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t6_23_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t7_23_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t7_32_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t8_34_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellD6_t8_36_64 (Sym.sym24 F)) hF

def AllWallE2_cellA2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellA2_t0_01_12 x F ∧
  WallE_cellA2_t0_02_10 x F ∧
  WallE_cellA2_t1_01_60 x F ∧
  WallE_cellA2_t1_06_61 x F ∧
  WallE_cellA2_t2_02_50 x F ∧
  WallE_cellA2_t2_05_52 x F ∧
  WallE_cellA2_t3_03_35 x F ∧
  WallE_cellA2_t3_03_40 x F ∧
  WallE_cellA2_t3_03_45 x F ∧
  WallE_cellA2_t3_04_35 x F ∧
  WallE_cellA2_t3_04_45 x F ∧
  WallE_cellA2_t3_05_30 x F ∧
  WallE_cellA2_t3_05_34 x F ∧
  WallE_cellA2_t3_05_40 x F ∧
  WallE_cellA2_t3_05_43 x F ∧
  WallE_cellA2_t3_30_43 x F ∧
  WallE_cellA2_t3_30_45 x F ∧
  WallE_cellA2_t3_34_45 x F ∧
  WallE_cellA2_t3_35_40 x F ∧
  WallE_cellA2_t3_35_43 x F ∧
  WallE_cellA2_t3_40_53 x F ∧
  WallE_cellA2_t3_43_50 x F ∧
  WallE_cellA2_t3_45_50 x F ∧
  WallE_cellA2_t3_45_53 x F ∧
  WallE_cellA2_t5_12_61 x F ∧
  WallE_cellA2_t5_16_62 x F ∧
  WallE_cellA2_t6_32_53 x F ∧
  WallE_cellA2_t6_35_52 x F ∧
  WallE_cellA2_t7_32_63 x F ∧
  WallE_cellA2_t7_36_62 x F ∧
  WallE_cellA2_t8_36_43 x F ∧
  WallE_cellA2_t8_46_63 x F

private lemma holeLeaf_allWallE2_cellA2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellA2 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellA2_t0_01_12 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t2_05_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_35_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t5_16_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t6_32_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t7_32_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t8_36_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA2_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cellA2_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellA2 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t0_01_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t2_05_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_35_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t5_16_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t6_32_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t7_32_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t8_36_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA2_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cellB2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellB2_t0_01_12 x F ∧
  WallE_cellB2_t0_02_10 x F ∧
  WallE_cellB2_t1_01_60 x F ∧
  WallE_cellB2_t1_06_61 x F ∧
  WallE_cellB2_t2_02_50 x F ∧
  WallE_cellB2_t2_05_52 x F ∧
  WallE_cellB2_t3_03_34 x F ∧
  WallE_cellB2_t3_03_35 x F ∧
  WallE_cellB2_t3_03_40 x F ∧
  WallE_cellB2_t3_03_45 x F ∧
  WallE_cellB2_t3_04_35 x F ∧
  WallE_cellB2_t3_04_43 x F ∧
  WallE_cellB2_t3_04_45 x F ∧
  WallE_cellB2_t3_05_30 x F ∧
  WallE_cellB2_t3_05_34 x F ∧
  WallE_cellB2_t3_05_40 x F ∧
  WallE_cellB2_t3_05_43 x F ∧
  WallE_cellB2_t3_40_53 x F ∧
  WallE_cellB2_t3_43_50 x F ∧
  WallE_cellB2_t3_43_54 x F ∧
  WallE_cellB2_t3_45_50 x F ∧
  WallE_cellB2_t3_45_53 x F ∧
  WallE_cellB2_t4_04_46 x F ∧
  WallE_cellB2_t4_06_64 x F ∧
  WallE_cellB2_t5_12_61 x F ∧
  WallE_cellB2_t5_16_62 x F ∧
  WallE_cellB2_t6_32_53 x F ∧
  WallE_cellB2_t6_35_52 x F ∧
  WallE_cellB2_t8_36_43 x F ∧
  WallE_cellB2_t8_46_63 x F

private lemma holeLeaf_allWallE2_cellB2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellB2 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellB2_t0_01_12 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t2_05_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_03_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_04_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_43_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t4_04_46 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t4_06_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t5_16_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t6_32_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t8_36_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB2_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cellB2_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellB2 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t0_01_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t2_05_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_03_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_04_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_43_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t4_04_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t4_06_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t5_16_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t6_32_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t8_36_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB2_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cellA0 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellA0_t0_10_21 x F ∧
  WallE_cellA0_t0_12_20 x F ∧
  WallE_cellA0_t1_10_61 x F ∧
  WallE_cellA0_t1_16_60 x F ∧
  WallE_cellA0_t2_20_52 x F ∧
  WallE_cellA0_t2_25_50 x F ∧
  WallE_cellA0_t3_03_34 x F ∧
  WallE_cellA0_t3_04_30 x F ∧
  WallE_cellA0_t3_04_35 x F ∧
  WallE_cellA0_t3_05_30 x F ∧
  WallE_cellA0_t3_05_34 x F ∧
  WallE_cellA0_t3_30_53 x F ∧
  WallE_cellA0_t3_30_54 x F ∧
  WallE_cellA0_t3_34_50 x F ∧
  WallE_cellA0_t3_34_53 x F ∧
  WallE_cellA0_t3_35_50 x F ∧
  WallE_cellA0_t3_35_54 x F ∧
  WallE_cellA0_t3_40_53 x F ∧
  WallE_cellA0_t3_40_54 x F ∧
  WallE_cellA0_t3_43_50 x F ∧
  WallE_cellA0_t3_43_54 x F ∧
  WallE_cellA0_t3_45_50 x F ∧
  WallE_cellA0_t5_21_62 x F ∧
  WallE_cellA0_t5_26_61 x F ∧
  WallE_cellA0_t6_23_35 x F ∧
  WallE_cellA0_t6_25_32 x F ∧
  WallE_cellA0_t7_23_36 x F ∧
  WallE_cellA0_t7_26_63 x F ∧
  WallE_cellA0_t8_34_63 x F ∧
  WallE_cellA0_t8_36_64 x F

private lemma holeLeaf_allWallE2_cellA0 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellA0 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellA0_t0_10_21 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t0_12_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t1_10_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t1_16_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t2_25_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_03_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_30_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_34_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_34_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_43_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t6_23_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t7_23_36 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t7_26_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t8_34_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellA0_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cellA0_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellA0 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t0_10_21 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t0_12_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t1_10_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t1_16_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t2_25_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_03_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_30_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_34_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_34_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_43_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t6_23_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t7_23_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t7_26_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t8_34_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellA0_t8_36_64 (Sym.sym24 F)) hF

def AllWallE2_cellB0 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellB0_t0_10_21 x F ∧
  WallE_cellB0_t0_12_20 x F ∧
  WallE_cellB0_t1_10_61 x F ∧
  WallE_cellB0_t1_16_60 x F ∧
  WallE_cellB0_t2_20_52 x F ∧
  WallE_cellB0_t2_25_50 x F ∧
  WallE_cellB0_t3_04_30 x F ∧
  WallE_cellB0_t3_04_35 x F ∧
  WallE_cellB0_t3_05_30 x F ∧
  WallE_cellB0_t3_05_34 x F ∧
  WallE_cellB0_t3_30_43 x F ∧
  WallE_cellB0_t3_30_45 x F ∧
  WallE_cellB0_t3_30_53 x F ∧
  WallE_cellB0_t3_30_54 x F ∧
  WallE_cellB0_t3_34_40 x F ∧
  WallE_cellB0_t3_34_45 x F ∧
  WallE_cellB0_t3_34_50 x F ∧
  WallE_cellB0_t3_35_40 x F ∧
  WallE_cellB0_t3_35_50 x F ∧
  WallE_cellB0_t3_35_54 x F ∧
  WallE_cellB0_t3_40_53 x F ∧
  WallE_cellB0_t3_40_54 x F ∧
  WallE_cellB0_t3_43_50 x F ∧
  WallE_cellB0_t3_45_50 x F ∧
  WallE_cellB0_t4_40_64 x F ∧
  WallE_cellB0_t4_46_60 x F ∧
  WallE_cellB0_t5_21_62 x F ∧
  WallE_cellB0_t5_26_61 x F ∧
  WallE_cellB0_t6_23_35 x F ∧
  WallE_cellB0_t6_25_32 x F ∧
  WallE_cellB0_t8_34_63 x F ∧
  WallE_cellB0_t8_36_64 x F

private lemma holeLeaf_allWallE2_cellB0 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellB0 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellB0_t0_10_21 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t0_12_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t1_10_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t1_16_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t2_25_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_30_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_34_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_34_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t4_40_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t6_23_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t8_34_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cellB0_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cellB0_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellB0 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t0_10_21 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t0_12_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t1_10_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t1_16_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t2_25_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_30_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_34_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_34_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t4_40_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t6_23_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t8_34_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellB0_t8_36_64 (Sym.sym24 F)) hF

def AllWallE2_cellCp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellCp_t1_01_60 x F ∧
  WallE_cellCp_t1_06_61 x F ∧
  WallE_cellCp_t2_02_50 x F ∧
  WallE_cellCp_t2_20_52 x F ∧
  WallE_cellCp_t2_50_52 x F ∧
  WallE_cellCp_t3_03_40 x F ∧
  WallE_cellCp_t3_04_35 x F ∧
  WallE_cellCp_t3_04_45 x F ∧
  WallE_cellCp_t3_05_30 x F ∧
  WallE_cellCp_t3_05_34 x F ∧
  WallE_cellCp_t3_05_40 x F ∧
  WallE_cellCp_t3_30_43 x F ∧
  WallE_cellCp_t3_30_45 x F ∧
  WallE_cellCp_t3_30_53 x F ∧
  WallE_cellCp_t3_34_45 x F ∧
  WallE_cellCp_t3_35_40 x F ∧
  WallE_cellCp_t3_35_50 x F ∧
  WallE_cellCp_t3_35_54 x F ∧
  WallE_cellCp_t3_40_53 x F ∧
  WallE_cellCp_t3_43_50 x F ∧
  WallE_cellCp_t3_45_50 x F ∧
  WallE_cellCp_t4_06_40 x F ∧
  WallE_cellCp_t4_46_60 x F ∧
  WallE_cellCp_t5_21_62 x F ∧
  WallE_cellCp_t5_26_61 x F ∧
  WallE_cellCp_t6_25_32 x F ∧
  WallE_cellCp_t6_35_52 x F ∧
  WallE_cellCp_t7_26_32 x F ∧
  WallE_cellCp_t7_36_62 x F

private lemma holeLeaf_allWallE2_cellCp {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellCp x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellCp_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t2_50_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t7_26_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellCp_t7_36_62 F) hF

private lemma holeLeaf_allWallE2_cellCp_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellCp (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t2_50_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t7_26_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellCp_t7_36_62 (Sym.sym24 F)) hF

def AllWallE2_cell0236 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell0236_t0_01_20 x F ∧
  WallE_cell0236_t0_02_21 x F ∧
  WallE_cell0236_t1_01_60 x F ∧
  WallE_cell0236_t1_06_61 x F ∧
  WallE_cell0236_t2_02_50 x F ∧
  WallE_cell0236_t2_20_52 x F ∧
  WallE_cell0236_t3_03_40 x F ∧
  WallE_cell0236_t3_03_50 x F ∧
  WallE_cell0236_t3_04_35 x F ∧
  WallE_cell0236_t3_04_45 x F ∧
  WallE_cell0236_t3_05_34 x F ∧
  WallE_cell0236_t3_05_54 x F ∧
  WallE_cell0236_t3_30_43 x F ∧
  WallE_cell0236_t3_30_53 x F ∧
  WallE_cell0236_t3_34_45 x F ∧
  WallE_cell0236_t3_35_54 x F ∧
  WallE_cell0236_t3_40_43 x F ∧
  WallE_cell0236_t3_40_53 x F ∧
  WallE_cell0236_t3_43_50 x F ∧
  WallE_cell0236_t3_50_53 x F ∧
  WallE_cell0236_t4_06_40 x F ∧
  WallE_cell0236_t4_46_60 x F ∧
  WallE_cell0236_t6_23_52 x F ∧
  WallE_cell0236_t6_32_53 x F ∧
  WallE_cell0236_t7_26_32 x F ∧
  WallE_cell0236_t7_32_36 x F ∧
  WallE_cell0236_t7_36_62 x F ∧
  WallE_cell0236_t8_36_43 x F ∧
  WallE_cell0236_t8_46_63 x F

private lemma holeLeaf_allWallE2_cell0236 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell0236 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell0236_t0_01_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t0_02_21 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_03_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_05_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_40_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t3_50_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t6_23_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t6_32_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t7_26_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t7_32_36 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t8_36_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0236_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cell0236_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell0236 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t0_01_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t0_02_21 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_03_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_05_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_40_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t3_50_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t6_23_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t6_32_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t7_26_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t7_32_36 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t8_36_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0236_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cell0536 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell0536_t1_01_60 x F ∧
  WallE_cell0536_t1_06_61 x F ∧
  WallE_cell0536_t2_02_50 x F ∧
  WallE_cell0536_t2_05_52 x F ∧
  WallE_cell0536_t3_03_35 x F ∧
  WallE_cell0536_t3_03_40 x F ∧
  WallE_cell0536_t3_03_45 x F ∧
  WallE_cell0536_t3_04_35 x F ∧
  WallE_cell0536_t3_04_45 x F ∧
  WallE_cell0536_t3_05_30 x F ∧
  WallE_cell0536_t3_05_34 x F ∧
  WallE_cell0536_t3_05_40 x F ∧
  WallE_cell0536_t3_05_43 x F ∧
  WallE_cell0536_t3_30_43 x F ∧
  WallE_cell0536_t3_30_45 x F ∧
  WallE_cell0536_t3_34_45 x F ∧
  WallE_cell0536_t3_35_40 x F ∧
  WallE_cell0536_t3_35_43 x F ∧
  WallE_cell0536_t3_40_53 x F ∧
  WallE_cell0536_t3_43_50 x F ∧
  WallE_cell0536_t3_45_50 x F ∧
  WallE_cell0536_t3_45_53 x F ∧
  WallE_cell0536_t4_06_40 x F ∧
  WallE_cell0536_t4_46_60 x F ∧
  WallE_cell0536_t6_32_53 x F ∧
  WallE_cell0536_t6_35_52 x F ∧
  WallE_cell0536_t7_32_63 x F ∧
  WallE_cell0536_t7_36_62 x F ∧
  WallE_cell0536_t8_36_43 x F ∧
  WallE_cell0536_t8_46_63 x F

private lemma holeLeaf_allWallE2_cell0536 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell0536 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell0536_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t2_05_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_35_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t6_32_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t7_32_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t8_36_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0536_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cell0536_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell0536 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t2_05_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_35_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t6_32_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t7_32_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t8_36_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0536_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cellP (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cellP_t2_02_50 x F ∧
  WallE_cellP_t2_20_52 x F ∧
  WallE_cellP_t3_04_30 x F ∧
  WallE_cellP_t3_04_35 x F ∧
  WallE_cellP_t3_05_30 x F ∧
  WallE_cellP_t3_05_34 x F ∧
  WallE_cellP_t3_30_43 x F ∧
  WallE_cellP_t3_30_45 x F ∧
  WallE_cellP_t3_30_53 x F ∧
  WallE_cellP_t3_30_54 x F ∧
  WallE_cellP_t3_34_40 x F ∧
  WallE_cellP_t3_34_45 x F ∧
  WallE_cellP_t3_34_50 x F ∧
  WallE_cellP_t3_35_40 x F ∧
  WallE_cellP_t3_35_50 x F ∧
  WallE_cellP_t3_35_54 x F ∧
  WallE_cellP_t3_40_53 x F ∧
  WallE_cellP_t3_40_54 x F ∧
  WallE_cellP_t3_43_50 x F ∧
  WallE_cellP_t3_45_50 x F ∧
  WallE_cellP_t4_06_40 x F ∧
  WallE_cellP_t4_46_60 x F ∧
  WallE_cellP_t5_21_62 x F ∧
  WallE_cellP_t5_26_61 x F ∧
  WallE_cellP_t6_25_32 x F ∧
  WallE_cellP_t6_35_52 x F ∧
  WallE_cellP_t7_26_32 x F ∧
  WallE_cellP_t7_36_62 x F ∧
  WallE_cellP_t8_34_46 x F ∧
  WallE_cellP_t8_36_64 x F

private lemma holeLeaf_allWallE2_cellP {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cellP x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cellP_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_30_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_34_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_34_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t7_26_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t8_34_46 F) hF
  · exact holeLeaf_of_cert2 (cert_cellP_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cellP_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cellP (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cellP_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_30_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_34_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_34_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t7_26_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t8_34_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cellP_t8_36_64 (Sym.sym24 F)) hF

def AllWallE2_cell0164 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell0164_t0_01_12 x F ∧
  WallE_cell0164_t0_02_10 x F ∧
  WallE_cell0164_t1_01_60 x F ∧
  WallE_cell0164_t1_06_61 x F ∧
  WallE_cell0164_t3_03_34 x F ∧
  WallE_cell0164_t3_03_35 x F ∧
  WallE_cell0164_t3_03_40 x F ∧
  WallE_cell0164_t3_03_45 x F ∧
  WallE_cell0164_t3_04_35 x F ∧
  WallE_cell0164_t3_04_43 x F ∧
  WallE_cell0164_t3_04_45 x F ∧
  WallE_cell0164_t3_05_30 x F ∧
  WallE_cell0164_t3_05_34 x F ∧
  WallE_cell0164_t3_05_40 x F ∧
  WallE_cell0164_t3_05_43 x F ∧
  WallE_cell0164_t3_40_53 x F ∧
  WallE_cell0164_t3_43_50 x F ∧
  WallE_cell0164_t3_43_54 x F ∧
  WallE_cell0164_t3_45_50 x F ∧
  WallE_cell0164_t3_45_53 x F ∧
  WallE_cell0164_t4_04_60 x F ∧
  WallE_cell0164_t4_04_64 x F ∧
  WallE_cell0164_t4_06_64 x F ∧
  WallE_cell0164_t5_12_61 x F ∧
  WallE_cell0164_t5_16_62 x F ∧
  WallE_cell0164_t8_43_64 x F ∧
  WallE_cell0164_t8_46_63 x F

private lemma holeLeaf_allWallE2_cell0164 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell0164 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell0164_t0_01_12 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_03_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_04_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_43_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t4_04_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t4_04_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t4_06_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t5_16_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t8_43_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cell0164_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cell0164_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell0164 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t0_01_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_03_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_04_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_43_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t4_04_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t4_04_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t4_06_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t5_16_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t8_43_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell0164_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cell01634 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell01634_t0_01_12 x F ∧
  WallE_cell01634_t0_02_10 x F ∧
  WallE_cell01634_t1_01_60 x F ∧
  WallE_cell01634_t1_06_61 x F ∧
  WallE_cell01634_t3_03_35 x F ∧
  WallE_cell01634_t3_03_40 x F ∧
  WallE_cell01634_t3_03_45 x F ∧
  WallE_cell01634_t3_04_35 x F ∧
  WallE_cell01634_t3_04_45 x F ∧
  WallE_cell01634_t3_05_30 x F ∧
  WallE_cell01634_t3_05_34 x F ∧
  WallE_cell01634_t3_05_40 x F ∧
  WallE_cell01634_t3_05_43 x F ∧
  WallE_cell01634_t3_30_43 x F ∧
  WallE_cell01634_t3_30_45 x F ∧
  WallE_cell01634_t3_34_45 x F ∧
  WallE_cell01634_t3_35_40 x F ∧
  WallE_cell01634_t3_35_43 x F ∧
  WallE_cell01634_t3_40_53 x F ∧
  WallE_cell01634_t3_43_50 x F ∧
  WallE_cell01634_t3_45_50 x F ∧
  WallE_cell01634_t3_45_53 x F ∧
  WallE_cell01634_t4_04_60 x F ∧
  WallE_cell01634_t4_40_64 x F ∧
  WallE_cell01634_t5_12_61 x F ∧
  WallE_cell01634_t5_16_62 x F ∧
  WallE_cell01634_t7_32_63 x F ∧
  WallE_cell01634_t7_36_62 x F ∧
  WallE_cell01634_t8_43_64 x F ∧
  WallE_cell01634_t8_46_63 x F

private lemma holeLeaf_allWallE2_cell01634 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell01634 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell01634_t0_01_12 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t0_02_10 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_35_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t4_04_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t4_40_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t5_12_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t5_16_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t7_32_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t7_36_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t8_43_64 F) hF
  · exact holeLeaf_of_cert2 (cert_cell01634_t8_46_63 F) hF

private lemma holeLeaf_allWallE2_cell01634_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell01634 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t0_01_12 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t0_02_10 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_35_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t4_04_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t4_40_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t5_12_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t5_16_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t7_32_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t7_36_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t8_43_64 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell01634_t8_46_63 (Sym.sym24 F)) hF

def AllWallE2_cell05326 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell05326_t1_01_60 x F ∧
  WallE_cell05326_t1_06_61 x F ∧
  WallE_cell05326_t2_02_50 x F ∧
  WallE_cell05326_t2_05_52 x F ∧
  WallE_cell05326_t3_03_35 x F ∧
  WallE_cell05326_t3_03_40 x F ∧
  WallE_cell05326_t3_03_45 x F ∧
  WallE_cell05326_t3_04_35 x F ∧
  WallE_cell05326_t3_04_45 x F ∧
  WallE_cell05326_t3_05_30 x F ∧
  WallE_cell05326_t3_05_34 x F ∧
  WallE_cell05326_t3_05_40 x F ∧
  WallE_cell05326_t3_05_43 x F ∧
  WallE_cell05326_t3_05_45 x F ∧
  WallE_cell05326_t3_30_43 x F ∧
  WallE_cell05326_t3_30_45 x F ∧
  WallE_cell05326_t3_34_45 x F ∧
  WallE_cell05326_t3_35_40 x F ∧
  WallE_cell05326_t3_35_43 x F ∧
  WallE_cell05326_t3_40_53 x F ∧
  WallE_cell05326_t3_43_45 x F ∧
  WallE_cell05326_t3_43_50 x F ∧
  WallE_cell05326_t3_45_50 x F ∧
  WallE_cell05326_t3_45_53 x F ∧
  WallE_cell05326_t4_06_40 x F ∧
  WallE_cell05326_t4_46_60 x F ∧
  WallE_cell05326_t5_21_62 x F ∧
  WallE_cell05326_t5_26_61 x F ∧
  WallE_cell05326_t6_25_32 x F ∧
  WallE_cell05326_t6_35_52 x F ∧
  WallE_cell05326_t7_32_63 x F ∧
  WallE_cell05326_t7_36_62 x F

private lemma holeLeaf_allWallE2_cell05326 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell05326 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell05326_t1_01_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t1_06_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t2_05_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_03_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_03_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_03_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_04_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_05_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_05_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_05_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_35_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_43_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t3_45_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t7_32_63 F) hF
  · exact holeLeaf_of_cert2 (cert_cell05326_t7_36_62 F) hF

private lemma holeLeaf_allWallE2_cell05326_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell05326 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t1_01_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t1_06_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t2_05_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_03_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_03_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_03_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_04_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_05_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_05_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_05_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_35_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_43_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t3_45_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t7_32_63 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell05326_t7_36_62 (Sym.sym24 F)) hF

def AllWallE2_cell046125 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  WallE_cell046125_t0_10_21 x F ∧
  WallE_cell046125_t0_12_20 x F ∧
  WallE_cell046125_t1_10_61 x F ∧
  WallE_cell046125_t1_16_60 x F ∧
  WallE_cell046125_t2_02_50 x F ∧
  WallE_cell046125_t2_20_52 x F ∧
  WallE_cell046125_t3_04_30 x F ∧
  WallE_cell046125_t3_04_35 x F ∧
  WallE_cell046125_t3_05_30 x F ∧
  WallE_cell046125_t3_05_34 x F ∧
  WallE_cell046125_t3_30_43 x F ∧
  WallE_cell046125_t3_30_45 x F ∧
  WallE_cell046125_t3_30_53 x F ∧
  WallE_cell046125_t3_30_54 x F ∧
  WallE_cell046125_t3_34_40 x F ∧
  WallE_cell046125_t3_34_45 x F ∧
  WallE_cell046125_t3_34_50 x F ∧
  WallE_cell046125_t3_35_40 x F ∧
  WallE_cell046125_t3_35_50 x F ∧
  WallE_cell046125_t3_35_54 x F ∧
  WallE_cell046125_t3_40_53 x F ∧
  WallE_cell046125_t3_40_54 x F ∧
  WallE_cell046125_t3_43_50 x F ∧
  WallE_cell046125_t3_45_50 x F ∧
  WallE_cell046125_t4_06_40 x F ∧
  WallE_cell046125_t4_46_60 x F ∧
  WallE_cell046125_t5_21_62 x F ∧
  WallE_cell046125_t5_26_61 x F ∧
  WallE_cell046125_t6_25_32 x F ∧
  WallE_cell046125_t6_35_52 x F ∧
  WallE_cell046125_t8_34_46 x F ∧
  WallE_cell046125_t8_36_64 x F

private lemma holeLeaf_allWallE2_cell046125 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2_cell046125 x F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2 (cert_cell046125_t0_10_21 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t0_12_20 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t1_10_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t1_16_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t2_02_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t2_20_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_04_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_04_35 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_05_30 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_05_34 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_30_43 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_30_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_30_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_30_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_34_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_34_45 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_34_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_35_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_35_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_35_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_40_53 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_40_54 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_43_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t3_45_50 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t4_06_40 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t4_46_60 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t5_21_62 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t5_26_61 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t6_25_32 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t6_35_52 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t8_34_46 F) hF
  · exact holeLeaf_of_cert2 (cert_cell046125_t8_36_64 F) hF

private lemma holeLeaf_allWallE2_cell046125_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2_cell046125 (x ∘ Sym.pi24) (Sym.sym24 F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t0_10_21 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t0_12_20 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t1_10_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t1_16_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t2_02_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t2_20_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_04_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_04_35 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_05_30 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_05_34 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_30_43 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_30_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_30_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_30_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_34_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_34_45 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_34_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_35_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_35_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_35_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_40_53 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_40_54 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_43_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t3_45_50 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t4_06_40 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t4_46_60 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t5_21_62 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t5_26_61 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t6_25_32 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t6_35_52 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t8_34_46 (Sym.sym24 F)) hF
  · exact holeLeaf_of_cert2_twin (cert_cell046125_t8_36_64 (Sym.sym24 F)) hF

/-- Conjunction of `WallE` across all 594 `cells28` walls (`140` from `AllWallE` + `454` new). -/
def AllWallE2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  AllWallE x F ∧
  AllWallE2_cellC x F ∧
  AllWallE2_cellD x F ∧
  AllWallE2_cellD6 x F ∧
  AllWallE2_cellA2 x F ∧
  AllWallE2_cellB2 x F ∧
  AllWallE2_cellA0 x F ∧
  AllWallE2_cellB0 x F ∧
  AllWallE2_cellCp x F ∧
  AllWallE2_cell0236 x F ∧
  AllWallE2_cell0536 x F ∧
  AllWallE2_cellP x F ∧
  AllWallE2_cell0164 x F ∧
  AllWallE2_cell01634 x F ∧
  AllWallE2_cell05326 x F ∧
  AllWallE2_cell046125 x F

/-- **Hole fact:** at a `HoleLeaf`, `AllWallE2 x F` holds. -/
theorem holeLeaf_allWallE2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : AllWallE2 x F :=
  ⟨holeLeaf_allWallE hF, holeLeaf_allWallE2_cellC hF, holeLeaf_allWallE2_cellD hF, holeLeaf_allWallE2_cellD6 hF, holeLeaf_allWallE2_cellA2 hF, holeLeaf_allWallE2_cellB2 hF, holeLeaf_allWallE2_cellA0 hF, holeLeaf_allWallE2_cellB0 hF, holeLeaf_allWallE2_cellCp hF, holeLeaf_allWallE2_cell0236 hF, holeLeaf_allWallE2_cell0536 hF, holeLeaf_allWallE2_cellP hF, holeLeaf_allWallE2_cell0164 hF, holeLeaf_allWallE2_cell01634 hF, holeLeaf_allWallE2_cell05326 hF, holeLeaf_allWallE2_cell046125 hF⟩

/-- **Twin hole fact:** at a `HoleLeaf`, `AllWallE2 (x ∘ Sym.pi24) (Sym.sym24 F)` holds. -/
theorem holeLeaf_allWallE2_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    AllWallE2 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  ⟨holeLeaf_allWallE_twin hF, holeLeaf_allWallE2_cellC_twin hF, holeLeaf_allWallE2_cellD_twin hF, holeLeaf_allWallE2_cellD6_twin hF, holeLeaf_allWallE2_cellA2_twin hF, holeLeaf_allWallE2_cellB2_twin hF, holeLeaf_allWallE2_cellA0_twin hF, holeLeaf_allWallE2_cellB0_twin hF, holeLeaf_allWallE2_cellCp_twin hF, holeLeaf_allWallE2_cell0236_twin hF, holeLeaf_allWallE2_cell0536_twin hF, holeLeaf_allWallE2_cellP_twin hF, holeLeaf_allWallE2_cell0164_twin hF, holeLeaf_allWallE2_cell01634_twin hF, holeLeaf_allWallE2_cell05326_twin hF, holeLeaf_allWallE2_cell046125_twin hF⟩

/-- **[OPEN] `CellCoverEmptyAll2 L`**: on `CbarIn`, `OB1`, with `AllWallE2` on `x` and on the twin, the point
is not in the cell-cover residue of `L`. -/
def CellCoverEmptyAll2 (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → AllWallE2 x F →
    AllWallE2 (x ∘ Sym.pi24) (Sym.sym24 F) → ¬ CellCoverResidue L x F

/-- `CellCoverEmptyAll L` implies `CellCoverEmptyAll2 L`. -/
theorem cellCoverEmptyAll2_of_cellCoverEmptyAll {L : List Cell24} (h : CellCoverEmptyAll L) :
    CellCoverEmptyAll2 L :=
  fun x F hC hO hA hA' => h x F hC hO hA.1 hA'.1

/-- `CellCoverEmptyAll2 L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyAll2 {L : List Cell24} (hN : CellCoverEmptyAll2 L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_allWallE2 h) (holeLeaf_allWallE2_twin h) (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyAll2 L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyAll2 {L : List Cell24} (hN : CellCoverEmptyAll2 L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyAll2 hN x F hO (holeLeaf_of_holeFull hF)

end Minimality.T24.Cell
