module

public import Minimality.EdgeTiltBD
public import Minimality.RimCellClosed
public import Mathlib
public import Minimality.Type24
public import Minimality.SlideDS
public import Minimality.Type24Side
public import Minimality.LemmaTQ
public import Minimality.SilS0XC
public import Minimality.Type24SAT.Facets24



@[expose] public section

/-!
# Hexagon Edge Leaves at Untilted End-On Views (Theorems Q9.1 and Q9.1m)

Formalization of the verified hexagon edge leaf at the untilted end-on view
`W06 = x 6 - x 0` (Theorem Q9.1) and its mirror `W02 = x 2 - x 0` (Theorem Q9.1m)
under the `(2 6)(4 5)` relabelling.

For a type-24 solid, at `W06 = x 6 - x 0`, the rim is `K6 = ![x 1, x 6, x 4, x 3, x 2]`,
with hidden axle end `w = x 0` (`i₀ = 1`), middles `M = ∅`, and hidden vertex `x 5`.
Using `Minimality.isRupert_of_edgeView_depthSeparated_rim` with edge `e = [x 3, x 2]`
and corner `c = x 1` (`a = 3, c = 0` in `ZMod 5`), `DepthSepAt (K6 x) (W06 x) 3 0`
holds algebraically for every `b3 < 1` and `a3 + c3 > 0` from the determinant identities
in corner coordinates.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.HexEdge06

open Minimality
open Minimality.H21
open Minimality.T24.SAT
open Minimality.T24.TQ

/-- Rim cycle around vertex 6 at view `W06`: corners 1, 6, 4, 3, 2. -/
def K6 (x : Fin 7 → ℝ³) : ZMod 5 → ℝ³ := ![x 1, x 6, x 4, x 3, x 2]

/-- Untilted end-on view along edge `0-6`. -/
def W06 (x : Fin 7 → ℝ³) : ℝ³ := x 6 - x 0

/-- Rim cycle around vertex 2 at view `W02`: corners 1, 2, 5, 3, 6. -/
def K2 (x : Fin 7 → ℝ³) : ZMod 5 → ℝ³ := ![x 1, x 2, x 5, x 3, x 6]

/-- Untilted end-on view along edge `0-2`. -/
def W02 (x : Fin 7 → ℝ³) : ℝ³ := x 2 - x 0

/-! ### Determinant and volume identities at `W06` -/

theorem vol3_swap23 (a b c : ℝ³) : vol3 a c b = - vol3 a b c := by
  simp only [vol3]; ring

theorem W06_eq_comb (x : Fin 7 → ℝ³) :
    W06 x = (-1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
  ext i; fin_cases i <;> { simp only [W06, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring }

theorem det3_comb_W06 (ea eb ec : ℝ³) (a0 a1 a2 b0 b1 b2 : ℝ) :
    det3 (a0 • ea + a1 • eb + a2 • ec) (b0 • ea + b1 • eb + b2 • ec)
        ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      ((a0 + a2) * b1 - a1 * (b0 + b2)) * vol3 ea eb ec := by
  rw [det3_comb]
  ring

theorem det3_x23_x13_W06 (ea eb ec : ℝ³) (a3 b3 c3 : ℝ) :
    det3 ((-a3) • ea + (1 - b3) • eb + (-c3) • ec)
         ((-a3) • ea + (-b3) • eb + (-c3) • ec)
         ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      (a3 + c3) * vol3 ea eb ec := by
  rw [det3_comb_W06]; ring

theorem det3_x23_x61_W06 (ea eb ec : ℝ³) (a3 b3 c3 : ℝ) :
    det3 ((-a3) • ea + (1 - b3) • eb + (-c3) • ec)
         ((0 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec)
         ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      -(1 - b3) * vol3 ea eb ec := by
  rw [det3_comb_W06]; ring

theorem det3_x23_x41_W06 (ea eb ec : ℝ³) (a3 b3 c3 a4 b4 c4 : ℝ) :
    det3 ((-a3) • ea + (1 - b3) • eb + (-c3) • ec)
         (a4 • ea + b4 • eb + c4 • ec)
         ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      -((a3 + c3) * b4 + (1 - b3) * (a4 + c4)) * vol3 ea eb ec := by
  rw [det3_comb_W06]; ring

theorem det3_x23_x31_W06 (ea eb ec : ℝ³) (a3 b3 c3 : ℝ) :
    det3 ((-a3) • ea + (1 - b3) • eb + (-c3) • ec)
         (a3 • ea + b3 • eb + c3 • ec)
         ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      -(a3 + c3) * vol3 ea eb ec := by
  rw [det3_comb_W06]; ring

theorem det3_x23_x21_W06 (ea eb ec : ℝ³) (a3 b3 c3 : ℝ) :
    det3 ((-a3) • ea + (1 - b3) • eb + (-c3) • ec)
         ((0 : ℝ) • ea + (1 : ℝ) • eb + (0 : ℝ) • ec)
         ((-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec) =
      -(a3 + c3) * vol3 ea eb ec := by
  rw [det3_comb_W06]; ring

/-! ### Corner coordinates and depth separation at `W06` -/

/-- Corner coordinates of vertices 3 and 4 in the frame `(x 0 - x 1, x 2 - x 1, x 6 - x 1)`. -/
structure CornerCoords06 (x : Fin 7 → ℝ³) where
  a3 : ℝ
  b3 : ℝ
  c3 : ℝ
  a4 : ℝ
  b4 : ℝ
  c4 : ℝ
  hx3 : x 3 - x 1 = a3 • (x 0 - x 1) + b3 • (x 2 - x 1) + c3 • (x 6 - x 1)
  hx4 : x 4 - x 1 = a4 • (x 0 - x 1) + b4 • (x 2 - x 1) + c4 • (x 6 - x 1)
  ha3c3 : 0 < a3 + c3
  hb3 : b3 < 1
  ha4c4 : 0 < a4 + c4
  hb4 : 0 < b4

theorem det3_products_of_coords (x : Fin 7 → ℝ³) (C : CornerCoords06 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0) :
    let Dbase := det3 (x 2 - x 3) (x 1 - x 3) (W06 x)
    det3 (x 2 - x 3) (x 6 - x 1) (W06 x) * Dbase < 0 ∧
    det3 (x 2 - x 3) (x 4 - x 1) (W06 x) * Dbase < 0 ∧
    det3 (x 2 - x 3) (x 3 - x 1) (W06 x) * Dbase < 0 ∧
    det3 (x 2 - x 3) (x 2 - x 1) (W06 x) * Dbase < 0 := by
  intro Dbase
  set ea := x 0 - x 1
  set eb := x 2 - x 1
  set ec := x 6 - x 1
  have hW : W06 x = (-1 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec := W06_eq_comb x
  have he23 : x 2 - x 3 = (-C.a3) • ea + (1 - C.b3) • eb + (-C.c3) • ec := by
    have h : x 2 - x 3 = (x 2 - x 1) - (x 3 - x 1) := by
      ext i; fin_cases i <;> { simp only [PiLp.sub_apply]; ring }
    rw [h, C.hx3]
    ext i; fin_cases i <;> {
      dsimp only [ea, eb, ec]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    }
  have he13 : x 1 - x 3 = (-C.a3) • ea + (-C.b3) • eb + (-C.c3) • ec := by
    have h : x 1 - x 3 = -(x 3 - x 1) := by
      ext i; fin_cases i <;> { simp only [PiLp.sub_apply, PiLp.neg_apply]; ring }
    rw [h, C.hx3]
    ext i; fin_cases i <;> {
      dsimp only [ea, eb, ec]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    }
  have he61 : x 6 - x 1 = (0 : ℝ) • ea + (0 : ℝ) • eb + (1 : ℝ) • ec := by
    ext i; fin_cases i <;> {
      dsimp only [ea, eb, ec]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    }
  have he41 : x 4 - x 1 = C.a4 • ea + C.b4 • eb + C.c4 • ec := C.hx4
  have he31 : x 3 - x 1 = C.a3 • ea + C.b3 • eb + C.c3 • ec := C.hx3
  have he21 : x 2 - x 1 = (0 : ℝ) • ea + (1 : ℝ) • eb + (0 : ℝ) • ec := by
    ext i; fin_cases i <;> {
      dsimp only [ea, eb, ec]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    }
  have hbase : Dbase = (C.a3 + C.c3) * vol3 ea eb ec := by
    dsimp [Dbase]
    rw [he23, he13, hW, det3_x23_x13_W06]
  have h1 : det3 (x 2 - x 3) (x 6 - x 1) (W06 x) = -(1 - C.b3) * vol3 ea eb ec := by
    rw [he23, he61, hW, det3_x23_x61_W06]
  have h2 : det3 (x 2 - x 3) (x 4 - x 1) (W06 x) =
      -((C.a3 + C.c3) * C.b4 + (1 - C.b3) * (C.a4 + C.c4)) * vol3 ea eb ec := by
    rw [he23, he41, hW, det3_x23_x41_W06]
  have h3 : det3 (x 2 - x 3) (x 3 - x 1) (W06 x) = -(C.a3 + C.c3) * vol3 ea eb ec := by
    rw [he23, he31, hW, det3_x23_x31_W06]
  have h4 : det3 (x 2 - x 3) (x 2 - x 1) (W06 x) = -(C.a3 + C.c3) * vol3 ea eb ec := by
    rw [he23, he21, hW, det3_x23_x21_W06]
  set V0 := vol3 ea eb ec
  have hV2 : 0 < V0 ^ 2 := sq_pos_of_ne_zero hV0
  have hb3_pos : 0 < 1 - C.b3 := sub_pos.mpr C.hb3
  have h_prod1 : 0 < (1 - C.b3) * (C.a3 + C.c3) * V0 ^ 2 := by
    apply mul_pos (mul_pos hb3_pos C.ha3c3) hV2
  have h_inner : 0 < (C.a3 + C.c3) * C.b4 + (1 - C.b3) * (C.a4 + C.c4) := by
    apply add_pos (mul_pos C.ha3c3 C.hb4) (mul_pos hb3_pos C.ha4c4)
  have h_prod2 : 0 < ((C.a3 + C.c3) * C.b4 + (1 - C.b3) * (C.a4 + C.c4)) * (C.a3 + C.c3) * V0 ^ 2 := by
    apply mul_pos (mul_pos h_inner C.ha3c3) hV2
  have h_sq : 0 < (C.a3 + C.c3) ^ 2 := sq_pos_of_ne_zero (ne_of_gt C.ha3c3)
  have h_prod3 : 0 < (C.a3 + C.c3) ^ 2 * V0 ^ 2 := mul_pos h_sq hV2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, hbase]
    have : -(1 - C.b3) * V0 * ((C.a3 + C.c3) * V0) = -((1 - C.b3) * (C.a3 + C.c3) * V0 ^ 2) := by ring
    rw [this]
    linarith
  · rw [h2, hbase]
    have : -((C.a3 + C.c3) * C.b4 + (1 - C.b3) * (C.a4 + C.c4)) * V0 * ((C.a3 + C.c3) * V0) =
        -(((C.a3 + C.c3) * C.b4 + (1 - C.b3) * (C.a4 + C.c4)) * (C.a3 + C.c3) * V0 ^ 2) := by ring
    rw [this]
    linarith
  · rw [h3, hbase]
    have : -(C.a3 + C.c3) * V0 * ((C.a3 + C.c3) * V0) = -((C.a3 + C.c3) ^ 2 * V0 ^ 2) := by ring
    rw [this]
    linarith
  · rw [h4, hbase]
    have : -(C.a3 + C.c3) * V0 * ((C.a3 + C.c3) * V0) = -((C.a3 + C.c3) ^ 2 * V0 ^ 2) := by ring
    rw [this]
    linarith

theorem depth_part_proof (x : Fin 7 → ℝ³)
    (hz2 : ⟪x 2 - x 1, W06 x⟫ < 0)
    (hz4 : 0 < ⟪x 4 - x 1, W06 x⟫)
    (hz3 : 0 < ⟪x 3 - x 1, W06 x⟫)
    (hz6 : 0 < ⟪x 6 - x 1, W06 x⟫) :
    (∀ s : ℕ, 0 < s → s ≤ (3 - (0 : ZMod 5)).val → ⟪K6 x 0, W06 x⟫ < ⟪K6 x (0 + (s : ZMod 5)), W06 x⟫) ∧
    (∀ s : ℕ, (3 - (0 : ZMod 5)).val < s → s < 5 → ⟪K6 x (0 + (s : ZMod 5)), W06 x⟫ < ⟪K6 x 0, W06 x⟫) := by
  have hval : (3 - (0 : ZMod 5)).val = 3 := by decide
  rw [hval]
  refine ⟨fun s hs0 hs3 => ?_, fun s hs3 hs5 => ?_⟩
  · interval_cases s
    · show ⟪x 1, W06 x⟫ < ⟪x 6, W06 x⟫
      rw [← sub_pos, ← inner_sub_left]
      exact hz6
    · show ⟪x 1, W06 x⟫ < ⟪x 4, W06 x⟫
      rw [← sub_pos, ← inner_sub_left]
      exact hz4
    · show ⟪x 1, W06 x⟫ < ⟪x 3, W06 x⟫
      rw [← sub_pos, ← inner_sub_left]
      exact hz3
  · interval_cases s
    · show ⟪x 2, W06 x⟫ < ⟪x 1, W06 x⟫
      rw [← sub_neg, ← inner_sub_left]
      exact hz2

theorem depthSepAt_K6 (x : Fin 7 → ℝ³) (C : CornerCoords06 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz2 : ⟪x 2 - x 1, W06 x⟫ < 0)
    (hz4 : 0 < ⟪x 4 - x 1, W06 x⟫)
    (hz3 : 0 < ⟪x 3 - x 1, W06 x⟫)
    (hz6 : 0 < ⟪x 6 - x 1, W06 x⟫) :
    DepthSepAt (K6 x) (W06 x) 3 0 := by
  refine ⟨fun j hj => ?_, Or.inl (depth_part_proof x hz2 hz4 hz3 hz6)⟩
  have hp := det3_products_of_coords x C hV0
  fin_cases j
  · contradiction
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2

/-! ### Strict convexity and depth predicates -/

/-- Strict convexity of rim `K6` and strict containment of `x 5` at view `W06`. -/
def HexConv06 (x : Fin 7 → ℝ³) : Prop :=
  (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < det3 (K6 x (i + 1) - K6 x i) (K6 x j - K6 x i) (W06 x)) ∧
  (∀ i : ZMod 5, 0 < det3 (K6 x (i + 1) - K6 x i) (x 5 - K6 x i) (W06 x))

/-- Depth conditions at view `W06`: vertex 1 at depth 0, 2 behind, 4, 3, 6 in front. -/
def DepthSepDepths06 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 2 - x 1, W06 x⟫ < 0 ∧
  0 < ⟪x 4 - x 1, W06 x⟫ ∧
  0 < ⟪x 3 - x 1, W06 x⟫ ∧
  0 < ⟪x 6 - x 1, W06 x⟫

/-- Strict convexity of rim `K2` and strict containment of `x 4` at view `W02`. -/
def HexConv02 (x : Fin 7 → ℝ³) : Prop :=
  (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < det3 (K2 x (i + 1) - K2 x i) (K2 x j - K2 x i) (W02 x)) ∧
  (∀ i : ZMod 5, 0 < det3 (K2 x (i + 1) - K2 x i) (x 4 - K2 x i) (W02 x))

/-- Depth conditions at view `W02`: vertex 1 at depth 0, 6 behind, 5, 3, 2 in front. -/
def DepthSepDepths02 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 6 - x 1, W02 x⟫ < 0 ∧
  0 < ⟪x 5 - x 1, W02 x⟫ ∧
  0 < ⟪x 3 - x 1, W02 x⟫ ∧
  0 < ⟪x 2 - x 1, W02 x⟫

/-! ### Raw leaf at `W06` from `isRupert_of_edgeView_depthSeparated_rim` -/

theorem isRupert_hexQ91_raw (x : Fin 7 → ℝ³)
    (hu : W06 x ≠ 0)
    (hconv_cyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < det3 (K6 x (i + 1) - K6 x i) (K6 x j - K6 x i) (W06 x))
    (hconv_x5 : ∀ i : ZMod 5, 0 < det3 (K6 x (i + 1) - K6 x i) (x 5 - K6 x i) (W06 x))
    (hds : DepthSepAt (K6 x) (W06 x) 3 0)
    (hhdn : NoHDNRim (K6 x) (W06 x)) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_of_edgeView_depthSeparated_rim (Finset.univ.image x) ∅ (W06 x) hu
    (hk := by decide) (p := K6 x) (i₀ := 1) (w := x 0) (h := 1)
    (hwV := Finset.mem_image_of_mem x (Finset.mem_univ 0))
    (hw := by dsimp [K6, W06]; simp only [one_smul, sub_sub_cancel])
    (hh := by norm_num)
    (hpV := by intro i; fin_cases i <;> exact Finset.mem_image_of_mem x (Finset.mem_univ _))
    (hpM := fun i hi => nomatch hi)
    (hcyc := hconv_cyc)
    (hrest := ?_)
    (hds := hds)
    (hnd := hhdn)
    (hM := fun m hm => nomatch hm)
  intro v hv _ hvw hvp i
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hv
  fin_cases m
  · exact (hvw rfl).elim
  · exact (hvp 0 rfl).elim
  · exact (hvp 4 rfl).elim
  · exact (hvp 3 rfl).elim
  · exact (hvp 2 rfl).elim
  · exact hconv_x5 i
  · exact (hvp 1 rfl).elim

/-- **Theorem Q9.1**: hexagon edge leaf at the untilted view `W06 = x 6 - x 0`. -/
theorem isRupert_hexQ91 (x : Fin 7 → ℝ³)
    (hconv : HexConv06 x)
    (hds : DepthSepAt (K6 x) (W06 x) 3 0)
    (hhdn : NoHDNRim (K6 x) (W06 x))
    (hu : W06 x ≠ 0) :
    IsRupert (Finset.univ.image x) :=
  isRupert_hexQ91_raw x hu hconv.1 hconv.2 hds hhdn

/-- **Theorem Q9.1** (with corner coordinates): hexagon edge leaf at `W06 = x 6 - x 0`. -/
theorem isRupert_hexQ91_of_coords (x : Fin 7 → ℝ³) (C : CornerCoords06 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths06 x)
    (hconv : HexConv06 x)
    (hhdn : NoHDNRim (K6 x) (W06 x)) :
    IsRupert (Finset.univ.image x) := by
  have hu : W06 x ≠ 0 := by
    intro hu0
    have : ⟪x 4 - x 1, W06 x⟫ = 0 := by rw [hu0, inner_zero_right]
    linarith [hz.2.1]
  have hds := depthSepAt_K6 x C hV0 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact isRupert_hexQ91 x hconv hds hhdn hu

/-- **Theorem Q9.1** for a type-24 solid: hexagon edge leaf at `W06 = x 6 - x 0`. -/
theorem isRupert_hexQ91_fac {x : Fin 7 → ℝ³} (_F : S0xFac 9 s0x_S24 x) (C : CornerCoords06 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths06 x)
    (hconv : HexConv06 x)
    (hhdn : NoHDNRim (K6 x) (W06 x)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_hexQ91_of_coords x C hV0 hz hconv hhdn

/-! ### The mirror leaf at `W02` under `(2 6)(4 5)` relabelling -/

/-- Corner coordinates for vertex 2 view in the frame `(x 0 - x 1, x 2 - x 1, x 6 - x 1)`. -/
structure CornerCoords02 (x : Fin 7 → ℝ³) where
  a3 : ℝ
  b3 : ℝ
  c3 : ℝ
  a5 : ℝ
  b5 : ℝ
  c5 : ℝ
  hx3 : x 3 - x 1 = a3 • (x 0 - x 1) + b3 • (x 2 - x 1) + c3 • (x 6 - x 1)
  hx5 : x 5 - x 1 = a5 • (x 0 - x 1) + b5 • (x 2 - x 1) + c5 • (x 6 - x 1)
  ha3b3 : 0 < a3 + b3
  hc3 : c3 < 1
  ha5b5 : 0 < a5 + b5
  hc5 : 0 < c5

def relab_coords {x : Fin 7 → ℝ³} (C : CornerCoords02 x) : CornerCoords06 (x ∘ sg) where
  a3 := C.a3
  b3 := C.c3
  c3 := C.b3
  a4 := C.a5
  b4 := C.c5
  c4 := C.b5
  hx3 := by
    change x 3 - x 1 = C.a3 • (x 0 - x 1) + C.c3 • (x 6 - x 1) + C.b3 • (x 2 - x 1)
    rw [C.hx3]
    abel
  hx4 := by
    change x 5 - x 1 = C.a5 • (x 0 - x 1) + C.c5 • (x 6 - x 1) + C.b5 • (x 2 - x 1)
    rw [C.hx5]
    abel
  ha3c3 := C.ha3b3
  hb3 := C.hc3
  ha4c4 := C.ha5b5
  hb4 := C.hc5

theorem depthSepAt_K2 (x : Fin 7 → ℝ³) (C : CornerCoords02 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz6 : ⟪x 6 - x 1, W02 x⟫ < 0)
    (hz5 : 0 < ⟪x 5 - x 1, W02 x⟫)
    (hz3 : 0 < ⟪x 3 - x 1, W02 x⟫)
    (hz2 : 0 < ⟪x 2 - x 1, W02 x⟫) :
    DepthSepAt (K2 x) (W02 x) 3 0 := by
  have hK : K6 (x ∘ sg) = K2 x := by
    funext i; fin_cases i <;> rfl
  have hW : W06 (x ∘ sg) = W02 x := rfl
  have hV0' : vol3 ((x ∘ sg) 0 - (x ∘ sg) 1) ((x ∘ sg) 2 - (x ∘ sg) 1) ((x ∘ sg) 6 - (x ∘ sg) 1) ≠ 0 := by
    change vol3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) ≠ 0
    rw [vol3_swap23]
    exact neg_ne_zero.mpr hV0
  have hds := depthSepAt_K6 (x ∘ sg) (relab_coords C) hV0' hz6 hz5 hz3 hz2
  rw [← hK, ← hW]
  exact hds

theorem isRupert_hexQ91m_raw (x : Fin 7 → ℝ³)
    (hu : W02 x ≠ 0)
    (hconv_cyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < det3 (K2 x (i + 1) - K2 x i) (K2 x j - K2 x i) (W02 x))
    (hconv_x4 : ∀ i : ZMod 5, 0 < det3 (K2 x (i + 1) - K2 x i) (x 4 - K2 x i) (W02 x))
    (hds : DepthSepAt (K2 x) (W02 x) 3 0)
    (hhdn : NoHDNRim (K2 x) (W02 x)) :
    IsRupert (Finset.univ.image x) := by
  have himg : Finset.univ.image (x ∘ sg) = Finset.univ.image x := by
    rw [← Finset.image_image, show Finset.univ.image sg = Finset.univ from
      Finset.image_univ_of_surjective (Finite.surjective_of_injective sg_inj)]
  rw [← himg]
  have hK : K6 (x ∘ sg) = K2 x := by
    funext i; fin_cases i <;> rfl
  have hW : W06 (x ∘ sg) = W02 x := rfl
  refine isRupert_hexQ91_raw (x ∘ sg) ?_ ?_ ?_ ?_ ?_
  · rw [hW]; exact hu
  · rw [hK, hW]; exact hconv_cyc
  · rw [hK, hW]; exact hconv_x4
  · rw [hK, hW]; exact hds
  · rw [hK, hW]; exact hhdn

/-- **Theorem Q9.1 mirror**: hexagon edge leaf at the untilted view `W02 = x 2 - x 0`. -/
theorem isRupert_hexQ91m (x : Fin 7 → ℝ³)
    (hconv : HexConv02 x)
    (hds : DepthSepAt (K2 x) (W02 x) 3 0)
    (hhdn : NoHDNRim (K2 x) (W02 x))
    (hu : W02 x ≠ 0) :
    IsRupert (Finset.univ.image x) :=
  isRupert_hexQ91m_raw x hu hconv.1 hconv.2 hds hhdn

/-- **Theorem Q9.1 mirror** (with corner coordinates): hexagon edge leaf at `W02 = x 2 - x 0`. -/
theorem isRupert_hexQ91m_of_coords (x : Fin 7 → ℝ³) (C : CornerCoords02 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths02 x)
    (hconv : HexConv02 x)
    (hhdn : NoHDNRim (K2 x) (W02 x)) :
    IsRupert (Finset.univ.image x) := by
  have hu : W02 x ≠ 0 := by
    intro hu0
    have : ⟪x 5 - x 1, W02 x⟫ = 0 := by rw [hu0, inner_zero_right]
    linarith [hz.2.1]
  have hds := depthSepAt_K2 x C hV0 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact isRupert_hexQ91m x hconv hds hhdn hu

/-- **Theorem Q9.1 mirror** for a type-24 solid: hexagon edge leaf at `W02 = x 2 - x 0`. -/
theorem isRupert_hexQ91m_fac {x : Fin 7 → ℝ³} (_F : S0xFac 9 s0x_S24 x) (C : CornerCoords02 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths02 x)
    (hconv : HexConv02 x)
    (hhdn : NoHDNRim (K2 x) (W02 x)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_hexQ91m_of_coords x C hV0 hz hconv hhdn


#print axioms isRupert_hexQ91
#print axioms isRupert_hexQ91_of_coords
#print axioms isRupert_hexQ91_fac
#print axioms isRupert_hexQ91m
#print axioms isRupert_hexQ91m_of_coords
#print axioms isRupert_hexQ91m_fac


/-! ### Link chamber torque theorems (Zero HDN, Zero Conv) via Lemma EV-Tilt -/

open Minimality.EdgeTilt
open Minimality.RimCell

/-- Silhouette vertex sequence for rim `K6` at `W06`. -/
def c6 : ZMod 5 → Fin 7 := ![1, 6, 4, 3, 2]

/-- Up facets along rim `K6` at `W06`: facets 5 (126), 7 (236), 8 (346). -/
def U6 : Finset (Fin 9) := {5, 7, 8}

/-- Down facets along rim `K6` at `W06`: facets 0 (012), 1 (016), 2 (025), 3 (0345), 4 (046), 6 (235). -/
def D6 : Finset (Fin 9) := {0, 1, 2, 3, 4, 6}

theorem inj_c6 : Function.Injective c6 := by decide
theorem cyc_c6 : S0xCycUD s0x_S24 c6 U6 D6 := by decide

/-- Silhouette vertex sequence for mirror rim `K2` at `W02`. -/
def c2 : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]

/-- **Theorem Q9.1 (Link Chamber / Zero HDN)**: hexagon edge leaf at `W06 = x 6 - x 0`.
Applies `isRupert_edgeView_link_torque` in the link chamber of edge `0 -> 6` hiding `x 0`
(facets 016, 046). Requires NO `NoHDNRim` and NO `HexConv06` hypothesis! -/
theorem isRupert_hexQ91_link {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h5 : ⟪F.N 6, x 6 - x 0⟫ < 0)
    (hpp : ParPairAt (K6 x) (W06 x) 3 0)
    (hz : DepthSepZ (fun i => ⟪K6 x i, W06 x⟫) 3 0) :
    IsRupert (Finset.univ.image x) := by
  have up6 : ∀ t, (6 : Fin 7) ∈ s0x_S24 t → (0 : Fin 7) ∉ s0x_S24 t →
      0 < ⟪F.N t, x 6 - x 0⟫ := fun t h6 h0 => by
    rw [F.inner_sub, F.zero t 6 h6]; have := F.neg t 0 h0; linarith
  have dn0 : ∀ t, (0 : Fin 7) ∈ s0x_S24 t → (6 : Fin 7) ∉ s0x_S24 t →
      ⟪F.N t, x 6 - x 0⟫ < 0 := fun t h0 h6 => by
    rw [F.inner_sub, F.zero t 0 h0]; have := F.neg t 6 h6; linarith
  have hx : Function.Injective x := EdgeViewLink.inj_of_fac24 F
  have hK : (fun i => x (c6 i)) = K6 x := by funext i; fin_cases i <;> rfl
  have hpp' : ParPairAt (fun i => x (c6 i)) (x 6 - x 0) 3 0 := by rwa [hK]
  have hz' : DepthSepZ (fun i => ⟪x (c6 i), x 6 - x 0⟫) 3 0 := by
    have : (fun i => ⟪x (c6 i), x 6 - x 0⟫) = (fun i => ⟪K6 x i, W06 x⟫) := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact hz
  refine isRupert_edgeView_link_torque F hx (by norm_num) inj_c6 cyc_c6
    (F₁ := 1) (F₂ := 4) (p := 0) (J := 6) (v₁ := 4) (v₂ := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun t ht => ?_) (fun t ht h1 h4 => ?_) hpp' hz'
  · simp only [U6, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact up6 5 (by decide) (by decide)
    · exact up6 7 (by decide) (by decide)
    · exact up6 8 (by decide) (by decide)
  · simp only [D6, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact dn0 0 (by decide) (by decide)
    · exact absurd rfl h1
    · exact dn0 2 (by decide) (by decide)
    · exact dn0 3 (by decide) (by decide)
    · exact absurd rfl h4
    · exact h5

/-- **Theorem Q9.1 (Link Chamber / Zero HDN)** from corner coordinates: hexagon edge leaf at `W06 = x 6 - x 0`. -/
theorem isRupert_hexQ91_link_of_coords {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (C : CornerCoords06 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths06 x)
    (h5 : ⟪F.N 6, x 6 - x 0⟫ < 0) :
    IsRupert (Finset.univ.image x) := by
  have hds := depthSepAt_K6 x C hV0 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact isRupert_hexQ91_link F h5 hds.1 hds.2

/-- **Theorem Q9.1m (Link Chamber / Zero HDN)**: mirror hexagon edge leaf at `W02 = x 2 - x 0`.
Applies `isRupert_edgeView_link_torque` under `(2 6)(4 5)` relabelling.
Requires NO `NoHDNRim` and NO `HexConv02` hypothesis! -/
theorem isRupert_hexQ91m_link {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h8 : ⟪F.N 8, x 2 - x 0⟫ < 0)
    (hpp : ParPairAt (K2 x) (W02 x) 3 0)
    (hz : DepthSepZ (fun i => ⟪K2 x i, W02 x⟫) 3 0) :
    IsRupert (Finset.univ.image x) := by
  have himg : Finset.univ.image (x ∘ sg) = Finset.univ.image x := by
    rw [← Finset.image_image, show Finset.univ.image sg = Finset.univ from
      Finset.image_univ_of_surjective (Finite.surjective_of_injective sg_inj)]
  rw [← himg]
  have hK : K6 (x ∘ sg) = K2 x := by funext i; fin_cases i <;> rfl
  have hW : W06 (x ∘ sg) = W02 x := rfl
  have h8' : ⟪(relab F).N 6, (x ∘ sg) 6 - (x ∘ sg) 0⟫ < 0 := by
    show ⟪F.N 8, x 2 - x 0⟫ < 0
    exact h8
  have hpp' : ParPairAt (K6 (x ∘ sg)) (W06 (x ∘ sg)) 3 0 := by
    rw [hK, hW]; exact hpp
  have hz' : DepthSepZ (fun i => ⟪K6 (x ∘ sg) i, W06 (x ∘ sg)⟫) 3 0 := by
    have : (fun i => ⟪K6 (x ∘ sg) i, W06 (x ∘ sg)⟫) = (fun i => ⟪K2 x i, W02 x⟫) := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact hz
  exact isRupert_hexQ91_link (relab F) h8' hpp' hz'

/-- **Theorem Q9.1m (Link Chamber / Zero HDN)** from corner coordinates: mirror hexagon edge leaf at `W02 = x 2 - x 0`. -/
theorem isRupert_hexQ91m_link_of_coords {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (C : CornerCoords02 x)
    (hV0 : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hz : DepthSepDepths02 x)
    (h8 : ⟪F.N 8, x 2 - x 0⟫ < 0) :
    IsRupert (Finset.univ.image x) := by
  have hds := depthSepAt_K2 x C hV0 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  exact isRupert_hexQ91m_link F h8 hds.1 hds.2

#print axioms isRupert_hexQ91_link
#print axioms isRupert_hexQ91_link_of_coords
#print axioms isRupert_hexQ91m_link
#print axioms isRupert_hexQ91m_link_of_coords

end Minimality.HexEdge06
