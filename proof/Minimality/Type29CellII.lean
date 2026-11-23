module

public import Minimality.Type29SubPencil
public import Minimality.Type29Quad2
public import Minimality.Type29HoleReduce

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`: Refereed Pieces (`A38-REFEREE`, `A39-REFEREE`, `A40-REFEREE`)

Formalizes the refereed pieces of Cell II (`A35 < 0 < B35` inside `NF29 ∩ K1a ∩ G*`):
1. **Region lemmas** (`ring` / `nlinarith` / `positivity`): `C35_pos`, `KW_neg` (`A39 L1`),
   `Pol_pos` (`A40 L1`), `c1_pos` (`A40 L2`), `v4_neg_of_KY_nonneg` (`A40 L3`),
   `w4_pos`, `w5_pos` (`A40 L4`), `phi346_u1523_gt_one` (`A40 L5`).
2. **Certificates as `False`-lemmas** (`linear_combination`): `cert_WI_Q8_false` (`A38 R1`),
   `cert_WI_Q7_false` (`A38 R2`), `cert_WIII_1523_false` (`A40 L7`, corrected `S^2 * Pol`
   coefficient), `cert_QII_FA_sub_false` (`A40 L8`), and `cert_WI_CaseA_*_false` (`A40 L9`).
3. **`F015xF124_closes` (`A40 L6`)**: metric-free `LexAny29` closure at `-N.u015_124 x` (`= u_{15,24}`)
   on the coplanar rim `![1, 4, 6, 5]` for `{W-III, 346+ at u_{15,23}, b2 + h2 * t > 0}`.
4. **`M_cone` (`A39 L2`) & `order_WI_cones` (`A39 L4`)**: `M+` and `0 ≤ (z3 - z4)(u35)` from the
   `u35` Radon circuit + PD metric, and the 120-order `F234xF346` cone lemma by `decide`.

## Carbon ↔ Lean `NF29` naming dictionary
* Carbon `D0` = `N.D02 = a0 * b2 - a2 * b0`
* Carbon `P4` = `N.P5 = P4C_sp b0 h0 b2 h2 = b0 * h2 - b2 * h0`
* Carbon `P5` = `N.P4 = P5C_sp a0 h0 a2 h2 = a2 * h0 - a0 * h2`
* Carbon `G4` = `N.dG4 = b0 * (1 - h2) - b2 * (1 - h0)`
* Carbon `G5` = `N.dG = a2 * (1 - h0) - a0 * (1 - h2)`
* Carbon `DG4, DG5, D023, V` = `N.DG4, N.DG5, N.D023, N.V`
* Carbon `del0, del2` = `N.del0, N.del2` (`1 - a0 - b0 - h0`, `1 - a2 - b2 - h2`)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

section CellIIScalars

variable {R : Type*} [CommRing R]
variable (a0 b0 h0 a2 b2 h2 s t : R)

def A35_sp : R := DG4_sp a0 b0 h0 a2 b2 h2 - (1 - a2 - b2 - h2)
def B35_sp : R := (1 - a0 - b0 - h0) - DG5_sp a0 b0 h0 a2 b2 h2
def C35_sp : R := DG4_sp a0 b0 h0 a2 b2 h2 - (1 - h0) * (1 - a2 - b2 - h2)
def L_sp : R := DG4_sp a0 b0 h0 a2 b2 h2 + (h2 - 1) * (1 - a2 - b2 - h2)
def KY_sp : R := C35_sp a0 b0 h0 a2 b2 h2 * P2_sp a2 b2 h2 s t -
  L_sp a0 b0 h0 a2 b2 h2 * D035_sp a0 b0 h0 s t
def KW_sp : R := C35_sp a0 b0 h0 a2 b2 h2 * (D234_sp a2 b2 h2 s t - P0_sp a0 b0 h0 s t) -
  (h2 - h0) * (1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t
def Pol_sp : R := a0 * b0 * h2 * (h2 - 1) - a0 * b2 * h0 * h2 + a0 * b2 * h0 + a0 * b2 * h2 -
  a2 * b0 * h0 * h2 + a2 * b2 * h0 ^ 2 - a2 * b2 * h0
def detAB_sp : R := (P2_sp a2 b2 h2 s t - s) * (s * DG5_sp a0 b0 h0 a2 b2 h2 -
  G5_sp a0 h0 a2 h2 * D035_sp a0 b0 h0 s t) -- placeholder? No, let's check B4, B5!
def B4_sp : R := s * DG5_sp a0 b0 h0 a2 b2 h2 - G5_sp a0 h0 a2 h2 * D035_sp a0 b0 h0 s t
def B5_sp : R := -a0 * D234_sp a2 b2 h2 s t + (P5C_sp a0 h0 a2 h2 + a0) * P0_sp a0 b0 h0 s t
def detBC_sp : R := B4_sp a0 b0 h0 a2 b2 h2 s t * t - B5_sp a0 b0 h0 a2 b2 h2 s t * (1 - t)
def v012_4_sp : R := (1 - t) * P5C_sp a0 h0 a2 h2 - s * P4C_sp b0 h0 b2 h2
def v012_5_sp : R := t * P5C_sp a0 h0 a2 h2 + (s - 1) * P4C_sp b0 h0 b2 h2
def w4_sp : R := s * (h2 - P4C_sp b0 h0 b2 h2) + (1 - t) * P5C_sp a0 h0 a2 h2
def w5_sp : R := t * (h2 + P5C_sp a0 h0 a2 h2) + (s - 1) * P4C_sp b0 h0 b2 h2
def w21s_sp : R := t * (P2_sp a2 b2 h2 s t - s) + (1 - t) * (D234_sp a2 b2 h2 s t - t) +
  S_sp s t * h2 * t
def w23s_sp : R := (P2_sp a2 b2 h2 s t + S_sp s t * (h2 - 1)) * t +
  D234_sp a2 b2 h2 s t * (1 - t)
def KA012_sp : R := (s - P2_sp a2 b2 h2 s t) * v012_5_sp a0 b0 h0 a2 b2 h2 s t +
  (t - D234_sp a2 b2 h2 s t) * (-v012_4_sp a0 b0 h0 a2 b2 h2 s t)

end CellIIScalars

/-! ## 1. Region Lemmas (`A39 L1`, `A40 L1-L5`) -/

section RegionLemmas

variable {x : Fin 7 → ℝ³} (N : NF29 x)

theorem S_pos_of_NF29 : 0 < S_sp N.s N.t := by
  dsimp only [S_sp]; linarith [N.hst]

theorem del0_pos_of_NF29 : 0 < N.del0 := by
  dsimp only [NF29.del0]; linarith [N.t345_0]

theorem del2_pos_of_NF29 : 0 < N.del2 := by
  dsimp only [NF29.del2]; linarith [N.t345_2]

theorem D02_pos_of_NF29 : 0 < N.D02 := by
  dsimp only [NF29.D02]; exact N.hDD

theorem P4_pos_of_NF29 : 0 < N.P4 := by
  dsimp only [NF29.P4]; linarith [N.hF5]

theorem P5_pos_of_NF29 : 0 < N.P5 := by
  dsimp only [NF29.P5]; linarith [N.hF4]

theorem dG_neg_of_Gstar (ha2 : N.a2 < 0) (hh0 : N.h0 < 1) (hh2 : 1 < N.h2) : N.dG < 0 := by
  dsimp only [NF29.dG]
  nlinarith [N.ha0]

/-- `C35 > 0` on `G*` (`DG5 > 0`, `1 < h2`, `del0 > 0`). -/
theorem C35_pos (hh2 : 1 < N.h2) :
    0 < C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
  have hid : C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 =
      DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 + (N.h2 - 1) * (1 - N.a0 - N.b0 - N.h0) := by
    dsimp only [C35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]; ring
  rw [hid]
  have hDG5 : 0 < DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    dsimp only [DG5_sp, D0_sp, G5_sp]; linarith [N.hDG5]
  have hdel0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  nlinarith

/-- **`A39 L1` (`KW_neg`)**: on `NF29 ∩ K1a ∩ G* ∩ Cell II`, `C35 > 0`,
`DG4 * del0 - DG5 * del2 > 0`, and `K_W < 0`. -/
theorem KW_neg (hh0 : N.h0 < 1) (hh2 : 1 < N.h2) (hV : N.V < 0)
    (hA35 : A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 < 0) :
    0 < C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 ∧
    0 < DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
        DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2) ∧
    KW_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t < 0 := by
  have hC35 := C35_pos N hh2
  have hS := S_pos_of_NF29 N
  have hdel0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hdel2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hDG4 : 0 < DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    dsimp only [DG4_sp, D0_sp, G4_sp]; linarith [N.hDG4]
  have hDG5 : 0 < DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    dsimp only [DG5_sp, D0_sp, G5_sp]; linarith [N.hDG5]
  have hD234 : 0 < D234_sp N.a2 N.b2 N.h2 N.s N.t := by
    dsimp only [D234_sp]; linarith [N.d234]
  have hV_eq : -N.V = N.h2 * (1 - N.a0 - N.b0 - N.h0) - N.h0 * (1 - N.a2 - N.b2 - N.h2) := by
    dsimp only [NF29.V]; ring
  have hX1 : DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
      DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2) =
      (-N.V) * (1 - N.a2 - N.b2 - N.h2) +
      (-A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) *
        ((1 - N.a2 - N.b2 - N.h2) - (1 - N.a0 - N.b0 - N.h0)) := by
    rw [hV_eq]; dsimp only [A35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]; ring
  have hX2 : DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
      DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2) =
      (1 - N.h0) * (1 - N.a0 - N.b0 - N.h0) * (1 - N.a2 - N.b2 - N.h2) +
      (N.h2 - 1) * (1 - N.a0 - N.b0 - N.h0) ^ 2 +
      DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
        ((1 - N.a0 - N.b0 - N.h0) - (1 - N.a2 - N.b2 - N.h2)) := by
    dsimp only [DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]; ring
  have hX : 0 < DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
      DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2) := by
    rcases le_total (1 - N.a0 - N.b0 - N.h0) (1 - N.a2 - N.b2 - N.h2) with hle | hle
    · rw [hX1]
      exact add_pos_of_pos_of_nonneg (mul_pos (neg_pos.mpr hV) hdel2)
        (mul_nonneg (neg_pos.mpr hA35).le (sub_nonneg.mpr hle))
    · rw [hX2]
      exact add_pos_of_pos_of_nonneg
        (add_pos (mul_pos (mul_pos (sub_pos.mpr hh0) hdel0) hdel2)
          (mul_pos (sub_pos.mpr hh2) (sq_pos_of_pos hdel0)))
        (mul_nonneg hDG5.le (sub_nonneg.mpr hle))
  have hKW_id : (1 - N.a2 - N.b2 - N.h2) * KW_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
      -S_sp N.s N.t * DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
        C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 -
      (DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
        DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2)) *
        D234_sp N.a2 N.b2 N.h2 N.s N.t := by
    dsimp only [KW_sp, C35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, D234_sp, P0_sp, S_sp]; ring
  have hdel2KW : (1 - N.a2 - N.b2 - N.h2) * KW_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t < 0 := by
    rw [hKW_id]
    have ht1 : 0 < S_sp N.s N.t * DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
        C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := mul_pos (mul_pos hS hDG4) hC35
    have ht2 : 0 < (DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a0 - N.b0 - N.h0) -
        DG5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.a2 - N.b2 - N.h2)) *
        D234_sp N.a2 N.b2 N.h2 N.s N.t := mul_pos hX hD234
    linarith
  exact ⟨hC35, hX, neg_of_mul_neg_right hdel2KW hdel2.le⟩

/-- **`A40 L1` (`Pol_pos`)**: `Pol = h0 * D0 + P5_C * G4 > 0` on `NF29 ∩ G*`. -/
theorem Pol_pos (hdG4 : 0 < N.dG4) :
    Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 =
      N.h0 * N.D02 + N.P4 * N.dG4 ∧
    0 < Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
  have hid : Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 = N.h0 * N.D02 + N.P4 * N.dG4 := by
    dsimp only [Pol_sp, NF29.D02, NF29.P4, NF29.dG4]; ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have hD0 := D02_pos_of_NF29 N
  have hP4 := P4_pos_of_NF29 N
  nlinarith [N.hh0]

/-- **`A40 L2` (`c1_pos`)**: `det(B, C) > S * DG5 > 0` on `NF29 ∩ K1a ∩ G*`. -/
theorem c1_pos (ha2 : N.a2 < 0) (hh0 : N.h0 < 1) (hh2 : 1 < N.h2) (ht : N.t < 1)
    (h1bh : 0 < 1 - N.b0 - N.h0) :
    detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
      S_sp N.s N.t * (N.DG5 + (1 - N.b0 - N.h0 * N.t) * (-N.dG)) ∧
    N.dG = N.a2 * (1 - N.h0) + N.a0 * (N.h2 - 1) ∧
    S_sp N.s N.t * N.DG5 < detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
    0 < detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
  have h1 : detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
      S_sp N.s N.t * (N.DG5 + (1 - N.b0 - N.h0 * N.t) * (-N.dG)) := by
    dsimp only [detBC_sp, B4_sp, B5_sp, DG5_sp, D0_sp, G5_sp, D035_sp, D234_sp, P0_sp, P5C_sp,
      S_sp, NF29.DG5, NF29.D02, NF29.dG]
    ring
  have h2 : N.dG = N.a2 * (1 - N.h0) + N.a0 * (N.h2 - 1) := by
    dsimp only [NF29.dG]; ring
  have hdG : N.dG < 0 := dG_neg_of_Gstar N ha2 hh0 hh2
  have hS := S_pos_of_NF29 N
  have hDG5 : 0 < N.DG5 := by dsimp only [NF29.DG5, NF29.D02, NF29.dG]; linarith [N.hDG5]
  have h1bht : 0 < 1 - N.b0 - N.h0 * N.t := by
    have : 0 < N.h0 * (1 - N.t) := mul_pos N.hh0 (sub_pos.mpr ht)
    linarith
  have h3 : S_sp N.s N.t * N.DG5 < detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
    rw [h1]
    nlinarith [mul_pos h1bht (neg_pos.mpr hdG)]
  have h4 : 0 < detBC_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
    nlinarith [mul_pos hS hDG5]
  exact ⟨h1, h2, h3, h4⟩

/-- **`A40 L3` (`v4_neg_of_KY_nonneg`)**: `K_Y ≥ 0 → v_{012,4} < 0` on `K1a ∩ G* ∩ Cell II`. -/
theorem v4_neg_of_KY_nonneg (hb0 : 0 < N.b0) (_hh0 : N.h0 < 1) (hh2 : 1 < N.h2)
    (ht : N.t < 1) (h1bh : 0 < 1 - N.b0 - N.h0)
    (hA35 : A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 < 0)
    (hKY : 0 ≤ KY_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) :
    v012_4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t < 0 := by
  have hC35 := C35_pos N hh2
  have hdel2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hL : 0 < L_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
    have hidL : L_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 =
        DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 + (N.h2 - 1) * (1 - N.a2 - N.b2 - N.h2) := by
      dsimp only [L_sp]
    rw [hidL]
    have hDG4 : 0 < DG4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := by
      dsimp only [DG4_sp, D0_sp, G4_sp]; linarith [N.hDG4]
    exact add_pos hDG4 (mul_pos (sub_pos.mpr hh2) hdel2)
  have hid : C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
        (-v012_4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) =
      N.h0 * KY_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t +
      N.s * C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (N.b0 * N.h2 + N.h0 * (N.h2 - 1)) +
      N.s * N.h0 * L_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.b0 - N.h0) +
      (1 - N.t) * (-N.a0) * (N.h2 - N.h0) * (-A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) := by
    dsimp only [C35_sp, v012_4_sp, KY_sp, L_sp, A35_sp, DG4_sp, D0_sp, G4_sp, P2_sp,
      D035_sp, P4C_sp, P5C_sp]
    ring
  have h1 : 0 < N.s * C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
      (N.b0 * N.h2 + N.h0 * (N.h2 - 1)) := by
    have hb0h2 : 0 < N.b0 * N.h2 + N.h0 * (N.h2 - 1) :=
      add_pos (mul_pos hb0 N.hh2) (mul_pos N.hh0 (sub_pos.mpr hh2))
    exact mul_pos (mul_pos N.hs hC35) hb0h2
  have h2 : 0 < N.s * N.h0 * L_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.b0 - N.h0) :=
    mul_pos (mul_pos (mul_pos N.hs N.hh0) hL) h1bh
  have h3 : 0 < (1 - N.t) * (-N.a0) * (N.h2 - N.h0) *
      (-A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) := by
    have hh20 : 0 < N.h2 - N.h0 := by linarith
    exact mul_pos (mul_pos (mul_pos (sub_pos.mpr ht) (neg_pos.mpr N.ha0)) hh20) (neg_pos.mpr hA35)
  have h4 : 0 ≤ N.h0 * KY_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t :=
    mul_nonneg N.hh0.le hKY
  have hpos : 0 < C35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 *
      (-v012_4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) := by
    rw [hid]; linarith
  have hneg : 0 < -v012_4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t :=
    pos_of_mul_pos_right hpos hC35.le
  linarith

/-- **`A40 L4` (`w4_pos`, `w5_pos`)**: `0 < w4` and `0 < w5` on `K1a ∩ G* ∩ Cell II`. -/
theorem w4_w5_pos (_hb0 : 0 < N.b0) (_hh0 : N.h0 < 1) (hh2 : 1 < N.h2) (ht : N.t < 1)
    (h1bh : 0 < 1 - N.b0 - N.h0) (hV : N.V < 0)
    (hA35 : A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 < 0) :
    0 < w4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ∧
    0 < w5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
  have hdel0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hP4C : 0 < P4C_sp N.b0 N.h0 N.b2 N.h2 := by dsimp only [P4C_sp]; linarith [N.hF4]
  have hP5C : 0 < P5C_sp N.a0 N.h0 N.a2 N.h2 := by dsimp only [P5C_sp]; linarith [N.hF5]
  have hid : (1 - N.a0 - N.b0 - N.h0) * (N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2) =
      (1 - N.b0) * (-N.V) + N.h0 * (-A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) := by
    dsimp only [P4C_sp, NF29.V, A35_sp, DG4_sp, D0_sp, G4_sp]; ring
  have h1b0 : 0 < 1 - N.b0 := by linarith [N.hh0]
  have h_h2P4 : 0 < N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2 := by
    have : 0 < (1 - N.a0 - N.b0 - N.h0) * (N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2) := by
      rw [hid]; nlinarith [N.hh0]
    exact pos_of_mul_pos_right this hdel0.le
  have hw4 : 0 < w4_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
    dsimp only [w4_sp]; nlinarith [N.hs]
  have hw5 : 0 < w5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t := by
    rcases le_total 1 N.s with hs1 | hs1
    · dsimp only [w5_sp]; nlinarith [N.ht, N.hh2]
    · have hid5 : w5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
          N.t * N.h2 + (N.t * P5C_sp N.a0 N.h0 N.a2 N.h2 + (N.s - 1) * P4C_sp N.b0 N.h0 N.b2 N.h2) := by
        dsimp only [w5_sp]; ring
      have hv5_lb : (1 - N.s) * P4C_sp N.b0 N.h0 N.b2 N.h2 < N.t * N.h2 := by
        have h1s : 0 ≤ 1 - N.s := sub_nonneg.mpr hs1
        have hst' : 1 - N.s < N.t := by linarith [N.hst]
        nlinarith [mul_lt_mul_of_pos_right hst' hP4C, mul_lt_mul_of_pos_left h_h2P4 N.ht]
      dsimp only [w5_sp] at *; nlinarith [N.ht]
  exact ⟨hw4, hw5⟩

/-- **`A40 L5` (`phi346_u1523_gt_one`)**: `a0 + h0 < 0` and `B5 ≤ 0` (`phi_346(u_{15,23}) ≥ 0`)
forces `1 < s` (and `a0 + h0 ≤ 0`, `B5 < 0` also forces `1 < s`). -/
theorem phi346_u1523_gt_one (ha2 : N.a2 < 0) (hh0 : N.h0 < 1) (hh2 : 1 < N.h2)
    (ht : N.t < 1) (h1bh : 0 < 1 - N.b0 - N.h0) :
    (N.D02 + N.b0 * N.dG) * (N.s * N.h0 + N.a0) + N.h0 * B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
      (N.a0 + N.h0) * (N.D02 + (N.b0 + N.h0 * N.t) * N.dG) ∧
    (N.a0 + N.h0 < 0 → B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0 → 1 < N.s) ∧
    (N.a0 + N.h0 ≤ 0 → B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t < 0 → 1 < N.s) := by
  have hid : (N.D02 + N.b0 * N.dG) * (N.s * N.h0 + N.a0) +
        N.h0 * B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
      (N.a0 + N.h0) * (N.D02 + (N.b0 + N.h0 * N.t) * N.dG) := by
    dsimp only [B5_sp, D234_sp, P5C_sp, P0_sp, NF29.D02, NF29.dG]; ring
  have hdG := dG_neg_of_Gstar N ha2 hh0 hh2
  have hDG5 : 0 < N.DG5 := by dsimp only [NF29.DG5, NF29.D02, NF29.dG]; linarith [N.hDG5]
  have h1bht : 0 < 1 - N.b0 - N.h0 * N.t := by
    have : 0 < N.h0 * (1 - N.t) := mul_pos N.hh0 (sub_pos.mpr ht)
    linarith
  have hc1_fac : 0 < N.D02 + (N.b0 + N.h0 * N.t) * N.dG := by
    have : N.D02 + (N.b0 + N.h0 * N.t) * N.dG = N.DG5 + (1 - N.b0 - N.h0 * N.t) * (-N.dG) := by
      dsimp only [NF29.DG5, NF29.D02, NF29.dG]; ring
    rw [this]; nlinarith
  have hD0b0 : 0 < N.D02 + N.b0 * N.dG := by
    have : 0 < N.h0 * N.t * (-N.dG) := mul_pos (mul_pos N.hh0 N.ht) (neg_pos.mpr hdG)
    linarith
  refine ⟨hid, ?_, ?_⟩
  · intro hah hB5
    by_contra hs
    push Not at hs
    have h1 : N.s * N.h0 + N.a0 ≤ N.a0 + N.h0 := by nlinarith [N.hh0]
    have h2 : (N.D02 + N.b0 * N.dG) * (N.s * N.h0 + N.a0) ≤
        (N.D02 + N.b0 * N.dG) * (N.a0 + N.h0) := mul_le_mul_of_nonneg_left h1 hD0b0.le
    have h3 : (N.D02 + N.b0 * N.dG) * (N.a0 + N.h0) <
        (N.D02 + (N.b0 + N.h0 * N.t) * N.dG) * (N.a0 + N.h0) := by
      have hlt : N.D02 + (N.b0 + N.h0 * N.t) * N.dG < N.D02 + N.b0 * N.dG := by
        have : 0 < N.h0 * N.t * (-N.dG) := mul_pos (mul_pos N.hh0 N.ht) (neg_pos.mpr hdG)
        linarith
      exact mul_lt_mul_of_neg_right hlt hah
    have h4 : N.h0 * B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos N.hh0.le hB5
    linarith [hid]
  · intro hah hB5
    by_contra hs
    push Not at hs
    have h1 : N.s * N.h0 + N.a0 ≤ N.a0 + N.h0 := by nlinarith [N.hh0]
    have h2 : (N.D02 + N.b0 * N.dG) * (N.s * N.h0 + N.a0) ≤
        (N.D02 + N.b0 * N.dG) * (N.a0 + N.h0) := mul_le_mul_of_nonneg_left h1 hD0b0.le
    have h3 : (N.D02 + N.b0 * N.dG) * (N.a0 + N.h0) ≤
        (N.D02 + (N.b0 + N.h0 * N.t) * N.dG) * (N.a0 + N.h0) := by
      have hlt : N.D02 + (N.b0 + N.h0 * N.t) * N.dG ≤ N.D02 + N.b0 * N.dG := by
        have : 0 ≤ N.h0 * N.t * (-N.dG) := mul_nonneg (mul_nonneg N.hh0.le N.ht.le) (neg_pos.mpr hdG).le
        linarith
      exact mul_le_mul_of_nonpos_right hlt hah
    have h4 : N.h0 * B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t < 0 :=
      mul_neg_of_pos_of_neg N.hh0 hB5
    linarith [hid]

end RegionLemmas

/-! ## 2. Certificates as `False`-Lemmas (`A38 R1/R2`, `A40 L7-L9`) -/

section CertFalse

/-- Symmetric 3×3 Gram quadratic form in `(e3, e4, e5)`. -/
def gramQ (G33 G44 G55 g34 g35 g45 x y z : ℝ) : ℝ :=
  G33 * x ^ 2 + G44 * y ^ 2 + G55 * z ^ 2 + 2 * g34 * x * y + 2 * g35 * x * z + 2 * g45 * y * z

/-- Symmetric 3×3 Gram bilinear form in `(e3, e4, e5)`. -/
def gramB (G33 G44 G55 g34 g35 g45 x1 y1 z1 x2 y2 z2 : ℝ) : ℝ :=
  G33 * x1 * x2 + G44 * y1 * y2 + G55 * z1 * z2 +
    g34 * (x1 * y2 + y1 * x2) + g35 * (x1 * z2 + z1 * x2) + g45 * (y1 * z2 + z1 * y2)

/-- `S • (dx • (x4 - x1) + dy • (x5 - x1) + dz • (x3 - x1))` in `(e3, e4, e5)` coordinates. -/
def vecE3 (s t _dx _dy dz : ℝ) : ℝ := S_sp s t * dz
def vecE4 (s t dx dy dz : ℝ) : ℝ := S_sp s t * dx - s * (dx + dy + dz)
def vecE5 (s t dx dy dz : ℝ) : ℝ := S_sp s t * dy - t * (dx + dy + dz)

/-- **`A38 R1` (`Cert-WI-Q8`)**: kills `Q_8` and `C_{WI,4}` for every PD metric (no OB6, no SUB). -/
theorem cert_WI_Q8_false (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hS : 0 < S_sp s t) (hdel0 : 0 < 1 - a0 - b0 - h0)
    (hDG4 : 0 < DG4_sp a0 b0 h0 a2 b2 h2) (hDG5 : 0 < DG5_sp a0 b0 h0 a2 b2 h2)
    (hmV : 0 < h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2))
    (hA35 : A35_sp a0 b0 h0 a2 b2 h2 < 0)
    (hPD : 0 < G33 + G44 - 2 * g34)
    (hM : 0 ≤ gramB G33 G44 G55 g34 g35 g45 1 (-1) 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (h20 : 0 ≤ gramB G33 G44 G55 g34 g35 g45
        (vecE3 s t (a2 - a0) (b2 - b0) (h2 - h0))
        (vecE4 s t (a2 - a0) (b2 - b0) (h2 - h0))
        (vecE5 s t (a2 - a0) (b2 - b0) (h2 - h0)) 1 (-1) 0)
    (h50 : 0 ≤ gramB G33 G44 G55 g34 g35 g45
        (vecE3 s t (-a0) (1 - b0) (-h0))
        (vecE4 s t (-a0) (1 - b0) (-h0))
        (vecE5 s t (-a0) (1 - b0) (-h0)) 1 (-1) 0) :
    False := by
  have m1_pos : 0 < (h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2)) + DG5_sp a0 b0 h0 a2 b2 h2 :=
    add_pos hmV hDG5
  have m2_pos : 0 < (1 - a0 - b0 - h0) * (-A35_sp a0 b0 h0 a2 b2 h2) :=
    mul_pos hdel0 (neg_pos.mpr hA35)
  have m3_pos : 0 < (1 - a0 - b0 - h0) * DG4_sp a0 b0 h0 a2 b2 h2 :=
    mul_pos hdel0 hDG4
  have hid :
      ((h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2)) + DG5_sp a0 b0 h0 a2 b2 h2) *
          gramB G33 G44 G55 g34 g35 g45 1 (-1) 0
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) +
        ((1 - a0 - b0 - h0) * (-A35_sp a0 b0 h0 a2 b2 h2)) *
          gramB G33 G44 G55 g34 g35 g45
            (vecE3 s t (a2 - a0) (b2 - b0) (h2 - h0))
            (vecE4 s t (a2 - a0) (b2 - b0) (h2 - h0))
            (vecE5 s t (a2 - a0) (b2 - b0) (h2 - h0)) 1 (-1) 0 +
        ((1 - a0 - b0 - h0) * DG4_sp a0 b0 h0 a2 b2 h2) *
          gramB G33 G44 G55 g34 g35 g45
            (vecE3 s t (-a0) (1 - b0) (-h0))
            (vecE4 s t (-a0) (1 - b0) (-h0))
            (vecE5 s t (-a0) (1 - b0) (-h0)) 1 (-1) 0 =
      -S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 *
        (G33 + G44 - 2 * g34) := by
    have hx :
        ((h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2)) + DG5_sp a0 b0 h0 a2 b2 h2) *
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) +
          ((1 - a0 - b0 - h0) * (-A35_sp a0 b0 h0 a2 b2 h2)) *
            vecE3 s t (a2 - a0) (b2 - b0) (h2 - h0) +
          ((1 - a0 - b0 - h0) * DG4_sp a0 b0 h0 a2 b2 h2) *
            vecE3 s t (-a0) (1 - b0) (-h0) =
        -S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 := by
      dsimp only [vecE3, S_sp, C35_sp, A35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp]; ring1
    have hy :
        ((h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2)) + DG5_sp a0 b0 h0 a2 b2 h2) *
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t) +
          ((1 - a0 - b0 - h0) * (-A35_sp a0 b0 h0 a2 b2 h2)) *
            vecE4 s t (a2 - a0) (b2 - b0) (h2 - h0) +
          ((1 - a0 - b0 - h0) * DG4_sp a0 b0 h0 a2 b2 h2) *
            vecE4 s t (-a0) (1 - b0) (-h0) =
        S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 := by
      dsimp only [vecE4, S_sp, C35_sp, A35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, D035_sp]; ring1
    have hz :
        ((h2 * (1 - a0 - b0) - h0 * (1 - a2 - b2)) + DG5_sp a0 b0 h0 a2 b2 h2) *
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) +
          ((1 - a0 - b0 - h0) * (-A35_sp a0 b0 h0 a2 b2 h2)) *
            vecE5 s t (a2 - a0) (b2 - b0) (h2 - h0) +
          ((1 - a0 - b0 - h0) * DG4_sp a0 b0 h0 a2 b2 h2) *
            vecE5 s t (-a0) (1 - b0) (-h0) = 0 := by
      dsimp only [vecE5, S_sp, C35_sp, A35_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, D234_sp]; ring1
    dsimp only [gramB]
    linear_combination (G33 - g34) * hx + (-G44 + g34) * hy + (g35 - g45) * hz
  have h_lhs : 0 ≤ -S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 *
      (G33 + G44 - 2 * g34) := by
    rw [← hid]
    exact add_nonneg (add_nonneg (mul_nonneg m1_pos.le hM) (mul_nonneg m2_pos.le h20))
      (mul_nonneg m3_pos.le h50)
  have h_rhs : -S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 *
      (G33 + G44 - 2 * g34) < 0 := by
    have hp : 0 < S_sp s t * (-A35_sp a0 b0 h0 a2 b2 h2) * DG5_sp a0 b0 h0 a2 b2 h2 *
        (G33 + G44 - 2 * g34) :=
      mul_pos (mul_pos (mul_pos hS (neg_pos.mpr hA35)) hDG5) hPD
    linarith
  linarith

/-- **`A38 R2` (`Cert-WI-Q7`)**: kills `Q_7` and `C_{WI,3}` under `K_Y < 0`, `K_W < 0`, `g34 ≤ 0`. -/
theorem cert_WI_Q7_false (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (_hS : 0 < S_sp s t) (hC35 : 0 < C35_sp a0 b0 h0 a2 b2 h2) (hh20 : 0 < h2 - h0)
    (hKW : KW_sp a0 b0 h0 a2 b2 h2 s t < 0) (hKY : KY_sp a0 b0 h0 a2 b2 h2 s t < 0)
    (hg34 : g34 ≤ 0) (hG44 : 0 < G44)
    (hM : 0 ≤ gramB G33 G44 G55 g34 g35 g45 1 (-1) 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (h02 : 0 ≤ gramB G33 G44 G55 g34 g35 g45
        (vecE3 s t (a0 - a2) (b0 - b2) (h0 - h2))
        (vecE4 s t (a0 - a2) (b0 - b2) (h0 - h2))
        (vecE5 s t (a0 - a2) (b0 - b2) (h0 - h2)) 1 (-1) 0)
    (h65 : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0 0 (-1) 1 (-1) 0) :
    False := by
  have n1_pos : 0 < C35_sp a0 b0 h0 a2 b2 h2 := hC35
  have n2_pos : 0 < h2 - h0 := hh20
  have n3_pos : 0 < -KW_sp a0 b0 h0 a2 b2 h2 s t := neg_pos.mpr hKW
  have hid :
      C35_sp a0 b0 h0 a2 b2 h2 *
          gramB G33 G44 G55 g34 g35 g45
            (vecE3 s t (a0 - a2) (b0 - b2) (h0 - h2))
            (vecE4 s t (a0 - a2) (b0 - b2) (h0 - h2))
            (vecE5 s t (a0 - a2) (b0 - b2) (h0 - h2)) 1 (-1) 0 +
        (h2 - h0) *
          gramB G33 G44 G55 g34 g35 g45 1 (-1) 0
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) +
        (-KW_sp a0 b0 h0 a2 b2 h2 s t) *
          gramB G33 G44 G55 g34 g35 g45 0 0 (-1) 1 (-1) 0 =
      KY_sp a0 b0 h0 a2 b2 h2 s t * (G44 - g34) := by
    have hx :
        C35_sp a0 b0 h0 a2 b2 h2 * vecE3 s t (a0 - a2) (b0 - b2) (h0 - h2) +
          (h2 - h0) * (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) +
          (-KW_sp a0 b0 h0 a2 b2 h2 s t) * 0 = 0 := by
      dsimp only [vecE3, S_sp]; ring1
    have hy :
        C35_sp a0 b0 h0 a2 b2 h2 * vecE4 s t (a0 - a2) (b0 - b2) (h0 - h2) +
          (h2 - h0) * ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t) +
          (-KW_sp a0 b0 h0 a2 b2 h2 s t) * 0 =
        -KY_sp a0 b0 h0 a2 b2 h2 s t := by
      dsimp only [vecE4, S_sp, C35_sp, KY_sp, L_sp, DG4_sp, D0_sp, G4_sp, D035_sp,
        P2_sp]; ring1
    have hz :
        C35_sp a0 b0 h0 a2 b2 h2 * vecE5 s t (a0 - a2) (b0 - b2) (h0 - h2) +
          (h2 - h0) * ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) +
          (-KW_sp a0 b0 h0 a2 b2 h2 s t) * (-1) = 0 := by
      dsimp only [vecE5, S_sp, C35_sp, KW_sp, DG4_sp, D0_sp, G4_sp, D234_sp, P0_sp]; ring1
    dsimp only [gramB]
    linear_combination (G33 - g34) * hx + (-G44 + g34) * hy + (g35 - g45) * hz
  have h_lhs : 0 ≤ KY_sp a0 b0 h0 a2 b2 h2 s t * (G44 - g34) := by
    rw [← hid]
    exact add_nonneg (add_nonneg (mul_nonneg n1_pos.le h02) (mul_nonneg n2_pos.le hM))
      (mul_nonneg n3_pos.le h65)
  have h_rhs : KY_sp a0 b0 h0 a2 b2 h2 s t * (G44 - g34) < 0 :=
    mul_neg_of_neg_of_pos hKY (by linarith)
  linarith

/-- **`A40 L7` (`Cert-WIII-1523`)**: with the corrected `S^2 * Pol` coefficient.
`W21' ≥ 0` comes from `W14`; `U14' ≥ 0` is the `(0,1,4,3)` rim at `u_{15,23}` (needs `346-`). -/
theorem cert_WIII_1523_false (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45
    W21p U14p : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hS : 0 < S_sp s t)
    (hc1 : 0 < detBC_sp a0 b0 h0 a2 b2 h2 s t)
    (hc2 : 0 ≤ S_sp s t * (b2 + h2 * t))
    (hc3 : 0 < (P2_sp a2 b2 h2 s t - s) * B5_sp a0 b0 h0 a2 b2 h2 s t -
        (D234_sp a2 b2 h2 s t - t) * B4_sp a0 b0 h0 a2 b2 h2 s t)
    (hPol : 0 < Pol_sp a0 b0 h0 a2 b2 h2)
    (hPD : 0 < gramQ G33 G44 G55 g34 g35 g45 0 (1 - t) t)
    (hg34 : g34 ≤ 0) (hg35 : g35 ≤ 0)
    (hW21 : W21p = gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t))
    (hU14 : U14p = gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * h0 * (-G5_sp a0 h0 a2 h2))
        (B4_sp a0 b0 h0 a2 b2 h2 s t)
        (B5_sp a0 b0 h0 a2 b2 h2 s t))
    (hW21_nn : 0 ≤ W21p) (hU14_nn : 0 ≤ U14p) :
    False := by
  let c1 := detBC_sp a0 b0 h0 a2 b2 h2 s t
  let c2 := S_sp s t * (b2 + h2 * t)
  let c3 := (P2_sp a2 b2 h2 s t - s) * B5_sp a0 b0 h0 a2 b2 h2 s t -
    (D234_sp a2 b2 h2 s t - t) * B4_sp a0 b0 h0 a2 b2 h2 s t
  have hid :
      c1 * W21p + c2 * U14p + c3 * gramQ G33 G44 G55 g34 g35 g45 0 (1 - t) t =
      S_sp s t ^ 2 * Pol_sp a0 b0 h0 a2 b2 h2 * ((1 - t) * g34 + t * g35) := by
    rw [hW21, hU14]
    dsimp only [c1, c2, c3, gramB, gramQ, detBC_sp, B4_sp, B5_sp, Pol_sp, P2_sp, D234_sp,
      D035_sp, P0_sp, P5C_sp, DG5_sp, D0_sp, G5_sp, S_sp]
    ring
  have h_lhs : 0 < S_sp s t ^ 2 * Pol_sp a0 b0 h0 a2 b2 h2 * ((1 - t) * g34 + t * g35) := by
    rw [← hid]
    have h1 : 0 ≤ c1 * W21p := mul_nonneg hc1.le hW21_nn
    have h2 : 0 ≤ c2 * U14p := mul_nonneg hc2 hU14_nn
    have h3 : 0 < c3 * gramQ G33 G44 G55 g34 g35 g45 0 (1 - t) t := mul_pos hc3 hPD
    linarith
  have h_rhs : S_sp s t ^ 2 * Pol_sp a0 b0 h0 a2 b2 h2 * ((1 - t) * g34 + t * g35) ≤ 0 := by
    have hS2 : 0 < S_sp s t ^ 2 := sq_pos_of_pos hS
    have hg : (1 - t) * g34 + t * g35 ≤ 0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hg34)
        (mul_nonpos_of_nonneg_of_nonpos ht0 hg35)
    exact mul_nonpos_of_nonneg_of_nonpos (mul_pos hS2 hPol).le hg
  linarith

/-- **`A40 L8` (`Cert-QII-FA-Sub`)**: closes `QII, P2 < s, b2 + h2 t ≤ 0` on `F-A`. -/
theorem cert_QII_FA_sub_false (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hS : 0 < S_sp s t) (hP4C : 0 < P4C_sp b0 h0 b2 h2) (hh2 : 0 < h2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hb2ht : b2 + h2 * t ≤ 0)
    (hP2s : P2_sp a2 b2 h2 s t < s) (hD234t : D234_sp a2 b2 h2 s t ≤ t)
    (hv4 : v012_4_sp a0 b0 h0 a2 b2 h2 s t < 0) (hv5 : 0 < v012_5_sp a0 b0 h0 a2 b2 h2 s t)
    (hPD : 0 < gramQ G33 G44 G55 g34 g35 g45 0 (P2_sp a2 b2 h2 s t - s)
        (D234_sp a2 b2 h2 s t - t))
    (hg34 : g34 ≤ 0) (hg35 : g35 ≤ 0)
    (hRFA : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0
        (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
      h2 * gramB G33 G44 G55 g34 g35 g45 0
        (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
        (-S_sp s t) 0 0)
    (hW21 : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t)) :
    False := by
  let K := KA012_sp a0 b0 h0 a2 b2 h2 s t
  have hK : 0 < K := by
    dsimp only [K, KA012_sp]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hP2s) hv5)
      (mul_nonneg (sub_nonneg.mpr hD234t) (neg_pos.mpr hv4).le)
  have hm : 0 ≤ S_sp s t * (-(b2 + h2 * t)) := mul_nonneg hS.le (neg_nonneg.mpr hb2ht)
  have hid :
      S_sp s t * (-(b2 + h2 * t)) *
          (gramB G33 G44 G55 g34 g35 g45 0
            (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
            (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
          h2 * gramB G33 G44 G55 g34 g35 g45 0
            (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
            (-S_sp s t) 0 0) +
        K * gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
          (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) =
      -S_sp s t * P4C_sp b0 h0 b2 h2 *
          gramQ G33 G44 G55 g34 g35 g45 0 (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
        K * S_sp s t * h2 * ((1 - t) * g34 + t * g35) := by
    dsimp only [K, KA012_sp, gramB, gramQ, v012_4_sp, v012_5_sp, P2_sp, D234_sp, P4C_sp, P5C_sp,
      S_sp]
    ring
  have h_lhs : 0 ≤ -S_sp s t * P4C_sp b0 h0 b2 h2 *
      gramQ G33 G44 G55 g34 g35 g45 0 (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
      K * S_sp s t * h2 * ((1 - t) * g34 + t * g35) := by
    rw [← hid]
    exact add_nonneg (mul_nonneg hm hRFA) (mul_nonneg hK.le hW21)
  have h_rhs : -S_sp s t * P4C_sp b0 h0 b2 h2 *
      gramQ G33 G44 G55 g34 g35 g45 0 (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
      K * S_sp s t * h2 * ((1 - t) * g34 + t * g35) < 0 := by
    have h1 : 0 < S_sp s t * P4C_sp b0 h0 b2 h2 *
        gramQ G33 G44 G55 g34 g35 g45 0 (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) :=
      mul_pos (mul_pos hS hP4C) hPD
    have h2 : K * S_sp s t * h2 * ((1 - t) * g34 + t * g35) ≤ 0 := by
      have : (1 - t) * g34 + t * g35 ≤ 0 :=
        add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hg34)
          (mul_nonpos_of_nonneg_of_nonpos ht0 hg35)
      exact mul_nonpos_of_nonneg_of_nonpos (mul_pos (mul_pos hK hS) hh2).le this
    linarith
  linarith

/-- **`A40 L9` (`Cert-F012-FA`)**: W-I Case A1 (`P2 ≥ s, D234 ≤ t`). -/
theorem cert_WI_CaseA_F012_FA_false (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hh2 : 0 < h2)
    (hP2s : s ≤ P2_sp a2 b2 h2 s t) (hD234t : D234_sp a2 b2 h2 s t ≤ t)
    (hneq : P2_sp a2 b2 h2 s t - s ≠ 0 ∨ D234_sp a2 b2 h2 s t - t ≠ 0)
    (hv4 : v012_4_sp a0 b0 h0 a2 b2 h2 s t < 0) (hv5 : 0 < v012_5_sp a0 b0 h0 a2 b2 h2 s t)
    (hG44 : 0 < G44) (hG55 : 0 < G55) (hg45 : g45 ≤ 0)
    (hFA21 : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0
        (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t))
    (hFA3 : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0
        (v012_4_sp a0 b0 h0 a2 b2 h2 s t) (v012_5_sp a0 b0 h0 a2 b2 h2 s t)
        (-S_sp s t) 0 0) :
    False := by
  let A4 := P2_sp a2 b2 h2 s t - s
  let A5 := D234_sp a2 b2 h2 s t - t
  let v4 := v012_4_sp a0 b0 h0 a2 b2 h2 s t
  let v5 := v012_5_sp a0 b0 h0 a2 b2 h2 s t
  have hid :
      gramB G33 G44 G55 g34 g35 g45 0 v4 v5 (S_sp s t * h2) A4 A5 +
        h2 * gramB G33 G44 G55 g34 g35 g45 0 v4 v5 (-S_sp s t) 0 0 =
      (A4 * v4) * G44 + (A5 * v5) * G55 + (A4 * v5 + A5 * v4) * g45 := by
    dsimp only [A4, A5, v4, v5, gramB]; ring
  have h_lhs : 0 ≤ (A4 * v4) * G44 + (A5 * v5) * G55 + (A4 * v5 + A5 * v4) * g45 := by
    rw [← hid]; exact add_nonneg hFA21 (mul_nonneg hh2.le hFA3)
  have h44 : A4 * v4 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hP2s) hv4.le
  have h55 : A5 * v5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hD234t) hv5.le
  have hne : A4 * v4 < 0 ∨ A5 * v5 < 0 := by
    rcases hneq with hA4 | hA5
    · left; exact mul_neg_of_pos_of_neg (lt_of_le_of_ne (sub_nonneg.mpr hP2s) (Ne.symm hA4)) hv4
    · right; exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (sub_nonpos.mpr hD234t) hA5) hv5
  have h45_pos : 0 ≤ A4 * v5 + A5 * v4 :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hP2s) hv5.le)
      (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hD234t) hv4.le)
  have h45g : (A4 * v5 + A5 * v4) * g45 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h45_pos hg45
  have h_neg : (A4 * v4) * G44 + (A5 * v5) * G55 < 0 := by
    rcases hne with hA4 | hA5
    · linarith [mul_neg_of_neg_of_pos hA4 hG44, mul_nonpos_of_nonpos_of_nonneg h55 hG55.le]
    · linarith [mul_nonpos_of_nonpos_of_nonneg h44 hG44.le, mul_neg_of_neg_of_pos hA5 hG55]
  linarith

/-- **`A40 L9` (`W21*`)**: W-I Case A2 (`P2 < s, D234 ≤ t, w21s ≥ 0`). -/
theorem cert_WI_CaseA_W21_false (a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hS : 0 < S_sp s t) (hh2 : 0 < h2) (ht0 : 0 < t) (ht1 : t < 1)
    (hP2s : P2_sp a2 b2 h2 s t < s) (hD234t : D234_sp a2 b2 h2 s t ≤ t)
    (hw21s : 0 ≤ w21s_sp a2 b2 h2 s t)
    (hG44 : 0 < G44) (hG55 : 0 < G55) (hg34 : g34 ≤ 0) (hg45 : g45 ≤ 0)
    (hW21 : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t))
    (hW34 : 0 ≤ -g35 + g45) :
    False := by
  have hid :
      gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
          (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
        (S_sp s t * h2 * t) * (-g35 + g45) =
      (P2_sp a2 b2 h2 s t - s) * (1 - t) * G44 + (D234_sp a2 b2 h2 s t - t) * t * G55 +
        S_sp s t * h2 * (1 - t) * g34 + w21s_sp a2 b2 h2 s t * g45 := by
    dsimp only [gramB, P2_sp, D234_sp, w21s_sp, S_sp]; ring
  have h_lhs : 0 ≤ (P2_sp a2 b2 h2 s t - s) * (1 - t) * G44 +
      (D234_sp a2 b2 h2 s t - t) * t * G55 + S_sp s t * h2 * (1 - t) * g34 +
      w21s_sp a2 b2 h2 s t * g45 := by
    rw [← hid]
    exact add_nonneg hW21 (mul_nonneg (mul_nonneg (mul_nonneg hS.le hh2.le) ht0.le) hW34)
  have h_neg : (P2_sp a2 b2 h2 s t - s) * (1 - t) * G44 < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hP2s) (sub_pos.mpr ht1)) hG44
  have h_nonpos1 : (D234_sp a2 b2 h2 s t - t) * t * G55 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hD234t) ht0.le) hG55.le
  have h_nonpos2 : S_sp s t * h2 * (1 - t) * g34 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hS.le hh2.le) (sub_pos.mpr ht1).le) hg34
  have h_nonpos3 : w21s_sp a2 b2 h2 s t * g45 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw21s hg45
  linarith

/-- **`A40 L9` (`W21* + W23*`)**: W-I Case A2 (`P2 < s, D234 ≤ t, w21s < 0, 2t ≥ 1`). -/
theorem cert_WI_CaseA_W23_false (a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (ha2 : a2 < 0) (hb2 : b2 < 0) (hs : 0 < s) (ht0 : 0 < t) (ht1 : t < 1) (hthalf : 1 ≤ 2 * t)
    (hS : 0 < S_sp s t) (hh2 : 1 < h2)
    (hw21s : w21s_sp a2 b2 h2 s t < 0) (hw23s : 0 < w23s_sp a2 b2 h2 s t)
    (hG44 : 0 < G44) (hG55 : 0 < G55) (hg34 : g34 ≤ 0)
    (hW21s : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
        (S_sp s t * h2 * t) * (-g35 + g45))
    (hW23s : 0 ≤ gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
        (S_sp s t * (h2 - 1)) (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) +
        (S_sp s t * (h2 - 1) * t) * (-g35 + g45)) :
    False := by
  let W21s := gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
    (S_sp s t * h2) (P2_sp a2 b2 h2 s t - s) (D234_sp a2 b2 h2 s t - t) +
    (S_sp s t * h2 * t) * (-g35 + g45)
  let W23s := gramB G33 G44 G55 g34 g35 g45 0 (1 - t) t
    (S_sp s t * (h2 - 1)) (P2_sp a2 b2 h2 s t) (D234_sp a2 b2 h2 s t) +
    (S_sp s t * (h2 - 1) * t) * (-g35 + g45)
  have hid :
      w23s_sp a2 b2 h2 s t * W21s + (-w21s_sp a2 b2 h2 s t) * W23s =
      S_sp s t * (1 - t) * (2 * a2 * t * (1 - t) + b2 * s * (2 * t - 1)) * G44 +
        S_sp s t * t ^ 2 * b2 * G55 +
        S_sp s t * (1 - t) * (w23s_sp a2 b2 h2 s t * h2 - w21s_sp a2 b2 h2 s t * (h2 - 1)) * g34 := by
    dsimp only [W21s, W23s, gramB, w21s_sp, w23s_sp, P2_sp, D234_sp, S_sp]; ring
  have h_lhs : 0 ≤ S_sp s t * (1 - t) * (2 * a2 * t * (1 - t) + b2 * s * (2 * t - 1)) * G44 +
      S_sp s t * t ^ 2 * b2 * G55 +
      S_sp s t * (1 - t) * (w23s_sp a2 b2 h2 s t * h2 - w21s_sp a2 b2 h2 s t * (h2 - 1)) * g34 := by
    rw [← hid]
    exact add_nonneg (add_nonneg (mul_nonneg hw23s.le hW21s) (mul_nonneg (neg_pos.mpr hw21s).le hW23s))
      (le_refl 0) |> fun _ => add_nonneg (mul_nonneg hw23s.le hW21s) (mul_nonneg (neg_pos.mpr hw21s).le hW23s)
  have hc44 : 2 * a2 * t * (1 - t) + b2 * s * (2 * t - 1) < 0 := by
    have h1 : 2 * a2 * t * (1 - t) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) ht0) (sub_pos.mpr ht1)
    have h2 : b2 * s * (2 * t - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_neg_of_pos hb2 hs).le (by linarith)
    linarith
  have hc55 : S_sp s t * t ^ 2 * b2 < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hS (sq_pos_of_pos ht0)) hb2
  have hg34_term : S_sp s t * (1 - t) *
      (w23s_sp a2 b2 h2 s t * h2 - w21s_sp a2 b2 h2 s t * (h2 - 1)) * g34 ≤ 0 := by
    have hp : 0 < w23s_sp a2 b2 h2 s t * h2 - w21s_sp a2 b2 h2 s t * (h2 - 1) := by
      have h1 := mul_pos hw23s (by linarith : 0 < h2)
      have h2 := mul_pos (neg_pos.mpr hw21s) (sub_pos.mpr hh2)
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hS.le (sub_pos.mpr ht1).le) hp.le) hg34
  have h_rhs : S_sp s t * (1 - t) * (2 * a2 * t * (1 - t) + b2 * s * (2 * t - 1)) * G44 +
      S_sp s t * t ^ 2 * b2 * G55 +
      S_sp s t * (1 - t) * (w23s_sp a2 b2 h2 s t * h2 - w21s_sp a2 b2 h2 s t * (h2 - 1)) * g34 < 0 := by
    have h1 : S_sp s t * (1 - t) * (2 * a2 * t * (1 - t) + b2 * s * (2 * t - 1)) * G44 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hS (sub_pos.mpr ht1)) hc44) hG44
    have h2 : S_sp s t * t ^ 2 * b2 * G55 < 0 := mul_neg_of_neg_of_pos hc55 hG55
    linarith
  linarith

end CertFalse

/-! ## 3. `F015xF124_closes` (`A40 L6`) -/

section F015xF124

variable {x : Fin 7 → ℝ³}

private def c_1465 : ZMod 4 → Fin 7 := ![1, 4, 6, 5]
private def U_015_124_copl : Finset (Fin 9) := {0, 1, 2, 3, 4, 6, 7, 8}
private def Dn_015_124_copl : Finset (Fin 9) := {5}

private theorem c_1465_inj : Function.Injective c_1465 := by decide
private theorem cyc_015_124_copl :
    S0xCycUD s0x_S29 c_1465 U_015_124_copl Dn_015_124_copl := by decide

private theorem coplanar_radon_1465 (N : NF29 x) :
    S_sp N.s N.t • x 1 + (1 : ℝ) • x 6 = N.s • x 4 + N.t • x 5 := by
  dsimp only [S_sp]; nf29_vec N

private theorem not_M_coplanar_1465 (N : NF29 x) {b d1 d2 : ℝ³}
    (_hb : det3 b d1 d2 ≠ 0) :
    ¬ (LexLt3 (⟪x 1, b⟫, ⟪x 1, d1⟫, ⟪x 1, d2⟫) (⟪x 4, b⟫, ⟪x 4, d1⟫, ⟪x 4, d2⟫) ∧
       LexLt3 (⟪x 1, b⟫, ⟪x 1, d1⟫, ⟪x 1, d2⟫) (⟪x 5, b⟫, ⟪x 5, d1⟫, ⟪x 5, d2⟫) ∧
       LexLt3 (⟪x 6, b⟫, ⟪x 6, d1⟫, ⟪x 6, d2⟫) (⟪x 4, b⟫, ⟪x 4, d1⟫, ⟪x 4, d2⟫) ∧
       LexLt3 (⟪x 6, b⟫, ⟪x 6, d1⟫, ⟪x 6, d2⟫) (⟪x 5, b⟫, ⟪x 5, d1⟫, ⟪x 5, d2⟫)) := by
  intro ⟨h14, h15, h64, h65⟩
  have hrad := coplanar_radon_1465 N
  have hS := S_pos_of_NF29 N
  have hs := N.hs
  have ht := N.ht
  have hS1 : S_sp N.s N.t + 1 = N.s + N.t := by dsimp only [S_sp]; ring
  have eq_of_le : ∀ v : ℝ³,
      ⟪x 1, v⟫ ≤ ⟪x 4, v⟫ → ⟪x 1, v⟫ ≤ ⟪x 5, v⟫ →
      ⟪x 6, v⟫ ≤ ⟪x 4, v⟫ → ⟪x 6, v⟫ ≤ ⟪x 5, v⟫ →
      ⟪x 1, v⟫ = ⟪x 4, v⟫ ∧ ⟪x 6, v⟫ = ⟪x 4, v⟫ ∧ ⟪x 5, v⟫ = ⟪x 4, v⟫ := by
    intro v l14 l15 l64 l65
    have hd : S_sp N.s N.t * ⟪x 1, v⟫ + ⟪x 6, v⟫ = N.s * ⟪x 4, v⟫ + N.t * ⟪x 5, v⟫ := by
      have := congrArg (fun w => ⟪w, v⟫) hrad
      simpa only [inner_add_left, real_inner_smul_left, one_mul] using this
    have h1 : S_sp N.s N.t * (⟪x 4, v⟫ - ⟪x 1, v⟫) + (⟪x 4, v⟫ - ⟪x 6, v⟫) +
        N.t * (⟪x 5, v⟫ - ⟪x 4, v⟫) = 0 := by linear_combination -hd + ⟪x 4, v⟫ * hS1
    have h2 : S_sp N.s N.t * (⟪x 5, v⟫ - ⟪x 1, v⟫) + (⟪x 5, v⟫ - ⟪x 6, v⟫) +
        N.s * (⟪x 4, v⟫ - ⟪x 5, v⟫) = 0 := by linear_combination -hd + ⟪x 5, v⟫ * hS1
    rcases le_total ⟪x 4, v⟫ ⟪x 5, v⟫ with h45 | h45
    · have ha : S_sp N.s N.t * (⟪x 4, v⟫ - ⟪x 1, v⟫) = 0 := by nlinarith
      have hb' : ⟪x 4, v⟫ - ⟪x 6, v⟫ = 0 := by nlinarith
      have hc : N.t * (⟪x 5, v⟫ - ⟪x 4, v⟫) = 0 := by nlinarith
      exact ⟨by linarith [(mul_eq_zero.mp ha).resolve_left hS.ne'],
        by linarith,
        by linarith [(mul_eq_zero.mp hc).resolve_left ht.ne']⟩
    · have ha : S_sp N.s N.t * (⟪x 5, v⟫ - ⟪x 1, v⟫) = 0 := by nlinarith
      have hb' : ⟪x 5, v⟫ - ⟪x 6, v⟫ = 0 := by nlinarith
      have hc : N.s * (⟪x 4, v⟫ - ⟪x 5, v⟫) = 0 := by nlinarith
      exact ⟨by linarith [(mul_eq_zero.mp ha).resolve_left hS.ne',
          (mul_eq_zero.mp hc).resolve_left hs.ne'],
        by linarith [(mul_eq_zero.mp hc).resolve_left hs.ne'],
        by linarith [(mul_eq_zero.mp hc).resolve_left hs.ne']⟩
  have le_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}, LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ ≤ b₁ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨h, _⟩ <;> linarith
  have le2_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ},
      LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ = b₁ → a₂ ≤ b₂ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h he; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨_, h | ⟨h, _⟩⟩ <;> linarith
  have lt3_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ},
      LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ = b₁ → a₂ = b₂ → a₃ < b₃ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h he1 he2; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨_, h | ⟨_, h⟩⟩ <;> linarith
  obtain ⟨eb1, eb6, eb5⟩ := eq_of_le b (le_of_lex h14) (le_of_lex h15) (le_of_lex h64) (le_of_lex h65)
  obtain ⟨ed1, ed6, ed5⟩ := eq_of_le d1
    (le2_of_lex h14 eb1) (le2_of_lex h15 (eb1.trans eb5.symm))
    (le2_of_lex h64 eb6) (le2_of_lex h65 (eb6.trans eb5.symm))
  have lf14 := lt3_of_lex h14 eb1 ed1
  have lf15 := lt3_of_lex h15 (eb1.trans eb5.symm) (ed1.trans ed5.symm)
  have lf64 := lt3_of_lex h64 eb6 ed6
  have lf65 := lt3_of_lex h65 (eb6.trans eb5.symm) (ed6.trans ed5.symm)
  have hd : S_sp N.s N.t * ⟪x 1, d2⟫ + ⟪x 6, d2⟫ = N.s * ⟪x 4, d2⟫ + N.t * ⟪x 5, d2⟫ := by
    have := congrArg (fun w => ⟪w, d2⟫) hrad
    simpa only [inner_add_left, real_inner_smul_left, one_mul] using this
  rcases le_total ⟪x 4, d2⟫ ⟪x 5, d2⟫ with h45 | h45
  · have h1 : S_sp N.s N.t * (⟪x 4, d2⟫ - ⟪x 1, d2⟫) + (⟪x 4, d2⟫ - ⟪x 6, d2⟫) +
        N.t * (⟪x 5, d2⟫ - ⟪x 4, d2⟫) = 0 := by linear_combination -hd + ⟪x 4, d2⟫ * hS1
    nlinarith
  · have h2 : S_sp N.s N.t * (⟪x 5, d2⟫ - ⟪x 1, d2⟫) + (⟪x 5, d2⟫ - ⟪x 6, d2⟫) +
        N.s * (⟪x 4, d2⟫ - ⟪x 5, d2⟫) = 0 := by linear_combination -hd + ⟪x 5, d2⟫ * hS1
    nlinarith

private theorem not_Mp_coplanar_1465 (N : NF29 x) {b d1 d2 : ℝ³}
    (_hb : det3 b d1 d2 ≠ 0) :
    ¬ (LexLt3 (⟪x 4, b⟫, ⟪x 4, d1⟫, ⟪x 4, d2⟫) (⟪x 1, b⟫, ⟪x 1, d1⟫, ⟪x 1, d2⟫) ∧
       LexLt3 (⟪x 4, b⟫, ⟪x 4, d1⟫, ⟪x 4, d2⟫) (⟪x 6, b⟫, ⟪x 6, d1⟫, ⟪x 6, d2⟫) ∧
       LexLt3 (⟪x 5, b⟫, ⟪x 5, d1⟫, ⟪x 5, d2⟫) (⟪x 1, b⟫, ⟪x 1, d1⟫, ⟪x 1, d2⟫) ∧
       LexLt3 (⟪x 5, b⟫, ⟪x 5, d1⟫, ⟪x 5, d2⟫) (⟪x 6, b⟫, ⟪x 6, d1⟫, ⟪x 6, d2⟫)) := by
  intro ⟨h41, h46, h51, h56⟩
  have hrad := coplanar_radon_1465 N
  have hS := S_pos_of_NF29 N
  have hs := N.hs
  have ht := N.ht
  have hS1 : S_sp N.s N.t + 1 = N.s + N.t := by dsimp only [S_sp]; ring
  have eq_of_le : ∀ v : ℝ³,
      ⟪x 4, v⟫ ≤ ⟪x 1, v⟫ → ⟪x 4, v⟫ ≤ ⟪x 6, v⟫ →
      ⟪x 5, v⟫ ≤ ⟪x 1, v⟫ → ⟪x 5, v⟫ ≤ ⟪x 6, v⟫ →
      ⟪x 4, v⟫ = ⟪x 1, v⟫ ∧ ⟪x 5, v⟫ = ⟪x 1, v⟫ ∧ ⟪x 6, v⟫ = ⟪x 1, v⟫ := by
    intro v l41 l46 l51 l56
    have hd : S_sp N.s N.t * ⟪x 1, v⟫ + ⟪x 6, v⟫ = N.s * ⟪x 4, v⟫ + N.t * ⟪x 5, v⟫ := by
      have := congrArg (fun w => ⟪w, v⟫) hrad
      simpa only [inner_add_left, real_inner_smul_left, one_mul] using this
    have h1 : N.s * (⟪x 1, v⟫ - ⟪x 4, v⟫) + N.t * (⟪x 1, v⟫ - ⟪x 5, v⟫) +
        (⟪x 6, v⟫ - ⟪x 1, v⟫) = 0 := by linear_combination hd - ⟪x 1, v⟫ * hS1
    have h2 : N.s * (⟪x 6, v⟫ - ⟪x 4, v⟫) + N.t * (⟪x 6, v⟫ - ⟪x 5, v⟫) +
        S_sp N.s N.t * (⟪x 1, v⟫ - ⟪x 6, v⟫) = 0 := by linear_combination hd - ⟪x 6, v⟫ * hS1
    rcases le_total ⟪x 1, v⟫ ⟪x 6, v⟫ with h16 | h16
    · have ha : N.s * (⟪x 1, v⟫ - ⟪x 4, v⟫) = 0 := by nlinarith
      have hb' : N.t * (⟪x 1, v⟫ - ⟪x 5, v⟫) = 0 := by nlinarith
      have hc : ⟪x 6, v⟫ - ⟪x 1, v⟫ = 0 := by nlinarith
      exact ⟨by linarith [(mul_eq_zero.mp ha).resolve_left hs.ne'],
        by linarith [(mul_eq_zero.mp hb').resolve_left ht.ne'],
        by linarith⟩
    · have ha : N.s * (⟪x 6, v⟫ - ⟪x 4, v⟫) = 0 := by nlinarith
      have hb' : N.t * (⟪x 6, v⟫ - ⟪x 5, v⟫) = 0 := by nlinarith
      have hc : S_sp N.s N.t * (⟪x 1, v⟫ - ⟪x 6, v⟫) = 0 := by nlinarith
      have h16e : ⟪x 1, v⟫ = ⟪x 6, v⟫ := by linarith [(mul_eq_zero.mp hc).resolve_left hS.ne']
      exact ⟨by linarith [(mul_eq_zero.mp ha).resolve_left hs.ne'],
        by linarith [(mul_eq_zero.mp hb').resolve_left ht.ne'],
        h16e.symm⟩
  have le_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}, LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ ≤ b₁ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨h, _⟩ <;> linarith
  have le2_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ},
      LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ = b₁ → a₂ ≤ b₂ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h he; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨_, h | ⟨h, _⟩⟩ <;> linarith
  have lt3_of_lex : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ},
      LexLt3 (a₁, a₂, a₃) (b₁, b₂, b₃) → a₁ = b₁ → a₂ = b₂ → a₃ < b₃ := by
    intro a₁ a₂ a₃ b₁ b₂ b₃ h he1 he2; unfold LexLt3 LexPos3 at h
    rcases h with h | ⟨_, h | ⟨_, h⟩⟩ <;> linarith
  obtain ⟨eb4, eb5, eb6⟩ := eq_of_le b (le_of_lex h41) (le_of_lex h46) (le_of_lex h51) (le_of_lex h56)
  obtain ⟨ed4, ed5, ed6⟩ := eq_of_le d1
    (le2_of_lex h41 eb4) (le2_of_lex h46 (eb4.trans eb6.symm))
    (le2_of_lex h51 eb5) (le2_of_lex h56 (eb5.trans eb6.symm))
  have lf41 := lt3_of_lex h41 eb4 ed4
  have lf46 := lt3_of_lex h46 (eb4.trans eb6.symm) (ed4.trans ed6.symm)
  have lf51 := lt3_of_lex h51 eb5 ed5
  have lf56 := lt3_of_lex h56 (eb5.trans eb6.symm) (ed5.trans ed6.symm)
  have hd : S_sp N.s N.t * ⟪x 1, d2⟫ + ⟪x 6, d2⟫ = N.s * ⟪x 4, d2⟫ + N.t * ⟪x 5, d2⟫ := by
    have := congrArg (fun w => ⟪w, d2⟫) hrad
    simpa only [inner_add_left, real_inner_smul_left, one_mul] using this
  rcases le_total ⟪x 1, d2⟫ ⟪x 6, d2⟫ with h16 | h16
  · have h1 : N.s * (⟪x 1, d2⟫ - ⟪x 4, d2⟫) + N.t * (⟪x 1, d2⟫ - ⟪x 5, d2⟫) +
        (⟪x 6, d2⟫ - ⟪x 1, d2⟫) = 0 := by linear_combination hd - ⟪x 1, d2⟫ * hS1
    nlinarith
  · have h2 : N.s * (⟪x 6, d2⟫ - ⟪x 4, d2⟫) + N.t * (⟪x 6, d2⟫ - ⟪x 5, d2⟫) +
        S_sp N.s N.t * (⟪x 1, d2⟫ - ⟪x 6, d2⟫) = 0 := by linear_combination hd - ⟪x 6, d2⟫ * hS1
    nlinarith

/-- **`A40 L6` (`F015xF124_closes`)**: metric-free `LexAny29` closure at `-N.u015_124 x` (`= u_{15,24}`)
on rim `![1, 4, 6, 5]` for `{G*, a0 + h0 > 0, phi_346(u_{15,23}) ≥ 0, b2 + h2 * t > 0}`. -/
theorem F015xF124_closes (N : NF29 x)
    (ha2 : N.a2 < 0) (hh0 : N.h0 < 1) (hh2 : 1 < N.h2) (ht : N.t < 1)
    (hdG4 : 0 < N.dG4) (h1bh : 0 < 1 - N.b0 - N.h0)
    (hV : N.V < 0) (hA35 : A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 < 0)
    (hah : 0 < N.a0 + N.h0)
    (hB5 : B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0)
    (hb2ht : 0 < N.b2 + N.h2 * N.t) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := -N.u015_124 x
  let d1 : ℝ³ := x 1 - x 3
  let d2 : ℝ³ := x 4 - x 1
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hS := S_pos_of_NF29 N
  have hdG := dG_neg_of_Gstar N ha2 hh0 hh2
  have hb_eval : ∀ t : Fin 9, ⟪F.N t, b⟫ = -(F.f t (x 3 + N.u015_124 x) - F.f t (x 3)) := fun t => by
    change ⟪F.N t, -N.u015_124 x⟫ = _
    rw [inner_neg_right, F.hN t (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
  have u_eval : ∀ {S : Finset (Fin 7)} (f : Face16 x S), f.f (x 3 + N.u015_124 x) - f.f (x 3) =
      (-N.a0 * N.h2) * (f.f (x 4) - f.f (x 1)) - (N.h0 * N.b2) * (f.f (x 5) - f.f (x 1)) +
        (N.h0 * N.h2) * (f.f (x 1) - f.f (x 3)) := fun f => by
    rw [f.hN (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
    dsimp only [u015_124]
    rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← f.hN (x 4) (x 1), ← f.hN (x 5) (x 1), ← f.hN (x 1) (x 3)]
  have h012 : 0 < ⟪F.N 0, b⟫ := by
    rw [hb_eval 0]; change 0 < -(N.f012.f (x 3 + N.u015_124 x) - N.f012.f (x 3))
    linarith [f012_u015_124_neg N]
  have h015 : ⟪F.N 1, b⟫ = 0 := by
    rw [hb_eval 1]; change -(N.f015.f (x 3 + N.u015_124 x) - N.f015.f (x 3)) = 0
    rw [f015_u015_124 N, neg_zero]
  have h124 : ⟪F.N 4, b⟫ = 0 := by
    rw [hb_eval 4]; change -(N.f124.f (x 3 + N.u015_124 x) - N.f124.f (x 3)) = 0
    rw [f124_u015_124 N, neg_zero]
  have h1456 : ⟪F.N 5, b⟫ < 0 := by
    rw [hb_eval 5]; change -(N.f1456.f (x 3 + N.u015_124 x) - N.f1456.f (x 3)) < 0
    linarith [f1456_u015_124_pos N]
  have hPol : 0 < Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 := (Pol_pos N hdG4).2
  have h023 : 0 < ⟪F.N 2, b⟫ := by
    rw [hb_eval 2]; change 0 < -(N.f023.f (x 3 + N.u015_124 x) - N.f023.f (x 3))
    have hval : -(N.f023.f (x 3 + N.u015_124 x) - N.f023.f (x 3)) =
        Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * N.D ^ 2 := by
      rw [u_eval N.f023]; dsimp only [Pol_sp, f023, Face16.ofPoly]; nf29_simp N
      simp only [det3c, NF29.D]; ring
    rw [hval]; exact mul_pos hPol hD2
  have h035 : 0 < ⟪F.N 3, b⟫ := by
    rw [hb_eval 3]; change 0 < -(N.f035.f (x 3 + N.u015_124 x) - N.f035.f (x 3))
    have hval : -(N.f035.f (x 3 + N.u015_124 x) - N.f035.f (x 3)) =
        (-N.a0) * (N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2) * N.D ^ 2 := by
      rw [u_eval N.f035]; dsimp only [P4C_sp, f035, Face16.ofPoly]; nf29_simp N
      simp only [det3c, NF29.D]; ring
    rw [hval]
    have hdel0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
    have h1b0 : 0 < 1 - N.b0 := by linarith [N.hh0]
    have hid : (1 - N.a0 - N.b0 - N.h0) * (N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2) =
        (1 - N.b0) * (-N.V) + N.h0 * (-A35_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2) := by
      dsimp only [P4C_sp, NF29.V, A35_sp, DG4_sp, D0_sp, G4_sp]; ring
    have h_h2P4 : 0 < N.h2 - P4C_sp N.b0 N.h0 N.b2 N.h2 :=
      pos_of_mul_pos_right (by rw [hid]; nlinarith [N.hh0]) hdel0.le
    exact mul_pos (mul_pos (neg_pos.mpr N.ha0) h_h2P4) hD2
  have hP0 : 0 < P0_sp N.a0 N.b0 N.h0 N.s N.t := by
    have hval : N.f346.f (x 3) - N.f346.f (x 0) = P0_sp N.a0 N.b0 N.h0 N.s N.t * N.D ^ 2 := by
      dsimp only [P0_sp, f346, Face16.ofPoly]; nf29_simp N; simp only [det3c, NF29.D]; ring
    have hpos : 0 < N.f346.f (x 3) - N.f346.f (x 0) := by
      rw [N.f346.zero 3 (by decide), zero_sub, neg_pos]; exact N.f346.neg 0 (by decide)
    rw [hval] at hpos; exact pos_of_mul_pos_left hpos hD2.le
  have hD234 : 0 < D234_sp N.a2 N.b2 N.h2 N.s N.t := by
    dsimp only [D234_sp]; linarith [N.d234]
  have h_a0P5 : 0 < -N.a0 - P5C_sp N.a0 N.h0 N.a2 N.h2 := by
    have hid : B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t =
        (-N.a0) * D234_sp N.a2 N.b2 N.h2 N.s N.t -
          (-N.a0 - P5C_sp N.a0 N.h0 N.a2 N.h2) * P0_sp N.a0 N.b0 N.h0 N.s N.t := by
      dsimp only [B5_sp]; ring
    have : 0 < (-N.a0) * D234_sp N.a2 N.b2 N.h2 N.s N.t := by nlinarith [N.ha0]
    have : 0 < (-N.a0 - P5C_sp N.a0 N.h0 N.a2 N.h2) * P0_sp N.a0 N.b0 N.h0 N.s N.t := by linarith
    exact pos_of_mul_pos_left this hP0.le
  have h234 : 0 < ⟪F.N 6, b⟫ := by
    rw [hb_eval 6]; change 0 < -(N.f234.f (x 3 + N.u015_124 x) - N.f234.f (x 3))
    have hval : -(N.f234.f (x 3 + N.u015_124 x) - N.f234.f (x 3)) =
        (-N.b2) * ((N.a0 + N.h0) + (-N.a0 - P5C_sp N.a0 N.h0 N.a2 N.h2)) * N.D ^ 2 := by
      rw [u_eval N.f234]; dsimp only [P5C_sp, f234, Face16.ofPoly]; nf29_simp N
      simp only [det3c, NF29.D]; ring
    rw [hval]
    exact mul_pos (mul_pos (neg_pos.mpr N.hb2) (add_pos hah h_a0P5)) hD2
  have h346 : 0 < ⟪F.N 7, b⟫ := by
    rw [hb_eval 7]; change 0 < -(N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3))
    have hval1 : -(N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3)) =
        (N.h2 * N.t * (N.a0 + N.h0) + (-N.b2) * N.h0 * (N.s - 1)) * N.D ^ 2 := by
      rw [u_eval N.f346]; dsimp only [f346, Face16.ofPoly]; nf29_simp N
      simp only [det3c, NF29.D]; ring
    have hval2 : (-N.dG) * (-(N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3))) =
        (N.h2 * (-B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t) +
          Pol_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 * (1 - N.s)) * N.D ^ 2 := by
      rw [u_eval N.f346]; dsimp only [B5_sp, Pol_sp, D234_sp, P5C_sp, P0_sp, NF29.dG, f346, Face16.ofPoly]
      nf29_simp N; simp only [det3c, NF29.D]; ring
    rcases lt_or_ge N.s 1 with hs1 | hs1
    · have hpos : 0 < (-N.dG) * (-(N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3))) := by
        rw [hval2]
        exact mul_pos (add_pos_of_nonneg_of_pos (mul_nonneg N.hh2.le (neg_nonneg.mpr hB5))
          (mul_pos hPol (sub_pos.mpr hs1))) hD2
      exact pos_of_mul_pos_right hpos (neg_pos.mpr hdG).le
    · rw [hval1]
      exact mul_pos (add_pos_of_pos_of_nonneg (mul_pos (mul_pos N.hh2 N.ht) hah)
        (mul_nonneg (mul_pos (neg_pos.mpr N.hb2) N.hh0).le (sub_nonneg.mpr hs1))) hD2
  have h356 : 0 < ⟪F.N 8, b⟫ := by
    rw [hb_eval 8]; change 0 < -(N.f356.f (x 3 + N.u015_124 x) - N.f356.f (x 3))
    have hval : -(N.f356.f (x 3 + N.u015_124 x) - N.f356.f (x 3)) =
        (N.s * N.h0 * (N.b2 + N.h2 * N.t) + N.h2 * (1 - N.t) * (N.s * N.h0 + N.a0)) * N.D ^ 2 := by
      rw [u_eval N.f356]; dsimp only [f356, Face16.ofPoly]; nf29_simp N
      simp only [det3c, NF29.D]; ring
    have hsha : 0 < N.s * N.h0 + N.a0 := by
      have hid := (phi346_u1523_gt_one N ha2 hh0 hh2 ht h1bh).1
      have hDG5 : 0 < N.DG5 := by dsimp only [NF29.DG5, NF29.D02, NF29.dG]; linarith [N.hDG5]
      have h1bht : 0 < 1 - N.b0 - N.h0 * N.t := by
        have : 0 < N.h0 * (1 - N.t) := mul_pos N.hh0 (sub_pos.mpr ht)
        linarith
      have hc1 : 0 < N.D02 + (N.b0 + N.h0 * N.t) * N.dG := by
        have : N.D02 + (N.b0 + N.h0 * N.t) * N.dG = N.DG5 + (1 - N.b0 - N.h0 * N.t) * (-N.dG) := by
          dsimp only [NF29.DG5, NF29.D02, NF29.dG]; ring
        rw [this]; nlinarith
      have hD0b0 : 0 < N.D02 + N.b0 * N.dG := by
        have : 0 < N.h0 * N.t * (-N.dG) := mul_pos (mul_pos N.hh0 N.ht) (neg_pos.mpr hdG)
        linarith
      have hprod : 0 < (N.D02 + N.b0 * N.dG) * (N.s * N.h0 + N.a0) := by
        have h1 : N.h0 * B5_sp N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos N.hh0.le hB5
        have h2 : 0 < (N.a0 + N.h0) * (N.D02 + (N.b0 + N.h0 * N.t) * N.dG) :=
          mul_pos hah hc1
        linarith [hid]
      exact pos_of_mul_pos_right hprod hD0b0.le
    rw [hval]
    exact mul_pos (add_pos (mul_pos (mul_pos N.hs N.hh0) hb2ht)
      (mul_pos (mul_pos N.hh2 (sub_pos.mpr ht)) hsha)) hD2
  have hdet : det3 b d1 d2 ≠ 0 := by
    have hval : det3 b d1 d2 = (N.h0 * N.b2) * N.D := by
      dsimp only [b, d1, d2, u015_124]
      nf29_simp N
      simp only [nfV, det3_expand, PiLp.neg_apply, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul, NF29.D]
      ring
    rw [hval]
    exact mul_ne_zero (mul_ne_zero N.hh0.ne' N.hb2.ne) N.hD
  have lex_of_not : ∀ {i j : Fin 7}, i ≠ j →
      ¬ LexLt3 (⟪x i, b⟫, ⟪x i, d1⟫, ⟪x i, d2⟫) (⟪x j, b⟫, ⟪x j, d1⟫, ⟪x j, d2⟫) →
      LexLt3 (⟪x j, b⟫, ⟪x j, d1⟫, ⟪x j, d2⟫) (⟪x i, b⟫, ⟪x i, d1⟫, ⟪x i, d2⟫) := by
    intro i j hij hnot
    by_contra hnot2
    have h1 : ⟪x i, b⟫ = ⟪x j, b⟫ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hnot (Or.inl (sub_pos.mpr h))
      · exact hnot2 (Or.inl (sub_pos.mpr h))
    have h2 : ⟪x i, d1⟫ = ⟪x j, d1⟫ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hnot (Or.inr ⟨by linarith, Or.inl (sub_pos.mpr h)⟩)
      · exact hnot2 (Or.inr ⟨by linarith, Or.inl (sub_pos.mpr h)⟩)
    have h3 : ⟪x i, d2⟫ = ⟪x j, d2⟫ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hnot (Or.inr ⟨by linarith, Or.inr ⟨by linarith, sub_pos.mpr h⟩⟩)
      · exact hnot2 (Or.inr ⟨by linarith, Or.inr ⟨by linarith, sub_pos.mpr h⟩⟩)
    have hdiff : x i - x j = 0 := by
      have h0b : ⟪x i - x j, b⟫ = 0 := by rw [inner_sub_left]; linarith
      have h0d1 : ⟪x i - x j, d1⟫ = 0 := by rw [inner_sub_left]; linarith
      have h0d2 : ⟪x i - x j, d2⟫ = 0 := by rw [inner_sub_left]; linarith
      have hc0 : det3 b d1 d2 • (x i - x j) = 0 := by
        have hb' : b 0 * (x i - x j) 0 + b 1 * (x i - x j) 1 + b 2 * (x i - x j) 2 = 0 := by
          simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
            Fin.isValue] using h0b
        have hd1' : d1 0 * (x i - x j) 0 + d1 1 * (x i - x j) 1 + d1 2 * (x i - x j) 2 = 0 := by
          simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
            Fin.isValue] using h0d1
        have hd2' : d2 0 * (x i - x j) 0 + d2 1 * (x i - x j) 1 + d2 2 * (x i - x j) 2 = 0 := by
          simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
            Fin.isValue] using h0d2
        ext k
        simp only [PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply, det3_expand, Fin.isValue]
        fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
        · linear_combination (d1 1 * d2 2 - d1 2 * d2 1) * hb' +
            (b 2 * d2 1 - b 1 * d2 2) * hd1' + (b 1 * d1 2 - b 2 * d1 1) * hd2'
        · linear_combination (d1 2 * d2 0 - d1 0 * d2 2) * hb' +
            (b 0 * d2 2 - b 2 * d2 0) * hd1' + (b 2 * d1 0 - b 0 * d1 2) * hd2'
        · linear_combination (d1 0 * d2 1 - d1 1 * d2 0) * hb' +
            (b 1 * d2 0 - b 0 * d2 1) * hd1' + (b 0 * d1 1 - b 1 * d1 0) * hd2'
      exact (smul_eq_zero.mp hc0).resolve_left hdet
    exact hij (N.inj (sub_eq_zero.mp hdiff))
  refine lexAny_of_clauses F (le_refl 4) c_1465_inj cyc_015_124_copl b d1 d2 ?_ ?_ ?_
  · intro t ht'
    fin_cases t
    · exact Or.inl h012
    · refine Or.inr ⟨h015, Or.inl ?_⟩
      change 0 < ⟪F.N 1, x 1 - x 3⟫
      rw [← F.hN 1 (x 1) (x 3), F.zero 1 1 (by decide), zero_sub, neg_pos]
      exact F.neg 1 3 (by decide)
    · exact Or.inl h023
    · exact Or.inl h035
    · refine Or.inr ⟨h124, Or.inl ?_⟩
      change 0 < ⟪F.N 4, x 1 - x 3⟫
      rw [← F.hN 4 (x 1) (x 3), F.zero 4 1 (by decide), zero_sub, neg_pos]
      exact F.neg 4 3 (by decide)
    · exact absurd ht' (by decide)
    · exact Or.inl h234
    · exact Or.inl h346
    · exact Or.inl h356
  · intro t ht'
    fin_cases t <;> try exact absurd ht' (by decide)
    exact Or.inl (neg_pos.mpr h1456)
  · intro B b' c' d' hb' hbc' hcd' hd'
    have hb1 : b' = 1 := by omega
    have hc2 : c' = 2 := by omega
    have hd3 : d' = 3 := by omega
    subst hb1 hc2 hd3
    have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by revert B; decide
    have e01 : (0 : ZMod 4) + 1 = 1 := rfl
    have e02 : (0 : ZMod 4) + 2 = 2 := rfl
    have e03 : (0 : ZMod 4) + 3 = 3 := rfl
    have e11 : (1 : ZMod 4) + 1 = 2 := rfl
    have e12 : (1 : ZMod 4) + 2 = 3 := rfl
    have e13 : (1 : ZMod 4) + 3 = 0 := rfl
    have e21 : (2 : ZMod 4) + 1 = 3 := rfl
    have e22 : (2 : ZMod 4) + 2 = 0 := rfl
    have e23 : (2 : ZMod 4) + 3 = 1 := rfl
    have e31 : (3 : ZMod 4) + 1 = 0 := rfl
    have e32 : (3 : ZMod 4) + 2 = 1 := rfl
    have e33 : (3 : ZMod 4) + 3 = 2 := rfl
    have clause_of_notMp : LexClause (x 4) (x 5) (x 1) (x 6) b d1 d2 := by
      by_contra hc
      simp only [LexClause, not_or] at hc
      exact not_Mp_coplanar_1465 N hdet
        ⟨lex_of_not (by decide) hc.1, lex_of_not (by decide) hc.2.1,
         lex_of_not (by decide) hc.2.2.1, lex_of_not (by decide) hc.2.2.2⟩
    have clause_of_notMp' : LexClause (x 5) (x 4) (x 6) (x 1) b d1 d2 := by
      by_contra hc
      simp only [LexClause, not_or] at hc
      exact not_Mp_coplanar_1465 N hdet
        ⟨lex_of_not (by decide) hc.2.2.2, lex_of_not (by decide) hc.2.2.1,
         lex_of_not (by decide) hc.2.1, lex_of_not (by decide) hc.1⟩
    have clause_of_notM : LexClause (x 6) (x 1) (x 4) (x 5) b d1 d2 := by
      by_contra hc
      simp only [LexClause, not_or] at hc
      exact not_M_coplanar_1465 N hdet
        ⟨lex_of_not (by decide) hc.2.2.1, lex_of_not (by decide) hc.2.2.2,
         lex_of_not (by decide) hc.1, lex_of_not (by decide) hc.2.1⟩
    have clause_of_notM' : LexClause (x 1) (x 6) (x 5) (x 4) b d1 d2 := by
      by_contra hc
      simp only [LexClause, not_or] at hc
      exact not_M_coplanar_1465 N hdet
        ⟨lex_of_not (by decide) hc.2.1, lex_of_not (by decide) hc.1,
         lex_of_not (by decide) hc.2.2.2, lex_of_not (by decide) hc.2.2.1⟩
    rcases hB with rfl | rfl | rfl | rfl
    · simp only [Nat.cast_one, Nat.cast_ofNat, e01, e02, e03, c_1465, Matrix.cons_val, Fin.isValue]
      exact clause_of_notMp
    · simp only [Nat.cast_one, Nat.cast_ofNat, e11, e12, e13, c_1465, Matrix.cons_val, Fin.isValue]
      exact clause_of_notM
    · simp only [Nat.cast_one, Nat.cast_ofNat, e21, e22, e23, c_1465, Matrix.cons_val, Fin.isValue]
      exact clause_of_notMp'
    · simp only [Nat.cast_one, Nat.cast_ofNat, e31, e32, e33, c_1465, Matrix.cons_val, Fin.isValue]
      exact clause_of_notM'

end F015xF124

/-! ## 4. `M_cone` (`A39 L2`) & `order_WI_cones` (`A39 L4`) -/

section MConeAndOrders

/-- **`A39 L2` (Circuit refutation of `M-`)**:
For any PD metric `G` (represented by `‖u35‖_G^2 > 0`), `M-` (`max(z1, z3)(u35) ≤ min(z4, z5)(u35)`)
is impossible under `S, -a0, -b2, del0, del2, C35 > 0`. -/
theorem not_M_neg_of_circuit (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hS : 0 < S_sp s t) (ha0 : a0 < 0) (hb2 : b2 < 0)
    (hdel0 : 0 < 1 - a0 - b0 - h0) (hdel2 : 0 < 1 - a2 - b2 - h2)
    (hC35 : 0 < C35_sp a0 b0 h0 a2 b2 h2)
    (hPD : 0 < gramQ G33 G44 G55 g34 g35 g45
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (hz14 : gramB G33 G44 G55 g34 g35 g45 0 (s / S_sp s t) (t / S_sp s t)
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) ≤
      gramB G33 G44 G55 g34 g35 g45 0 1 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (hz34 : gramB G33 G44 G55 g34 g35 g45 1 0 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) ≤
      gramB G33 G44 G55 g34 g35 g45 0 1 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (hz15 : gramB G33 G44 G55 g34 g35 g45 0 (s / S_sp s t) (t / S_sp s t)
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) ≤
      gramB G33 G44 G55 g34 g35 g45 0 0 1
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (hz35 : gramB G33 G44 G55 g34 g35 g45 1 0 0
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t) ≤
      gramB G33 G44 G55 g34 g35 g45 0 0 1
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)) :
    False := by
  let S := S_sp s t
  let del0 := 1 - a0 - b0 - h0
  let del2 := 1 - a2 - b2 - h2
  let C35 := C35_sp a0 b0 h0 a2 b2 h2
  let Wp := S * (-a0 * del2 - b2 * del0)
  let u3 := S * C35
  let u4 := del2 * D035_sp a0 b0 h0 s t
  let u5 := del0 * D234_sp a2 b2 h2 s t
  let z1 := gramB G33 G44 G55 g34 g35 g45 0 (s / S) (t / S) u3 u4 u5
  let z3 := gramB G33 G44 G55 g34 g35 g45 1 0 0 u3 u4 u5
  let z4 := gramB G33 G44 G55 g34 g35 g45 0 1 0 u3 u4 u5
  let z5 := gramB G33 G44 G55 g34 g35 g45 0 0 1 u3 u4 u5
  have hS0 : S ≠ 0 := hS.ne'
  have hWp_eq : Wp = S * (del0 * del2 + C35) := by
    dsimp only [Wp, C35, del0, del2, C35_sp, DG4_sp, D0_sp, G4_sp]; ring
  have hWp_pos : 0 < Wp := by
    dsimp only [Wp]
    have h1 : 0 < -a0 * del2 := mul_pos (neg_pos.mpr ha0) hdel2
    have h2 : 0 < -b2 * del0 := mul_pos (neg_pos.mpr hb2) hdel0
    nlinarith
  have hz1_mul : S * z1 = gramB G33 G44 G55 g34 g35 g45 0 s t u3 u4 u5 := by
    dsimp only [z1, gramB]; field_simp [hS0]; ring
  have hgram_lin : ∀ c1 c2 c3 c4 c5 x1 y1 z1' x2 y2 z2' x3 y3 z3' x4 y4 z4' x5 y5 z5' : ℝ,
      c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 + c5 * x5 = 0 →
      c1 * y1 + c2 * y2 + c3 * y3 + c4 * y4 + c5 * y5 = 0 →
      c1 * z1' + c2 * z2' + c3 * z3' + c4 * z4' + c5 * z5' = 0 →
      c1 * gramB G33 G44 G55 g34 g35 g45 x1 y1 z1' u3 u4 u5 +
        c2 * gramB G33 G44 G55 g34 g35 g45 x2 y2 z2' u3 u4 u5 +
        c3 * gramB G33 G44 G55 g34 g35 g45 x3 y3 z3' u3 u4 u5 +
        c4 * gramB G33 G44 G55 g34 g35 g45 x4 y4 z4' u3 u4 u5 +
        c5 * gramB G33 G44 G55 g34 g35 g45 x5 y5 z5' u3 u4 u5 = 0 := by
    intro c1 c2 c3 c4 c5 x1 y1 z1' x2 y2 z2' x3 y3 z3' x4 y4 z4' x5 y5 z5' hx hy hz
    dsimp only [gramB]
    linear_combination (G33 * u3 + g34 * u4 + g35 * u5) * hx +
      (g34 * u3 + G44 * u4 + g45 * u5) * hy + (g35 * u3 + g45 * u4 + G55 * u5) * hz
  have hcirc :
      S ^ 2 * (-a0 * del2) * (del0 * del2) * (z4 - z1) +
        S ^ 2 * (-a0 * del2) * C35 * (z4 - z3) +
        S ^ 2 * (-b2 * del0) * (del0 * del2) * (z5 - z1) +
        S ^ 2 * (-b2 * del0) * C35 * (z5 - z3) +
        Wp * gramQ G33 G44 G55 g34 g35 g45 u3 u4 u5 = 0 := by
    have hq : gramQ G33 G44 G55 g34 g35 g45 u3 u4 u5 =
        gramB G33 G44 G55 g34 g35 g45 u3 u4 u5 u3 u4 u5 := by
      dsimp only [gramQ, gramB]; ring
    have hz41 : S * z4 - S * z1 = gramB G33 G44 G55 g34 g35 g45 0 (S - s) (-t) u3 u4 u5 := by
      rw [hz1_mul]; dsimp only [z4, gramB]; ring
    have hz43 : z4 - z3 = gramB G33 G44 G55 g34 g35 g45 (-1) 1 0 u3 u4 u5 := by
      dsimp only [z4, z3, gramB]; ring
    have hz51 : S * z5 - S * z1 = gramB G33 G44 G55 g34 g35 g45 0 (-s) (S - t) u3 u4 u5 := by
      rw [hz1_mul]; dsimp only [z5, gramB]; ring
    have hz53 : z5 - z3 = gramB G33 G44 G55 g34 g35 g45 (-1) 0 1 u3 u4 u5 := by
      dsimp only [z5, z3, gramB]; ring
    have hlin := hgram_lin
      (S * (-a0 * del2) * (del0 * del2)) (S ^ 2 * (-a0 * del2) * C35)
      (S * (-b2 * del0) * (del0 * del2)) (S ^ 2 * (-b2 * del0) * C35) Wp
      0 (S - s) (-t) (-1) 1 0 0 (-s) (S - t) (-1) 0 1 u3 u4 u5
      (by dsimp only [Wp, u3, del0, del2, C35, S, C35_sp, DG4_sp, D0_sp, G4_sp, S_sp]; ring)
      (by dsimp only [Wp, u4, del0, del2, C35, S, C35_sp, DG4_sp, D0_sp, G4_sp, D035_sp, S_sp]; ring)
      (by dsimp only [Wp, u5, del0, del2, C35, S, C35_sp, DG4_sp, D0_sp, G4_sp, D234_sp, S_sp]; ring)
    rw [← hz41, ← hz43, ← hz51, ← hz53, ← hq] at hlin
    linarith [hlin]
  have ha0d2 : 0 < -a0 * del2 := mul_pos (neg_pos.mpr ha0) hdel2
  have hb2d0 : 0 < -b2 * del0 := mul_pos (neg_pos.mpr hb2) hdel0
  have hd0d2 : 0 < del0 * del2 := mul_pos hdel0 hdel2
  have h1 : 0 ≤ S ^ 2 * (-a0 * del2) * (del0 * del2) * (z4 - z1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg S) ha0d2.le) hd0d2.le) (sub_nonneg.mpr hz14)
  have h2 : 0 ≤ S ^ 2 * (-a0 * del2) * C35 * (z4 - z3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg S) ha0d2.le) hC35.le) (sub_nonneg.mpr hz34)
  have h3 : 0 ≤ S ^ 2 * (-b2 * del0) * (del0 * del2) * (z5 - z1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg S) hb2d0.le) hd0d2.le) (sub_nonneg.mpr hz15)
  have h4 : 0 ≤ S ^ 2 * (-b2 * del0) * C35 * (z5 - z3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg S) hb2d0.le) hC35.le) (sub_nonneg.mpr hz35)
  have h5 : 0 < Wp * gramQ G33 G44 G55 g34 g35 g45 u3 u4 u5 := mul_pos hWp_pos hPD
  linarith

/-- **`A39 L2` (`M_cone`)**: if the `R_{--} = ![1, 4, 3, 5]` rim fails `RobUniLex` at `u35`
under a PD metric `G` (represented by `z_i(u35)` with `‖u35‖_G^2 > 0`), then `M-` is impossible,
forcing `M+` (`max(z4, z5)(u35) ≤ min(z1, z3)(u35)`) and in particular `z4(u35) ≤ z3(u35)`. -/
theorem M_cone (a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45 : ℝ)
    (hS : 0 < S_sp s t) (ha0 : a0 < 0) (hb2 : b2 < 0)
    (hdel0 : 0 < 1 - a0 - b0 - h0) (hdel2 : 0 < 1 - a2 - b2 - h2)
    (hC35 : 0 < C35_sp a0 b0 h0 a2 b2 h2)
    (hPD : 0 < gramQ G33 G44 G55 g34 g35 g45
        (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
        ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
        ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t))
    (e f : ZMod 4 → ℝ)
    (hfail : ¬ RobUniLex (fun i : ZMod 4 =>
      ((![gramB G33 G44 G55 g34 g35 g45 0 (s / S_sp s t) (t / S_sp s t)
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t),
          gramB G33 G44 G55 g34 g35 g45 0 1 0
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t),
          gramB G33 G44 G55 g34 g35 g45 1 0 0
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t),
          gramB G33 G44 G55 g34 g35 g45 0 0 1
            (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2)
            ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
            ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)] : Fin 4 → ℝ) ⟨i.val, ZMod.val_lt i⟩, e i, f i))) :
    let u3 := S_sp s t * C35_sp a0 b0 h0 a2 b2 h2
    let u4 := (1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t
    let u5 := (1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t
    let z1 := gramB G33 G44 G55 g34 g35 g45 0 (s / S_sp s t) (t / S_sp s t) u3 u4 u5
    let z3 := gramB G33 G44 G55 g34 g35 g45 1 0 0 u3 u4 u5
    let z4 := gramB G33 G44 G55 g34 g35 g45 0 1 0 u3 u4 u5
    let z5 := gramB G33 G44 G55 g34 g35 g45 0 0 1 u3 u4 u5
    (z4 ≤ z1 ∧ z4 ≤ z3 ∧ z5 ≤ z1 ∧ z5 ≤ z3) ∧ z4 ≤ z3 := by
  dsimp only
  set z1 := gramB G33 G44 G55 g34 g35 g45 0 (s / S_sp s t) (t / S_sp s t)
    (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
    ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)
  set z3 := gramB G33 G44 G55 g34 g35 g45 1 0 0
    (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
    ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)
  set z4 := gramB G33 G44 G55 g34 g35 g45 0 1 0
    (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
    ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)
  set z5 := gramB G33 G44 G55 g34 g35 g45 0 0 1
    (S_sp s t * C35_sp a0 b0 h0 a2 b2 h2) ((1 - a2 - b2 - h2) * D035_sp a0 b0 h0 s t)
    ((1 - a0 - b0 - h0) * D234_sp a2 b2 h2 s t)
  have hlt : ∀ {a b e₁ e₂ f₁ f₂ : ℝ}, a < b → LexLt3 (a, e₁, f₁) (b, e₂, f₂) :=
    fun h => Or.inl (sub_pos.mpr h)
  have hMp : z4 ≤ z1 ∧ z4 ≤ z3 ∧ z5 ≤ z1 ∧ z5 ≤ z3 := by
    by_contra hnotM
    have hn : ∃ p ∈ Minimality.RimCell.diagPairs,
        LexLt3 ((![z1, z4, z3, z5] ⟨p.1.val, ZMod.val_lt p.1⟩), e p.1, f p.1)
               ((![z1, z4, z3, z5] ⟨p.2.val, ZMod.val_lt p.2⟩), e p.2, f p.2) := by
      rcases not_and_or.mp hnotM with h41 | hnotM
      · exact ⟨(0, 1), by decide, hlt (lt_of_not_ge h41)⟩
      · rcases not_and_or.mp hnotM with h43 | hnotM
        · exact ⟨(2, 1), by decide, hlt (lt_of_not_ge h43)⟩
        · rcases not_and_or.mp hnotM with h51 | h53
          · exact ⟨(0, 3), by decide, hlt (lt_of_not_ge h51)⟩
          · exact ⟨(2, 3), by decide, hlt (lt_of_not_ge h53)⟩
    have hnotMm : ¬ (z1 ≤ z4 ∧ z3 ≤ z4 ∧ z1 ≤ z5 ∧ z3 ≤ z5) := fun ⟨a, b, c, d⟩ =>
      not_M_neg_of_circuit a0 b0 h0 a2 b2 h2 s t G33 G44 G55 g34 g35 g45
        hS ha0 hb2 hdel0 hdel2 hC35 hPD a b c d
    have hp : ∃ q ∈ Minimality.RimCell.diagPairs,
        LexLt3 ((![z1, z4, z3, z5] ⟨q.2.val, ZMod.val_lt q.2⟩), e q.2, f q.2)
               ((![z1, z4, z3, z5] ⟨q.1.val, ZMod.val_lt q.1⟩), e q.1, f q.1) := by
      rcases not_and_or.mp hnotMm with h14 | hnotMm
      · exact ⟨(0, 1), by decide, hlt (lt_of_not_ge h14)⟩
      · rcases not_and_or.mp hnotMm with h34 | hnotMm
        · exact ⟨(2, 1), by decide, hlt (lt_of_not_ge h34)⟩
        · rcases not_and_or.mp hnotMm with h15 | h35
          · exact ⟨(0, 3), by decide, hlt (lt_of_not_ge h15)⟩
          · exact ⟨(2, 3), by decide, hlt (lt_of_not_ge h35)⟩
    exact hfail (robUniLex_four_of_mixed hn hp)
  exact ⟨hMp, hMp.2.1⟩

/-! ### `A39 L4`: 120-order `F234xF346` cone lemma (`order_WI_cones`) -/

/-- Non-unimodality of a cycle of distinct integers (`List ℕ` of indices into a rank list). -/
def nonUni6 (r : List Nat) (c : List Nat) : Bool :=
  let k := c.length
  (List.range k).all fun B =>
    (List.range k).all fun b =>
      (List.range k).all fun c' =>
        (List.range k).all fun d =>
          if 0 < b && b < c' && c' < d then
            let vB := r.getD (c.getD B 0) 0
            let vb := r.getD (c.getD ((B + b) % k) 0) 0
            let vc := r.getD (c.getD ((B + c') % k) 0) 0
            let vd := r.getD (c.getD ((B + d) % k) 0) 0
            !((vB < vb && vc < vb) || (vB < vd && vc < vd))
          else true

/-- Generate all permutations of a list up to `fuel` elements. -/
def perms6Aux : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => [[]]
  | n + 1, xs => xs.flatMap fun x => (perms6Aux n (xs.erase x)).map (x :: ·)

def perms6 : List (List Nat) := perms6Aux 7 [0, 1, 2, 3, 4, 5]

/-- Indices `0 ↦ z0, 1 ↦ z2, 2 ↦ z3, 3 ↦ z4, 4 ↦ z5, 5 ↦ z6`.
Rims `(0,2,4,6,5)`, `(0,2,3,6,5)`, `(0,2,4,3,6,5)`, `(0,2,3,4,6,5)`. -/
def orderWI_ok (r : List Nat) : Bool :=
  let z0 := r.getD 0 0; let z2 := r.getD 1 0; let z3 := r.getD 2 0
  let z4 := r.getD 3 0; let z5 := r.getD 4 0; let z6 := r.getD 5 0
  if z3 < z6 && z6 < z4 then
    let allFail :=
      nonUni6 r [0, 1, 3, 5, 4] &&
      nonUni6 r [0, 1, 2, 5, 4] &&
      nonUni6 r [0, 1, 3, 2, 5, 4] &&
      nonUni6 r [0, 1, 2, 3, 5, 4]
    if allFail then
      let inQ7 := z0 < z2 && z0 < z5 && z6 < z2 && z6 < z5
      let inQ8 := z2 < z0 && z5 < z0 && z2 < z4 && z5 < z4
      let inC3 := z6 < z4 && z2 < z4 && z6 < z5 && z2 < z5 && z0 < z2 && z3 < z2
      let inC4 := z2 < z0 && z5 < z0
      inQ7 || inQ8 || inC3 || inC4
    else true
  else true

/-- **`A39 L4` (`order_WI_cones`)**: among all 120 strict depth orders of `(z0, z2, z3, z4, z5, z6)`
with `z3 < z6 < z4`, all four `F234xF346` rims non-unimodal implies `Q_7 ∨ Q_8 ∨ C_{WI,3} ∨ C_{WI,4}`. -/
theorem order_WI_cones : perms6.all orderWI_ok = true := by
  decide +kernel

end MConeAndOrders

end Minimality.NF29
