module

public import Minimality.FiveRim
public import Minimality.SameView
public import Minimality.LexCell
public import Minimality.GenRev24

/-!
# ER: Lemma A5, the apex edge of a 5-rim

The k = 5 analogue of the Q4 two-end lemma.

Setting: `R : ZMod 5 → ℝ³`, a view `u`, a strictly convex screen rim with orientation sign `ρ`
(`StrictConvex5 R u ρ`, the hcyc form of `SplitApex.lean`), the five 4-subsets non-coplanar.

Shape-only data (constant on a cell): for each of the five quartets the diagonal that passes in
front along `u` (Lemma 20.26, `FrontDiag`, here in its det3 Cramer form `DiagFront`).  A labelling
`p k = a + k ε` of the rim (start `a`, direction `ε = ±1`) is an APEX LABELLING (`ApexPat R u a ε`)
when the five quartets have the front diagonals of Fable's bipyramid pattern, in 1-based labels
r1..r5 = p 0..p 4:
  omit 5: 13 over 24;  omit 4: 13 over 25;  omit 3: 14 over 25;  omit 2: 14 over 35;
  omit 1: 35 over 24.
Then: the non-edge of conv(R) is (r3, r5) = (p 2, p 4), the apex edge is (r1, r2) = (p 0, p 1),
the upper apex is `r1 = R a` and the lower apex `r2 = R (a + ε)`.

A5 (i): injective non-unimodal depths force `z r1 > z r2` (and one of five edge-sign vectors).
A5 (ii): `z r1 < z r2` (strict, other ties allowed) forces `RobUni z`.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.A5

/-- `[y, c]` passes in front of `[a, b]` along `u` (Lemma 20.26, Cramer form: the two
determinants `[c - y, b - a, y - a]` and `[c - y, b - a, u]` have the same sign).  Invariant under
swapping `y, c` and under swapping `a, b`. -/
def DiagFront (y c a b u : ℝ³) : Prop :=
  0 < det3 (c - y) (b - a) (y - a) * det3 (c - y) (b - a) u

/-- The depth is the view pairing. -/
noncomputable def depth (R : ZMod 5 → ℝ³) (u : ℝ³) : ZMod 5 → ℝ := fun i => ⟪R i, u⟫

/-- The five 4-subsets are non-coplanar: for each omitted vertex `m`, the quartet
`m+1, m+2, m+3, m+4` spans a 3-dimensional simplex. -/
def NonCoplanar5 (R : ZMod 5 → ℝ³) : Prop :=
  ∀ m : ZMod 5,
    det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 1)) ≠ 0

/-- The apex labelling of the rim from start `a` and direction `ε = ±1`, `p k = a + k ε`
(0-based; `p 0 = r1`, `p 1 = r2`): the five front diagonals of the bipyramid pattern. -/
def ApexPat (R : ZMod 5 → ℝ³) (u : ℝ³) (a ε : ZMod 5) : Prop :=
  (ε = 1 ∨ ε = -1) ∧
  -- omit r5: 13 over 24
  DiagFront (R a) (R (a + 2 * ε)) (R (a + ε)) (R (a + 3 * ε)) u ∧
  -- omit r4: 13 over 25
  DiagFront (R a) (R (a + 2 * ε)) (R (a + 4 * ε)) (R (a + ε)) u ∧
  -- omit r3: 14 over 25
  DiagFront (R a) (R (a + 3 * ε)) (R (a + ε)) (R (a + 4 * ε)) u ∧
  -- omit r2: 14 over 35
  DiagFront (R a) (R (a + 3 * ε)) (R (a + 2 * ε)) (R (a + 4 * ε)) u ∧
  -- omit r1: 35 over 24
  DiagFront (R (a + 2 * ε)) (R (a + 4 * ε)) (R (a + ε)) (R (a + 3 * ε)) u

/-! ### Bridges to the tree -/

/-- `DiagFront` is `FrontDiag` for the crossing diagonals of a strictly convex quartet
(Lemma 20.26, `QuadTestR'.frontDiag` / `frontDiag_of_rim`).  Stated for the 5-rim quartet omitting `m`:
corners `m+1, m+2, m+3, m+4`, diagonals `[m+1, m+3]`, `[m+2, m+4]`. -/
private theorem zmod5_add_ne (m a b : ZMod 5) (h : a ≠ b) : m + a ≠ m + b :=
  fun h' => h (by linear_combination h')

private theorem zmod5_add_eq (a b c d : ZMod 5) (h : b + c = d) : a + b + c = a + d := by
  rw [add_assoc, h]

private theorem zmod5_add_zero (a b c : ZMod 5) (h : b + c = 0) : a + b + c = a := by
  rw [add_assoc, h, add_zero]

theorem diagFront_iff_frontDiag (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (m : ZMod 5) :
    DiagFront (R (m + 1)) (R (m + 3)) (R (m + 2)) (R (m + 4)) u ↔
      FrontDiag (R (m + 1)) (R (m + 3)) (R (m + 2)) (R (m + 4)) u := by
  have hρ_ne : ρ ≠ 0 := by
    have h0 := hcvx 0 2 (by decide) (by decide)
    intro h0'; simp [h0'] at h0
  have q1 := hcvx (m + 1) (m + 3) (zmod5_add_ne m 3 1 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 3 (1 + 1) (by decide))
  have q2 := hcvx (m + 2) (m + 4) (zmod5_add_ne m 4 2 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 4 (2 + 1) (by decide))
  have q3 := hcvx (m + 3) (m + 1) (zmod5_add_ne m 1 3 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 1 (3 + 1) (by decide))
  have q4' := hcvx (m + 1) (m + 4) (zmod5_add_ne m 4 1 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 4 (1 + 1) (by decide))
  rw [zmod5_add_eq m 1 1 2 rfl] at q1 q4'
  rw [zmod5_add_eq m 2 1 3 rfl] at q2
  rw [zmod5_add_eq m 3 1 4 rfl] at q3
  have hq4_eq : det3 (R (m + 1) - R (m + 4)) (R (m + 2) - R (m + 4)) u =
      det3 (R (m + 2) - R (m + 1)) (R (m + 4) - R (m + 1)) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hΔ : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u =
      det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u +
      det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  constructor
  · intro hDF
    rcases lt_or_gt_of_ne hρ_ne with hρ | hρ
    · have q1n : det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u < 0 := by nlinarith
      have q2n : det3 (R (m + 3) - R (m + 2)) (R (m + 4) - R (m + 2)) u < 0 := by nlinarith
      have q3n : det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u < 0 := by nlinarith
      have q4n : det3 (R (m + 1) - R (m + 4)) (R (m + 2) - R (m + 4)) u < 0 := by
        rw [hq4_eq]; nlinarith
      have hΔ_neg : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u < 0 := by
        rw [hΔ]; linarith
      have hnum : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) < 0 := by
        rw [DiagFront] at hDF; nlinarith [hDF]
      have c1 : 0 < det3 (R (m + 4) - R (m + 1)) (R (m + 3) - R (m + 1)) u := by
        have h : det3 (R (m + 4) - R (m + 1)) (R (m + 3) - R (m + 1)) u =
            -det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        linarith
      have c2 : 0 < det3 (R (m + 3) - R (m + 4)) (R (m + 2) - R (m + 4)) u := by
        have h : det3 (R (m + 3) - R (m + 4)) (R (m + 2) - R (m + 4)) u =
            -det3 (R (m + 3) - R (m + 2)) (R (m + 4) - R (m + 2)) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        linarith
      have c3 : 0 < det3 (R (m + 2) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
        have h : det3 (R (m + 2) - R (m + 3)) (R (m + 1) - R (m + 3)) u =
            -det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        linarith
      have c4 : 0 < det3 (R (m + 1) - R (m + 2)) (R (m + 4) - R (m + 2)) u := by
        have h : det3 (R (m + 1) - R (m + 2)) (R (m + 4) - R (m + 2)) u =
            -det3 (R (m + 1) - R (m + 4)) (R (m + 2) - R (m + 4)) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        linarith
      have hnum' : 0 < det3 (R (m + 3) - R (m + 1)) (R (m + 2) - R (m + 4)) (R (m + 1) - R (m + 4)) := by
        have h : det3 (R (m + 3) - R (m + 1)) (R (m + 2) - R (m + 4)) (R (m + 1) - R (m + 4)) =
            -det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        linarith
      exact ((frontDiag_of_rim c1 c2 c3 c4).1 hnum').swap_e
    · have c1 : 0 < det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u :=
        pos_of_mul_pos_right q1 hρ.le
      have c2 : 0 < det3 (R (m + 3) - R (m + 2)) (R (m + 4) - R (m + 2)) u :=
        pos_of_mul_pos_right q2 hρ.le
      have c3 : 0 < det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u :=
        pos_of_mul_pos_right q3 hρ.le
      have c4 : 0 < det3 (R (m + 1) - R (m + 4)) (R (m + 2) - R (m + 4)) u := by
        rw [hq4_eq]; exact pos_of_mul_pos_right q4' hρ.le
      have hΔ_pos : 0 < det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u := by
        rw [hΔ]; linarith
      have hnum : 0 < det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) :=
        pos_of_mul_pos_left hDF hΔ_pos.le
      exact (frontDiag_of_rim c1 c2 c3 c4).1 hnum
  · rintro ⟨s, t, γ, hs0, hs1, ht0, ht1, hγ, he⟩
    have hΔ_ne : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u ≠ 0 := by
      rcases lt_or_gt_of_ne hρ_ne with hρ | hρ
      · have c1 : det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u < 0 := by nlinarith
        have c3 : det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u < 0 := by nlinarith
        rw [hΔ]; linarith
      · have c1 : 0 < det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u :=
          pos_of_mul_pos_right q1 hρ.le
        have c3 : 0 < det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u :=
          pos_of_mul_pos_right q3 hρ.le
        rw [hΔ]; linarith
    have key : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) =
        γ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u := by
      have e := congrArg (fun X => det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) X) he
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e ⊢
      linear_combination e
    rw [DiagFront, key, mul_assoc, ← sq]
    exact mul_pos hγ (sq_pos_of_ne_zero hΔ_ne)

private noncomputable def quartDet (R : ZMod 5 → ℝ³) (m : ZMod 5) : ℝ :=
  det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 1))

private theorem quartDet_sum_zero (R : ZMod 5 → ℝ³) :
    quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4 = 0 := by
  simp only [quartDet, det3_expand, PiLp.sub_apply]
  have h01 : (0 + 1 : ZMod 5) = 1 := rfl
  have h02 : (0 + 2 : ZMod 5) = 2 := rfl
  have h03 : (0 + 3 : ZMod 5) = 3 := rfl
  have h04 : (0 + 4 : ZMod 5) = 4 := rfl
  have h12 : (1 + 2 : ZMod 5) = 3 := rfl
  have h13 : (1 + 3 : ZMod 5) = 4 := rfl
  have h14 : (1 + 4 : ZMod 5) = 0 := rfl
  have h22 : (2 + 2 : ZMod 5) = 4 := rfl
  have h23 : (2 + 3 : ZMod 5) = 0 := rfl
  have h24 : (2 + 4 : ZMod 5) = 1 := rfl
  have h32 : (3 + 2 : ZMod 5) = 0 := rfl
  have h33 : (3 + 3 : ZMod 5) = 1 := rfl
  have h34 : (3 + 4 : ZMod 5) = 2 := rfl
  have h42 : (4 + 2 : ZMod 5) = 1 := rfl
  have h43 : (4 + 3 : ZMod 5) = 2 := rfl
  have h44 : (4 + 4 : ZMod 5) = 3 := rfl
  rw [h01, h02, h03, h04, h12, h13, h14, h22, h23, h24, h32, h33, h34, h42, h43, h44,
    show (1 + 1 : ZMod 5) = 2 from rfl, show (2 + 1 : ZMod 5) = 3 from rfl,
    show (3 + 1 : ZMod 5) = 4 from rfl, show (4 + 1 : ZMod 5) = 0 from rfl]
  ring

private theorem quartDet_vec_sum_zero (R : ZMod 5 → ℝ³) :
    quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
      quartDet R 3 • R 3 + quartDet R 4 • R 4 = 0 := by
  ext k
  have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
    quartDet, det3_expand, PiLp.sub_apply,
    show (0 + 1 : ZMod 5) = 1 from rfl, show (0 + 2 : ZMod 5) = 2 from rfl,
    show (0 + 3 : ZMod 5) = 3 from rfl, show (0 + 4 : ZMod 5) = 4 from rfl,
    show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
    show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl,
    show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
    show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl,
    show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
    show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl,
    show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
    show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl]
  rcases hk k with rfl | rfl | rfl <;> ring

private theorem quartDet_proj_zero (R : ZMod 5 → ℝ³) (u : ℝ³) (i : ZMod 5) :
    quartDet R (i + 2) * det3 (R (i + 1) - R i) (R (i + 2) - R i) u +
    quartDet R (i + 3) * det3 (R (i + 1) - R i) (R (i + 3) - R i) u +
    quartDet R (i + 4) * det3 (R (i + 1) - R i) (R (i + 4) - R i) u = 0 := by
  have hsum := quartDet_sum_zero R
  have hv := quartDet_vec_sum_zero R
  have hi : ∀ j : ZMod 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
  have hdiff : quartDet R i • (R i - R i) + quartDet R (i + 1) • (R (i + 1) - R i) +
      quartDet R (i + 2) • (R (i + 2) - R i) + quartDet R (i + 3) • (R (i + 3) - R i) +
      quartDet R (i + 4) • (R (i + 4) - R i) = 0 := by
    rcases hi i with rfl | rfl | rfl | rfl | rfl
    · simp only [show (0 + 1 : ZMod 5) = 1 from rfl, show (0 + 2 : ZMod 5) = 2 from rfl,
        show (0 + 3 : ZMod 5) = 3 from rfl, show (0 + 4 : ZMod 5) = 4 from rfl]
      rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
      calc (quartDet R 0 • R 0 - quartDet R 0 • R 0) + (quartDet R 1 • R 1 - quartDet R 1 • R 0) +
            (quartDet R 2 • R 2 - quartDet R 2 • R 0) + (quartDet R 3 • R 3 - quartDet R 3 • R 0) +
            (quartDet R 4 • R 4 - quartDet R 4 • R 0)
          = (quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
              quartDet R 3 • R 3 + quartDet R 4 • R 4) -
            (quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4) • R 0 := by
            module
        _ = 0 := by rw [hv, hsum, zero_smul, sub_zero]
    · simp only [show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
        show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl]
      rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
      calc (quartDet R 1 • R 1 - quartDet R 1 • R 1) + (quartDet R 2 • R 2 - quartDet R 2 • R 1) +
            (quartDet R 3 • R 3 - quartDet R 3 • R 1) + (quartDet R 4 • R 4 - quartDet R 4 • R 1) +
            (quartDet R 0 • R 0 - quartDet R 0 • R 1)
          = (quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
              quartDet R 3 • R 3 + quartDet R 4 • R 4) -
            (quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4) • R 1 := by
            module
        _ = 0 := by rw [hv, hsum, zero_smul, sub_zero]
    · simp only [show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
        show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl]
      rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
      calc (quartDet R 2 • R 2 - quartDet R 2 • R 2) + (quartDet R 3 • R 3 - quartDet R 3 • R 2) +
            (quartDet R 4 • R 4 - quartDet R 4 • R 2) + (quartDet R 0 • R 0 - quartDet R 0 • R 2) +
            (quartDet R 1 • R 1 - quartDet R 1 • R 2)
          = (quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
              quartDet R 3 • R 3 + quartDet R 4 • R 4) -
            (quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4) • R 2 := by
            module
        _ = 0 := by rw [hv, hsum, zero_smul, sub_zero]
    · simp only [show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
        show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl]
      rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
      calc (quartDet R 3 • R 3 - quartDet R 3 • R 3) + (quartDet R 4 • R 4 - quartDet R 4 • R 3) +
            (quartDet R 0 • R 0 - quartDet R 0 • R 3) + (quartDet R 1 • R 1 - quartDet R 1 • R 3) +
            (quartDet R 2 • R 2 - quartDet R 2 • R 3)
          = (quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
              quartDet R 3 • R 3 + quartDet R 4 • R 4) -
            (quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4) • R 3 := by
            module
        _ = 0 := by rw [hv, hsum, zero_smul, sub_zero]
    · simp only [show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
        show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl]
      rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
      calc (quartDet R 4 • R 4 - quartDet R 4 • R 4) + (quartDet R 0 • R 0 - quartDet R 0 • R 4) +
            (quartDet R 1 • R 1 - quartDet R 1 • R 4) + (quartDet R 2 • R 2 - quartDet R 2 • R 4) +
            (quartDet R 3 • R 3 - quartDet R 3 • R 4)
          = (quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
              quartDet R 3 • R 3 + quartDet R 4 • R 4) -
            (quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4) • R 4 := by
            module
        _ = 0 := by rw [hv, hsum, zero_smul, sub_zero]
  have e := congrArg (fun X => det3 (R (i + 1) - R i) X u) hdiff
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply,
    smul_eq_mul] at e ⊢
  linear_combination e

private theorem diagFront_iff_quartDet_neg (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (m : ZMod 5) :
    DiagFront (R (m + 1)) (R (m + 3)) (R (m + 2)) (R (m + 4)) u ↔ ρ * quartDet R m < 0 := by
  have q1 := hcvx (m + 1) (m + 3) (zmod5_add_ne m 3 1 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 3 (1 + 1) (by decide))
  have q3 := hcvx (m + 3) (m + 1) (zmod5_add_ne m 1 3 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 1 (3 + 1) (by decide))
  rw [zmod5_add_eq m 1 1 2 rfl] at q1
  rw [zmod5_add_eq m 3 1 4 rfl] at q3
  have hΔ : ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u =
      ρ * det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u +
      ρ * det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
    have h : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u =
        det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u +
        det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h, mul_add]
  have hA : 0 < ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u := by linarith
  have hnum : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) =
      -quartDet R m := by
    simp only [quartDet, det3_expand, PiLp.sub_apply]; ring
  have hρ_ne : ρ ≠ 0 := by intro h0; simp [h0] at hA
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_ne_zero hρ_ne
  rw [DiagFront, hnum]
  constructor
  · intro h
    have hmul : 0 < (- (ρ * quartDet R m)) *
        (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by
      have heq : (- (ρ * quartDet R m)) *
          (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) =
          ρ ^ 2 * (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by ring
      rw [heq]; exact mul_pos hρ2 h
    have := pos_of_mul_pos_left hmul hA.le
    linarith
  · intro h
    have hmul : 0 < ρ ^ 2 *
        (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by
      have heq : ρ ^ 2 *
          (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) =
          (- (ρ * quartDet R m)) *
            (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by ring
      rw [heq]; exact mul_pos (by linarith) hA
    exact pos_of_mul_pos_right hmul hρ2.le

private theorem diagFront_iff_quartDet_pos (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (m : ZMod 5) :
    DiagFront (R (m + 2)) (R (m + 4)) (R (m + 1)) (R (m + 3)) u ↔ 0 < ρ * quartDet R m := by
  have heq : DiagFront (R (m + 2)) (R (m + 4)) (R (m + 1)) (R (m + 3)) u ↔
      det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) *
        det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u < 0 := by
    simp only [DiagFront]
    have h2 : det3 (R (m + 4) - R (m + 2)) (R (m + 3) - R (m + 1)) u =
        -det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have h1' : det3 (R (m + 4) - R (m + 2)) (R (m + 3) - R (m + 1)) (R (m + 2) - R (m + 1)) =
        det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h1', h2]
    constructor <;> intro h <;> linarith
  rw [heq]
  have q1 := hcvx (m + 1) (m + 3) (zmod5_add_ne m 3 1 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 3 (1 + 1) (by decide))
  have q3 := hcvx (m + 3) (m + 1) (zmod5_add_ne m 1 3 (by decide))
    (by rw [add_assoc]; exact zmod5_add_ne m 1 (3 + 1) (by decide))
  rw [zmod5_add_eq m 1 1 2 rfl] at q1
  rw [zmod5_add_eq m 3 1 4 rfl] at q3
  have hΔ : ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u =
      ρ * det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u +
      ρ * det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
    have h : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u =
        det3 (R (m + 2) - R (m + 1)) (R (m + 3) - R (m + 1)) u +
        det3 (R (m + 4) - R (m + 3)) (R (m + 1) - R (m + 3)) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h, mul_add]
  have hA : 0 < ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u := by linarith
  have hnum : det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) (R (m + 1) - R (m + 2)) =
      -quartDet R m := by
    simp only [quartDet, det3_expand, PiLp.sub_apply]; ring
  have hρ_ne : ρ ≠ 0 := by intro h0; simp [h0] at hA
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_ne_zero hρ_ne
  rw [hnum]
  constructor
  · intro h
    have hmul : 0 < (ρ * quartDet R m) *
        (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by
      have heq' : (ρ * quartDet R m) *
          (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) =
          -(ρ ^ 2 * (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u)) := by ring
      rw [heq']; exact neg_pos.mpr (mul_neg_of_pos_of_neg hρ2 h)
    exact pos_of_mul_pos_left hmul hA.le
  · intro h
    have hmul : 0 < -(ρ ^ 2 * (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u)) := by
      have heq' : -(ρ ^ 2 * (-quartDet R m * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u)) =
          (ρ * quartDet R m) *
            (ρ * det3 (R (m + 3) - R (m + 1)) (R (m + 4) - R (m + 2)) u) := by ring
      rw [heq']; exact mul_pos h hA
    nlinarith [hρ2]

private theorem diagFront_swap_d {y c a b u : ℝ³} :
    DiagFront y c a b u ↔ DiagFront c y a b u := by
  simp only [DiagFront]
  have h1 : det3 (y - c) (b - a) (c - a) = -det3 (c - y) (b - a) (y - a) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have h2 : det3 (y - c) (b - a) u = -det3 (c - y) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [h1, h2, neg_mul_neg]

private theorem diagFront_swap_e {y c a b u : ℝ³} :
    DiagFront y c a b u ↔ DiagFront y c b a u := by
  simp only [DiagFront]
  have h1 : det3 (c - y) (a - b) (y - b) = -det3 (c - y) (b - a) (y - a) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have h2 : det3 (c - y) (a - b) u = -det3 (c - y) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [h1, h2, neg_mul_neg]

private theorem apexPat_iff_quartDet (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (hnc : NonCoplanar5 R) (a ε : ZMod 5) :
    ApexPat R u a ε ↔
      (ε = 1 ∧ 0 < ρ * quartDet R a ∧ 0 < ρ * quartDet R (a + 1) ∧
        ρ * quartDet R (a + 2) < 0 ∧ 0 < ρ * quartDet R (a + 3) ∧ ρ * quartDet R (a + 4) < 0) ∨
      (ε = -1 ∧ ρ * quartDet R a < 0 ∧ 0 < ρ * quartDet R (a + 1) ∧
        ρ * quartDet R (a + 2) < 0 ∧ 0 < ρ * quartDet R (a + 3) ∧ ρ * quartDet R (a + 4) < 0) := by
  have hne : ∀ m, ρ * quartDet R m ≠ 0 := by
    intro m
    have hρ : ρ ≠ 0 := by
      have h0 := hcvx 0 2 (by decide) (by decide)
      intro h0'; simp [h0'] at h0
    exact mul_ne_zero hρ (hnc m)
  have e11 : a + 1 + 1 = a + 2 := zmod5_add_eq a 1 1 2 rfl
  have e12 : a + 1 + 2 = a + 3 := zmod5_add_eq a 1 2 3 rfl
  have e13 : a + 1 + 3 = a + 4 := zmod5_add_eq a 1 3 4 rfl
  have e14 : a + 1 + 4 = a := zmod5_add_zero a 1 4 rfl
  have e21 : a + 2 + 1 = a + 3 := zmod5_add_eq a 2 1 3 rfl
  have e22 : a + 2 + 2 = a + 4 := zmod5_add_eq a 2 2 4 rfl
  have e23 : a + 2 + 3 = a := zmod5_add_zero a 2 3 rfl
  have e24 : a + 2 + 4 = a + 1 := zmod5_add_eq a 2 4 1 rfl
  have e31 : a + 3 + 1 = a + 4 := zmod5_add_eq a 3 1 4 rfl
  have e32 : a + 3 + 2 = a := zmod5_add_zero a 3 2 rfl
  have e33 : a + 3 + 3 = a + 1 := zmod5_add_eq a 3 3 1 rfl
  have e34 : a + 3 + 4 = a + 2 := zmod5_add_eq a 3 4 2 rfl
  have e41 : a + 4 + 1 = a := zmod5_add_zero a 4 1 rfl
  have e42 : a + 4 + 2 = a + 1 := zmod5_add_eq a 4 2 1 rfl
  have e43 : a + 4 + 3 = a + 2 := zmod5_add_eq a 4 3 2 rfl
  have e44 : a + 4 + 4 = a + 3 := zmod5_add_eq a 4 4 3 rfl
  have m1 : a + (-1 : ZMod 5) = a + 4 := by rw [show (-1 : ZMod 5) = 4 from rfl]
  have m2 : a + 2 * (-1 : ZMod 5) = a + 3 := by rw [show (2 * (-1 : ZMod 5)) = 3 from rfl]
  have m3 : a + 3 * (-1 : ZMod 5) = a + 2 := by rw [show (3 * (-1 : ZMod 5)) = 2 from rfl]
  have m4 : a + 4 * (-1 : ZMod 5) = a + 1 := by rw [show (4 * (-1 : ZMod 5)) = 1 from rfl]
  have p1 : a + (1 : ZMod 5) = a + 1 := rfl
  have p2 : a + 2 * (1 : ZMod 5) = a + 2 := by rw [mul_one]
  have p3 : a + 3 * (1 : ZMod 5) = a + 3 := by rw [mul_one]
  have p4 : a + 4 * (1 : ZMod 5) = a + 4 := by rw [mul_one]
  constructor
  · rintro ⟨hε | hε, d1, d2, d3, d4, d5⟩
    · subst hε
      left; refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [p2, p4, p3] at d5
        exact (diagFront_iff_quartDet_pos R u ρ hcvx a).1 d5
      · rw [p3, p2, p4, diagFront_swap_d] at d4
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 1)).1
        rw [e12, e14, e11, e13] at h
        exact h d4
      · rw [p3, p4, diagFront_swap_d, diagFront_swap_e] at d3
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 2)).1
        rw [e21, e23, e22, e24] at h
        exact h d3
      · rw [p2, p4] at d2
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 3)).1
        rw [e32, e34, e31, e33] at h
        exact h d2
      · rw [p2, p3] at d1
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 4)).1
        rw [e41, e43, e42, e44] at h
        exact h d1
    · subst hε
      right; refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [m2, m4, m1, m3, diagFront_swap_d, diagFront_swap_e] at d5
        exact (diagFront_iff_quartDet_neg R u ρ hcvx a).1 d5
      · rw [m2, m1, m3, diagFront_swap_d, diagFront_swap_e] at d1
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 1)).1
        rw [e12, e14, e11, e13] at h
        exact h d1
      · rw [m2, m4, m1, diagFront_swap_d, diagFront_swap_e] at d2
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 2)).1
        rw [e21, e23, e22, e24] at h
        exact h d2
      · rw [m3, m1, m4] at d3
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 3)).1
        rw [e32, e34, e31, e33] at h
        exact h d3
      · rw [m3, m2, m4, diagFront_swap_e] at d4
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 4)).1
        rw [e41, e43, e42, e44] at h
        exact h d4
  · rintro (⟨rfl, h0, h1, h2, h3, h4⟩ | ⟨rfl, h0, h1, h2, h3, h4⟩)
    · refine ⟨Or.inl rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [p2, p3]
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 4)).2 h4
        rwa [e41, e43, e42, e44] at h
      · rw [p2, p4]
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 3)).2 h3
        rwa [e32, e34, e31, e33] at h
      · rw [p3, p4, diagFront_swap_d, diagFront_swap_e]
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 2)).2 h2
        rwa [e21, e23, e22, e24] at h
      · rw [p3, p2, p4, diagFront_swap_d]
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 1)).2 h1
        rwa [e12, e14, e11, e13] at h
      · rw [p2, p4, p3]
        exact (diagFront_iff_quartDet_pos R u ρ hcvx a).2 h0
    · refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [m2, m1, m3, diagFront_swap_d, diagFront_swap_e]
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 1)).2 h1
        rwa [e12, e14, e11, e13] at h
      · rw [m2, m4, m1, diagFront_swap_d, diagFront_swap_e]
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 2)).2 h2
        rwa [e21, e23, e22, e24] at h
      · rw [m3, m1, m4]
        have h := (diagFront_iff_quartDet_pos R u ρ hcvx (a + 3)).2 h3
        rwa [e32, e34, e31, e33] at h
      · rw [m3, m2, m4, diagFront_swap_e]
        have h := (diagFront_iff_quartDet_neg R u ρ hcvx (a + 4)).2 h4
        rwa [e41, e43, e42, e44] at h
      · rw [m2, m4, m1, m3, diagFront_swap_d, diagFront_swap_e]
        exact (diagFront_iff_quartDet_neg R u ρ hcvx a).2 h0

/-- The apex labelling exists and is unique (10 candidates `(a, ε)`; exactly one holds):
the non-edge, upper and lower apex are well defined from shape.  (Spec of the gate.) -/
theorem apexPat_existsUnique (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (hnc : NonCoplanar5 R) :
    ∃! p : ZMod 5 × ZMod 5, ApexPat R u p.1 p.2 := by
  let mkB : Bool → Bool → Bool → Bool → Bool → ZMod 5 → Bool :=
    fun b0 b1 b2 b3 b4 i =>
      if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else if i = 3 then b3 else b4
  have hbool_ex : ∀ b0 b1 b2 b3 b4 : Bool,
      (∀ i : ZMod 5, ¬ (mkB b0 b1 b2 b3 b4 (i + 2) = true ∧
        mkB b0 b1 b2 b3 b4 (i + 3) = true ∧ mkB b0 b1 b2 b3 b4 (i + 4) = true)) →
      (∀ i : ZMod 5, ¬ (mkB b0 b1 b2 b3 b4 (i + 2) = false ∧
        mkB b0 b1 b2 b3 b4 (i + 3) = false ∧ mkB b0 b1 b2 b3 b4 (i + 4) = false)) →
      ∃ p : ZMod 5 × ZMod 5,
        (p.2 = 1 ∧ mkB b0 b1 b2 b3 b4 p.1 = true ∧ mkB b0 b1 b2 b3 b4 (p.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 4) = false) ∨
        (p.2 = -1 ∧ mkB b0 b1 b2 b3 b4 p.1 = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 4) = false) := by
    decide
  have hbool_un1 : ∀ b0 b1 b2 b3 b4 : Bool, ∀ p q : ZMod 5,
      (mkB b0 b1 b2 b3 b4 p = true ∧ mkB b0 b1 b2 b3 b4 (p + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 4) = false) →
      (mkB b0 b1 b2 b3 b4 q = true ∧ mkB b0 b1 b2 b3 b4 (q + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 2) = false ∧ mkB b0 b1 b2 b3 b4 (q + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 4) = false) → p = q := by
    decide
  have hbool_un2 : ∀ b0 b1 b2 b3 b4 : Bool, ∀ p q : ZMod 5,
      (mkB b0 b1 b2 b3 b4 p = false ∧ mkB b0 b1 b2 b3 b4 (p + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 4) = false) →
      (mkB b0 b1 b2 b3 b4 q = false ∧ mkB b0 b1 b2 b3 b4 (q + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 2) = false ∧ mkB b0 b1 b2 b3 b4 (q + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 4) = false) → p = q := by
    decide
  have hbool_disj : ∀ b0 b1 b2 b3 b4 : Bool, ∀ p q : ZMod 5,
      (mkB b0 b1 b2 b3 b4 p = true ∧ mkB b0 b1 b2 b3 b4 (p + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (p + 4) = false) →
      ¬ (mkB b0 b1 b2 b3 b4 q = false ∧ mkB b0 b1 b2 b3 b4 (q + 1) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 2) = false ∧ mkB b0 b1 b2 b3 b4 (q + 3) = true ∧
        mkB b0 b1 b2 b3 b4 (q + 4) = false) := by
    decide
  have hbool_un : ∀ b0 b1 b2 b3 b4 : Bool, ∀ p q : ZMod 5 × ZMod 5,
      ((p.2 = 1 ∧ mkB b0 b1 b2 b3 b4 p.1 = true ∧ mkB b0 b1 b2 b3 b4 (p.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 4) = false) ∨
        (p.2 = -1 ∧ mkB b0 b1 b2 b3 b4 p.1 = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (p.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (p.1 + 4) = false)) →
      ((q.2 = 1 ∧ mkB b0 b1 b2 b3 b4 q.1 = true ∧ mkB b0 b1 b2 b3 b4 (q.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (q.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (q.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (q.1 + 4) = false) ∨
        (q.2 = -1 ∧ mkB b0 b1 b2 b3 b4 q.1 = false ∧ mkB b0 b1 b2 b3 b4 (q.1 + 1) = true ∧
          mkB b0 b1 b2 b3 b4 (q.1 + 2) = false ∧ mkB b0 b1 b2 b3 b4 (q.1 + 3) = true ∧
          mkB b0 b1 b2 b3 b4 (q.1 + 4) = false)) → p.1 = q.1 ∧ p.2 = q.2 := by
    rintro b0 b1 b2 b3 b4 p q (⟨hp2, hp⟩ | ⟨hp2, hp⟩) (⟨hq2, hq⟩ | ⟨hq2, hq⟩)
    · exact ⟨hbool_un1 b0 b1 b2 b3 b4 p.1 q.1 hp hq, hp2.trans hq2.symm⟩
    · exact absurd hq (hbool_disj b0 b1 b2 b3 b4 p.1 q.1 hp)
    · exact absurd hp (hbool_disj b0 b1 b2 b3 b4 q.1 p.1 hq)
    · exact ⟨hbool_un2 b0 b1 b2 b3 b4 p.1 q.1 hp hq, hp2.trans hq2.symm⟩
  have hbool' : ∀ b : ZMod 5 → Bool,
      (∀ i : ZMod 5, ¬ (b (i + 2) = true ∧ b (i + 3) = true ∧ b (i + 4) = true)) →
      (∀ i : ZMod 5, ¬ (b (i + 2) = false ∧ b (i + 3) = false ∧ b (i + 4) = false)) →
      ∃! p : ZMod 5 × ZMod 5,
        (p.2 = 1 ∧ b p.1 = true ∧ b (p.1 + 1) = true ∧ b (p.1 + 2) = false ∧
          b (p.1 + 3) = true ∧ b (p.1 + 4) = false) ∨
        (p.2 = -1 ∧ b p.1 = false ∧ b (p.1 + 1) = true ∧ b (p.1 + 2) = false ∧
          b (p.1 + 3) = true ∧ b (p.1 + 4) = false) := by
    intro b h1 h2
    have hmk : ∀ i : ZMod 5, mkB (b 0) (b 1) (b 2) (b 3) (b 4) i = b i := by
      intro i
      have hi : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
      rcases hi i with rfl | rfl | rfl | rfl | rfl <;> rfl
    have h1' : ∀ i : ZMod 5, ¬ (mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 2) = true ∧
        mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 3) = true ∧
        mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 4) = true) := by
      intro i; simp only [hmk]; exact h1 i
    have h2' : ∀ i : ZMod 5, ¬ (mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 2) = false ∧
        mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 3) = false ∧
        mkB (b 0) (b 1) (b 2) (b 3) (b 4) (i + 4) = false) := by
      intro i; simp only [hmk]; exact h2 i
    obtain ⟨p, hp⟩ := hbool_ex (b 0) (b 1) (b 2) (b 3) (b 4) h1' h2'
    refine ⟨p, ?_, ?_⟩
    · simpa only [hmk] using hp
    · intro q hq
      have hpq := hbool_un (b 0) (b 1) (b 2) (b 3) (b 4) q p
        (by simpa only [hmk] using hq) hp
      exact Prod.ext hpq.1 hpq.2
  classical
  let s : ZMod 5 → Bool := fun m => decide (0 < ρ * quartDet R m)
  have hne : ∀ m, ρ * quartDet R m ≠ 0 := by
    intro m
    have hρ : ρ ≠ 0 := by
      have h0 := hcvx 0 2 (by decide) (by decide)
      intro h0'; simp [h0'] at h0
    exact mul_ne_zero hρ (hnc m)
  have hno3t : ∀ i : ZMod 5, ¬ (s (i + 2) = true ∧ s (i + 3) = true ∧ s (i + 4) = true) := by
    intro i ⟨h2, h3, h4⟩
    simp only [s, decide_eq_true_eq] at h2 h3 h4
    have hproj := quartDet_proj_zero R u i
    have hρ2 := hcvx i (i + 2) (by intro h; apply (by decide : (2 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 2 1 (by decide))
    have hρ3 := hcvx i (i + 3) (by intro h; apply (by decide : (3 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 3 1 (by decide))
    have hρ4 := hcvx i (i + 4) (by intro h; apply (by decide : (4 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 4 1 (by decide))
    have hcomb : (ρ * quartDet R (i + 2)) * (ρ * det3 (R (i + 1) - R i) (R (i + 2) - R i) u) +
        (ρ * quartDet R (i + 3)) * (ρ * det3 (R (i + 1) - R i) (R (i + 3) - R i) u) +
        (ρ * quartDet R (i + 4)) * (ρ * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) = 0 := by
      have heq : (ρ * quartDet R (i + 2)) * (ρ * det3 (R (i + 1) - R i) (R (i + 2) - R i) u) +
          (ρ * quartDet R (i + 3)) * (ρ * det3 (R (i + 1) - R i) (R (i + 3) - R i) u) +
          (ρ * quartDet R (i + 4)) * (ρ * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) =
          ρ ^ 2 * (quartDet R (i + 2) * det3 (R (i + 1) - R i) (R (i + 2) - R i) u +
            quartDet R (i + 3) * det3 (R (i + 1) - R i) (R (i + 3) - R i) u +
            quartDet R (i + 4) * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) := by ring
      rw [heq, hproj, mul_zero]
    nlinarith [mul_pos h2 hρ2, mul_pos h3 hρ3, mul_pos h4 hρ4]
  have hno3f : ∀ i : ZMod 5, ¬ (s (i + 2) = false ∧ s (i + 3) = false ∧ s (i + 4) = false) := by
    intro i ⟨h2, h3, h4⟩
    simp only [s, decide_eq_false_iff_not, not_lt] at h2 h3 h4
    have h2' : ρ * quartDet R (i + 2) < 0 := lt_of_le_of_ne h2 (hne _)
    have h3' : ρ * quartDet R (i + 3) < 0 := lt_of_le_of_ne h3 (hne _)
    have h4' : ρ * quartDet R (i + 4) < 0 := lt_of_le_of_ne h4 (hne _)
    have hproj := quartDet_proj_zero R u i
    have hρ2 := hcvx i (i + 2) (by intro h; apply (by decide : (2 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 2 1 (by decide))
    have hρ3 := hcvx i (i + 3) (by intro h; apply (by decide : (3 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 3 1 (by decide))
    have hρ4 := hcvx i (i + 4) (by intro h; apply (by decide : (4 : ZMod 5) ≠ 0); linear_combination h)
      (zmod5_add_ne i 4 1 (by decide))
    have hcomb : (ρ * quartDet R (i + 2)) * (ρ * det3 (R (i + 1) - R i) (R (i + 2) - R i) u) +
        (ρ * quartDet R (i + 3)) * (ρ * det3 (R (i + 1) - R i) (R (i + 3) - R i) u) +
        (ρ * quartDet R (i + 4)) * (ρ * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) = 0 := by
      have heq : (ρ * quartDet R (i + 2)) * (ρ * det3 (R (i + 1) - R i) (R (i + 2) - R i) u) +
          (ρ * quartDet R (i + 3)) * (ρ * det3 (R (i + 1) - R i) (R (i + 3) - R i) u) +
          (ρ * quartDet R (i + 4)) * (ρ * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) =
          ρ ^ 2 * (quartDet R (i + 2) * det3 (R (i + 1) - R i) (R (i + 2) - R i) u +
            quartDet R (i + 3) * det3 (R (i + 1) - R i) (R (i + 3) - R i) u +
            quartDet R (i + 4) * det3 (R (i + 1) - R i) (R (i + 4) - R i) u) := by ring
      rw [heq, hproj, mul_zero]
    nlinarith [mul_neg_of_neg_of_pos h2' hρ2, mul_neg_of_neg_of_pos h3' hρ3, mul_neg_of_neg_of_pos h4' hρ4]
  obtain ⟨p, hp, huniq⟩ := hbool' s hno3t hno3f
  refine ⟨p, ?_, ?_⟩
  · dsimp only
    rw [apexPat_iff_quartDet R u ρ hcvx hnc p.1 p.2]
    rcases hp with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · left
      simp only [s, decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, lt_of_le_of_ne h4 (hne _), h5, lt_of_le_of_ne h6 (hne _)⟩
    · right
      simp only [s, decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at h2 h3 h4 h5 h6
      exact ⟨h1, lt_of_le_of_ne h2 (hne _), h3, lt_of_le_of_ne h4 (hne _), h5, lt_of_le_of_ne h6 (hne _)⟩
  · intro q hq
    rw [apexPat_iff_quartDet R u ρ hcvx hnc q.1 q.2] at hq
    apply huniq
    rcases hq with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · left
      simp only [s, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
      exact ⟨h1, h2, h3, h4.le, h5, h6.le⟩
    · right
      simp only [s, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
      exact ⟨h1, h2.le, h3, h4.le, h5, h6.le⟩

/-- The non-edge `(r3, r5) = (a + 2ε, a - ε)` is the Radon non-edge of the five points: the
segment `[R (a+2ε), R (a-ε)]` meets the triangle `R a, R (a+ε), R (a+3ε)` (bipyramid axis).  Optional
sanity statement; only the equivalence with the pattern is needed. -/
theorem apexPat_nonEdge (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) (a ε : ZMod 5)
    (hcvx : StrictConvex5 R u ρ) (hnc : NonCoplanar5 R) (h : ApexPat R u a ε) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t < 1 ∧
      ∃ l : ℝ, 0 < l ∧ l < 1 ∧
        R (a + 2 * ε) + l • (R (a - ε) - R (a + 2 * ε)) =
          R a + s • (R (a + ε) - R a) + t • (R (a + 3 * ε) - R a) := by
  rw [apexPat_iff_quartDet R u ρ hcvx hnc a ε] at h
  let σ : ℝ := if ε = 1 then ρ else -ρ
  let w : ZMod 5 → ℝ := fun m => σ * quartDet R m
  have hw_signs : 0 < w a ∧ 0 < w (a + ε) ∧ 0 < w (a + 3 * ε) ∧
      w (a + 2 * ε) < 0 ∧ w (a - ε) < 0 := by
    rcases h with ⟨rfl, h0, h1, h2, h3, h4⟩ | ⟨rfl, h0, h1, h2, h3, h4⟩
    · simp only [w, σ, ↓reduceIte, mul_one]
      rw [show a - (1 : ZMod 5) = a + 4 from by rw [sub_eq_add_neg]; rfl]
      exact ⟨h0, h1, h3, h2, h4⟩
    · have hne1 : (-1 : ZMod 5) ≠ 1 := by decide
      simp only [w, σ, hne1, ↓reduceIte, neg_mul]
      rw [show a + (-1 : ZMod 5) = a + 4 from rfl,
          show a + 3 * (-1 : ZMod 5) = a + 2 from by rw [show (3 * (-1 : ZMod 5)) = 2 from rfl],
          show a + 2 * (-1 : ZMod 5) = a + 3 from by rw [show (2 * (-1 : ZMod 5)) = 3 from rfl],
          show a - (-1 : ZMod 5) = a + 1 from by rw [sub_neg_eq_add]]
      exact ⟨neg_pos.mpr h0, neg_pos.mpr h4, neg_pos.mpr h2, neg_lt_zero.mpr h3, neg_lt_zero.mpr h1⟩
  have hε : ε = 1 ∨ ε = -1 := by
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hsum0 : w a + w (a + ε) + w (a + 3 * ε) + w (a + 2 * ε) + w (a - ε) = 0 := by
    have hs := quartDet_sum_zero R
    have hperm : quartDet R a + quartDet R (a + ε) + quartDet R (a + 3 * ε) +
        quartDet R (a + 2 * ε) + quartDet R (a - ε) =
        quartDet R 0 + quartDet R 1 + quartDet R 2 + quartDet R 3 + quartDet R 4 := by
      have ha : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
      rcases hε with rfl | rfl <;> rcases ha a with rfl | rfl | rfl | rfl | rfl <;>
        simp only [show (0 + 1 : ZMod 5) = 1 from rfl, show (0 + 2 : ZMod 5) = 2 from rfl,
          show (0 + 3 : ZMod 5) = 3 from rfl, show (0 + 4 : ZMod 5) = 4 from rfl,
          show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
          show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl,
          show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
          show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl,
          show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
          show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl,
          show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
          show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl,
          show (0 - 1 : ZMod 5) = 4 from rfl, show (1 - 1 : ZMod 5) = 0 from rfl,
          show (2 - 1 : ZMod 5) = 1 from rfl, show (3 - 1 : ZMod 5) = 2 from rfl,
          show (4 - 1 : ZMod 5) = 3 from rfl, show (0 + (-1 : ZMod 5)) = 4 from rfl,
          show (1 + (-1 : ZMod 5)) = 0 from rfl, show (2 + (-1 : ZMod 5)) = 1 from rfl,
          show (3 + (-1 : ZMod 5)) = 2 from rfl, show (4 + (-1 : ZMod 5)) = 3 from rfl,
          show (0 - (-1 : ZMod 5)) = 1 from rfl, show (1 - (-1 : ZMod 5)) = 2 from rfl,
          show (2 - (-1 : ZMod 5)) = 3 from rfl, show (3 - (-1 : ZMod 5)) = 4 from rfl,
          show (4 - (-1 : ZMod 5)) = 0 from rfl,
          show (2 * (1 : ZMod 5)) = 2 from rfl, show (3 * (1 : ZMod 5)) = 3 from rfl,
          show (2 * (-1 : ZMod 5)) = 3 from rfl, show (3 * (-1 : ZMod 5)) = 2 from rfl] <;> ring
    simp only [w]
    calc σ * quartDet R a + σ * quartDet R (a + ε) + σ * quartDet R (a + 3 * ε) +
          σ * quartDet R (a + 2 * ε) + σ * quartDet R (a - ε)
        = σ * (quartDet R a + quartDet R (a + ε) + quartDet R (a + 3 * ε) +
            quartDet R (a + 2 * ε) + quartDet R (a - ε)) := by ring
      _ = 0 := by rw [hperm, hs, mul_zero]
  have hv0 : w a • R a + w (a + ε) • R (a + ε) + w (a + 3 * ε) • R (a + 3 * ε) +
      w (a + 2 * ε) • R (a + 2 * ε) + w (a - ε) • R (a - ε) = 0 := by
    have hv := quartDet_vec_sum_zero R
    have hperm : quartDet R a • R a + quartDet R (a + ε) • R (a + ε) +
        quartDet R (a + 3 * ε) • R (a + 3 * ε) + quartDet R (a + 2 * ε) • R (a + 2 * ε) +
        quartDet R (a - ε) • R (a - ε) =
        quartDet R 0 • R 0 + quartDet R 1 • R 1 + quartDet R 2 • R 2 +
          quartDet R 3 • R 3 + quartDet R 4 • R 4 := by
      have ha : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
      rcases hε with rfl | rfl <;> rcases ha a with rfl | rfl | rfl | rfl | rfl <;>
        simp only [show (0 + 1 : ZMod 5) = 1 from rfl, show (0 + 2 : ZMod 5) = 2 from rfl,
          show (0 + 3 : ZMod 5) = 3 from rfl, show (0 + 4 : ZMod 5) = 4 from rfl,
          show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
          show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl,
          show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
          show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl,
          show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
          show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl,
          show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
          show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl,
          show (0 - 1 : ZMod 5) = 4 from rfl, show (1 - 1 : ZMod 5) = 0 from rfl,
          show (2 - 1 : ZMod 5) = 1 from rfl, show (3 - 1 : ZMod 5) = 2 from rfl,
          show (4 - 1 : ZMod 5) = 3 from rfl, show (0 + (-1 : ZMod 5)) = 4 from rfl,
          show (1 + (-1 : ZMod 5)) = 0 from rfl, show (2 + (-1 : ZMod 5)) = 1 from rfl,
          show (3 + (-1 : ZMod 5)) = 2 from rfl, show (4 + (-1 : ZMod 5)) = 3 from rfl,
          show (0 - (-1 : ZMod 5)) = 1 from rfl, show (1 - (-1 : ZMod 5)) = 2 from rfl,
          show (2 - (-1 : ZMod 5)) = 3 from rfl, show (3 - (-1 : ZMod 5)) = 4 from rfl,
          show (4 - (-1 : ZMod 5)) = 0 from rfl,
          show (2 * (1 : ZMod 5)) = 2 from rfl, show (3 * (1 : ZMod 5)) = 3 from rfl,
          show (2 * (-1 : ZMod 5)) = 3 from rfl, show (3 * (-1 : ZMod 5)) = 2 from rfl] <;> module
    simp only [w]
    calc (σ * quartDet R a) • R a + (σ * quartDet R (a + ε)) • R (a + ε) +
          (σ * quartDet R (a + 3 * ε)) • R (a + 3 * ε) +
          (σ * quartDet R (a + 2 * ε)) • R (a + 2 * ε) + (σ * quartDet R (a - ε)) • R (a - ε)
        = σ • (quartDet R a • R a + quartDet R (a + ε) • R (a + ε) +
            quartDet R (a + 3 * ε) • R (a + 3 * ε) + quartDet R (a + 2 * ε) • R (a + 2 * ε) +
            quartDet R (a - ε) • R (a - ε)) := by module
      _ = 0 := by rw [hperm, hv, smul_zero]
  obtain ⟨wa, wa1, wa3, wa2, wa4⟩ := hw_signs
  set S : ℝ := w a + w (a + ε) + w (a + 3 * ε)
  have hS : 0 < S := by linarith
  have hS' : S = -w (a + 2 * ε) - w (a - ε) := by linarith
  refine ⟨w (a + ε) / S, w (a + 3 * ε) / S, div_pos wa1 hS, div_pos wa3 hS, ?_,
    -w (a - ε) / S, div_pos (neg_pos.mpr wa4) hS, ?_, ?_⟩
  · rw [← add_div, div_lt_one hS]; linarith
  · rw [div_lt_one hS]; linarith
  · apply smul_right_injective ℝ³ hS.ne'
    dsimp only
    have hs1 : S * (w (a + ε) / S) = w (a + ε) := mul_div_cancel₀ _ hS.ne'
    have hs3 : S * (w (a + 3 * ε) / S) = w (a + 3 * ε) := mul_div_cancel₀ _ hS.ne'
    have hl : S * (-w (a - ε) / S) = -w (a - ε) := mul_div_cancel₀ _ hS.ne'
    rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, hs1, hs3, hl]
    have hS_sub : S = -w (a + 2 * ε) + -w (a - ε) := by linarith
    calc S • R (a + 2 * ε) + (-w (a - ε)) • (R (a - ε) - R (a + 2 * ε))
        = (-w (a + 2 * ε)) • R (a + 2 * ε) + (-w (a - ε)) • R (a - ε) := by
          rw [hS_sub]; module
      _ = w a • R a + w (a + ε) • R (a + ε) + w (a + 3 * ε) • R (a + 3 * ε) := by
          rw [← add_zero ((-w (a + 2 * ε)) • R (a + 2 * ε) + (-w (a - ε)) • R (a - ε)), ← hv0]
          module
      _ = S • R a + w (a + ε) • (R (a + ε) - R a) + w (a + 3 * ε) • (R (a + 3 * ε) - R a) := by
          simp only [S]; module

/-! ### Lemma A5 -/

private theorem strictConvex5_reparam (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) (a ε : ZMod 5)
    (hcvx : StrictConvex5 R u ρ) (hε : ε = 1 ∨ ε = -1) :
    StrictConvex5 (fun k : ZMod 5 => R (a + k * ε)) u (if ε = 1 then ρ else -ρ) := by
  rcases hε with rfl | rfl
  · simp only [↓reduceIte, mul_one]
    intro i j hij hj1
    have h := hcvx (a + i) (a + j) (fun h' => hij (by linear_combination h'))
      (fun h' => hj1 (by linear_combination h'))
    rwa [show a + i + 1 = a + (i + 1) from by ring] at h
  · have hne : (-1 : ZMod 5) ≠ 1 := by decide
    simp only [hne, ↓reduceIte]
    intro i j hij hj1
    have h := hcvx (a + (i + 1) * (-1)) (a + j * (-1))
      (fun h' => hj1 (by linear_combination -h'))
      (fun h' => hij (by linear_combination -h'))
    rw [show a + (i + 1) * (-1) + 1 = a + i * (-1) from by ring] at h
    have heq : det3 (R (a + (i + 1) * (-1)) - R (a + i * (-1)))
        (R (a + j * (-1)) - R (a + i * (-1))) u =
        -det3 (R (a + i * (-1)) - R (a + (i + 1) * (-1)))
          (R (a + j * (-1)) - R (a + (i + 1) * (-1))) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [heq]; linarith

private theorem robUni_of_reparam {z : ZMod 5 → ℝ} (a ε : ZMod 5) (hε : ε = 1 ∨ ε = -1)
    (hR : RobUni (fun k : ZMod 5 => z (a + k * ε))) : RobUni z := by
  intro B b c d hb hc hd hdk
  rcases hε with rfl | rfl
  · have h := hR (B - a) b c d hb hc hd hdk
    simpa only [mul_one, show a + (B - a) = B from by ring,
      show a + (B - a + (b : ZMod 5)) = B + b from by ring,
      show a + (B - a + (c : ZMod 5)) = B + c from by ring,
      show a + (B - a + (d : ZMod 5)) = B + d from by ring] using h
  · have hbc : 0 < c - b := Nat.sub_pos_of_lt hc
    have hcd : c - b < c := by omega
    have hdb : c < c + (5 - d) := by omega
    have hdk' : c + (5 - d) < 5 := by omega
    have h := hR (a - (B + c)) (c - b) c (c + (5 - d)) hbc hcd hdb hdk'
    have e0 : a + (a - (B + c)) * (-1) = B + c := by ring
    have e1 : a + (a - (B + c) + ((c - b : ℕ) : ZMod 5)) * (-1) = B + b := by
      rw [Nat.cast_sub hc.le]; ring
    have e2 : a + (a - (B + c) + (c : ZMod 5)) * (-1) = B := by ring
    have e3 : a + (a - (B + c) + ((c + (5 - d) : ℕ) : ZMod 5)) * (-1) = B + d := by
      rw [Nat.cast_add, Nat.cast_sub hdk.le, show ((5 : ℕ) : ZMod 5) = 0 from rfl]; ring
    dsimp only at h
    rw [e0, e1, e2, e3] at h
    intro ⟨h1, h2, h3, h4⟩
    exact h ⟨h2, h1, h4, h3⟩

/-- **A5 (ii), the leaf form**.  If `z r1 < z r2` strictly (every other tie allowed), the rim depths
are robustly unimodal: no weak alternating quadruple. -/
theorem a5_robUni (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) (a ε : ZMod 5)
    (hcvx : StrictConvex5 R u ρ) (hpat : ApexPat R u a ε)
    (hlt : ⟪R a, u⟫ < ⟪R (a + ε), u⟫) :
    RobUni (fun i : ZMod 5 => ⟪R i, u⟫) := by
  have hu : u ≠ 0 := by
    intro h0
    have h := hcvx 0 2 (by decide) (by decide)
    simp [det3_expand, h0] at h
  rcases hpat with ⟨hε, d1, d2, d3, d4, d5⟩
  let R' : ZMod 5 → ℝ³ := fun k => R (a + k * ε)
  let ρ' : ℝ := if ε = 1 then ρ else -ρ
  have hcvx' : StrictConvex5 R' u ρ' := strictConvex5_reparam R u ρ a ε hcvx hε
  let z' : ZMod 5 → ℝ := fun k => ⟪R' k, u⟫
  have hlt' : z' 0 < z' 1 := by simpa [z', R'] using hlt
  let R'' : ZMod 5 → ℝ³ := fun k => R' (-k)
  have hcvx'' : StrictConvex5 R'' u (-ρ') := by
    have h := strictConvex5_reparam R' u ρ' 0 (-1) hcvx' (Or.inr rfl)
    have hne : (-1 : ZMod 5) ≠ 1 := by decide
    simp only [hne, ↓reduceIte, zero_add, mul_neg_one] at h
    exact h
  have hnb4 : ¬ (max (z' 0) (z' 2) ≤ min (z' 1) (z' 3)) := by
    have hd : DiagFront (R' (4 + 1)) (R' (4 + 3)) (R' (4 + 2)) (R' (4 + 4)) u := by
      simpa only [R', show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 3 : ZMod 5) = 2 from rfl,
        show (4 + 2 : ZMod 5) = 1 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl,
        zero_mul, add_zero, one_mul] using d1
    exact ((diagFront_iff_frontDiag R' u ρ' hcvx' 4).1 hd).not_back hu
  have hnb3 : ¬ (max (z' 0) (z' 2) ≤ min (z' 4) (z' 1)) := by
    have hd : DiagFront (R'' (2 + 1)) (R'' (2 + 3)) (R'' (2 + 2)) (R'' (2 + 4)) u := by
      rw [diagFront_swap_d, diagFront_swap_e]
      simpa only [R'', R', show -(2 + 1 : ZMod 5) = 2 from rfl, show -(2 + 3 : ZMod 5) = 0 from rfl,
        show -(2 + 2 : ZMod 5) = 1 from rfl, show -(2 + 4 : ZMod 5) = 4 from rfl,
        zero_mul, add_zero, one_mul] using d2
    have hnb := ((diagFront_iff_frontDiag R'' u (-ρ') hcvx'' 2).1 hd).not_back hu
    simp only [R'', show -(2 + 1 : ZMod 5) = 2 from rfl, show -(2 + 3 : ZMod 5) = 0 from rfl,
      show -(2 + 2 : ZMod 5) = 1 from rfl, show -(2 + 4 : ZMod 5) = 4 from rfl] at hnb
    change ¬ (max (z' 2) (z' 0) ≤ min (z' 1) (z' 4)) at hnb
    rwa [max_comm, min_comm] at hnb
  have hnb2 : ¬ (max (z' 0) (z' 3) ≤ min (z' 1) (z' 4)) := by
    have hd : DiagFront (R' (2 + 1)) (R' (2 + 3)) (R' (2 + 2)) (R' (2 + 4)) u := by
      rw [diagFront_swap_d, diagFront_swap_e]
      simpa only [R', show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 3 : ZMod 5) = 0 from rfl,
        show (2 + 2 : ZMod 5) = 4 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl,
        zero_mul, add_zero, one_mul] using d3
    have hnb := ((diagFront_iff_frontDiag R' u ρ' hcvx' 2).1 hd).not_back hu
    simp only [show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 3 : ZMod 5) = 0 from rfl,
      show (2 + 2 : ZMod 5) = 4 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl] at hnb
    change ¬ (max (z' 3) (z' 0) ≤ min (z' 4) (z' 1)) at hnb
    rwa [max_comm, min_comm] at hnb
  have hnb1 : ¬ (max (z' 0) (z' 3) ≤ min (z' 2) (z' 4)) := by
    have hd : DiagFront (R'' (4 + 1)) (R'' (4 + 3)) (R'' (4 + 2)) (R'' (4 + 4)) u := by
      rw [diagFront_swap_e]
      simpa only [R'', R', show -(4 + 1 : ZMod 5) = 0 from rfl, show -(4 + 3 : ZMod 5) = 3 from rfl,
        show -(4 + 2 : ZMod 5) = 4 from rfl, show -(4 + 4 : ZMod 5) = 2 from rfl,
        zero_mul, add_zero, one_mul] using d4
    have hnb := ((diagFront_iff_frontDiag R'' u (-ρ') hcvx'' 4).1 hd).not_back hu
    simp only [R'', show -(4 + 1 : ZMod 5) = 0 from rfl, show -(4 + 3 : ZMod 5) = 3 from rfl,
      show -(4 + 2 : ZMod 5) = 4 from rfl, show -(4 + 4 : ZMod 5) = 2 from rfl] at hnb
    change ¬ (max (z' 0) (z' 3) ≤ min (z' 4) (z' 2)) at hnb
    rwa [min_comm] at hnb
  have hnb0 : ¬ (max (z' 2) (z' 4) ≤ min (z' 1) (z' 3)) := by
    have hd : DiagFront (R'' (0 + 1)) (R'' (0 + 3)) (R'' (0 + 2)) (R'' (0 + 4)) u := by
      rw [diagFront_swap_d, diagFront_swap_e]
      simpa only [R'', R', show -(0 + 1 : ZMod 5) = 4 from rfl, show -(0 + 3 : ZMod 5) = 2 from rfl,
        show -(0 + 2 : ZMod 5) = 3 from rfl, show -(0 + 4 : ZMod 5) = 1 from rfl,
        zero_mul, add_zero, one_mul] using d5
    have hnb := ((diagFront_iff_frontDiag R'' u (-ρ') hcvx'' 0).1 hd).not_back hu
    simp only [R'', show -(0 + 1 : ZMod 5) = 4 from rfl, show -(0 + 3 : ZMod 5) = 2 from rfl,
      show -(0 + 2 : ZMod 5) = 3 from rfl, show -(0 + 4 : ZMod 5) = 1 from rfl] at hnb
    change ¬ (max (z' 4) (z' 2) ≤ min (z' 3) (z' 1)) at hnb
    rwa [max_comm, min_comm] at hnb
  apply robUni_of_reparam a ε hε
  intro B b c d hb hc hd hdk
  change ¬ (z' (B + b) ≤ z' B ∧ z' (B + b) ≤ z' (B + c) ∧ z' (B + d) ≤ z' B ∧ z' (B + d) ≤ z' (B + c))
  rintro ⟨h1, h2, h3, h4⟩
  have hB : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
  have hbcd : ((b : ZMod 5) = 1 ∧ (c : ZMod 5) = 2 ∧ (d : ZMod 5) = 3) ∨
      ((b : ZMod 5) = 1 ∧ (c : ZMod 5) = 2 ∧ (d : ZMod 5) = 4) ∨
      ((b : ZMod 5) = 1 ∧ (c : ZMod 5) = 3 ∧ (d : ZMod 5) = 4) ∨
      ((b : ZMod 5) = 2 ∧ (c : ZMod 5) = 3 ∧ (d : ZMod 5) = 4) := by
    rcases (by omega : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4)) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; right; exact ⟨rfl, rfl, rfl⟩
  simp only [max_le_iff, le_min_iff] at hnb0 hnb1 hnb2 hnb3 hnb4
  rcases hB B with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨hb1, hc1, hd1⟩ | ⟨hb1, hc1, hd1⟩ | ⟨hb1, hc1, hd1⟩ | ⟨hb1, hc1, hd1⟩ <;>
    (simp only [hb1, hc1, hd1] at h1 h2 h3 h4) <;>
    (try simp only [zero_add] at h1 h2 h3 h4) <;>
    (try simp only [show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
      show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl,
      show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
      show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl,
      show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
      show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl,
      show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
      show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl] at h1 h2 h3 h4)
  all_goals
    first
    | linarith
    | exact hnb0 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    | exact hnb1 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    | exact hnb2 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    | exact hnb3 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    | exact hnb4 ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **A5 (i)**.  On an apex labelling, injective non-unimodal depths have `z r1 > z r2`, and the edge
sign vector `(z p1 - z p0, ..., z p0 - z p4)` is one of the five staircase types
`T1 (-,+,-,+,-)`, `T5 (-,+,-,+,+)`, `T4 (-,+,-,-,+)`, `T3 (-,+,+,-,+)`, `T2 (-,-,+,-,+)`
(sign `-` means the depth decreases along `p k -> p (k+1)`). -/
theorem a5_two_peaked (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) (a ε : ZMod 5)
    (hcvx : StrictConvex5 R u ρ) (hpat : ApexPat R u a ε)
    (hinj : Function.Injective (depth R u))
    (hnu : ¬ IsCyclicUnimodal (depth R u)) :
    depth R u (a + ε) < depth R u a ∧
      (let e : ℕ → Prop := fun k => depth R u (a + ((k + 1 : ℕ) : ZMod 5) * ε) <
          depth R u (a + (k : ZMod 5) * ε)
       -- e k : the step p k -> p (k+1) decreases (e 4 closes the cycle: p 5 = p 0)
       (e 0 ∧ ¬ e 1 ∧ e 2 ∧ ¬ e 3 ∧ e 4) ∨
       (e 0 ∧ ¬ e 1 ∧ e 2 ∧ ¬ e 3 ∧ ¬ e 4) ∨
       (e 0 ∧ ¬ e 1 ∧ e 2 ∧ e 3 ∧ ¬ e 4) ∨
       (e 0 ∧ ¬ e 1 ∧ ¬ e 2 ∧ e 3 ∧ ¬ e 4) ∨
       (e 0 ∧ e 1 ∧ ¬ e 2 ∧ e 3 ∧ ¬ e 4)) := by
  have hε : ε = 1 ∨ ε = -1 := hpat.1
  let R' : ZMod 5 → ℝ³ := fun k => R (a + k * ε)
  let ρ' : ℝ := if ε = 1 then ρ else -ρ
  have hcvx' : StrictConvex5 R' u ρ' := strictConvex5_reparam R u ρ a ε hcvx hε
  have hinj' : Function.Injective (fun i => ⟪R' i, u⟫) := by
    intro i j hij
    have hij' := hinj hij
    rcases hε with rfl | rfl
    · linear_combination hij'
    · linear_combination -hij'
  have hnu' : ¬ IsCyclicUnimodal (fun i => ⟪R' i, u⟫) := by
    intro hcu
    apply hnu
    refine ⟨hinj, ?_⟩
    have heq : (Finset.univ.filter (fun i : ZMod 5 => ⟪R' (i - 1), u⟫ < ⟪R' i, u⟫ ∧
          ⟪R' (i + 1), u⟫ < ⟪R' i, u⟫)).card =
        (Finset.univ.filter (fun i : ZMod 5 =>
          depth R u (i - 1) < depth R u i ∧ depth R u (i + 1) < depth R u i)).card := by
      refine Finset.card_bij (fun k _ => a + k * ε) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        dsimp only [R', depth] at hk ⊢
        rcases hε with rfl | rfl
        · simp only [mul_one] at hk ⊢
          rw [show a + (k - 1) = a + k - 1 from by ring,
            show a + (k + 1) = a + k + 1 from by ring] at hk
          exact hk
        · rw [show a + (k - 1) * (-1) = a + k * (-1) + 1 from by ring,
              show a + (k + 1) * (-1) = a + k * (-1) - 1 from by ring] at hk
          exact ⟨hk.2, hk.1⟩
      · intro k1 _ k2 _ h
        rcases hε with rfl | rfl
        · linear_combination h
        · linear_combination -h
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        dsimp only [depth] at hi
        rcases hε with rfl | rfl
        · refine ⟨i - a, ?_, by ring⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [R']
          simp only [mul_one]
          rw [show a + (i - a - 1) = i - 1 from by ring,
            show a + (i - a) = i from by ring, show a + (i - a + 1) = i + 1 from by ring]
          exact hi
        · refine ⟨a - i, ?_, by ring⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [R']
          rw [show a + (a - i - 1) * (-1) = i + 1 from by ring,
            show a + (a - i) * (-1) = i from by ring,
            show a + (a - i + 1) * (-1) = i - 1 from by ring]
          exact ⟨hi.2, hi.1⟩
    rw [← heq, hcu.2]
  have sq0 : ∀ M : ZMod 5, subquad R' M 0 = R' (M + 1) := fun M => by simp [subquad]
  have sq1 : ∀ M : ZMod 5, subquad R' M 1 = R' (M + 2) := fun M => by
    simp [subquad, show ((1 : ZMod 4).val : ZMod 5) = 1 from rfl, add_assoc,
      show (1 + 1 : ZMod 5) = 2 from rfl]
  have sq2 : ∀ M : ZMod 5, subquad R' M 2 = R' (M + 3) := fun M => by
    simp [subquad, show ((2 : ZMod 4).val : ZMod 5) = 2 from rfl, add_assoc,
      show (1 + 2 : ZMod 5) = 3 from rfl]
  have sq3 : ∀ M : ZMod 5, subquad R' M 3 = R' (M + 4) := fun M => by
    simp [subquad, show ((3 : ZMod 4).val : ZMod 5) = 3 from rfl, add_assoc,
      show (1 + 3 : ZMod 5) = 4 from rfl]
  have hnot_rob : ¬ RobUni (fun i : ZMod 5 => ⟪R i, u⟫) := by
    intro hrob
    obtain ⟨M, ⟨_, halt⟩, -⟩ := fiveRim_structure R' u ρ' hcvx' hinj' hnu'
    have hrob' : RobUni (fun i : ZMod 5 => ⟪R' i, u⟫) := by
      intro B b c d hb hc hd hdk
      rcases hε with rfl | rfl
      · have h := hrob (a + B) b c d hb hc hd hdk
        simpa only [R', mul_one, add_assoc] using h
      · have hbc : 0 < c - b := Nat.sub_pos_of_lt hc
        have hcd : c - b < c := by omega
        have hdb : c < c + (5 - d) := by omega
        have hdk' : c + (5 - d) < 5 := by omega
        have h := hrob (a + (B + c) * (-1)) (c - b) c (c + (5 - d)) hbc hcd hdb hdk'
        rw [Nat.cast_sub hc.le, Nat.cast_add, Nat.cast_sub hdk.le,
          show ((5 : ℕ) : ZMod 5) = 0 from rfl] at h
        have f0 : a + (B + c) * (-1) + (c - b : ZMod 5) = a + (B + b) * (-1) := by ring
        have f1 : a + (B + c) * (-1) + (c : ZMod 5) = a + B * (-1) := by ring
        have f2 : a + (B + c) * (-1) + (c + (0 - d) : ZMod 5) = a + (B + d) * (-1) := by ring
        rw [f0, f1, f2] at h
        intro ⟨h1, h2, h3, h4⟩
        exact h ⟨h2, h1, h4, h3⟩
    rcases halt with ⟨h1, h2, hodd⟩ | ⟨h1, h2, heven⟩
    · simp only [QuadOddBelowEven, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff] at hodd
      have h := hrob' (M + 1) 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [Nat.cast_one, show ((2 : ℕ) : ZMod 5) = 2 from rfl,
        show ((3 : ℕ) : ZMod 5) = 3 from rfl,
        zmod5_add_eq M 1 1 2 rfl, zmod5_add_eq M 1 2 3 rfl, zmod5_add_eq M 1 3 4 rfl] at h
      exact h ⟨hodd.1.1.le, hodd.2.1.le, hodd.1.2.le, hodd.2.2.le⟩
    · simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff] at heven
      have h := hrob' (M + 2) 1 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [Nat.cast_one, show ((2 : ℕ) : ZMod 5) = 2 from rfl,
        show ((4 : ℕ) : ZMod 5) = 4 from rfl,
        zmod5_add_eq M 2 1 3 rfl, zmod5_add_eq M 2 2 4 rfl, zmod5_add_eq M 2 4 1 rfl] at h
      exact h ⟨heven.1.2.le, heven.2.2.le, heven.1.1.le, heven.2.1.le⟩
  have he0 : depth R u (a + ε) < depth R u a := by
    have hne : a + ε ≠ a := by
      rcases hε with rfl | rfl <;> intro h
      · exact absurd (by linear_combination h : (1 : ZMod 5) = 0) (by decide)
      · exact absurd (by linear_combination h : (-1 : ZMod 5) = 0) (by decide)
    rcases lt_or_gt_of_ne (fun h => hne (hinj h)) with h | h
    · exact h
    · exact absurd (a5_robUni R u ρ a ε hcvx hpat h) hnot_rob
  refine ⟨he0, ?_⟩
  have he0' : ⟪R' 1, u⟫ < ⟪R' 0, u⟫ := by simpa [R', depth] using he0
  obtain ⟨M, ⟨_, halt⟩, -⟩ := fiveRim_structure R' u ρ' hcvx' hinj' hnu'
  dsimp only
  change let e : ℕ → Prop := fun k => ⟪R' ((k + 1 : ℕ) : ZMod 5), u⟫ < ⟪R' (k : ZMod 5), u⟫
    (e 0 ∧ ¬ e 1 ∧ e 2 ∧ ¬ e 3 ∧ e 4) ∨ (e 0 ∧ ¬ e 1 ∧ e 2 ∧ ¬ e 3 ∧ ¬ e 4) ∨
    (e 0 ∧ ¬ e 1 ∧ e 2 ∧ e 3 ∧ ¬ e 4) ∨ (e 0 ∧ ¬ e 1 ∧ ¬ e 2 ∧ e 3 ∧ ¬ e 4) ∨
    (e 0 ∧ e 1 ∧ ¬ e 2 ∧ e 3 ∧ ¬ e 4)
  intro e
  have hM : M = 0 ∨ M = 1 ∨ M = 2 ∨ M = 3 ∨ M = 4 := by
    have hk : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
    exact hk M
  rcases hM with rfl | rfl | rfl | rfl | rfl
  · left
    rcases halt with ⟨hl, hr, _⟩ | ⟨hl, hr, heven⟩
    · exfalso; rw [show (0 - 1 : ZMod 5) = 4 from rfl] at hl; rw [zero_add] at hr; linarith
    · simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, zero_add, max_lt_iff, lt_min_iff] at heven
      rw [zero_add] at hl; rw [show (0 - 1 : ZMod 5) = 4 from rfl] at hr
      refine ⟨he0', ?_, ?_, ?_, ?_⟩ <;> dsimp [e] <;>
        (try rw [Nat.cast_one]) <;>
        (try rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl]) <;>
        (try rw [show ((3 : ℕ) : ZMod 5) = 3 from rfl]) <;>
        (try rw [show ((4 : ℕ) : ZMod 5) = 4 from rfl]) <;>
        (try rw [show (5 : ZMod 5) = 0 from rfl])
      · push Not; linarith [heven.1.1]
      · linarith [heven.2.1]
      · push Not; linarith [heven.2.2]
      · linarith [hr]
  · right; right; right; right
    rcases halt with ⟨hl, hr, _⟩ | ⟨hl, hr, heven⟩
    · exfalso; rw [show (1 - 1 : ZMod 5) = 0 from rfl] at hl; linarith
    · simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (1 + 1 : ZMod 5) = 2 from rfl, show (1 + 2 : ZMod 5) = 3 from rfl,
        show (1 + 3 : ZMod 5) = 4 from rfl, show (1 + 4 : ZMod 5) = 0 from rfl] at heven
      rw [show (1 + 1 : ZMod 5) = 2 from rfl] at hl
      refine ⟨he0', ?_, ?_, ?_, ?_⟩ <;> dsimp [e] <;>
        (try rw [Nat.cast_one]) <;>
        (try rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl]) <;>
        (try rw [show ((3 : ℕ) : ZMod 5) = 3 from rfl]) <;>
        (try rw [show ((4 : ℕ) : ZMod 5) = 4 from rfl]) <;>
        (try rw [show (5 : ZMod 5) = 0 from rfl])
      · linarith [hl]
      · push Not; linarith [heven.1.1]
      · linarith [heven.2.1]
      · push Not; linarith [heven.2.2]
  · right; right; right; left
    rcases halt with ⟨hl, hr, hodd⟩ | ⟨_, _, heven⟩
    · simp only [QuadOddBelowEven, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
        show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl] at hodd
      rw [show (2 - 1 : ZMod 5) = 1 from rfl] at hl; rw [show (2 + 1 : ZMod 5) = 3 from rfl] at hr
      refine ⟨he0', ?_, ?_, ?_, ?_⟩ <;> dsimp [e] <;>
        (try rw [Nat.cast_one]) <;>
        (try rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl]) <;>
        (try rw [show ((3 : ℕ) : ZMod 5) = 3 from rfl]) <;>
        (try rw [show ((4 : ℕ) : ZMod 5) = 4 from rfl]) <;>
        (try rw [show (5 : ZMod 5) = 0 from rfl])
      · push Not; linarith [hl]
      · push Not; linarith [hr]
      · linarith [hodd.1.1]
      · push Not; linarith [hodd.1.2]
    · exfalso
      simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (2 + 1 : ZMod 5) = 3 from rfl, show (2 + 2 : ZMod 5) = 4 from rfl,
        show (2 + 3 : ZMod 5) = 0 from rfl, show (2 + 4 : ZMod 5) = 1 from rfl] at heven
      linarith [he0', heven.1.2]
  · right; right; left
    rcases halt with ⟨_, _, hodd⟩ | ⟨hl, hr, heven⟩
    · exfalso
      simp only [QuadOddBelowEven, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
        show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl] at hodd
      linarith [he0', hodd.1.2]
    · simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (3 + 1 : ZMod 5) = 4 from rfl, show (3 + 2 : ZMod 5) = 0 from rfl,
        show (3 + 3 : ZMod 5) = 1 from rfl, show (3 + 4 : ZMod 5) = 2 from rfl] at heven
      rw [show (3 + 1 : ZMod 5) = 4 from rfl] at hl; rw [show (3 - 1 : ZMod 5) = 2 from rfl] at hr
      refine ⟨he0', ?_, ?_, ?_, ?_⟩ <;> dsimp [e] <;>
        (try rw [Nat.cast_one]) <;>
        (try rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl]) <;>
        (try rw [show ((3 : ℕ) : ZMod 5) = 3 from rfl]) <;>
        (try rw [show ((4 : ℕ) : ZMod 5) = 4 from rfl]) <;>
        (try rw [show (5 : ZMod 5) = 0 from rfl])
      · push Not; linarith [heven.1.1]
      · linarith [hl]
      · linarith [hr]
      · push Not; linarith [heven.2.1]
  · right; left
    rcases halt with ⟨hl, hr, hodd⟩ | ⟨_, _, heven⟩
    · simp only [QuadOddBelowEven, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
        show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl] at hodd
      rw [show (4 - 1 : ZMod 5) = 3 from rfl] at hl; rw [show (4 + 1 : ZMod 5) = 0 from rfl] at hr
      refine ⟨he0', ?_, ?_, ?_, ?_⟩ <;> dsimp [e] <;>
        (try rw [Nat.cast_one]) <;>
        (try rw [show ((2 : ℕ) : ZMod 5) = 2 from rfl]) <;>
        (try rw [show ((3 : ℕ) : ZMod 5) = 3 from rfl]) <;>
        (try rw [show ((4 : ℕ) : ZMod 5) = 4 from rfl]) <;>
        (try rw [show (5 : ZMod 5) = 0 from rfl])
      · push Not; linarith [hodd.1.1]
      · linarith [hodd.2.1]
      · push Not; linarith [hl]
      · push Not; linarith [hr]
    · exfalso
      simp only [QuadEvenBelowOdd, sq0, sq1, sq2, sq3, max_lt_iff, lt_min_iff,
        show (4 + 1 : ZMod 5) = 0 from rfl, show (4 + 2 : ZMod 5) = 1 from rfl,
        show (4 + 3 : ZMod 5) = 2 from rfl, show (4 + 4 : ZMod 5) = 3 from rfl] at heven
      linarith [he0', heven.1.1]

/-- The same with the apex labelling quantified (the form used in cells): any rim with an apex edge
whose depth row `z r1 < z r2` holds. -/
theorem a5_robUni_of_row (R : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 R u ρ) (_hnc : NonCoplanar5 R)
    (hrow : ∀ p : ZMod 5 × ZMod 5, ApexPat R u p.1 p.2 → ⟪R p.1, u⟫ < ⟪R (p.1 + p.2), u⟫)
    : (∃ p : ZMod 5 × ZMod 5, ApexPat R u p.1 p.2) →
      RobUni (fun i : ZMod 5 => ⟪R i, u⟫) := by
  rintro ⟨p, hp⟩
  exact a5_robUni R u ρ p.1 p.2 hcvx hp (hrow p hp)

/-! ### Cell corollary (the closed-cell leaf with one strict row) -/

open Minimality.GenRev Minimality.LexCell in
/-- **A5 cell leaf**.  In a cell `CellAt F U Dn a` whose rim is the 5-cycle `c`, at a closure point `u₀`
(`CellLe F U Dn u₀`) where the rim `x ∘ c` is strictly convex with non-coplanar quartets and has apex
labelling `(a₀, ε)`, the single strict row `z r1 < z r2` at `u₀` gives `LexAny`.  (Closed-cell
route `lexAny_of_closedCell` with `k = 5`; `Type24J54.isRupert_J54_rob5` is the Rupert-level
analogue.) -/
theorem lexAny_of_a5_row {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) {c : ZMod 5 → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) {ρ : ℝ} (hcvx : StrictConvex5 (fun i => x (c i)) u₀ ρ)
    {a₀ ε : ZMod 5} (hpat : ApexPat (fun i => x (c i)) u₀ a₀ ε)
    (hlt : ⟪x (c a₀), u₀⟫ < ⟪x (c (a₀ + ε)), u₀⟫) :
    Gen.LexAny F := by
  have hR := a5_robUni (fun i => x (c i)) u₀ ρ a₀ ε hcvx hpat hlt
  refine ⟨5, inferInstance, c, U, Dn, u₀, a - u₀, 0, by decide, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    rcases (hu.1 t ht).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.symm, Or.inl ?_⟩
      rw [inner_sub_right, ← h]; simpa using ha.1 t ht
  · intro t ht
    rcases (hu.2 t ht).lt_or_eq with h | h
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [h]; simp, Or.inl ?_⟩
      rw [inner_sub_right, h]; have := ha.2 t ht; simp; linarith
  · intro B b c' d' h1 h2 h3 h4
    have hnot := hR B b c' d' h1 h2 h3 h4
    rcases not_and_or.mp hnot with h | h
    · exact Or.inl (Or.inl (sub_pos.mpr (not_le.mp h)))
    · rcases not_and_or.mp h with h | h
      · exact Or.inr (Or.inl (Or.inl (sub_pos.mpr (not_le.mp h))))
      · rcases not_and_or.mp h with h | h
        · exact Or.inr (Or.inr (Or.inl (Or.inl (sub_pos.mpr (not_le.mp h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_pos.mpr (not_le.mp h)))))

end Minimality.A5
