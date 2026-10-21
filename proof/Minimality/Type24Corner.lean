module

public import Minimality.Type24Cap

@[expose] public section

/-!
# Type 24 near the cube corner: the circle of `236` and the exact corner (§17)

`FEWER-FACES-PROOFS.md` §17 (Z, BB) and its addendum (HH), the statements about the circle of `236`
and about exact corners.  The depth at a view `d` is `⟪·, d⟫` (`K`'s own metric); an **exact
corner** (`ExactCorner`) is a point set whose three axes at `1` are pairwise orthogonal (the
diagonal metric `diag (g_a, g_b, g_c)` in the corner frame, `g_a = ⟪e_a, e_a⟫` with
`e_a = x 0 − x 1`, `e_b = x 2 − x 1`, `e_c = x 6 − x 1`).  A 4-corner test *fails* when its
diagonals are weakly depth-separated (`Fails4`); a test that does not fail and has distinct
depths is unimodal (`QuadTest.isRupert`).

* **The circle identity (17.3 (c), every metric)** (`circle_vec`, `circle_depth` and the mirrors):
  `(1 + ω5) d_{T′(2,6)} − d_{S_2} = (1 + ω3)(x 2 − x 6)`, so
  `(1 + ω5)(z0 − z2)_{T′(2,6)} + (z2 − z0)_{S_2} = −(1 + ω3) ⟪x 2 − x 6, x 2 − x 0⟫`.
* **M3 (Theorem 17.7) in BB's off-corner form, at every metric** (`m3_not_both`, mirror
  `m3_not_both6`): if `z3 > z2` at `T′(2,6)`'s view, `z4 > λ z0 + (1 − λ) z6` at `S_2`'s view for
  some `λ ∈ [0, 1]`, and the angle of the triangle `026` at `2` is acute, then `T′(2,6)` (rim
  `(0, 2, 3, q)`) and `S_2` (rim `(0, 2, 6, 4)`) do not both fail.  At an exact corner in case C
  with `b3 ≥ 1` the three conditions hold (`m3_corner`; mirror `m3_corner6` with `c3 ≥ 1`).
* **One ratio on circle 2 (Lemma 17.14 (a))** (`fails4_circle2_iff`): at an exact corner, a test
  at the view `α e_a + β e_b` (`α > 0`) fails iff its rim fails in the pencil `ζ_ν = X_a + ν X_b`,
  `ν = β g_b / (α g_a)` (`PencilFails`).
* **Lemma 17.5 / Corollary 17.17 (closed forms)** (`pencil_0264`, `pencil_02x6`, `pencil_0234`)
  and **17.5 (b)** for `S_0` (`s0_fails_corner`).
* **M1 (Theorem 17.8)** (`m1_corner`): at an exact corner, `T′(2,6)` (rim `(0, 2, 6, 4)`) does not
  fail, or `S_0` (rim `(0, 2, 3, 6)`) does not fail, or WP_2's depth chain
  `z6 < z4 < z0 < z2` holds at a view `e_a + t e_b` with `t` in the face interval `(lo_f, ω3)`
  (case (a), or case (b) with `(H5)`).  The Cramer identities are `m1_link_a`, `m1_link_b`,
  `m3_link`.
* **The T′ pair (Corollary 17.17 (d) with the pair rule)** (`tpair_corner`): with both rims
  `(0, 2, 3, 4)`, `T′(0,6)` and `T′(2,6)` do not both fail when `m / ν34 < ω3 ω4`.
* **M3′ (Theorem 17.18)** (`m3prime_corner`): `S_6` with the rim `(0, 5, 3, 6)` against `T′(2,6)`,
  under (S′), (T′) and (R).
* **Rupert forms**: `QuadTest` bundles the hypotheses of a 4-corner test (rim, hidden points,
  middles, doubles, distinct depths, no horizontal double normal); `isRupert_of_two_tests` turns
  "not both fail" into a passage; `isRupert_m3` (every metric), `isRupert_m3_corner`,
  `isRupert_m3_corner6`, `isRupert_m3prime_corner`, `isRupert_m1_corner` (with Lemma W as a
  hypothesis), `isRupert_tpair_corner` and `isRupert_type24_Q` are the lemmas in Rupert form.

Not formalized: WP as a Rupert item (Lemma W and the face conditions of 17.6: `lo_f` is a
parameter here), the radii of 17.1′, 17.8′, 17.11, 17.12, 17.20, the arc criterion 17.16′ in
general, L7, and the exact-corner lemmas off the corner (only M3 is stated at every metric).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Views on the circle of `236` and on the cap circles -/

/-- The view of `T′(2,6) = 012/236`: oblique `(1, ω3, 0)`. -/
noncomputable def viewT26 (x : Fin 7 → ℝ³) : ℝ³ := (x 0 - x 1) + omega3 x • (x 2 - x 1)

/-- The view of `T′(6,2) = 016/236`: oblique `(1, 0, ω3)`. -/
noncomputable def viewT62 (x : Fin 7 → ℝ³) : ℝ³ := (x 0 - x 1) + omega3 x • (x 6 - x 1)

/-- The view of `T′(0,6) = 012/046`: oblique `(ω4, 1, 0) ∝ (1, 1/ω4, 0)`. -/
noncomputable def viewT06 (x : Fin 7 → ℝ³) : ℝ³ := omega4 x • (x 0 - x 1) + (x 2 - x 1)

/-- **The circle identity (17.3 (c)), vector form.** -/
theorem circle_vec (x : Fin 7 → ℝ³) :
    (1 + omega5 x) • viewT26 x - view2 x = (1 + omega3 x) • (x 2 - x 6) := by
  simp only [viewT26, view2, sideView]; module

/-- **The circle identity (17.3 (c)), every Gram matrix (BB).** -/
theorem circle_depth (x : Fin 7 → ℝ³) :
    (1 + omega5 x) * (⟪x 0, viewT26 x⟫ - ⟪x 2, viewT26 x⟫) + (⟪x 2, view2 x⟫ - ⟪x 0, view2 x⟫) =
      -((1 + omega3 x) * ⟪x 2 - x 6, x 2 - x 0⟫) := by
  have e : (1 + omega5 x) * (⟪x 0, viewT26 x⟫ - ⟪x 2, viewT26 x⟫) +
      (⟪x 2, view2 x⟫ - ⟪x 0, view2 x⟫) =
      ⟪x 0 - x 2, (1 + omega5 x) • viewT26 x - view2 x⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right]; ring
  rw [e, circle_vec, real_inner_smul_right]
  have : ⟪x 0 - x 2, x 2 - x 6⟫ = -⟪x 2 - x 6, x 2 - x 0⟫ := by
    rw [← neg_sub (x 2) (x 0), inner_neg_left, real_inner_comm (x 2 - x 0) (x 2 - x 6)]
  rw [this]; ring

/-- The circle identity, mirror: `(1 + ω4) d_{T′(6,2)} − d_{S_6} = (1 + ω3)(x 6 − x 2)`. -/
theorem circle_vec6 (x : Fin 7 → ℝ³) :
    (1 + omega4 x) • viewT62 x - view6 x = (1 + omega3 x) • (x 6 - x 2) := by
  simp only [viewT62, view6, sideView]; module

theorem circle_depth6 (x : Fin 7 → ℝ³) :
    (1 + omega4 x) * (⟪x 0, viewT62 x⟫ - ⟪x 6, viewT62 x⟫) + (⟪x 6, view6 x⟫ - ⟪x 0, view6 x⟫) =
      -((1 + omega3 x) * ⟪x 6 - x 2, x 6 - x 0⟫) := by
  have e : (1 + omega4 x) * (⟪x 0, viewT62 x⟫ - ⟪x 6, viewT62 x⟫) +
      (⟪x 6, view6 x⟫ - ⟪x 0, view6 x⟫) =
      ⟪x 0 - x 6, (1 + omega4 x) • viewT62 x - view6 x⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right]; ring
  rw [e, circle_vec6, real_inner_smul_right]
  have : ⟪x 0 - x 6, x 6 - x 2⟫ = -⟪x 6 - x 2, x 6 - x 0⟫ := by
    rw [← neg_sub (x 6) (x 0), inner_neg_left, real_inner_comm (x 6 - x 0) (x 6 - x 2)]
  rw [this]; ring

/-! ### M3 at every metric (Theorem 17.7, BB's off-corner form) -/

/-- The convex-combination bound used to exclude a failure pattern. -/
theorem le_comb_of_le {z0 z4 z6 l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (h0 : z4 ≤ z0) (h6 : z4 ≤ z6) :
    z4 ≤ l * z0 + (1 - l) * z6 := by
  nlinarith [mul_le_mul_of_nonneg_left h0 hl0, mul_le_mul_of_nonneg_left h6 (sub_nonneg.mpr hl1)]

/-- **M3, BB's off-corner form (17.7), at every metric.**  Let `1 + ω5 > 0`, `1 + ω3 > 0`, and
- (i) `z3 > z2` at `T′(2,6)`'s view,
- (ii) `z4 > λ z0 + (1 − λ) z6` at `S_2`'s view for some `λ ∈ [0, 1]`,
- (iii) `⟪x 2 − x 6, x 2 − x 0⟫ > 0` (the angle of `026` at `2` is acute).

Then `T′(2,6)` with the rim `(0, 2, 3, q)` and `S_2` with the rim `(0, 2, 6, 4)` do not both fail:
(i) leaves only `z0 ≥ z2` at `T′`, (ii) only `z2 ≥ z0` at `S_2`, and the circle identity
contradicts (iii). -/
theorem m3_not_both {x : Fin 7 → ℝ³} (q : Fin 7) (h5 : 0 < 1 + omega5 x) (h3 : 0 < 1 + omega3 x)
    (hi : ⟪x 2, viewT26 x⟫ < ⟪x 3, viewT26 x⟫) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hii : l * ⟪x 0, view2 x⟫ + (1 - l) * ⟪x 6, view2 x⟫ < ⟪x 4, view2 x⟫)
    (hiii : 0 < ⟪x 2 - x 6, x 2 - x 0⟫) :
    ¬ (Fails4 (x 0) (x 3) (x 2) (x q) (viewT26 x) ∧ Fails4 (x 0) (x 6) (x 2) (x 4) (view2 x)) := by
  rintro ⟨hT, hS⟩
  have hT' : ⟪x 2, viewT26 x⟫ ≤ ⟪x 0, viewT26 x⟫ := by
    rcases hT with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff] at h
    · linarith [h.2.1]
    · exact h.1.1
  have hS' : ⟪x 0, view2 x⟫ ≤ ⟪x 2, view2 x⟫ := by
    rcases hS with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff] at h
    · exact h.1.1
    · linarith [le_comb_of_le hl0 hl1 h.2.1 h.2.2]
  have e := circle_depth x
  nlinarith [mul_nonneg h5.le (sub_nonneg.mpr hT'), mul_pos h3 hiii]

/-- **M3, mirror (arc 6), at every metric**: `T′(6,2)` with the rim `(0, 6, 3, q)` and `S_6` with
the rim `(0, 5, 2, 6)` do not both fail when `z3 > z6` at `T′(6,2)`'s view,
`z5 > λ z0 + (1 − λ) z2` at `S_6`'s view and the angle of `026` at `6` is acute. -/
theorem m3_not_both6 {x : Fin 7 → ℝ³} (q : Fin 7) (h4 : 0 < 1 + omega4 x) (h3 : 0 < 1 + omega3 x)
    (hi : ⟪x 6, viewT62 x⟫ < ⟪x 3, viewT62 x⟫) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hii : l * ⟪x 0, view6 x⟫ + (1 - l) * ⟪x 2, view6 x⟫ < ⟪x 5, view6 x⟫)
    (hiii : 0 < ⟪x 6 - x 2, x 6 - x 0⟫) :
    ¬ (Fails4 (x 0) (x 3) (x 6) (x q) (viewT62 x) ∧ Fails4 (x 0) (x 2) (x 6) (x 5) (view6 x)) := by
  rintro ⟨hT, hS⟩
  have hT' : ⟪x 6, viewT62 x⟫ ≤ ⟪x 0, viewT62 x⟫ := by
    rcases hT with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff] at h
    · linarith [h.2.1]
    · exact h.1.1
  have hS' : ⟪x 0, view6 x⟫ ≤ ⟪x 6, view6 x⟫ := by
    rcases hS with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff] at h
    · exact h.1.1
    · linarith [le_comb_of_le hl0 hl1 h.2.1 h.2.2]
  have e := circle_depth6 x
  nlinarith [mul_nonneg h4.le (sub_nonneg.mpr hT'), mul_pos h3 hiii]

/-- The Cramer identity of M3 at the corner (17.7):
`(1 + ω5)(g_a − ω3 g_b) + ((ω3 ω5 − 1) g_b − (1 + ω5) g_a) = −(1 + ω3) g_b`. -/
theorem m3_link (w3 w5 ga gb : ℝ) :
    (1 + w5) * (ga - w3 * gb) + ((w3 * w5 - 1) * gb - (1 + w5) * ga) = -((1 + w3) * gb) := by
  ring

/-! ### The exact corner -/

/-- **An exact corner**: the axes `x 0 − x 1`, `x 2 − x 1`, `x 6 − x 1` at `1` are pairwise
orthogonal (`c = 0`; the metric is `diag (g_a, g_b, g_c)` in the corner frame). -/
def ExactCorner (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 0 - x 1, x 2 - x 1⟫ = 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ = 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ = 0

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

theorem oblX0_zero' : oblX0 x 0 = 1 := by
  simp only [oblX0]; exact div_self T.det_ne

theorem oblX2_two : oblX2 x 2 = 1 := by
  simp only [oblX2]; exact div_self T.det_ne

theorem oblX6_six : oblX6 x 6 = 1 := by
  simp only [oblX6]; exact div_self T.det_ne

omit T in
theorem oblX0_two : oblX0 x 2 = 0 := by simp only [oblX0, vol3]; ring_nf

omit T in
theorem oblX0_six : oblX0 x 6 = 0 := by simp only [oblX0, vol3]; ring_nf

omit T in
theorem oblX2_zero' : oblX2 x 0 = 0 := by simp only [oblX2, vol3]; ring_nf

/-- The depth of `x v` at a view, through the oblique coordinates at `1`. -/
theorem inner_obl (v : Fin 7) (w : ℝ³) :
    ⟪x v, w⟫ = ⟪x 1, w⟫ + oblX0 x v * ⟪x 0 - x 1, w⟫ + oblX2 x v * ⟪x 2 - x 1, w⟫ +
      oblX6 x v * ⟪x 6 - x 1, w⟫ := by
  conv_lhs => rw [T.rep v]
  simp only [inner_add_left, real_inner_smul_left]

/-- **Depth at an exact corner**: at the view `α e_a + β e_b + γ e_c`,
`z_v = z_1 + α g_a X_a(v) + β g_b X_b(v) + γ g_c X_c(v)`. -/
theorem depth_corner (hE : ExactCorner x) (v : Fin 7) (α β γ : ℝ) :
    ⟪x v, α • (x 0 - x 1) + β • (x 2 - x 1) + γ • (x 6 - x 1)⟫ =
      ⟪x 1, α • (x 0 - x 1) + β • (x 2 - x 1) + γ • (x 6 - x 1)⟫ +
        α * ⟪x 0 - x 1, x 0 - x 1⟫ * oblX0 x v + β * ⟪x 2 - x 1, x 2 - x 1⟫ * oblX2 x v +
        γ * ⟪x 6 - x 1, x 6 - x 1⟫ * oblX6 x v := by
  obtain ⟨e1, e2, e3⟩ := hE
  have e1' : ⟪x 2 - x 1, x 0 - x 1⟫ = 0 := by rw [real_inner_comm]; exact e1
  have e2' : ⟪x 6 - x 1, x 0 - x 1⟫ = 0 := by rw [real_inner_comm]; exact e2
  have e3' : ⟪x 6 - x 1, x 2 - x 1⟫ = 0 := by rw [real_inner_comm]; exact e3
  rw [T.inner_obl v]
  simp only [inner_add_right, real_inner_smul_right, e1, e2, e3, e1', e2', e3']
  ring

theorem ga_pos : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ :=
  real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))

theorem gb_pos : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
  real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))

theorem gc_pos : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ :=
  real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))

omit T in
theorem viewT26_eq : viewT26 x = (1 : ℝ) • (x 0 - x 1) + omega3 x • (x 2 - x 1) +
    (0 : ℝ) • (x 6 - x 1) := by
  simp only [viewT26]; module

omit T in
theorem viewT62_eq : viewT62 x = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) +
    omega3 x • (x 6 - x 1) := by
  simp only [viewT62]; module

omit T in
theorem viewT06_eq : viewT06 x = omega4 x • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) +
    (0 : ℝ) • (x 6 - x 1) := by
  simp only [viewT06]; module

omit T in
theorem view2_eq : view2 x = (1 + omega5 x) • (x 0 - x 1) +
    (omega5 x * omega3 x - 1) • (x 2 - x 1) + (1 + omega3 x) • (x 6 - x 1) := by
  simp only [view2, sideView]; module

omit T in
theorem view6_eq : view6 x = (1 + omega4 x) • (x 0 - x 1) + (1 + omega3 x) • (x 2 - x 1) +
    (omega4 x * omega3 x - 1) • (x 6 - x 1) := by
  rfl

omit T in
theorem view0_eq : view0 x = (omega5 x * omega4 x - 1) • (x 0 - x 1) +
    (1 + omega5 x) • (x 2 - x 1) + (1 + omega4 x) • (x 6 - x 1) := by
  simp only [view0, sideView]; module

omit T in
/-- `⟪x 2 − x 6, x 2 − x 0⟫ = g_b` at an exact corner. -/
theorem angle2_corner (hE : ExactCorner x) :
    ⟪x 2 - x 6, x 2 - x 0⟫ = ⟪x 2 - x 1, x 2 - x 1⟫ := by
  obtain ⟨e1, e2, e3⟩ := hE
  have h1 : x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) := by abel
  have h2 : x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) := by abel
  rw [h1, h2]
  generalize x 0 - x 1 = a at e1 e2 ⊢
  generalize x 2 - x 1 = b at e1 e3 ⊢
  generalize x 6 - x 1 = c at e2 e3 ⊢
  have e1' : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact e1
  have e3' : ⟪c, b⟫ = 0 := by rw [real_inner_comm]; exact e3
  simp only [inner_sub_left, inner_sub_right, e1', e3']
  have e2' : ⟪c, a⟫ = 0 := by rw [real_inner_comm]; exact e2
  rw [e2']; ring

omit T in
/-- `⟪x 6 − x 2, x 6 − x 0⟫ = g_c` at an exact corner. -/
theorem angle6_corner (hE : ExactCorner x) :
    ⟪x 6 - x 2, x 6 - x 0⟫ = ⟪x 6 - x 1, x 6 - x 1⟫ := by
  obtain ⟨e1, e2, e3⟩ := hE
  have h1 : x 6 - x 2 = (x 6 - x 1) - (x 2 - x 1) := by abel
  have h2 : x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) := by abel
  rw [h1, h2]
  generalize x 0 - x 1 = a at e1 e2 ⊢
  generalize x 2 - x 1 = b at e1 e3 ⊢
  generalize x 6 - x 1 = c at e2 e3 ⊢
  have e1' : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact e1
  have e2' : ⟪c, a⟫ = 0 := by rw [real_inner_comm]; exact e2
  have e3' : ⟪c, b⟫ = 0 := by rw [real_inner_comm]; exact e3
  simp only [inner_sub_left, inner_sub_right, e1', e2', e3]
  ring

/-- **M3 at the exact corner (Theorem 17.7, explicit form of (T)).**  In case C (here: `ω3, ω4,
ω5 > 0` and `ω3 ω5 > 1`), at an exact corner, with `b3 ≥ 1`: `T′(2,6)` with the rim
`(0, 2, 3, q)` (`c3 > 1` keeps `3`) and `S_2` with the rim `(0, 2, 6, 4)` do not both fail. -/
theorem m3_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h35 : 1 < omega3 x * omega5 x) (hb3 : 1 ≤ oblX2 x 3) (q : Fin 7) :
    ¬ (Fails4 (x 0) (x 3) (x 2) (x q) (viewT26 x) ∧ Fails4 (x 0) (x 6) (x 2) (x 4) (view2 x)) := by
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have dT := fun v => T.depth_corner hE v 1 (omega3 x) 0
  have dS := fun v => T.depth_corner hE v (1 + omega5 x) (omega5 x * omega3 x - 1)
    (1 + omega3 x)
  rw [← Type24.viewT26_eq] at dT
  rw [← Type24.view2_eq] at dS
  have a3 := T.X0_pos (v := 3) (by decide)
  have a4 := T.X0_pos (v := 4) (by decide)
  have b4 := T.X2_pos (v := 4) (by decide)
  have c4 := T.X6_pos (v := 4) (by decide)
  have e4 := T.eq4
  have hβ : 0 < omega5 x * omega3 x - 1 := by linarith [mul_comm (omega3 x) (omega5 x)]
  rcases le_or_gt (oblX0 x 4) 1 with ha4 | ha4
  · refine m3_not_both q (by linarith) (by linarith) ?_ a4.le ha4 ?_ ?_
    · rw [dT 2, dT 3, Type24.oblX0_two, T.oblX2_two]
      nlinarith [mul_nonneg (mul_pos h3 gb).le (show 0 ≤ oblX2 x 3 - 1 by linarith),
        mul_pos ga a3]
    · rw [dS 0, dS 4, dS 6, T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
        Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six]
      have : 0 < (omega5 x * omega3 x - 1) * ⟪x 2 - x 1, x 2 - x 1⟫ * oblX2 x 4 +
          (1 + omega3 x) * ⟪x 6 - x 1, x 6 - x 1⟫ * (omega4 x * oblX2 x 4) := by positivity
      have hc4 : oblX6 x 4 = 1 - oblX0 x 4 + omega4 x * oblX2 x 4 := by linarith
      rw [hc4]
      linarith
    · rw [Type24.angle2_corner hE]; exact gb
  · refine m3_not_both q (l := 1) (by linarith) (by linarith) ?_ zero_le_one le_rfl ?_ ?_
    · rw [dT 2, dT 3, Type24.oblX0_two, T.oblX2_two]
      nlinarith [mul_nonneg (mul_pos h3 gb).le (show 0 ≤ oblX2 x 3 - 1 by linarith),
        mul_pos ga a3]
    · rw [dS 0, dS 4, dS 6, T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
        Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six]
      have : 0 < (1 + omega5 x) * ⟪x 0 - x 1, x 0 - x 1⟫ * (oblX0 x 4 - 1) +
          (omega5 x * omega3 x - 1) * ⟪x 2 - x 1, x 2 - x 1⟫ * oblX2 x 4 +
          (1 + omega3 x) * ⟪x 6 - x 1, x 6 - x 1⟫ * oblX6 x 4 := by
        have : 0 < oblX0 x 4 - 1 := by linarith
        positivity
      nlinarith
    · rw [Type24.angle2_corner hE]; exact gb

/-- **M3 at the exact corner, mirror (arc 6)**, with `c3 ≥ 1`: `T′(6,2)` with the rim
`(0, 6, 3, q)` and `S_6` with the rim `(0, 5, 2, 6)` do not both fail. -/
theorem m3_corner6 (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h34 : 1 < omega3 x * omega4 x) (hc3 : 1 ≤ oblX6 x 3) (q : Fin 7) :
    ¬ (Fails4 (x 0) (x 3) (x 6) (x q) (viewT62 x) ∧ Fails4 (x 0) (x 2) (x 6) (x 5) (view6 x)) := by
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have dT := fun v => T.depth_corner hE v 1 0 (omega3 x)
  have dS := fun v => T.depth_corner hE v (1 + omega4 x) (1 + omega3 x)
    (omega4 x * omega3 x - 1)
  rw [← Type24.viewT62_eq] at dT
  rw [← Type24.view6_eq] at dS
  have a3 := T.X0_pos (v := 3) (by decide)
  have a5 := T.X0_pos (v := 5) (by decide)
  have b5 := T.X2_pos (v := 5) (by decide)
  have c5 := T.X6_pos (v := 5) (by decide)
  have e5 := T.eq5
  have hγ : 0 < omega4 x * omega3 x - 1 := by linarith [mul_comm (omega3 x) (omega4 x)]
  have hi : ⟪x 6, viewT62 x⟫ < ⟪x 3, viewT62 x⟫ := by
    rw [dT 6, dT 3, Type24.oblX0_six, T.oblX6_six]
    nlinarith [mul_nonneg (mul_pos h3 gc).le (show 0 ≤ oblX6 x 3 - 1 by linarith),
      mul_pos ga a3]
  have hiii : 0 < ⟪x 6 - x 2, x 6 - x 0⟫ := by rw [Type24.angle6_corner hE]; exact gc
  rcases le_or_gt (oblX0 x 5) 1 with ha5 | ha5
  · refine m3_not_both6 q (by linarith) (by linarith) hi a5.le ha5 ?_ hiii
    rw [dS 0, dS 5, dS 2, T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
      Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two]
    have : 0 < (1 + omega3 x) * ⟪x 2 - x 1, x 2 - x 1⟫ * (omega5 x * oblX6 x 5) +
        (omega4 x * omega3 x - 1) * ⟪x 6 - x 1, x 6 - x 1⟫ * oblX6 x 5 := by positivity
    have hb5 : oblX2 x 5 = 1 - oblX0 x 5 + omega5 x * oblX6 x 5 := by linarith
    rw [hb5]
    linarith
  · refine m3_not_both6 q (l := 1) (by linarith) (by linarith) hi zero_le_one le_rfl ?_ hiii
    rw [dS 0, dS 5, dS 2, T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
      Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two]
    have : 0 < (1 + omega4 x) * ⟪x 0 - x 1, x 0 - x 1⟫ * (oblX0 x 5 - 1) +
        (1 + omega3 x) * ⟪x 2 - x 1, x 2 - x 1⟫ * oblX2 x 5 +
        (omega4 x * omega3 x - 1) * ⟪x 6 - x 1, x 6 - x 1⟫ * oblX6 x 5 := by
      have : 0 < oblX0 x 5 - 1 := by linarith
      positivity
    linarith

/-! ### One ratio on circle 2 (Lemma 17.14 (a)) and the closed forms (17.5, 17.17) -/

/-- The pencil `ζ_ν = X_a + ν X_b` on circle 2. -/
noncomputable def pencil2 (x : Fin 7 → ℝ³) (ν : ℝ) (v : Fin 7) : ℝ := oblX0 x v + ν * oblX2 x v

omit T in
/-- The failure of a rim with diagonals `{d₀, d₁}`, `{e₀, e₁}` in the pencil. -/
def PencilFails (x : Fin 7 → ℝ³) (ν : ℝ) (d₀ d₁ e₀ e₁ : Fin 7) : Prop :=
  max (pencil2 x ν d₀) (pencil2 x ν d₁) ≤ min (pencil2 x ν e₀) (pencil2 x ν e₁) ∨
    max (pencil2 x ν e₀) (pencil2 x ν e₁) ≤ min (pencil2 x ν d₀) (pencil2 x ν d₁)

/-- **Lemma 17.14 (a), circle 2.**  At an exact corner, a test at the view `α e_a + β e_b`
(`α > 0`) fails iff its rim fails in the pencil, `ν = β g_b / (α g_a)`: one ratio. -/
theorem fails4_circle2_iff (hE : ExactCorner x) {α β : ℝ} (hα : 0 < α) (d₀ d₁ e₀ e₁ : Fin 7) :
    Fails4 (x d₀) (x d₁) (x e₀) (x e₁) (α • (x 0 - x 1) + β • (x 2 - x 1)) ↔
      PencilFails x (β * ⟪x 2 - x 1, x 2 - x 1⟫ / (α * ⟪x 0 - x 1, x 0 - x 1⟫)) d₀ d₁ e₀ e₁ := by
  have ga := T.ga_pos
  have hK : 0 < α * ⟪x 0 - x 1, x 0 - x 1⟫ := mul_pos hα ga
  have hu : α • (x 0 - x 1) + β • (x 2 - x 1) =
      α • (x 0 - x 1) + β • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    rw [zero_smul, add_zero]
  have hp : ∀ v : Fin 7, ⟪x v, α • (x 0 - x 1) + β • (x 2 - x 1)⟫ =
      ⟪x 1, α • (x 0 - x 1) + β • (x 2 - x 1)⟫ + α * ⟪x 0 - x 1, x 0 - x 1⟫ *
        pencil2 x (β * ⟪x 2 - x 1, x 2 - x 1⟫ / (α * ⟪x 0 - x 1, x 0 - x 1⟫)) v := by
    intro v
    rw [hu, T.depth_corner hE v]
    simp only [pencil2]
    field_simp
    ring
  have key : ∀ v w : Fin 7, ⟪x v, α • (x 0 - x 1) + β • (x 2 - x 1)⟫ ≤
      ⟪x w, α • (x 0 - x 1) + β • (x 2 - x 1)⟫ ↔
      pencil2 x (β * ⟪x 2 - x 1, x 2 - x 1⟫ / (α * ⟪x 0 - x 1, x 0 - x 1⟫)) v ≤
        pencil2 x (β * ⟪x 2 - x 1, x 2 - x 1⟫ / (α * ⟪x 0 - x 1, x 0 - x 1⟫)) w := by
    intro v w
    rw [hp v, hp w, add_le_add_iff_left, mul_le_mul_iff_right₀ hK]
  simp only [Fails4, PencilFails, max_le_iff, le_min_iff, key]

omit T in
/-- **17.5 (a), 17.17 (b)**: the rim `(0, 2, 6, v)` fails in the pencil at `ν > 0` iff `ν ≥ 1` and
`ζ_ν(v) ≥ 1` (`F = [max (1, r_v), ∞)`). -/
theorem pencil_0264 (hT : Type24 x) {ν : ℝ} (hν : 0 < ν) (v : Fin 7) :
    PencilFails x ν 0 6 2 v ↔ 1 ≤ ν ∧ 1 ≤ pencil2 x ν v := by
  have z0 : pencil2 x ν 0 = 1 := by simp only [pencil2, hT.oblX0_zero', Type24.oblX2_zero']; ring
  have z2 : pencil2 x ν 2 = ν := by simp only [pencil2, Type24.oblX0_two, hT.oblX2_two]; ring
  have z6 : pencil2 x ν 6 = 0 := by simp only [pencil2, Type24.oblX0_six, Type24.oblX2_six]; ring
  simp only [PencilFails, z0, z2, z6, le_min_iff, max_le_iff]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
    · exact ⟨h1, h3⟩
    · linarith
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨⟨h1, by linarith⟩, h2, by linarith⟩

omit T in
/-- **17.17 (c)**: the rim `(0, 2, v, 6)` with `ζ_ν(v) ≥ 0` fails in the pencil iff `ν ≤ 1` and
`ν ≤ ζ_ν(v)` (`F = (0, min (1, ν_v2)]`). -/
theorem pencil_02x6 (hT : Type24 x) {ν : ℝ} (v : Fin 7) (hv : 0 ≤ pencil2 x ν v) :
    PencilFails x ν 0 v 2 6 ↔ ν ≤ 1 ∧ ν ≤ pencil2 x ν v := by
  have z0 : pencil2 x ν 0 = 1 := by simp only [pencil2, hT.oblX0_zero', Type24.oblX2_zero']; ring
  have z2 : pencil2 x ν 2 = ν := by simp only [pencil2, Type24.oblX0_two, hT.oblX2_two]; ring
  have z6 : pencil2 x ν 6 = 0 := by simp only [pencil2, Type24.oblX0_six, Type24.oblX2_six]; ring
  simp only [PencilFails, z0, z2, z6, le_min_iff, max_le_iff]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
    · linarith
    · exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨⟨h1, zero_le_one⟩, h2, hv⟩

/-- **17.5 (a) at the exact corner**: `T′(2,6)` with the rim `(0, 2, 6, 4)` fails only where
`g_a ≤ ω3 g_b` (`μ_b ≥ 1`) and `g_a ≤ g_a a4 + ω3 g_b b4` (`μ_b ≥ r4`). -/
theorem t26_fails_corner (hE : ExactCorner x) (h3 : 0 < omega3 x)
    (hF : Fails4 (x 0) (x 6) (x 2) (x 4) (viewT26 x)) :
    ⟪x 0 - x 1, x 0 - x 1⟫ ≤ omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ ∧
      ⟪x 0 - x 1, x 0 - x 1⟫ ≤ ⟪x 0 - x 1, x 0 - x 1⟫ * oblX0 x 4 +
        omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ * oblX2 x 4 := by
  have gb := T.gb_pos
  have dT := fun v => T.depth_corner hE v 1 (omega3 x) 0
  rw [← Type24.viewT26_eq] at dT
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dT 0, dT 6, dT 2, dT 4] at h <;>
    simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero, Type24.oblX0_six,
      Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two] at h
  · constructor <;> linarith [h.1.1, h.1.2]
  · nlinarith [h.2.1, mul_pos h3 gb]

/-- **17.5 (b) at the exact corner**: `S_0 = 025/046` with the rim `(0, 2, 3, 6)` fails only where
`z0 ≥ z2` at its view: `(1 + ω5) g_b ≤ (ω4 ω5 − 1) g_a` (`μ_b ≤ τ_b`); the pattern
`{2, 6} ≥ {0, 3}` is impossible since `z3 > min (z2, z6)` (`b3 + c3 = 1 + ω3 a3 > 1`). -/
theorem s0_fails_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x)
    (hF : Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x)) :
    (1 + omega5 x) * ⟪x 2 - x 1, x 2 - x 1⟫ ≤
      (omega5 x * omega4 x - 1) * ⟪x 0 - x 1, x 0 - x 1⟫ := by
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have dS := fun v => T.depth_corner hE v (omega5 x * omega4 x - 1) (1 + omega5 x)
    (1 + omega4 x)
  rw [← Type24.view0_eq] at dS
  have a3 := T.X0_pos (v := 3) (by decide)
  have b3 := T.X2_pos (v := 3) (by decide)
  have c3 := T.X6_pos (v := 3) (by decide)
  have e3 := T.eq3
  have hα : 0 < omega5 x * omega4 x - 1 := by linarith [mul_comm (omega4 x) (omega5 x)]
  set α := (omega5 x * omega4 x - 1) * ⟪x 0 - x 1, x 0 - x 1⟫ with hαd
  set β := (1 + omega5 x) * ⟪x 2 - x 1, x 2 - x 1⟫ with hβd
  set γ := (1 + omega4 x) * ⟪x 6 - x 1, x 6 - x 1⟫ with hγd
  have hα0 : 0 < α := mul_pos hα ga
  have hβ0 : 0 < β := mul_pos (by linarith) gb
  have hγ0 : 0 < γ := mul_pos (by linarith) gc
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dS 0, dS 3, dS 2, dS 6] at h <;>
    simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero, Type24.oblX0_six,
      Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two] at h
  · -- `{0, 3}` below `{2, 6}`: `z3 ≤ min (z2, z6)` is impossible
    exfalso
    obtain ⟨-, h32, h36⟩ := h
    have hbc : oblX2 x 3 + oblX6 x 3 = 1 + omega3 x * oblX0 x 3 := by linarith
    have hpos : 0 < α * oblX0 x 3 := mul_pos hα0 a3
    have hω : 0 < omega3 x * oblX0 x 3 := mul_pos h3 a3
    rcases le_total β γ with hbg | hbg
    · nlinarith [mul_le_mul_of_nonneg_left hbg c3.le, mul_pos hβ0 hω]
    · nlinarith [mul_le_mul_of_nonneg_left hbg b3.le, mul_pos hγ0 hω]
  · linarith [h.1.1]

omit T in
/-- The Cramer identities of M1 (17.8): `T′(2,6)` against WP_2 below, and WP_2 above against
`S_0` (with `r4 = (1 − a4)/b4`). -/
theorem m1_link_a (w3 a4 b4 ga gb : ℝ) :
    b4 * (ga - w3 * gb) + ((a4 - 1) * ga + w3 * b4 * gb) = (a4 + b4 - 1) * ga := by ring

omit T in
theorem m1_link_b (w4 w5 lo r4 ga gb : ℝ) :
    (1 + w5) * (lo * gb - r4 * ga) + lo * ((w4 * w5 - 1) * ga - (1 + w5) * gb) =
      (lo * (w4 * w5 - 1) - r4 * (1 + w5)) * ga := by ring

/-- **WP_2's depth chain** at the view `e_a + t e_b` (the window-edge pattern on arc 2,
15.13 (b)): `z6 < z4 < z0 < z2`. -/
def WPChain2 (x : Fin 7 → ℝ³) (t : ℝ) : Prop :=
  ⟪x 6, (x 0 - x 1) + t • (x 2 - x 1)⟫ < ⟪x 4, (x 0 - x 1) + t • (x 2 - x 1)⟫ ∧
    ⟪x 4, (x 0 - x 1) + t • (x 2 - x 1)⟫ < ⟪x 0, (x 0 - x 1) + t • (x 2 - x 1)⟫ ∧
    ⟪x 0, (x 0 - x 1) + t • (x 2 - x 1)⟫ < ⟪x 2, (x 0 - x 1) + t • (x 2 - x 1)⟫

/-- **M1 (Theorem 17.8, the chain `T′ → WP → S_0`), at the exact corner.**  In case C (here:
`ω3, ω4, ω5 > 0`, `ω4 ω5 > 1`), let `lo ∈ (0, ω3)` be the lower end of WP_2's face interval
(17.6: `lo_f`).  Suppose
- (a) `τ_b < 1` or `τ_b < r4` (`τ_b = ω3 (ω4 ω5 − 1)/(1 + ω5)`, `r4 = (1 − a4)/b4`; stated
  multiplied out), or
- (b) `r4 > 1` and `(H5)`: `lo (ω4 ω5 − 1) < r4 (1 + ω5)` (multiplied out).

Then `T′(2,6)` with the rim `(0, 2, 6, 4)` does not fail, or WP_2's depth chain holds at a view
`e_a + t e_b` with `lo < t < ω3`, or `S_0` with the rim `(0, 2, 3, 6)` does not fail.  (Case (a)
never needs WP.) -/
theorem m1_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x) {lo : ℝ} (hlo : 0 < lo)
    (hlo3 : lo < omega3 x)
    (hab : (omega3 x * (omega4 x * omega5 x - 1) < 1 + omega5 x ∨
        omega3 x * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)) ∨
      (oblX2 x 4 < 1 - oblX0 x 4 ∧
        lo * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x))) :
    ¬ Fails4 (x 0) (x 6) (x 2) (x 4) (viewT26 x) ∨ (∃ t, lo < t ∧ t < omega3 x ∧ WPChain2 x t) ∨
      ¬ Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hT, hW, hS⟩ := hcon
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have a4 := T.X0_pos (v := 4) (by decide)
  have b4 := T.X2_pos (v := 4) (by decide)
  obtain ⟨t1, t2⟩ := T.t26_fails_corner hE h3 hT
  have s := T.s0_fails_corner hE h3 h4 h5 h45 hS
  have hm : omega5 x * omega4 x = omega4 x * omega5 x := mul_comm _ _
  rw [hm] at s
  set ga' := ⟪x 0 - x 1, x 0 - x 1⟫
  set gb' := ⟪x 2 - x 1, x 2 - x 1⟫
  have h5' : 0 < 1 + omega5 x := by linarith
  -- `ω3 × (S_0)`: `(1 + ω5) ω3 g_b ≤ ω3 (ω4 ω5 − 1) g_a`
  have s' := mul_le_mul_of_nonneg_left s h3.le
  rcases hab with (ha | ha) | ⟨hr4, hH5⟩
  · -- (a), `τ_b < 1`
    nlinarith [mul_lt_mul_of_pos_right ha ga, mul_le_mul_of_nonneg_left t1 h5'.le]
  · -- (a), `τ_b < r4`
    have k1 : (1 - oblX0 x 4) * ga' ≤ omega3 x * gb' * oblX2 x 4 := by linarith
    nlinarith [mul_lt_mul_of_pos_right ha ga, mul_le_mul_of_nonneg_left k1 h5'.le,
      mul_le_mul_of_nonneg_left s' b4.le]
  · -- (b): WP_2 holds at some `t` in the face interval
    have k1 : (1 - oblX0 x 4) * ga' ≤ omega3 x * gb' * oblX2 x 4 := by linarith
    have hgt : ga' < omega3 x * gb' := by nlinarith [mul_lt_mul_of_pos_right hr4 ga]
    have hlo' : lo * oblX2 x 4 * gb' < (1 - oblX0 x 4) * ga' := by
      have k2 := mul_le_mul_of_nonneg_left s (mul_pos hlo b4).le
      nlinarith [mul_lt_mul_of_pos_right hH5 ga]
    set U := min (omega3 x) ((1 - oblX0 x 4) * ga' / (oblX2 x 4 * gb')) with hU
    set L := max lo (ga' / gb') with hL
    have hLU : L < U := by
      rw [hL, hU, max_lt_iff, lt_min_iff, lt_min_iff, div_lt_iff₀ gb,
        lt_div_iff₀ (mul_pos b4 gb), div_lt_div_iff₀ gb (mul_pos b4 gb)]
      refine ⟨⟨hlo3, by nlinarith⟩, by linarith, ?_⟩
      nlinarith [mul_lt_mul_of_pos_right hr4 (mul_pos ga gb)]
    obtain ⟨t, htL, htU⟩ := exists_between hLU
    rw [hL, max_lt_iff, div_lt_iff₀ gb] at htL
    rw [hU, lt_min_iff, lt_div_iff₀ (mul_pos b4 gb)] at htU
    have dW := fun v => T.depth_corner hE v 1 t 0
    have hw : (1 : ℝ) • (x 0 - x 1) + t • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) =
        (x 0 - x 1) + t • (x 2 - x 1) := by module
    rw [hw] at dW
    have ht0 : 0 < t := by nlinarith
    have chain : WPChain2 x t := by
      simp only [WPChain2]
      rw [dW 6, dW 4, dW 0, dW 2]
      simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
        Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two,
        Type24.oblX6_two]
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_pos ga a4, mul_pos (mul_pos ht0 gb) b4]
      · nlinarith
      · nlinarith
    exact hW t htL.1 htU.1 chain

/-! ### The T′ pair (Corollary 17.17 (d), the pair rule) -/

omit T in
/-- The Cramer identity of the T′ pair (17.17): at the views `(1, t, 0)`,
`t2 B (z3 − z4)_{t1} + t1 (b3 − b4)(z_p − z_q)_{t2} = g_a [t1 (b3 − b4) A − t2 B (a4 − a3)]`
with `(z_p − z_q)_{t2} = g_a A − t2 g_b B`. -/
theorem tpair_link (t1 t2 a3 a4 b3 b4 A B ga gb : ℝ) :
    t2 * B * (ga * (a3 - a4) + t1 * gb * (b3 - b4)) + t1 * (b3 - b4) * (ga * A - t2 * gb * B) =
      ga * (t1 * (b3 - b4) * A - t2 * B * (a4 - a3)) := by ring

omit T in
/-- The pair rule for the rim `(0, 2, 3, 4)` in the pencil, real form: `ζ0 = 1`, `ζ2 = ν`,
`ζ3 = a3 + ν b3`, `ζ4 = a4 + ν b4`. -/
theorem tpair_real {a3 a4 b3 b4 ν K : ℝ} (hν : 0 < ν) (hK : 1 < K) (hb4 : 0 < b4)
    (hD : b4 < b3) (hle : a4 - a3 ≤ b3 - b4)
    (hcov : b3 - b4 < K * (a4 - a3) ∨ (1 - a4) * (b3 - b4) < K * (a4 - a3) * b4 ∨
      (b3 < 1 ∧ a3 * (b3 - b4) < K * (a4 - a3) * (1 - b3)))
    (h1 : max 1 (a3 + ν * b3) ≤ min ν (a4 + ν * b4) ∨
      max ν (a4 + ν * b4) ≤ min 1 (a3 + ν * b3))
    (h2 : max 1 (a3 + K * ν * b3) ≤ min (K * ν) (a4 + K * ν * b4) ∨
      max (K * ν) (a4 + K * ν * b4) ≤ min 1 (a3 + K * ν * b3)) : False := by
  have hD' : 0 < b3 - b4 := by linarith
  have e : ∀ μ : ℝ, (a4 + μ * b4) - (a3 + μ * b3) = (a4 - a3) - μ * (b3 - b4) := by
    intro μ; ring
  have hKν : ν < K * ν := by nlinarith
  simp only [max_le_iff, le_min_iff] at h1 h2
  rcases h1 with ⟨⟨p1, p2⟩, p3, p4⟩ | ⟨⟨p1, p2⟩, p3, p4⟩
  · -- `{0, 3}` below `{2, 4}` at `ν`: `1 ≤ ν` and `ν (b3 − b4) ≤ a4 − a3 ≤ b3 − b4`
    have r : ν * (b3 - b4) ≤ a4 - a3 := by linarith [e ν]
    have hν1 : ν ≤ 1 := by
      by_contra hc; push Not at hc; nlinarith [mul_pos (sub_pos.mpr hc) hD']
    rcases h2 with ⟨⟨q1, q2⟩, q3, q4⟩ | ⟨⟨q1, q2⟩, q3, q4⟩
    · have r' : K * ν * (b3 - b4) ≤ a4 - a3 := by linarith [e (K * ν)]
      have : K * ν ≤ 1 := by
        by_contra hc; push Not at hc; nlinarith [mul_pos (sub_pos.mpr hc) hD']
      linarith
    · linarith
  · -- `{2, 4}` below `{0, 3}` at `ν`: `a4 − a3 ≤ ν (b3 − b4)`
    have r : a4 - a3 ≤ ν * (b3 - b4) := by linarith [e ν]
    have m1 : K * (a4 - a3) ≤ K * ν * (b3 - b4) := by
      have := mul_le_mul_of_nonneg_left r (by linarith : (0 : ℝ) ≤ K)
      linarith
    rcases h2 with ⟨⟨q1, q2⟩, q3, q4⟩ | ⟨⟨q1, q2⟩, q3, q4⟩
    · -- the other pattern at `K ν`: `K ν (b3 − b4) ≤ a4 − a3 ≤ ν (b3 − b4)`
      have r' : K * ν * (b3 - b4) ≤ a4 - a3 := by linarith [e (K * ν)]
      nlinarith [mul_pos (sub_pos.mpr hKν) hD']
    · -- both patterns `{0, 3}` above `{2, 4}`: `K (a4 − a3)` beats the binding term of `m`
      rcases hcov with c | c | ⟨c0, c⟩
      · have : 1 * (b3 - b4) < (K * ν) * (b3 - b4) := by linarith
        have := lt_of_mul_lt_mul_right this hD'.le
        linarith
      · have k : (1 - a4) * (b3 - b4) < (K * ν * b4) * (b3 - b4) := by
          nlinarith [mul_le_mul_of_nonneg_right m1 hb4.le]
        have := lt_of_mul_lt_mul_right k hD'.le
        linarith
      · have k : a3 * (b3 - b4) < (K * ν * (1 - b3)) * (b3 - b4) := by
          nlinarith [mul_le_mul_of_nonneg_right m1 (show (0 : ℝ) ≤ 1 - b3 by linarith)]
        have := lt_of_mul_lt_mul_right k hD'.le
        linarith

omit T in
/-- **The pair rule for two tests with the rim `(0, 2, 3, 4)` on circle 2, pencil form.**
With `b4 < b3`, `ν34 = (a4 − a3)/(b3 − b4) ≤ 1` and `m < K ν34` for one of the terms
`m ∈ {1, r4, ν32}` of `min (1, r4, ν32)` (multiplied out), the rim cannot fail at both `ν` and
`K ν` (`K > 1`, `ν > 0`). -/
theorem tpair_pencil (hT : Type24 x) {ν K : ℝ} (hν : 0 < ν) (hK : 1 < K)
    (h34b : oblX2 x 4 < oblX2 x 3)
    (hle : oblX0 x 4 - oblX0 x 3 ≤ oblX2 x 3 - oblX2 x 4)
    (hcov : oblX2 x 3 - oblX2 x 4 < K * (oblX0 x 4 - oblX0 x 3) ∨
      (1 - oblX0 x 4) * (oblX2 x 3 - oblX2 x 4) < K * (oblX0 x 4 - oblX0 x 3) * oblX2 x 4 ∨
      (oblX2 x 3 < 1 ∧
        oblX0 x 3 * (oblX2 x 3 - oblX2 x 4) < K * (oblX0 x 4 - oblX0 x 3) * (1 - oblX2 x 3))) :
    ¬ (PencilFails x ν 0 3 2 4 ∧ PencilFails x (K * ν) 0 3 2 4) := by
  have z0 : ∀ ν, pencil2 x ν 0 = 1 := fun ν => by
    simp only [pencil2, hT.oblX0_zero', Type24.oblX2_zero']; ring
  have z2 : ∀ ν, pencil2 x ν 2 = ν := fun ν => by
    simp only [pencil2, Type24.oblX0_two, hT.oblX2_two]; ring
  rintro ⟨h1, h2⟩
  simp only [PencilFails, z0, z2] at h1 h2
  simp only [pencil2] at h1 h2
  exact tpair_real hν hK (hT.X2_pos (v := 4) (by decide)) h34b hle hcov h1 h2

/-- **The T′ pair (Corollary 17.17 (d) with the pair rule), at the exact corner.**  In case C
(`ω3, ω4 > 0`, `ω3 ω4 > 1`), with `b4 < b3`, `ν34 ≤ 1` and `m < ω3 ω4 ν34` (one term
of `m = min (1, r4, ν32)`, multiplied out), `T′(0,6)` and `T′(2,6)`, both with the rim
`(0, 2, 3, 4)`, do not both fail.  (The circle ratio is `t2 / t1 = ω3 ω4`.) -/
theorem tpair_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h34 : 1 < omega3 x * omega4 x)
    (h34b : oblX2 x 4 < oblX2 x 3)
    (hle : oblX0 x 4 - oblX0 x 3 ≤ oblX2 x 3 - oblX2 x 4)
    (hcov : oblX2 x 3 - oblX2 x 4 < omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) ∨
      (1 - oblX0 x 4) * (oblX2 x 3 - oblX2 x 4) <
        omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) * oblX2 x 4 ∨
      (oblX2 x 3 < 1 ∧ oblX0 x 3 * (oblX2 x 3 - oblX2 x 4) <
        omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) * (1 - oblX2 x 3))) :
    ¬ (Fails4 (x 0) (x 3) (x 2) (x 4) (viewT06 x) ∧
      Fails4 (x 0) (x 3) (x 2) (x 4) (viewT26 x)) := by
  have ga := T.ga_pos; have gb := T.gb_pos
  have v1 : viewT06 x = omega4 x • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) := by
    simp only [viewT06, one_smul]
  have v2 : viewT26 x = (1 : ℝ) • (x 0 - x 1) + omega3 x • (x 2 - x 1) := by
    simp only [viewT26, one_smul]
  rw [v1, v2, T.fails4_circle2_iff hE h4, T.fails4_circle2_iff hE one_pos]
  have hν : omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫ / (1 * ⟪x 0 - x 1, x 0 - x 1⟫) =
      (omega3 x * omega4 x) *
        (1 * ⟪x 2 - x 1, x 2 - x 1⟫ / (omega4 x * ⟪x 0 - x 1, x 0 - x 1⟫)) := by
    field_simp
  rw [hν]
  exact tpair_pencil T (by positivity) h34 h34b hle hcov

/-- **M3′ (Theorem 17.18) at the exact corner.**  In case C (here: `ω3, ω4 > 0`, `ω3 ω4 > 1`),
suppose
- (S′) `c3 ≥ 1`, or `c5 < c3 < 1` with `λ (a5 − a3) < a3` and `λ (b5 − b3) < b3`,
  `λ = (1 − c3)/(c3 − c5)` (multiplied out);
- (T′) the failure `PT` of `T′(2,6)` forces `g_a ≤ ω3 g_b` (`μ_b ≥ 1`; by `t26_fails_corner` this
  holds for the rim `(0, 2, 6, 4)`);
- (R) `a5 ≥ 1`, or `(1 − a5) ω3 (1 + ω4) < (1 + ω3) b5`.

Then `S_6 = 046/236` with the rim `(0, 5, 3, 6)` and `T′(2,6)` do not both fail. -/
theorem m3prime_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h34 : 1 < omega3 x * omega4 x)
    (hS' : 1 ≤ oblX6 x 3 ∨ (oblX6 x 5 < oblX6 x 3 ∧ oblX6 x 3 < 1 ∧
      (1 - oblX6 x 3) * (oblX0 x 5 - oblX0 x 3) < oblX0 x 3 * (oblX6 x 3 - oblX6 x 5) ∧
      (1 - oblX6 x 3) * (oblX2 x 5 - oblX2 x 3) < oblX2 x 3 * (oblX6 x 3 - oblX6 x 5)))
    {PT : Prop} (hT : PT → ⟪x 0 - x 1, x 0 - x 1⟫ ≤ omega3 x * ⟪x 2 - x 1, x 2 - x 1⟫)
    (hR : 1 ≤ oblX0 x 5 ∨
      (1 - oblX0 x 5) * omega3 x * (1 + omega4 x) < (1 + omega3 x) * oblX2 x 5) :
    ¬ (Fails4 (x 0) (x 3) (x 5) (x 6) (view6 x) ∧ PT) := by
  rintro ⟨hF, hPT⟩
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have dS := fun v => T.depth_corner hE v (1 + omega4 x) (1 + omega3 x)
    (omega4 x * omega3 x - 1)
  rw [← Type24.view6_eq] at dS
  have a3 := T.X0_pos (v := 3) (by decide)
  have b3 := T.X2_pos (v := 3) (by decide)
  have b5 := T.X2_pos (v := 5) (by decide)
  have c5 := T.X6_pos (v := 5) (by decide)
  have hγ : 0 < omega4 x * omega3 x - 1 := by linarith [mul_comm (omega3 x) (omega4 x)]
  set A := (1 + omega4 x) * ⟪x 0 - x 1, x 0 - x 1⟫ with hA
  set B := (1 + omega3 x) * ⟪x 2 - x 1, x 2 - x 1⟫ with hB
  set C := (omega4 x * omega3 x - 1) * ⟪x 6 - x 1, x 6 - x 1⟫ with hC
  have hA0 : 0 < A := mul_pos (by linarith) ga
  have hB0 : 0 < B := mul_pos (by linarith) gb
  have hC0 : 0 < C := mul_pos hγ gc
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dS 0, dS 3, dS 5, dS 6] at h <;>
    simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero, Type24.oblX0_six,
      Type24.oblX2_six, T.oblX6_six] at h
  · -- `{0, 3}` below `{5, 6}`: `z5 ≥ z3` and `z6 ≥ z3` contradict (S′)
    obtain ⟨-, h35, h36⟩ := h
    rcases hS' with hc3 | ⟨hc53, hc31, ha, hb⟩
    · nlinarith [mul_pos hA0 a3, mul_pos hB0 b3, mul_nonneg hC0.le (sub_nonneg.mpr hc3)]
    · have k1 := mul_le_mul_of_nonneg_left (sub_nonneg.mpr h35)
        (sub_nonneg.mpr hc31.le)
      have k2 := mul_le_mul_of_nonneg_left (sub_nonneg.mpr h36)
        (sub_nonneg.mpr hc53.le)
      nlinarith [mul_lt_mul_of_pos_left ha hA0, mul_lt_mul_of_pos_left hb hB0]
  · -- `{5, 6}` below `{0, 3}`: `z0 ≥ z5` contradicts (R) and (T′)
    obtain ⟨⟨h50, -⟩, -, -⟩ := h
    have t := hT hPT
    rcases hR with ha5 | hr
    · nlinarith [mul_pos hB0 b5, mul_pos hC0 c5, mul_nonneg hA0.le (sub_nonneg.mpr ha5)]
    · have h1a : 0 < 1 - oblX0 x 5 := by
        by_contra hn; push Not at hn
        nlinarith [mul_pos hB0 b5, mul_pos hC0 c5, mul_nonneg hA0.le (sub_nonneg.mpr hn)]
      have k := mul_le_mul_of_nonneg_left t (mul_pos (by linarith : (0 : ℝ) < 1 + omega4 x) h1a).le
      nlinarith [mul_lt_mul_of_pos_right hr gb, mul_pos hC0 c5]

end Type24

/-! ### Rupert forms -/

/-- **A 4-corner test** with the rim `(y, a, c, b)` at the view `u` (vertex crossing, edge
crossing or two faces without a common vertex), certified except for its depth pattern: the rim
is a strictly convex counterclockwise quadrilateral, every point of `V` other than the corners,
the middles `M` and the doubles `D` is strictly inside, the middles lie over sides of the rim
(Proposition 8.8, Lemma 17.15), the doubles over its corners (Theorem 8.9, Lemma 16.27′), the four
depths are distinct and the rim has no horizontal double normal. -/
def QuadTest (V : Finset ℝ³) (u y a c b : ℝ³) : Prop :=
  ∃ M D Wn : Finset ℝ³, u ≠ 0 ∧ y ∈ V ∧ a ∈ V ∧ b ∈ V ∧ c ∈ V ∧ y ∉ M ∧ a ∉ M ∧ b ∉ M ∧
    c ∉ M ∧ 0 < det3 (a - y) (c - y) u ∧ 0 < det3 (c - a) (b - a) u ∧
    0 < det3 (b - c) (y - c) u ∧ 0 < det3 (y - b) (a - b) u ∧
    (∀ z ∈ V, z ∉ M → z ∉ D → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z) ∧
    [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup ∧
    (∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u) ∧
    (∀ d ∈ D, ∃ i : ZMod 4, ∃ h : ℝ, h ≠ 0 ∧ d = quad y a c b i - h • u) ∧
    NoHDNAt Wn u ∧ y ∈ Wn ∧ a ∈ Wn ∧ c ∈ Wn ∧ b ∈ Wn

/-- A 4-corner test with the rim `(y, a, c, b)` in either orientation. -/
def QuadTest' (V : Finset ℝ³) (u y a c b : ℝ³) : Prop :=
  QuadTest V u y a c b ∨ QuadTest V u y b c a

theorem fails4_swap {d₀ d₁ e₀ e₁ u : ℝ³} : Fails4 d₀ d₁ e₀ e₁ u ↔ Fails4 d₀ d₁ e₁ e₀ u := by
  simp only [Fails4, max_comm ⟪e₀, u⟫, min_comm ⟪e₀, u⟫]

theorem QuadTest.isRupert {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest V u y a c b)
    (hF : ¬ Fails4 y c a b u) : IsRupert V := by
  obtain ⟨M, D, Wn, hu, hyV, haV, hbV, hcV, hyM, haM, hbM, hcM, q₁, q₂, q₃, q₄, hrest, hz, hM,
    hD, hnd, hW⟩ := h
  exact isRupert_quadView V M D Wn hu hyV haV hbV hcV hyM haM hbM hcM q₁ q₂ q₃ q₄ hrest hz
    (fun h' => hF h'.fails4) hM hD hnd hW

/-- **A test that does not fail certifies `V`** (Fact 17.0 for 4-corner rims). -/
theorem QuadTest'.isRupert {V : Finset ℝ³} {u y a c b : ℝ³} (h : QuadTest' V u y a c b)
    (hF : ¬ Fails4 y c a b u) : IsRupert V := by
  rcases h with h | h
  · exact h.isRupert hF
  · exact h.isRupert (fun h' => hF (fails4_swap.mp h'))

/-- **Two tests that do not both fail certify `V`.** -/
theorem isRupert_of_two_tests {V : Finset ℝ³} {u y a c b u' y' a' c' b' : ℝ³}
    (h₁ : QuadTest' V u y a c b) (h₂ : QuadTest' V u' y' a' c' b')
    (h : ¬ (Fails4 y c a b u ∧ Fails4 y' c' a' b' u')) : IsRupert V := by
  by_cases hF : Fails4 y c a b u
  · exact h₂.isRupert (fun h' => h ⟨hF, h'⟩)
  · exact h₁.isRupert hF

/-- **M3 (Theorem 17.7), BB's off-corner form, Rupert at `K`'s own metric.**  If `T′(2,6)` has the
rim `(0, 2, 3, q)` and `S_2` the rim `(0, 2, 6, 4)` (each certified up to its depth pattern,
`QuadTest'`), and (i)–(iii) of `m3_not_both` hold, the point set is Rupert. -/
theorem isRupert_m3 {x : Fin 7 → ℝ³} (q : Fin 7) (h5 : 0 < 1 + omega5 x)
    (h3 : 0 < 1 + omega3 x) (hi : ⟪x 2, viewT26 x⟫ < ⟪x 3, viewT26 x⟫) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (hii : l * ⟪x 0, view2 x⟫ + (1 - l) * ⟪x 6, view2 x⟫ < ⟪x 4, view2 x⟫)
    (hiii : 0 < ⟪x 2 - x 6, x 2 - x 0⟫)
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 3) (x q))
    (hS : QuadTest' (univ.image x) (view2 x) (x 0) (x 2) (x 6) (x 4)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hT hS (m3_not_both q h5 h3 hi hl0 hl1 hii hiii)

/-- **M3 (Theorem 17.7) at an exact corner, Rupert form.**  Case C, `b3 ≥ 1`, `T′(2,6)` with the
rim `(0, 2, 3, q)` and `S_2` with the rim `(0, 2, 6, 4)`. -/
theorem isRupert_m3_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h35 : 1 < omega3 x * omega5 x) (hb3 : 1 ≤ oblX2 x 3) (q : Fin 7)
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 3) (x q))
    (hS : QuadTest' (univ.image x) (view2 x) (x 0) (x 2) (x 6) (x 4)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hT hS (T.m3_corner hE h3 h4 h5 h35 hb3 q)

/-- **M3, mirror, at an exact corner, Rupert form**: `T′(6,2)` with the rim `(0, 6, 3, q)`,
`S_6` with the rim `(0, 5, 2, 6)`, `c3 ≥ 1`. -/
theorem isRupert_m3_corner6 {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h34 : 1 < omega3 x * omega4 x) (hc3 : 1 ≤ oblX6 x 3) (q : Fin 7)
    (hT : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 3) (x q))
    (hS : QuadTest' (univ.image x) (view6 x) (x 0) (x 5) (x 2) (x 6)) :
    IsRupert (univ.image x) := by
  refine isRupert_of_two_tests hT hS ?_
  rintro ⟨h1, h2⟩
  refine T.m3_corner6 hE h3 h4 h5 h34 hc3 q ⟨h1, ?_⟩
  -- the rim `(0, 5, 2, 6)` has the diagonals `{0, 2}`, `{5, 6}`
  rw [fails4_swap]; exact h2

/-- **M1 (Theorem 17.8) at an exact corner, Rupert form.**  With `T′(2,6)` (rim `(0, 2, 6, 4)`)
and `S_0` (rim `(0, 2, 3, 6)`) certified up to their depth patterns, and **Lemma W at the arc
views as a hypothesis** (`hWP`: WP_2's depth chain at a view `e_a + t e_b` with `lo < t < ω3`
makes `K` Rupert; 15.13 (b) with the face conditions of 17.6, not formalized here), the point set
is Rupert under (a) or (b). -/
theorem isRupert_m1_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h45 : 1 < omega4 x * omega5 x) {lo : ℝ} (hlo : 0 < lo) (hlo3 : lo < omega3 x)
    (hab : (omega3 x * (omega4 x * omega5 x - 1) < 1 + omega5 x ∨
        omega3 x * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)) ∨
      (oblX2 x 4 < 1 - oblX0 x 4 ∧
        lo * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)))
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 6) (x 4))
    (hS : QuadTest' (univ.image x) (view0 x) (x 0) (x 2) (x 3) (x 6))
    (hWP : ∀ t, lo < t → t < omega3 x → Type24.WPChain2 x t → IsRupert (univ.image x)) :
    IsRupert (univ.image x) := by
  rcases T.m1_corner hE h3 h4 h5 h45 hlo hlo3 hab with h | ⟨t, ht1, ht2, hc⟩ | h
  · exact hT.isRupert h
  · exact hWP t ht1 ht2 hc
  · exact hS.isRupert h

/-- **The T′ pair (Corollary 17.17 (d)) at an exact corner, Rupert form.**  `T′(0,6)` and
`T′(2,6)`, both with the rim `(0, 2, 3, 4)`, under the pair condition `m / ν34 < ω3 ω4`. -/
theorem isRupert_tpair_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h34 : 1 < omega3 x * omega4 x)
    (h34b : oblX2 x 4 < oblX2 x 3) (hle : oblX0 x 4 - oblX0 x 3 ≤ oblX2 x 3 - oblX2 x 4)
    (hcov : oblX2 x 3 - oblX2 x 4 < omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) ∨
      (1 - oblX0 x 4) * (oblX2 x 3 - oblX2 x 4) <
        omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) * oblX2 x 4 ∨
      (oblX2 x 3 < 1 ∧ oblX0 x 3 * (oblX2 x 3 - oblX2 x 4) <
        omega3 x * omega4 x * (oblX0 x 4 - oblX0 x 3) * (1 - oblX2 x 3)))
    (h06 : QuadTest' (univ.image x) (viewT06 x) (x 0) (x 2) (x 3) (x 4))
    (h26 : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 3) (x 4)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests h06 h26 (T.tpair_corner hE h3 h4 h34 h34b hle hcov)

/-- **M3′ (Theorem 17.18) at an exact corner, Rupert form**: `S_6` with the rim `(0, 5, 3, 6)`
and `T′(2,6)` with the rim `(0, 2, 6, 4)` (for which (T′) holds by 17.5 (a)). -/
theorem isRupert_m3prime_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h34 : 1 < omega3 x * omega4 x)
    (hS' : 1 ≤ oblX6 x 3 ∨ (oblX6 x 5 < oblX6 x 3 ∧ oblX6 x 3 < 1 ∧
      (1 - oblX6 x 3) * (oblX0 x 5 - oblX0 x 3) < oblX0 x 3 * (oblX6 x 3 - oblX6 x 5) ∧
      (1 - oblX6 x 3) * (oblX2 x 5 - oblX2 x 3) < oblX2 x 3 * (oblX6 x 3 - oblX6 x 5)))
    (hR : 1 ≤ oblX0 x 5 ∨
      (1 - oblX0 x 5) * omega3 x * (1 + omega4 x) < (1 + omega3 x) * oblX2 x 5)
    (hS : QuadTest' (univ.image x) (view6 x) (x 0) (x 5) (x 3) (x 6))
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 6) (x 4)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hS hT (T.m3prime_corner hE h3 h4 h34 hS'
    (fun h => (T.t26_fails_corner hE h3 h).1) hR)

/-- **Lemma Q (17.4) for type 24, Rupert form.**  If `S_0 = 025/046` (or any other crossing test)
has the rim `(0, 4, 3, 5)` and `3` lies in the plane of `0, 4, 5` opposite `0`, the test never
fails; certified up to its depth pattern, it makes the point set Rupert at every metric. -/
theorem isRupert_type24_Q {x : Fin 7 → ℝ³} {u : ℝ³} {s t : ℝ}
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0)) (hs : 0 < s) (ht : 0 < t)
    (hst : 1 < s + t) (hQ : QuadTest' (univ.image x) u (x 0) (x 4) (x 3) (x 5)) :
    IsRupert (univ.image x) := by
  refine hQ.isRupert fun hF => ?_
  obtain ⟨e1, e2, e3⟩ := planarQuad_fails4 hq hs ht hst hF
  rcases hQ with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz, -⟩ <;>
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact hz.1.1 (by linarith)

end Minimality

end
