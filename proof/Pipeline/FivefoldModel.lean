module

public import RationalApprox.TrigLemmas
public import Basic
public import Bounding
public import MatrixPose
public import BalancedSupport.RotationDistance
public import Mathlib.Analysis.Real.Pi.Bounds
public import Pipeline.SolidModel

@[expose] public section

/-!
# Fivefold solid models: C5 about the z axis

The icosahedral solids (deltoidal and pentagonal hexecontahedra, snub
dodecahedron) are modelled in a frame where z is a 5-fold axis: the vertex
slots are `5 · seedCount` rational points, slot `seedCount · k + s` being
seed `s` rotated by `2πk/5` about z, up to rounding. This module builds a
`SolidModel` from such data (`FivefoldSolid`); a solid supplies only its
rational vertices, its seeds and three facts about them that the kernel
checks on the data.

The exact rotations `Rz(2πk/5)` are irrational, so the model is not exact:

* `fivefoldMatrixQ k` holds rational Taylor values of cos and sin of
  `2πk/5` (with π replaced by a 20-digit rational `piQ`), within `κ/2` of
  `Rz(2πk/5)` in operator norm (`symmetryErrorQ = κ/2`);
* the published rational vertices are within `6 · 10⁻¹⁶` of the exactly
  rotated seeds (`modelErrorQ`). The bridge is `tightVertex`, the seeds
  rotated by 17-digit rational values of cos and sin of 72° and 144°: it is
  within `2 · 10⁻¹⁶` of the exact rotation (`tightVertex_exact_close`, from
  `cos(2π/5) = (√5 - 1)/4`), and the kernel checks that each rational vertex
  is within `4 · 10⁻¹⁶` of it (the solid's `tight_sq_close`).
-/

open RationalApprox Real

namespace Noperts.Pipeline

/-! ### Rational Taylor values of the fivefold rotations -/

/-- Rational approximation of π, matching Mathlib's `pi_gt_d20` bound. -/
def piQ : ℚ := 3.14159265358979323846

private lemma piQ_lt_pi : (piQ : ℝ) < π := pi_gt_d20

private lemma pi_sub_piQ_lt : π - (piQ : ℝ) < 1 / 10 ^ 20 := by
  have h := pi_lt_d20
  have : (3.14159265358979323847 : ℝ) =
      (piQ : ℝ) + 1 / 10 ^ 20 := by
    norm_num [piQ]
  linarith

def reducedOrbit (k : Fin 5) : ℚ :=
  if k.val ≤ 2 then k.val else k.val - 5

private lemma reducedOrbit_abs_le_two (k : Fin 5) :
    |(reducedOrbit k : ℝ)| ≤ 2 := by
  fin_cases k <;> norm_num [reducedOrbit]

private lemma rationalAngle_mem (k : Fin 5) :
    ((2 * piQ * reducedOrbit k / 5 : ℚ) : ℝ) ∈ Set.Icc (-4) 4 := by
  fin_cases k <;> norm_num [reducedOrbit, piQ]

private lemma cos_orbit_reduced (k : Fin 5) :
    Real.cos (2 * π * (k : ℝ) / 5) =
      Real.cos (2 * π * (reducedOrbit k : ℝ) / 5) := by
  fin_cases k <;> simp [reducedOrbit]
  · rw [show 2 * π * (3 : ℝ) / 5 = 2 * π * (-2 : ℝ) / 5 + 2 * π by ring]
    convert Real.cos_add_two_pi (2 * π * (-2 : ℝ) / 5) using 1
    all_goals norm_num
  · rw [show 2 * π * (4 : ℝ) / 5 = 2 * π * (-1 : ℝ) / 5 + 2 * π by ring]
    convert Real.cos_add_two_pi (2 * π * (-1 : ℝ) / 5) using 1
    all_goals norm_num

private lemma sin_orbit_reduced (k : Fin 5) :
    Real.sin (2 * π * (k : ℝ) / 5) =
      Real.sin (2 * π * (reducedOrbit k : ℝ) / 5) := by
  fin_cases k <;> simp [reducedOrbit]
  · rw [show 2 * π * (3 : ℝ) / 5 = 2 * π * (-2 : ℝ) / 5 + 2 * π by ring]
    convert Real.sin_add_two_pi (2 * π * (-2 : ℝ) / 5) using 1
    all_goals norm_num
  · rw [show 2 * π * (4 : ℝ) / 5 = 2 * π * (-1 : ℝ) / 5 + 2 * π by ring]
    convert Real.sin_add_two_pi (2 * π * (-1 : ℝ) / 5) using 1
    all_goals norm_num

private lemma angle_error (k : Fin 5) :
    |((2 * piQ * reducedOrbit k / 5 : ℚ) : ℝ) -
      2 * π * (reducedOrbit k : ℝ) / 5| ≤ κ / 42 := by
  have hpi : 0 ≤ π - (piQ : ℝ) :=
    le_of_lt (sub_pos.mpr piQ_lt_pi)
  have hk := reducedOrbit_abs_le_two k
  have hdiff :
      |((2 * piQ * reducedOrbit k / 5 : ℚ) : ℝ) -
          2 * π * (reducedOrbit k : ℝ) / 5| =
        (2 * |(reducedOrbit k : ℝ)| / 5) *
          (π - (piQ : ℝ)) := by
    push_cast
    rw [show 2 * (piQ : ℝ) * (reducedOrbit k : ℝ) / 5 -
        2 * π * (reducedOrbit k : ℝ) / 5 =
        -(2 * (reducedOrbit k : ℝ) / 5 *
          (π - (piQ : ℝ))) by ring]
    rw [abs_neg, abs_mul, abs_div, abs_mul, abs_of_nonneg hpi]
    norm_num
  rw [hdiff]
  calc
    (2 * |(reducedOrbit k : ℝ)| / 5) *
        (π - (piQ : ℝ))
      ≤ (4 / 5 : ℝ) * (π - (piQ : ℝ)) := by
        nlinarith [hk]
    _ ≤ (4 / 5 : ℝ) * (1 / 10 ^ 20) := by
        gcongr
        exact le_of_lt pi_sub_piQ_lt
    _ ≤ κ / 42 := by norm_num [κ]

theorem cos_symmetry_combined_error (k : Fin 5) :
    |((RationalApprox.cosℚ
        (2 * piQ * reducedOrbit k / 5) : ℚ) : ℝ) -
      Real.cos (2 * π * (k : ℝ) / 5)| ≤ κ / 6 := by
  let q : ℚ := 2 * piQ * reducedOrbit k / 5
  let x : ℝ := 2 * π * (reducedOrbit k : ℝ) / 5
  have ht := RationalApprox.cosℚ_approx' (q : ℝ) (rationalAngle_mem k)
  have hm : |Real.cos (q : ℝ) - Real.cos x| ≤ |(q : ℝ) - x| :=
    Real.abs_cos_sub_cos_le _ _
  have hq : |(q : ℝ) - x| ≤ κ / 42 := angle_error k
  rw [cos_orbit_reduced k]
  rw [← RationalApprox.cosℚ_match q] at ht
  calc
    |((RationalApprox.cosℚ q : ℚ) : ℝ) - Real.cos x|
      ≤ |((RationalApprox.cosℚ q : ℚ) : ℝ) - Real.cos (q : ℝ)| +
          |Real.cos (q : ℝ) - Real.cos x| := by
        exact abs_sub_le
          (((RationalApprox.cosℚ q : ℚ) : ℝ))
          (Real.cos (q : ℝ)) (Real.cos x)
    _ ≤ κ / 7 + κ / 42 :=
      add_le_add (by simpa [abs_sub_comm] using ht) (hm.trans hq)
    _ = κ / 6 := by ring

theorem sin_symmetry_combined_error (k : Fin 5) :
    |((RationalApprox.sinℚ
        (2 * piQ * reducedOrbit k / 5) : ℚ) : ℝ) -
      Real.sin (2 * π * (k : ℝ) / 5)| ≤ κ / 6 := by
  let q : ℚ := 2 * piQ * reducedOrbit k / 5
  let x : ℝ := 2 * π * (reducedOrbit k : ℝ) / 5
  have ht := RationalApprox.sinℚ_approx' (q : ℝ) (rationalAngle_mem k)
  have hm : |Real.sin (q : ℝ) - Real.sin x| ≤ |(q : ℝ) - x| :=
    Real.abs_sin_sub_sin_le _ _
  have hq : |(q : ℝ) - x| ≤ κ / 42 := angle_error k
  rw [sin_orbit_reduced k]
  rw [← RationalApprox.sinℚ_match q] at ht
  calc
    |((RationalApprox.sinℚ q : ℚ) : ℝ) - Real.sin x|
      ≤ |((RationalApprox.sinℚ q : ℚ) : ℝ) - Real.sin (q : ℝ)| +
          |Real.sin (q : ℝ) - Real.sin x| := by
        exact abs_sub_le
          (((RationalApprox.sinℚ q : ℚ) : ℝ))
          (Real.sin (q : ℝ)) (Real.sin x)
    _ ≤ κ / 7 + κ / 42 :=
      add_le_add (by simpa [abs_sub_comm] using ht) (hm.trans hq)
    _ = κ / 6 := by ring

/-- The exact rotation by `2πk/5` about the z axis. -/
noncomputable def fivefoldRotation (k : Fin 5) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat (2 * Real.pi * (k : ℝ) / 5)

theorem fivefoldRotation_eq_mul (k : Fin 5) :
    fivefoldRotation k = Rz_mat ((k : ℝ) * (2 * Real.pi / 5)) := by
  unfold fivefoldRotation
  congr 1
  ring

theorem fivefoldRotation_mem (k : Fin 5) :
    fivefoldRotation k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  MatrixPose.Rz_mat_mem_SO3 _

theorem fivefoldRotation_zero : fivefoldRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fivefoldRotation, Rz_mat]

theorem fivefoldRotation_mul (a b : Fin 5) :
    fivefoldRotation a * fivefoldRotation b = fivefoldRotation (a + b) := by
  rw [fivefoldRotation_eq_mul, fivefoldRotation_eq_mul, fivefoldRotation_eq_mul]
  rw [Bounding.Rz_mat_mul_Rz_mat]
  have hdecomp : (a.val : ℝ) + (b.val : ℝ) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) +
        5 * (((a.val + b.val) / 5 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div (a.val + b.val) 5).symm
  have hangle :
      (a : ℝ) * (2 * Real.pi / 5) +
          (b : ℝ) * (2 * Real.pi / 5) =
        ((a + b : Fin 5) : ℝ) * (2 * Real.pi / 5) +
          ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi)) := by
    change (a.val : ℝ) * (2 * Real.pi / 5) +
        (b.val : ℝ) * (2 * Real.pi / 5) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) * (2 * Real.pi / 5) +
        ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi))
    calc
      _ = ((a.val : ℝ) + b.val) * (2 * Real.pi / 5) := by ring
      _ = ((((a.val + b.val) % 5 : ℕ) : ℝ) +
          5 * (((a.val + b.val) / 5 : ℕ) : ℝ)) *
            (2 * Real.pi / 5) := by rw [hdecomp]
      _ = _ := by ring
  rw [hangle]
  convert Rz_mat_add_int_mul_two_pi
    (Int.ofNat ((a.val + b.val) / 5))
    (((a + b : Fin 5) : ℝ) * (2 * Real.pi / 5)) using 1 <;>
    norm_num

/-- Rational Taylor approximation to the exact fivefold rotation. -/
def fivefoldMatrixQ (g : Fin 5) : Matrix (Fin 3) (Fin 3) ℚ :=
  let q := 2 * piQ * reducedOrbit g / 5
  !![RationalApprox.cosℚ q, -RationalApprox.sinℚ q, 0;
     RationalApprox.sinℚ q,  RationalApprox.cosℚ q, 0;
     0, 0, 1]

theorem fivefoldMatrixQ_close (g : Fin 5) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (fivefoldRotation g - (fivefoldMatrixQ g).map fun x => (x : ℝ)))‖ ≤
      ((κℚ / 2 : ℚ) : ℝ) := by
  set A : Matrix (Fin 3) (Fin 3) ℝ :=
    fivefoldRotation g - (fivefoldMatrixQ g).map fun x => (x : ℝ)
  apply Noperts.BalancedSupport.matrix_opNorm_le_of_sum_sq_le
  · norm_num [RationalApprox.κℚ]
  · have hc := cos_symmetry_combined_error g
    have hs := sin_symmetry_combined_error g
    have hsum :
        ∑ i, ∑ j, A i j ^ 2 =
          2 * (((RationalApprox.cosℚ
              (2 * piQ * reducedOrbit g / 5) : ℚ) : ℝ) -
                Real.cos (2 * Real.pi * (g : ℝ) / 5)) ^ 2 +
          2 * (((RationalApprox.sinℚ
              (2 * piQ * reducedOrbit g / 5) : ℚ) : ℝ) -
                Real.sin (2 * Real.pi * (g : ℝ) / 5)) ^ 2 := by
      simp [A, fivefoldRotation, fivefoldMatrixQ, Rz_mat, Fin.sum_univ_three]
      ring
    rw [hsum]
    let ce : ℝ := ((RationalApprox.cosℚ
      (2 * piQ * reducedOrbit g / 5) : ℚ) : ℝ) -
        Real.cos (2 * Real.pi * (g : ℝ) / 5)
    let se : ℝ := ((RationalApprox.sinℚ
      (2 * piQ * reducedOrbit g / 5) : ℚ) : ℝ) -
        Real.sin (2 * Real.pi * (g : ℝ) / 5)
    have hc2 : ce ^ 2 ≤ (RationalApprox.κ / 6) ^ 2 :=
      sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
    have hs2 : se ^ 2 ≤ (RationalApprox.κ / 6) ^ 2 :=
      sq_le_sq' (abs_le.mp hs).1 (abs_le.mp hs).2
    change 2 * ce ^ 2 + 2 * se ^ 2 ≤ _
    norm_num [RationalApprox.κ, RationalApprox.κℚ] at ⊢ hc2 hs2
    nlinarith

/-! ### The tight bridge from the rational vertices to the exact rotations -/

theorem pos_of_fin_five_mul {s : ℕ} (i : Fin (5 * s)) : 0 < s :=
  Nat.pos_of_ne_zero fun h => by subst h; exact absurd i.isLt (by simp)

/-- The rotation (orbit) index of slot `i`. -/
def fivefoldOrbit {s : ℕ} (i : Fin (5 * s)) : Fin 5 :=
  ⟨i.val / s, Nat.div_lt_of_lt_mul (Nat.mul_comm 5 s ▸ i.isLt)⟩

/-- The seed index of slot `i`. -/
def fivefoldSeed {s : ℕ} (i : Fin (5 * s)) : Fin s :=
  ⟨i.val % s, Nat.mod_lt _ (pos_of_fin_five_mul i)⟩

def cos72Q : ℚ := 30901699437494745 / 10^17
def sin72Q : ℚ := 9510565162951535 / 10^16
def cos144Q : ℚ := 2 * cos72Q ^ 2 - 1
def sin144Q : ℚ := 2 * sin72Q * cos72Q
noncomputable def tightTrigError : ℝ := 1 / 10^16

theorem cos72_tight :
    |Real.cos (2 * Real.pi / 5) - (cos72Q : ℝ)| ≤ 4 / 10^17 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower :
      (22360679774997896 / 10^16 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997896 / 10^16)]
  have hsqrtUpper :
      Real.sqrt 5 ≤ (22360679774997898 / 10^16 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997898 / 10^16)]
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  have hformula :
      2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1 =
        (Real.sqrt 5 - 1) / 4 := by
    nlinarith [hsqrtSq]
  rw [hformula]
  rw [abs_le]
  norm_num [cos72Q, tightTrigError]
  constructor <;> nlinarith

theorem sin72_tight :
    |Real.sin (2 * Real.pi / 5) - (sin72Q : ℝ)| ≤ tightTrigError := by
  have hangle0 : 0 < 2 * Real.pi / 5 := by positivity
  have hanglePi : 2 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcos := cos72_tight
  rw [abs_le] at hcos ⊢
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
  norm_num [cos72Q, sin72Q, tightTrigError] at hcos ⊢
  constructor <;> nlinarith [
    sq_nonneg (Real.sin (2 * Real.pi / 5) -
      (9510565162951534 / 10^16 : ℝ)),
    sq_nonneg (Real.sin (2 * Real.pi / 5) -
      (9510565162951536 / 10^16 : ℝ))]

theorem cos144_tight :
    |Real.cos (4 * Real.pi / 5) - (cos144Q : ℝ)| ≤ 4 / 10^17 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower :
      (22360679774997896 / 10^16 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997896 / 10^16)]
  have hsqrtUpper :
      Real.sqrt 5 ≤ (22360679774997898 / 10^16 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997898 / 10^16)]
  rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_five]
  rw [abs_le]
  norm_num [cos72Q, cos144Q, tightTrigError]
  constructor <;> nlinarith

theorem sin144_tight :
    |Real.sin (4 * Real.pi / 5) - (sin144Q : ℝ)| ≤ tightTrigError := by
  have hangle0 : 0 < 4 * Real.pi / 5 := by positivity
  have hanglePi : 4 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (4 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcos := cos144_tight
  rw [abs_le] at hcos ⊢
  rcases hcos with ⟨hcosLower, hcosUpper⟩
  have htrig := Real.sin_sq_add_cos_sq (4 * Real.pi / 5)
  norm_num [cos72Q, cos144Q, sin72Q, sin144Q, tightTrigError]
    at hcosLower hcosUpper ⊢
  have hcosNeg : 0 ≤ -Real.cos (4 * Real.pi / 5) := by linarith
  have habsLower :
      -(((cos144Q : ℚ) : ℝ) + 4 / 10^17) ≤
        -Real.cos (4 * Real.pi / 5) := by
    norm_num [cos72Q, cos144Q]
    linarith
  have hcosSqLower :
      (-(((cos144Q : ℚ) : ℝ) + 4 / 10^17)) ^ 2 ≤
        (-Real.cos (4 * Real.pi / 5)) ^ 2 := by
    apply (sq_le_sq₀ (by norm_num [cos72Q, cos144Q]) hcosNeg).2
    exact habsLower
  norm_num [cos72Q, cos144Q] at hcosSqLower
  constructor
  · nlinarith [sq_nonneg (Real.sin (4 * Real.pi / 5) -
      ((sin144Q : ℚ) : ℝ) - tightTrigError)]
  · let upper : ℝ := ((sin144Q : ℚ) : ℝ) + tightTrigError
    have hupper0 : 0 ≤ upper := by norm_num [upper, sin72Q, sin144Q,
      cos72Q, tightTrigError]
    have hsq : Real.sin (4 * Real.pi / 5) ^ 2 ≤ upper ^ 2 := by
      dsimp [upper]
      norm_num [sin144Q, sin72Q, cos72Q, tightTrigError]
      nlinarith
    have hu := (sq_le_sq₀ (le_of_lt hsin0) hupper0).mp hsq
    norm_num [upper, tightTrigError, sin72Q, sin144Q, cos72Q] at hu ⊢
    exact hu

def tightCos : Fin 5 → ℚ := ![1, cos72Q, cos144Q, cos144Q, cos72Q]
def tightSin : Fin 5 → ℚ := ![0, sin72Q, sin144Q, -sin144Q, -sin72Q]

theorem tightCos_close (k : Fin 5) :
    |((tightCos k : ℚ) : ℝ) - Real.cos (2 * Real.pi * (k : ℝ) / 5)| ≤
      tightTrigError := by
  fin_cases k
  · norm_num [tightCos, tightTrigError]
  · calc
      _ ≤ 4 / 10^17 := by simpa [tightCos, abs_sub_comm] using cos72_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    calc
      _ ≤ 4 / 10^17 := by
        simpa [show 2 * Real.pi * (2 : ℝ) / 5 = 4 * Real.pi / 5 by ring,
          abs_sub_comm] using cos144_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    rw [show 2 * Real.pi * (3 : ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub]
    calc
      _ ≤ 4 / 10^17 := by simpa [abs_sub_comm] using cos144_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    rw [show 2 * Real.pi * (4 : ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub]
    calc
      _ ≤ 4 / 10^17 := by simpa [abs_sub_comm] using cos72_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]

theorem tightSin_close (k : Fin 5) :
    |((tightSin k : ℚ) : ℝ) - Real.sin (2 * Real.pi * (k : ℝ) / 5)| ≤
      tightTrigError := by
  fin_cases k
  · norm_num [tightSin, tightTrigError]
  · simpa [tightSin, abs_sub_comm] using sin72_tight
  · norm_num [tightSin]
    have h := sin144_tight
    norm_num at h ⊢
    simpa [show 2 * Real.pi * (2 : ℝ) / 5 = 4 * Real.pi / 5 by ring,
      abs_sub_comm] using h
  · norm_num [tightSin]
    rw [show 2 * Real.pi * (3 : ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 by ring,
      Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (4 * Real.pi / 5) - ((sin144Q : ℚ) : ℝ)| := by
        congr 1 <;> ring
      _ ≤ tightTrigError := sin144_tight
  · norm_num [tightSin]
    rw [show 2 * Real.pi * (4 : ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring,
      Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (2 * Real.pi / 5) - ((sin72Q : ℚ) : ℝ)| := by
        congr 1 <;> ring
      _ ≤ tightTrigError := sin72_tight

/-- Seed `i % s` rotated by the 17-digit rational cos and sin of
`2π (i / s) / 5`. -/
def tightVertex {s : ℕ} (seeds : Fin s → Fin 3 → ℚ) (i : Fin (5 * s)) : Fin 3 → ℚ :=
  let c := tightCos (fivefoldOrbit i)
  let sn := tightSin (fivefoldOrbit i)
  let v := seeds (fivefoldSeed i)
  ![c * v 0 - sn * v 1, sn * v 0 + c * v 1, v 2]

private lemma tight_RzL_apply_0 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
  ring

private lemma tight_RzL_apply_1 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma tight_RzL_apply_2 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
theorem tightVertex_exact_close {s : ℕ} (seeds : Fin s → Fin 3 → ℚ)
    (hxy : ∀ t, ((seeds t 0 : ℚ) : ℝ) ^ 2 + ((seeds t 1 : ℚ) : ℝ) ^ 2 ≤ 1)
    (i : Fin (5 * s)) :
    ‖toR3 (tightVertex seeds i) -
        (fivefoldRotation (fivefoldOrbit i)).toEuclideanLin (toR3 (seeds (fivefoldSeed i)))‖ ≤
      2 / 10^16 := by
  let k := fivefoldOrbit i
  let t := fivefoldSeed i
  let θ : ℝ := 2 * Real.pi * (k : ℝ) / 5
  let ce : ℝ := (tightCos k : ℚ) - Real.cos θ
  let se : ℝ := (tightSin k : ℚ) - Real.sin θ
  let a : ℝ := (seeds t 0 : ℚ)
  let b : ℝ := (seeds t 1 : ℚ)
  change ‖toR3 (tightVertex seeds i) - RzL θ (toR3 (seeds t))‖ ≤ 2 / 10^16
  let d := toR3 (tightVertex seeds i) - RzL θ (toR3 (seeds t))
  have hce : |ce| ≤ 1 / 10^16 := tightCos_close k
  have hse : |se| ≤ 1 / 10^16 := tightSin_close k
  have hab : a ^ 2 + b ^ 2 ≤ 1 := hxy t
  have hd0 : d 0 = ce * a - se * b := by
    simp only [d, tightVertex, k, t, θ, ce, se, a, b,
      toR3, PiLp.sub_apply, Matrix.cons_val_zero, tight_RzL_apply_0]
    push_cast
    ring
  have hd1 : d 1 = se * a + ce * b := by
    simp only [d, tightVertex, k, t, θ, ce, se, a, b,
      toR3, PiLp.sub_apply, Matrix.cons_val_one, tight_RzL_apply_1]
    push_cast
    ring
  have hd2 : d 2 = 0 := by
    simp [d, t, tightVertex, toR3, tight_RzL_apply_2]
  have hsq : d 0 ^ 2 + d 1 ^ 2 =
      (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2) := by
    rw [hd0, hd1]
    ring
  have hce_sq : ce ^ 2 ≤ (1 / 10^16 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (1 / 10^16 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  have he : (0 : ℝ) ≤ 2 / 10^16 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  rw [hd2, zero_pow (by omega), add_zero, hsq]
  nlinarith

theorem rational_tight_close {s : ℕ} (seeds : Fin s → Fin 3 → ℚ)
    (verts : Fin (5 * s) → Fin 3 → ℚ) (i : Fin (5 * s))
    (h : (verts i 0 - tightVertex seeds i 0) ^ 2 +
      (verts i 1 - tightVertex seeds i 1) ^ 2 +
      (verts i 2 - tightVertex seeds i 2) ^ 2 ≤ (4 / 10^16 : ℚ) ^ 2) :
    ‖toR3 (verts i) - toR3 (tightVertex seeds i)‖ ≤ 4 / 10^16 := by
  have he : (0 : ℝ) ≤ 4 / 10^16 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3, PiLp.sub_apply]
  have hreal :
      (((verts i 0 - tightVertex seeds i 0) ^ 2 +
        (verts i 1 - tightVertex seeds i 1) ^ 2 +
        (verts i 2 - tightVertex seeds i 2) ^ 2 : ℚ) : ℝ) ≤
          (((4 / 10^16 : ℚ) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hreal
  norm_num at hreal ⊢
  exact hreal

/-- The exactly rotated seeds are within `6 · 10⁻¹⁶` of the rational
vertices, given the solid's kernel-checked facts. -/
theorem fivefold_seed_close {s : ℕ} (seeds : Fin s → Fin 3 → ℚ)
    (verts : Fin (5 * s) → Fin 3 → ℚ)
    (hxy : ∀ t, (seeds t 0) ^ 2 + (seeds t 1) ^ 2 ≤ 1)
    (htight : ∀ i, (verts i 0 - tightVertex seeds i 0) ^ 2 +
      (verts i 1 - tightVertex seeds i 1) ^ 2 +
      (verts i 2 - tightVertex seeds i 2) ^ 2 ≤ (4 / 10^16 : ℚ) ^ 2)
    (i : Fin (5 * s)) :
    ‖(fivefoldRotation (fivefoldOrbit i)).toEuclideanLin (toR3 (seeds (fivefoldSeed i))) -
        toR3 (verts i)‖ ≤ ((6 / 10^16 : ℚ) : ℝ) := by
  have hxy' : ∀ t, ((seeds t 0 : ℚ) : ℝ) ^ 2 + ((seeds t 1 : ℚ) : ℝ) ^ 2 ≤ 1 := by
    intro t
    exact_mod_cast hxy t
  rw [norm_sub_rev]
  calc
    ‖toR3 (verts i) -
        (fivefoldRotation (fivefoldOrbit i)).toEuclideanLin (toR3 (seeds (fivefoldSeed i)))‖ =
        ‖(toR3 (verts i) - toR3 (tightVertex seeds i)) +
          (toR3 (tightVertex seeds i) -
            (fivefoldRotation (fivefoldOrbit i)).toEuclideanLin
              (toR3 (seeds (fivefoldSeed i))))‖ := by
      congr 1
      abel
    _ ≤ ‖toR3 (verts i) - toR3 (tightVertex seeds i)‖ +
        ‖toR3 (tightVertex seeds i) -
          (fivefoldRotation (fivefoldOrbit i)).toEuclideanLin
            (toR3 (seeds (fivefoldSeed i)))‖ := norm_add_le _ _
    _ ≤ 4 / 10^16 + 2 / 10^16 :=
      add_le_add (rational_tight_close seeds verts i (htight i))
        (tightVertex_exact_close seeds hxy' i)
    _ = ((6 / 10^16 : ℚ) : ℝ) := by norm_num

/-! ### Fivefold solids -/

/-- The data of a fivefold solid: its seeds and rational vertices, and the
three facts about them that the kernel checks (`decide +kernel` on the
solid's data). The `SolidModel` instance below is derived from it. -/
class FivefoldSolid where
  seedCount : ℕ
  seedCount_pos : 0 < seedCount
  rationalVertices : Fin (5 * seedCount) → Fin 3 → ℚ
  seedVertex : Fin seedCount → Fin 3 → ℚ
  seed_xy_sq_le_one : ∀ t, (seedVertex t 0) ^ 2 + (seedVertex t 1) ^ 2 ≤ 1
  tight_sq_close : ∀ i, (rationalVertices i 0 - tightVertex seedVertex i 0) ^ 2 +
      (rationalVertices i 1 - tightVertex seedVertex i 1) ^ 2 +
      (rationalVertices i 2 - tightVertex seedVertex i 2) ^ 2 ≤ (4 / 10^16 : ℚ) ^ 2
  rationalVertex_sq_norm_bounds : ∀ i,
    (1 / 100 : ℚ) ≤ rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 +
        rationalVertices i 2 ^ 2 ∧
      rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2

/-- The solid model of a fivefold solid: C5 about z, Taylor symmetry
matrices within `κ/2`, model error `6 · 10⁻¹⁶`; C++ vertex `n` is slot `n`.
(Reducible, so that compiled code specializes it to the solid's data.) -/
@[reducible] instance FivefoldSolid.toSolidModel [F : FivefoldSolid] : SolidModel where
  orbitCount := 5
  seedCount := F.seedCount
  orbitCount_pos := by norm_num
  seedCount_pos := F.seedCount_pos
  rationalVertices := F.rationalVertices
  seedVertex := F.seedVertex
  symmetryMatrixErased := Erased.mk fivefoldRotation
  symmetryMatrixQ := fivefoldMatrixQ
  symmetryErrorQ := κℚ / 2
  modelErrorQ := 6 / 10^16
  vertexSlot n := ⟨n % (5 * F.seedCount), Nat.mod_lt _ (by have := F.seedCount_pos; omega)⟩
  symmetry_mem k := by rw [Erased.out_mk]; exact fivefoldRotation_mem k
  symmetry_mul a b := by rw [Erased.out_mk]; exact fivefoldRotation_mul a b
  symmetry_zero := by rw [Erased.out_mk]; exact fivefoldRotation_zero
  symmetryQ_close k := by rw [Erased.out_mk]; exact fivefoldMatrixQ_close k
  seed_close i := by
    rw [Erased.out_mk]
    exact fivefold_seed_close F.seedVertex F.rationalVertices F.seed_xy_sq_le_one
      F.tight_sq_close i
  modelErrorQ_nonneg := by norm_num
  modelErrorQ_le := by norm_num
  rationalVertex_sq_norm_bounds := F.rationalVertex_sq_norm_bounds

variable [FivefoldSolid]

theorem symmetryMatrix_eq_fivefoldRotation (k : OrbitIndex) :
    symmetryMatrix k = fivefoldRotation k :=
  congrFun (Erased.out_mk fivefoldRotation) k

@[simp] theorem orbitCount_eq_five : SolidModel.orbitCount = 5 := rfl

theorem card_vertexIndex : Fintype.card VertexIndex = 5 * SolidModel.seedCount := by
  simp

/-- The exact symmetry acts on points as `RzL (2πk/5)`. -/
theorem symmetryMatrix_apply_eq_RzL (k : OrbitIndex) (v : ℝ³) :
    (symmetryMatrix k).toEuclideanLin v = RzL (2 * Real.pi * (k : ℝ) / 5) v := by
  rw [symmetryMatrix_eq_fivefoldRotation]
  rfl

/-- Vertex `i` of a fivefold model is its seed rotated by `2π (orbitIndex i)/5`. -/
theorem CyclicModel.vertex_eq_RzL (P : CyclicModel) (i : VertexIndex) :
    P.vertex i = RzL (2 * Real.pi * (orbitIndex i : ℝ) / 5) (P.seed (seedIndex i)) :=
  symmetryMatrix_apply_eq_RzL _ _

omit [FivefoldSolid] in
/-- Slot arithmetic for the rotation-major layout. -/
theorem fivefold_slot_lt {S k s : ℕ} (hk : k + 1 < 5) (hs : s < S) :
    S * k + s < 5 * S - S := by
  have h1 : S * k + s < S * (k + 1) := by rw [Nat.mul_succ]; omega
  have h2 : S * (k + 1) ≤ S * 4 := Nat.mul_le_mul_left _ (by omega)
  omega

end Noperts.Pipeline

end
