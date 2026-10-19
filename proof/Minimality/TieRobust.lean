module

public import Minimality.TieForces

@[expose] public section

/-!
# Lemma T at the tie, robust form: the geometric layer

Views `tw v ε = e_z + ε v`; every quantity the scalar core `tie_core` needs
is a polynomial in `ε`, so its eventual bounds come from two elementary
facts (`ev_half`, `ev_abs_quad`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The tilted view `e_z + ε v`. -/
noncomputable def tw (v : ℝ³) (ε : ℝ) : ℝ³ := ez + ε • v

theorem ev_half {A B : ℝ} (h : 0 < A) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A / 2 ≤ A + ε * B := by
  have hc : Continuous fun ε : ℝ => A + ε * B := by fun_prop
  have : ∀ᶠ ε in 𝓝 (0 : ℝ), A / 2 < A + ε * B :=
    hc.continuousAt.eventually (lt_mem_nhds (by simp; linarith))
  exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

theorem ev_le_one : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := gt_mem_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds] with ε h0 h1
  exact ⟨h0, h1.le⟩

theorem ev_abs_quad (A B C : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), |A + ε * B + ε ^ 2 * C| ≤ |A| + |B| + |C| := by
  filter_upwards [ev_le_one] with ε ⟨h0, h1⟩
  have e1 : |ε * B| ≤ |B| := by
    rw [abs_mul, abs_of_pos h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
  have e2 : |ε ^ 2 * C| ≤ |C| := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by nlinarith)
  calc |A + ε * B + ε ^ 2 * C| ≤ |A| + |ε * B| + |ε ^ 2 * C| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ _ := by linarith

theorem ev_small {k : ℝ} : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * k < 1 := by
  have hc : Continuous fun ε : ℝ => ε * k := by fun_prop
  exact (hc.continuousAt.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds

theorem inner_tw (x v : ℝ³) (ε : ℝ) : ⟪x, tw v ε⟫ = x 2 + ε * ⟪x, v⟫ := by
  rw [tw, inner_add_right, real_inner_smul_right, inner_ez]

theorem cross_tw_left (v d : ℝ³) (ε : ℝ) : cross (tw v ε) d = cross ez d + ε • cross v d := by
  ext i; fin_cases i <;> simp [tw, cross, ez] <;> ring

theorem cross_tw_right (v d : ℝ³) (ε : ℝ) : cross d (tw v ε) = cross d ez + ε • cross d v := by
  ext i; fin_cases i <;> simp [tw, cross, ez] <;> ring

theorem cross_swap (a b : ℝ³) : cross a b = -cross b a := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem cross_neg_sub (w a b : ℝ³) : cross w (a - b) = cross (b - a) w := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- Inner products of a tilted generator with a fixed vector are affine in `ε`. -/
theorem inner_gen_left (v d x : ℝ³) (ε : ℝ) :
    ⟪cross (tw v ε) d, x⟫ = ⟪cross ez d, x⟫ + ε * ⟪cross v d, x⟫ := by
  rw [cross_tw_left, inner_add_left, real_inner_smul_left]

theorem inner_gen_right (v d x : ℝ³) (ε : ℝ) :
    ⟪cross d (tw v ε), x⟫ = ⟪cross d ez, x⟫ + ε * ⟪cross d v, x⟫ := by
  rw [cross_tw_right, inner_add_left, real_inner_smul_left]

/-- Torques of tilted generators are quadratic in `ε`. -/
theorem torque_quad (y G0 G1 v : ℝ³) (ε : ℝ) :
    ⟪cross y (G0 + ε • G1), ez + ε • v⟫ =
      ⟪cross y G0, ez⟫ + ε * (⟪cross y G1, ez⟫ + ⟪cross y G0, v⟫) + ε ^ 2 * ⟪cross y G1, v⟫ := by
  have : cross y (G0 + ε • G1) = cross y G0 + ε • cross y G1 := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [this]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

end Minimality

end
