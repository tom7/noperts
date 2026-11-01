module

public import Minimality.Type08S.C2K6

@[expose] public section

/-!
# K8A: infrastructure for the `s = 0` cells of package K3

* `k8_cell_gen`: `k3_cell_gen` with a lex hypothesis that may depend on the tilt parameter `lam`
  (and on the explicit form of `w`).
* `k8_wdiff`: tilt-weight difference of two frame points.
* `k8_tilt_pos` / `k8_tilt_neg`: choice of a tilt segment in a quadrant with prescribed sign of a tie form.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
theorem k8_cell_gen (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hcyc : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (u1 + lam * t1, u2 + lam * t2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i)
        (u1 + lam * t1, u2 + lam * t2, 0))
    (hlex : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ w : ZMod k → ℝ,
      (∀ i, w i = ⟪fpoint p q r d (Y i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫) →
      (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ → w i = w j → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) w) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y hYinj hut (lo := 0) (hi := 1) (by norm_num)
  have hlexY := hlex lam hl0 hl1
    (fun i => ⟪fpoint p q r d (Y i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫) (fun i => rfl)
    (fun i j h1 h2 => hsep i j h1 h2)
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨k, inferInstance, fun i => fpoint p q r d (Y (-i)), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0, ?_⟩
    refine lexCell_coord V p q r d hk (fun i => Y (-i)) (u1 + lam * t1, u2 + lam * t2, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc lam hl0 hl1 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    obtain ⟨t, rfl, ht⟩ := hrest y hy (fun j h => hyx (-j) (by simpa using h))
    exact ⟨t, rfl, hrest_rev (ht lam hl0 hl1 _ hD)⟩
  · refine ⟨k, inferInstance, fun i => fpoint p q r d (Y i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0, ?_⟩
    refine lexCell_coord V p q r d hk Y (u1 + lam * t1, u2 + lam * t2, 0) hmem
      (hcyc lam hl0 hl1 _ hpos) ?_ hlexY
    intro y hy hyx
    obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
    exact ⟨t, rfl, ht lam hl0 hl1 _ hpos⟩

/-- Weight difference of two frame points for the tilt `fcomb p q r v1 v2 0`. -/
theorem k8_wdiff (p q r d : ℝ³) (s t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    ⟪fpoint p q r d s, fcomb p q r v1 v2 0⟫ - ⟪fpoint p q r d t, fcomb p q r v1 v2 0⟫ =
      v1 * ⟪fpoint p q r d s - fpoint p q r d t, p⟫ + v2 * ⟪fpoint p q r d s - fpoint p q r d t, q⟫ := by
  rw [← inner_sub_left]
  simp only [fcomb, inner_sub_left, inner_add_right, inner_smul_right, zero_smul, inner_zero_right]
  rw [real_inner_comm p, real_inner_comm q]
  ring

/-- Real numbers `η > 0` with `2 η |x| < -y` when `y < 0`. -/
theorem k8_eta {x y : ℝ} (hy : y ≠ 0) : ∃ η : ℝ, 0 < η ∧ 2 * η * |x| < |y| := by
  have h1 : 0 < |y| := abs_pos.2 hy
  have h2 : 0 ≤ |x| := abs_nonneg x
  have hpos : 0 < 4 * (|x| + 1) := by positivity
  refine ⟨|y| / (4 * (|x| + 1)), by positivity, ?_⟩
  have e : |y| / (4 * (|x| + 1)) * (4 * (|x| + 1)) = |y| := div_mul_cancel₀ _ hpos.ne'
  have hη : 0 < |y| / (4 * (|x| + 1)) := by positivity
  nlinarith [mul_nonneg hη.le h2]

end C2
end Type08Sp
end Minimality
