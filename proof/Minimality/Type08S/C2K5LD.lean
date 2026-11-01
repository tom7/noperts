module

public import Minimality.Type08S.C2K5LC

@[expose] public section


/-!
# K5L / D: K5e (QTouch), the case `β1 < 1`: face cell `Q_bc = (d, b, a', c)` at `b' - c`
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `β1 - 1` as a point-form determinant ratio: `det3 (a-d) (c'-b) (c-d) = (β1 - 1) Δ`. -/
theorem det_beta1 {a b c c' d : ℝ³} {α1 β1 : ℝ} (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) :
    det3 (a - d) (c' - b) (c - d) = (β1 - 1) * det3 (a - d) (b - d) (c - d) := by
  rw [hc']
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem k5e_lt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6, -⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  have hβ11 : β1 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hw : 0 < 1 - γ4 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ γ4 - 1), mul_pos hα4 (sub_pos.2 hβ11)]
  obtain ⟨w, hwdef⟩ : ∃ w, w = 1 - γ4 := ⟨_, rfl⟩
  rw [← hwdef] at hw hκ'
  obtain ⟨m, hm⟩ : ∃ m, m = α4 / w := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = -1 / w := ⟨_, rfl⟩
  have hmw : m * w = α4 := by rw [hm]; field_simp
  have hsw : s * w = -1 := by rw [hs]; field_simp
  have hm1 : 1 < m := by
    by_contra hh; push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh hw.le]
  have hs0 : s < 0 := by rw [hs]; exact div_neg_of_neg_of_pos (by norm_num) hw
  have hα1m : α1 = m * (1 - β1) := by
    have : (α1 - m * (1 - β1)) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := b' - c with hR
  have hRv : R = α4 • p + (γ4 - 1) • r := by
    rw [hR, hb', hp, hr]; module
  have hmα : m + s * α4 = 0 := by
    have : (m + s * α4) * w = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_right hw.ne'
  have hcR : m • p + s • R = r := by
    rw [hRv]
    match_scalars <;> nlinarith
  have hΔ : det3 q p R ≠ 0 := by
    have e : det3 q p R = w * det3 p q r := by
      rw [hRv, hwdef]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero hw.ne' hdet
  have hfp : ∀ x y z : ℝ, fpoint q p R d (x, y, z) = d + x • q + y • p + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint q p R d (0, 0, 0) = d := by rw [hfp]; simp
  have eB : fpoint q p R d (1, 0, 0) = b := by rw [hfp, hq]; module
  have eA : fpoint q p R d (0, 1, 0) = a := by rw [hfp, hp]; module
  have eC : fpoint q p R d (0, m, s) = c := by
    rw [hfp]; rw [hr] at hcR
    linear_combination (norm := module) hcR
  have eA' : fpoint q p R d (β6, m, s) = a' := by
    rw [hfp, ha']; rw [hr] at hcR
    linear_combination (norm := module) hcR
  have eC' : fpoint q p R d (β1, α1, 0) = c' := by rw [hfp, hc']; module
  have eB' : fpoint q p R d (0, m, s + 1) = b' := by
    rw [hfp]; rw [hr] at hcR
    linear_combination (norm := module) hcR + (1 : ℝ) • hR
  refine ⟨R, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  · refine k5e_fcbc_frame (V8 a a' b b' c c' d) q p R d hΔ hm1 hs0 hβ6 hβ1 hβ11 hα1m ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [kcCyc_0, eO]; simp [V8]
      · simp only [kcCyc_1, eB]; simp [V8]
      · simp only [kcCyc_2, eA']; simp [V8]
      · simp only [kcCyc_3, eC]; simp [V8]
    · intro y hy
      rw [eO, eB, eA', eC, eA, eC', eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
