module

public import Minimality.Type08S.C2K5LG

@[expose] public section


/-!
# K5L / H: K5e (QTouch), the case `β1 > 1`: pentagon `(a, d, c, a', c')` at `b' - c`
Uses the far triple tie `TieT4` (`⟪c - b', q⟫ = 0 = ⟪c' - b', q⟫`, `q = b - d`) and `1 < α1` (T4 region).
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

set_option maxHeartbeats 1600000 in
theorem k5e_gt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hTie : TieT4 b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  have hβ11 : 1 < β1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  have hw : 0 < γ4 - 1 := by
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ 1 - γ4), mul_pos hα4 (sub_pos.2 hβ11)]
  obtain ⟨w, hwdef⟩ : ∃ w, w = γ4 - 1 := ⟨_, rfl⟩
  rw [← hwdef] at hw
  obtain ⟨m, hm⟩ : ∃ m, m = -α4 / w := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = 1 / w := ⟨_, rfl⟩
  have hmw : m * w = -α4 := by rw [hm]; field_simp
  have hsw : s * w = 1 := by rw [hs]; field_simp
  have hm0 : m < 0 := by rw [hm]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hs0 : 0 < s := by rw [hs]; positivity
  have hα1m : α1 = m * (1 - β1) := by
    have : (α1 - m * (1 - β1)) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := b' - c with hR
  have hRv : R = α4 • p + w • r := by
    rw [hR, hb', hp, hr, hwdef]; module
  have hmα : m + s * α4 = 0 := by
    have : (m + s * α4) * w = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_right hw.ne'
  have hcR : m • p + s • R = r := by
    rw [hRv]
    match_scalars <;> nlinarith
  have hΔ : det3 q p R ≠ 0 := by
    have e : det3 q p R = -w * det3 p q r := by
      rw [hRv]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (neg_ne_zero.2 hw.ne') hdet
  have hfp : ∀ x y z : ℝ, fpoint q p R d (x, y, z) = d + x • q + y • p + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint q p R d (0, 0, 0) = d := by rw [hfp]; simp
  have eB : fpoint q p R d (1, 0, 0) = b := by rw [hfp, hq]; module
  have eA : fpoint q p R d (0, 1, 0) = a := by rw [hfp, hp]; module
  have eC : fpoint q p R d (0, m, s) = c := by
    rw [hfp]; have h := hcR; rw [hr] at h
    linear_combination (norm := module) h
  have eA' : fpoint q p R d (β6, m, s) = a' := by
    rw [hfp, ha']; have h := hcR; rw [hr] at h
    linear_combination (norm := module) h
  have eC' : fpoint q p R d (β1, α1, 0) = c' := by rw [hfp, hc']; module
  have eB' : fpoint q p R d (0, m, s + 1) = b' := by
    rw [hfp]; have h := hcR; rw [hr] at h
    linear_combination (norm := module) h + (1 : ℝ) • hR
  -- metric: `⟪q, R⟫ = 0` and `⟪q, p⟫ < 0`
  have hBq : ⟪q, R⟫ = 0 := by
    obtain ⟨h1, h2⟩ := hTie
    have : ⟪b' - c, b - d⟫ = 0 := by rw [inner_sub_left, h1]; ring
    rw [real_inner_comm]; exact this
  have hqc : ⟪c' - c, q⟫ = 0 := by
    obtain ⟨h1, h2⟩ := hTie
    rw [inner_sub_left, h2, h1]; ring
  have hN : 0 < ⟪q, q⟫ := by
    apply real_inner_self_pos.2
    intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hcc : c' - c = β1 • q + (α1 - m) • p - s • R := by
    rw [hc']
    have h := hcR; rw [hr] at h
    linear_combination (norm := module) h
  have hqp : ⟪q, p⟫ < 0 := by
    rw [hcc] at hqc
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at hqc
    have e1 : ⟪R, q⟫ = 0 := by rw [real_inner_comm]; exact hBq
    have e2 : ⟪p, q⟫ = ⟪q, p⟫ := real_inner_comm _ _
    rw [e1, e2] at hqc
    have hmm : 0 < α1 - m := by linarith
    nlinarith [mul_pos hβ1 hN]
  refine ⟨R, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  · refine k5e_pent_frame (V8 a a' b b' c c' d) q p R d hΔ hm0 hs0 hβ6 hβ11 hα1m hα11.le hBq hqp ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kpCyc_0, eA]; simp [V8]
      · simp only [kpCyc_1, eO]; simp [V8]
      · simp only [kpCyc_2, eC]; simp [V8]
      · simp only [kpCyc_3, eA']; simp [V8]
      · simp only [kpCyc_4, eC']; simp [V8]
    · intro y hy
      rw [eA, eO, eC, eA', eC', eB, eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
