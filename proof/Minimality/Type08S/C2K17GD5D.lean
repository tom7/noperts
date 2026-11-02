module

public import Minimality.Type08S.C2K17GD5C

@[expose] public section


/-!
# K17GD / GD5: the slice `K6tTaE` (Ta box E: `α4 > 1`, `β1 > 1`, `β6 < 1`, `ζ_E = ⟪b-a', a-c'⟫ = 0`), generic part `⟪b-b', a-c'⟫ ≠ 0`

View `R = a - c'`, frame `(p, r, R)` of K5f box E.  On the tie `z(a') = z(b)` with `L = z(b) - z(b') = ⟪b-b',R⟫`:
* `L < 0`: cell E1 `(a,b',a',b,d)` (cone `v1 < 0 < v2`): `z(b) < z(d)` (algebra of `k5f_E1_real`, equality allowed), `y = ⟪r,R⟫ < 0`, `a` not a valley.
* `L > 0`: cell E2 `(c',b',a',b)` (cone `0 < v1`, `v2 < 0`): `z(c') < z(b)` (algebra of `k5f_E2_real`), the peak is the larger of `a', b` (any tilt).
* Leftover `L = 0` (the S1.9 double tie).  No tilt-dependent tie-breaking is needed.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- **K6tTaE, generic part**: a lex cell, or the leftover `⟪b-b', a-c'⟫ = 0`.  Needs `hfar := k5z_far2 W hT hT'`. -/
theorem k17gd_taE {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6tTaE a a' b b' c c' d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪b - b', a - c'⟫ = 0 := by
  obtain ⟨hT, hκ, hβ, hα, hβ6, hζ0⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6p, hfar'⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  rw [det_alpha4 hb'] at hα
  rw [k5f_det_beta6 ha'] at hβ6
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  have hβ11 : 1 < β1 := by nlinarith
  have hα41 : 1 < α4 := by nlinarith
  have hβ61 : β6 < 1 := by nlinarith
  have hα11 : 1 < α1 := hfar' hfar
  have hγ41 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ 1 - γ4), mul_pos (by linarith : 0 < α4) (sub_pos.2 hβ11)]
  have hb1 : β1 ≠ 0 := by positivity
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := a - c' with hR
  obtain ⟨m, hmdef⟩ : ∃ m, m = (α1 - 1) / β1 := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = 1 / β1 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact div_pos (by linarith) hβ1
  have hk : 0 < k := by rw [hkdef]; exact div_pos one_pos hβ1
  have hk1 : k < 1 := by rw [hkdef, div_lt_one hβ1]; exact hβ11
  have hrel : (γ4 - 1) * (m + k) = α4 * (1 - k) := by
    rw [hmdef, hkdef]; field_simp; linarith
  have hRv : R = (1 - α1) • p - β1 • q := by rw [hR, hc', hp, hq]; module
  have hqv : q = (-m) • p + (-k) • R := by
    rw [hRv, hmdef, hkdef]
    match_scalars <;> field_simp <;> ring
  have hΔ : det3 p r R ≠ 0 := by
    have : det3 p r R = β1 * det3 (a - d) (b - d) (c - d) := by
      rw [hRv]; simp only [hp, hq, hr, det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [this]; exact mul_ne_zero hb1 hdet
  have eO : fpoint p r R d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p r R d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eC : fpoint p r R d (0, 1, 0) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p r R d (1, 0, -1) = c' := by simp only [fpoint, fcomb, hR]; module
  have eB : fpoint p r R d (-m, 0, -k) = b := by
    simp only [fpoint, fcomb]
    have : b = d + q := by rw [hq]; module
    rw [this, hqv]; module
  have eB' : fpoint p r R d (α4, γ4, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p r R d (-β6 * m, 1, -β6 * k) = a' := by
    simp only [fpoint, fcomb]
    have : a' = d + β6 • q + r := by rw [ha', hr]; module
    rw [this, hqv]; module
  have hne : R ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p r R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪p, R⟫ + t.2.1 * ⟪r, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hLid : ⟪b - b', R⟫ = (-m * ⟪p, R⟫ - k * ⟪R, R⟫) - (α4 * ⟪p, R⟫ + γ4 * ⟪r, R⟫) := by
    have e : ⟪b - b', R⟫ = ⟪fpoint p r R d (-m, 0, -k), R⟫ - ⟪fpoint p r R d (α4, γ4, 0), R⟫ := by
      rw [eB, eB', inner_sub_left]
    rw [e, hz, hz]; simp only; ring
  have hTid : ⟪b - a', R⟫ = (-m * ⟪p, R⟫ - k * ⟪R, R⟫) - (-β6 * ⟪p, R⟫ * m + ⟪r, R⟫ - β6 * k * ⟪R, R⟫) := by
    have e : ⟪b - a', R⟫ = ⟪fpoint p r R d (-m, 0, -k), R⟫ - ⟪fpoint p r R d (-β6 * m, 1, -β6 * k), R⟫ := by
      rw [eB, eA', inner_sub_left]
    rw [e, hz, hz]; simp only; ring
  have hT : -β6 * ⟪p, R⟫ * m + ⟪r, R⟫ - β6 * k * ⟪R, R⟫ = -m * ⟪p, R⟫ - k * ⟪R, R⟫ := by
    have := hTid; rw [hζ0] at this; linarith
  rcases lt_trichotomy ⟪b - b', R⟫ 0 with hneg | hzero | hpos
  · refine Or.inl ⟨R, hne, k17gdE1_frame (V8 a a' b b' c c' d) p r R d hΔ hm hk hk1 hβ6p hβ61 hα41 hγ41 hrel hT
      (by rw [hLid] at hneg; linarith) ?_ ?_⟩
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k5fE1Cyc, pc5_0, eA]; simp [V8]
      · simp only [k5fE1Cyc, pc5_1, eB']; simp [V8]
      · simp only [k5fE1Cyc, pc5_2, eA']; simp [V8]
      · simp only [k5fE1Cyc, pc5_3, eB]; simp [V8]
      · simp only [k5fE1Cyc, pc5_4, eO]; simp [V8]
    · intro y hy
      rw [eA, eB', eA', eB, eO, eC', eC]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · exact Or.inr hzero
  · refine Or.inl ⟨R, hne, k17gdE2_frame (V8 a a' b b' c c' d) p r R d hΔ hm hk hk1 hβ6p hβ61 hα41 hγ41 hrel hT
      (by rw [hLid] at hpos; linarith) ?_ ?_⟩
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [k5fE2Cyc_0, eC']; simp [V8]
      · simp only [k5fE2Cyc_1, eB']; simp [V8]
      · simp only [k5fE2Cyc_2, eA']; simp [V8]
      · simp only [k5fE2Cyc_3, eB]; simp [V8]
    · intro y hy
      rw [eC', eB', eA', eB, eA, eO, eC]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
