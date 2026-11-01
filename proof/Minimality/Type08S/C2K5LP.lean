module

public import Minimality.Type08S.C2K5LO

@[expose] public section


/-!
# K5L / P: QTc with `α4 > 1` (T, κ_c = 0): the two cells at `a - b'`, split by `ζ(d,b) = ⟪d - b, a - b'⟫`
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

set_option maxHeartbeats 3200000 in
/-- **QTc, `α4 > 1`**: `T`, `κ_c = 0`, `ζ(d,b) = ⟪d - b, a - b'⟫ ≠ 0`.  Needs the T4 far end `1 < α1` and `κ_b > 0`
(for `κ_a ≥ 0 ⇒ α4(1-β1) ≥ α1(1-γ4)`). -/
theorem k5c_qtc_gt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκc : det3 (b - a) (a' - a) (b' - a) = 0)
    (hα4 : 0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d))
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hκb : 0 < galeD W.G.l W.G.m b b')
    (hζ : ⟪d - b, a - b'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  -- Gale: `E ≥ 0`
  obtain ⟨μ, hμa, hμb⟩ := gale_pt W hdet hc' hb' ha' (by linarith)
  have hμ : 0 < μ := by
    rw [hμb] at hκb
    have : 0 < β6 * (α1 - 1) := mul_pos hβ6 (by linarith)
    by_contra hh; push Not at hh
    nlinarith
  have hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4 := by
    have := W.hκa
    rw [hμa] at this
    exact nonneg_of_mul_nonneg_right this hμ
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = -1 / w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = -γ4 / w := ⟨_, rfl⟩
  have hσw : σ * w = -1 := by rw [hσ]; field_simp
  have hκw : κ * w = -γ4 := by rw [hκ]; field_simp
  have hσ0 : σ < 0 := by rw [hσ]; exact div_neg_of_neg_of_pos (by norm_num) hw
  have hκ0 : κ < 0 := by rw [hκ]; exact div_neg_of_neg_of_pos (by linarith) hw
  have hκσ : κ = σ * γ4 := by
    have : (κ - σ * γ4) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hb6 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (by linarith : 0 ≤ 1 - β6)]
  have hκ6 : κ * (1 - β6) = 1 := by
    have : (κ * (1 - β6) - 1) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  have hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ) := by
    have : ((σ - 1) * (1 - β1) - α1 * (σ - κ)) * w ≤ 0 := by nlinarith
    by_contra hh; push Not at hh
    nlinarith [mul_pos (sub_pos.2 hh) hw]
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := a - b' with hR
  have hRv : R = (-w) • p - γ4 • r := by
    rw [hR, hb', hp, hr, hwdef]; module
  have hpR : p = σ • R + κ • r := by
    rw [hRv]
    match_scalars <;> nlinarith
  have hΔ : det3 q r R ≠ 0 := by
    have e : det3 q r R = (-w) * det3 p q r := by
      rw [hRv]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (neg_ne_zero.2 hw.ne') hdet
  have hfp : ∀ x y z : ℝ, fpoint q r R d (x, y, z) = d + x • q + y • r + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint q r R d (0, 0, 0) = d := by rw [hfp]; simp
  have eB : fpoint q r R d (1, 0, 0) = b := by rw [hfp, hq]; module
  have eC : fpoint q r R d (0, 1, 0) = c := by rw [hfp, hr]; module
  have eA : fpoint q r R d (0, κ, σ) = a := by
    rw [hfp]; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-1 : ℝ) • h
  have eB' : fpoint q r R d (0, κ, σ - 1) = b' := by
    rw [hfp]; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-1 : ℝ) • h + (1 : ℝ) • hR
  have eC' : fpoint q r R d (β1, κ * α1, α1 * σ) = c' := by
    rw [hfp, hc']; have h := hpR; rw [hp] at h
    linear_combination (norm := module) (-α1) • h
  have eA' : fpoint q r R d (β6, 1, 0) = a' := by
    rw [hfp, ha']; module
  have hBR : ⟪q, R⟫ = -⟪d - b, a - b'⟫ := by
    rw [hq, hR, ← inner_neg_left]; congr 1; abel
  have hRne : R ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine ⟨R, hRne, ?_⟩
  rcases lt_or_gt_of_ne hζ with hneg | hpos
  · -- `ζ(d,b) < 0`: cell 2
    refine k5c_qtc2_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hκ6 hE
      (by rw [hBR]; linarith) ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [kmCyc2_0, eB']; simp [V8]
      · simp only [kmCyc2_1, eC']; simp [V8]
      · simp only [kmCyc2_2, eA']; simp [V8]
      · simp only [kmCyc2_3, eC]; simp [V8]
    · intro y hy
      rw [eB', eC', eA', eC, eA, eO, eB]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · -- `ζ(d,b) > 0`: cell 1
    refine k5c_qtc1_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hκ6 hE
      (by rw [hBR]; linarith) ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kmCyc1_0, eA]; simp [V8]
      · simp only [kmCyc1_1, eC']; simp [V8]
      · simp only [kmCyc1_2, eA']; simp [V8]
      · simp only [kmCyc1_3, eC]; simp [V8]
      · simp only [kmCyc1_4, eO]; simp [V8]
    · intro y hy
      rw [eA, eC', eA', eC, eO, eB, eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
