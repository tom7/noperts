module

public import Minimality.Type08S.C2K5LK

@[expose] public section


/-!
# K5L / L: K5c, FC-ab at `a - b'`: core (coordinates) + QPc (`T'`) and QTc (`T`) wrappers for `α4 < 1`
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
theorem k5c_fcab_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ1 : 0 < β1) (hαβ : 1 < α1 + β1) (hα4 : α4 < 1) (hγ4 : 0 < γ4)
    (hαγ : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hκc : γ6 * (1 - α4) = γ4 * (1 - β6)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hw : 0 < 1 - α4 := by linarith
  obtain ⟨w, hwdef⟩ : ∃ w, w = 1 - α4 := ⟨_, rfl⟩
  rw [← hwdef] at hw hκc
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 1 / w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = γ4 / w := ⟨_, rfl⟩
  have hσw : σ * w = 1 := by rw [hσ]; field_simp
  have hκw : κ * w = γ4 := by rw [hκ]; field_simp
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hκ1 : 1 < κ := by
    by_contra hh; push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh hw.le]
  have hb61 : β6 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hγ4 (by linarith : (0:ℝ) < 1)]
  have hγ6κ : γ6 = κ * (1 - β6) := by
    have : (γ6 - κ * (1 - β6)) * w = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw.ne')
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := a - b' with hR
  have hRv : R = w • p - γ4 • r := by
    rw [hR, hb', hp, hr, hwdef]; module
  have hpR : p = σ • R + κ • r := by
    rw [hRv]
    match_scalars <;> nlinarith
  have hΔ : det3 q r R ≠ 0 := by
    have e : det3 q r R = w * det3 p q r := by
      rw [hRv]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero hw.ne' hdet
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
  have eA' : fpoint q r R d (β6, κ * (1 - β6), 0) = a' := by
    rw [hfp, ha', hγ6κ]; module
  refine ⟨R, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  · refine k5c_fcab_frame (V8 a a' b b' c c' d) q r R d hΔ hκ1 hσ0 hα1 hβ1 hαβ hβ6 hb61 ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [krCyc_0, eA]; simp [V8]
      · simp only [krCyc_1, eO]; simp [V8]
      · simp only [krCyc_2, eB]; simp [V8]
      · simp only [krCyc_3, eC']; simp [V8]
    · intro y hy
      rw [eA, eO, eB, eC', eC, eA', eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

/-- **QPc, `α4 < 1`** (`T'`, `κ_c = 0`): FC-ab at `a - b'`. -/
theorem k5c_qpc_lt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκc : det3 (b - a) (a' - a) (b' - a) = 0)
    (hα4 : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, -⟩ :=
    norm08w_coordsTp W hT'
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  exact k5c_fcab_core hdet (α1 := 1) hc' hb' ha' one_pos hβ1 (by linarith) hα41 hγ4
    hαγ hβ6 hγ6 hκ'

/-- **QTc, `α4 < 1`** (`T`, `κ_c = 0`): FC-ab at `a - b'`. -/
theorem k5c_qtc_lt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκc : det3 (b - a) (a' - a) (b' - a) = 0)
    (hα4 : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, -⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  rw [det_alpha4 hb'] at hα4
  have hα41 : α4 < 1 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  exact k5c_fcab_core hdet hc' hb' ha' hα1 hβ1 hαβ hα41 hγ4 hαγ hβ6 one_pos (by linarith)

end C2
end Type08Sp
end Minimality
