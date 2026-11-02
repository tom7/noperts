module

public import Minimality.Type08S.C2K6TDB

@[expose] public section

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

/-- **Zdb leftover (K6TL4)**: `ζ(d,b) = 0` and either `ζ_{a-b'}(c',c) = ⟪c' - c, a - b'⟫ = 0` or `z(a) = z(d)` at the view
`a - b'`; both codim 5. -/
def K6t4Zdb0 (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪d - b, a - b'⟫ = 0 ∧ (⟪c' - c, a - b'⟫ = 0 ∨ ⟪a - d, a - b'⟫ = 0)

set_option maxHeartbeats 3200000 in
/-- Core of 2b and 4g with the spec's two cells (no feasible-tilt hypothesis): `ζ(d,b) = 0`; cell `(a,d,c,a',c')` if
`ζ(c',c) > 0` (and `z(a) ≠ z(d)`), cell `(c',a',c,b')` if `ζ(c',c) < 0`. -/
theorem k6t4_zdb_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d))
    (hα11 : 1 < α1) (hα41 : 1 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6)
    (hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6))
    (hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4) (hζ0 : ⟪d - b, a - b'⟫ = 0)
    (hz1 : ⟪c' - c, a - b'⟫ ≠ 0) (hz2 : 0 < ⟪c' - c, a - b'⟫ → ⟪a - d, a - b'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
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
  have hbc : 1 < β1 + κ * α1 * (1 - β6) := by rw [hκ, hwdef]; exact hbc0
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
  have hB0 : ⟪q, R⟫ = 0 := by rw [hBR, hζ0]; simp
  -- `ζ(c',c)` and `z(a) - z(d)` in frame coordinates
  have hcc : ⟪c' - c, a - b'⟫ = α1 * (κ * ⟪r, R⟫ + σ * ⟪R, R⟫) - ⟪r, R⟫ := by
    have e : c' - c = β1 • q + (κ * α1 - 1) • r + (α1 * σ) • R := by
      have h : p = σ • R + κ • r := hpR
      have hc : c = d + r := by rw [hr]; abel
      rw [hc', hc]
      linear_combination (norm := module) α1 • h
    rw [e, ← hR, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hB0]
    ring
  have haa : ⟪a - d, a - b'⟫ = κ * ⟪r, R⟫ + σ * ⟪R, R⟫ := by
    rw [← hR, ← hp, hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [real_inner_comm R r]; ring
  rcases lt_or_gt_of_ne hz1 with hneg | hpos
  · -- `ζ(c',c) < 0`: cell 2
    rw [hcc] at hneg
    refine k6t4_qtc2_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hbc hE hB0 (by linarith) ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [kmCyc2_0, eB']; simp [V8]
      · simp only [kmCyc2_1, eC']; simp [V8]
      · simp only [kmCyc2_2, eA']; simp [V8]
      · simp only [kmCyc2_3, eC]; simp [V8]
    · intro y hy
      rw [eA, eC', eA', eC, eO, eB, eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · -- `ζ(c',c) > 0`: cell 1
    have hZ := hz2 hpos
    rw [haa] at hZ
    rw [hcc] at hpos
    refine k6t4_qtc1_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hbc hE hB0 hZ (by linarith) ?_ ?_
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
