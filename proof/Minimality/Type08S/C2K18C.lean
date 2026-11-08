module

public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K17GA11

@[expose] public section


/-!
# K18 / C: S1.2a on the closed side (`⟪a-d,a-c'⟫ ≥ 0`), closing the Zdb(ii) slice (L3)

`k17ga_s12a_core` uses `ζ_{a-c'}(a,d) > 0` only for `qr > 0`; on the tie `β1 qr = (1-α1) pr - ⟪a-c',r⟫ > 0` still
(`pr < 0` from `pp = κ pr`).  So S1.2a covers `≥ 0` and S1.2b (`< 0`, K17GA) the rest: no leftover.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- **S1.2a core**: Zdb(ii) (`ζ(d,b) = 0`, `z(a) = z(d)` at `a - b'`) with `ζ_{a-c'}(a,d) = ⟪a-d,a-c'⟫ > 0`:
the cell `(a,b',c,a',c')@a-b'`. -/
theorem k18_s12a_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d))
    (hα11 : 1 < α1) (hα41 : 1 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6)
    (hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6))
    (hE0 : 0 ≤ α4 - α4 * β1 - α1 + α1 * γ4) (hζ0 : ⟪d - b, a - b'⟫ = 0)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : 0 ≤ ⟪a - d, a - c'⟫) :
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
  have haa : ⟪a - d, a - b'⟫ = κ * ⟪r, R⟫ + σ * ⟪R, R⟫ := by
    rw [← hR, ← hp, hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [real_inner_comm R r]; ring
  have hZa : κ * ⟪r, R⟫ + σ * ⟪R, R⟫ = 0 := by rw [← haa]; exact hZ
  have hac : a - c' = (-β1) • q + (κ * (1 - α1)) • r + (σ * (1 - α1)) • R := by
    have h : p = σ • R + κ • r := hpR
    rw [hc']
    have : a - (d + α1 • (a - d) + β1 • (b - d)) = (1 - α1) • p - β1 • q := by rw [hp, hq]; module
    rw [this, h]; module
  have h1 : ⟪a - c', r⟫ = -β1 * ⟪q, r⟫ + κ * (1 - α1) * ⟪r, r⟫ + σ * (1 - α1) * ⟪r, R⟫ := by
    rw [hac, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm R r]
  have h2 : ⟪a - d, a - c'⟫ = κ * ⟪a - c', r⟫ := by
    rw [h1, ← hp, hpR]
    conv_lhs => rw [hac]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm q R, real_inner_comm q r, real_inner_comm r R]
    linear_combination (-σ * β1) * hB0 + σ * (1 - α1) * hZa
  have hpr : ⟪a - d, r⟫ = σ * ⟪r, R⟫ + κ * ⟪r, r⟫ := by
    rw [← hp, hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm R r]
  have hpp : ⟪a - d, a - d⟫ = κ * ⟪a - d, r⟫ := by
    have : ⟪a - d, a - d⟫ = ⟪a - d, σ • R + κ • r⟫ := by rw [← hpR]
    rw [this, inner_add_right, real_inner_smul_right, real_inner_smul_right, hZ]; ring
  have hppos : 0 < ⟪a - d, a - d⟫ := real_inner_self_pos.2 (by
    intro h0; apply hdet
    have h0' : p = 0 := by rw [hp]; exact h0
    rw [h0']; simp [det3_expand])
  have hL : 0 < ⟪q, r⟫ := by
    have hX : ⟪a - c', r⟫ ≤ 0 := by
      by_contra hh; push Not at hh; nlinarith [mul_pos (neg_pos.2 hκ0) hh]
    have hpr0 : ⟪a - d, r⟫ < 0 := by
      by_contra hh; push Not at hh; nlinarith [mul_nonneg (neg_pos.2 hκ0).le hh]
    have hkey : β1 * ⟪q, r⟫ = (1 - α1) * ⟪a - d, r⟫ - ⟪a - c', r⟫ := by rw [h1, hpr]; ring
    have : 0 < β1 * ⟪q, r⟫ := by rw [hkey]; nlinarith [mul_pos (by linarith : (0:ℝ) < α1 - 1) (neg_pos.2 hpr0)]
    exact pos_of_mul_pos_right this hβ1.le
  refine k17ga_s12a_frame (V8 a a' b b' c c' d) q r R d hΔ hκ0 hσ0 hα11 hβ1 hb6 hbc hE hB0 hZa hL ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gaA, pc5_0, eC']; simp [V8]
    · simp only [k17gaA, pc5_1, eA']; simp [V8]
    · simp only [k17gaA, pc5_2, eC]; simp [V8]
    · simp only [k17gaA, pc5_3, eB']; simp [V8]
    · simp only [k17gaA, pc5_4, eA]; simp [V8]
  · intro y hy
    rw [eA, eC', eA', eC, eO, eB, eB']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

/-- **S1.2a, Tc regime** (Zdb(ii), `ζ_{a-c'}(a,d) > 0`): cell `(a,b',c,a',c')@a-b'`. -/
theorem k18_s12a_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : 0 ≤ ⟪a - d, a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hpl, hE0⟩ :=
    k17ga_tc_coords W h
  have hb61 : 1 < β6 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hγ4.le (sub_nonneg.2 hh)]
  have hbc0 : 1 < β1 + (-γ4 / (α4 - 1)) * α1 * (1 - β6) := by
    have : (-γ4 / (α4 - 1)) * (1 - β6) = 1 := by
      have hne : β6 - 1 ≠ 0 := (sub_pos.2 hb61).ne'
      rw [hpl]; field_simp; ring
    have e : (-γ4 / (α4 - 1)) * α1 * (1 - β6) = α1 := by
      calc (-γ4 / (α4 - 1)) * α1 * (1 - β6) = ((-γ4 / (α4 - 1)) * (1 - β6)) * α1 := by ring
        _ = α1 := by rw [this]; ring
    rw [e]; linarith
  exact k18_s12a_core hdet hc' hb' ha' hα11 hα41 hβ1 hγ4 hb6 hbc0 hE0 hζ0 hZ hlit

/-- **S1.2a, Ta regime**. -/
theorem k18_s12a_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) (hlit : 0 ≤ ⟪a - d, a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hbc0, hE0⟩ :=
    k17ga_ta_coords W h
  exact k18_s12a_core hdet hc' hb' ha' hα11 hα41 (by linarith) hγ4 hb6 hbc0 hE0 hζ0 hZ hlit

/-- **S1.2 (Zdb(ii)), Tc: closed.** -/
theorem k18_s12_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  rcases le_or_gt 0 ⟪a - d, a - c'⟫ with hl | hl
  · exact k18_s12a_tc W h hZ hl
  · exact k17ga_s12b_tc W h hZ hl

/-- **S1.2 (Zdb(ii)), Ta: closed.** -/
theorem k18_s12_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hZ : ⟪a - d, a - b'⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  rcases le_or_gt 0 ⟪a - d, a - c'⟫ with hl | hl
  · exact k18_s12a_ta W h hZ hl
  · exact k17ga_s12b_ta W h hZ hl

end C2
end Type08Sp
end Minimality
