module

public import Minimality.Type08S.C2K5LI

@[expose] public section


/-!
# K5L / J: K5c, QPc with `α4 > 1`: FC-ac at `d - b` (item wrapper; no planarity needed)
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

/-- `α4 - 1` as a point-form determinant: `det3 (b' - a) (b - d) (c - d) = (α4 - 1) Δ`. -/
theorem det_alpha4 {a b b' c d : ℝ³} {α4 γ4 : ℝ} (hb' : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    det3 (b' - a) (b - d) (c - d) = (α4 - 1) * det3 (a - d) (b - d) (c - d) := by
  rw [hb']
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem k5c_qpc_gt_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (hα4 : 0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hγ61⟩ :=
    norm08w_coordsTp W hT'
  have hγ61 := hγ61 hfar
  rw [det_alpha4 hb'] at hα4
  have hα41 : 1 < α4 := by
    have : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
    nlinarith
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set R := d - b with hR
  have hΔ : det3 p r R ≠ 0 := by
    have e : det3 p r R = det3 p q r := by
      rw [hR, hp, hq, hr]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact hdet
  have hfp : ∀ x y z : ℝ, fpoint p r R d (x, y, z) = d + x • p + y • r + z • R := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint p r R d (0, 0, 0) = d := by rw [hfp]; simp
  have eA : fpoint p r R d (1, 0, 0) = a := by rw [hfp, hp]; module
  have eB' : fpoint p r R d (α4, γ4, 0) = b' := by rw [hfp, hb']; module
  have eC : fpoint p r R d (0, 1, 0) = c := by rw [hfp, hr]; module
  have eB : fpoint p r R d (0, 0, -1) = b := by rw [hfp, hR]; module
  have eC' : fpoint p r R d (1, 0, -β1) = c' := by
    rw [hfp, hc', hR, hq]; module
  have eA' : fpoint p r R d (0, γ6, -β6) = a' := by
    rw [hfp, ha', hR, hq, hr]; module
  refine ⟨R, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  · refine k5c_fcac_frame (V8 a a' b b' c c' d) p r R d hΔ hα41 hγ4 hβ1 hβ6 hγ6 hγ61 ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [kqCyc_0, eO]; simp [V8]
      · simp only [kqCyc_1, eA]; simp [V8]
      · simp only [kqCyc_2, eB']; simp [V8]
      · simp only [kqCyc_3, eC]; simp [V8]
    · intro y hy
      rw [eO, eA, eB', eC, eB, eC', eA']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
