module

public import Minimality.Type08S.C2K20HB

@[expose] public section


/-!
# K20H5 / C: H5 rule r3 (line view `L15`): `⟪b' - a, α1 (a - d) - (β6 + γ6 - β1)(c - d)⟫ > 0`.
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

/-- The `L15` view as a combination of `a - d` and `c - d`. -/
noncomputable def k20V3 (a c d : ℝ³) (α1 s : ℝ) : ℝ³ := α1 • (a - d) - s • (c - d)

set_option maxHeartbeats 6400000 in
theorem k20_r3_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d)
    (hlit : 0 < ⟪b' - a, k20V3 a c d α1 (β6 + γ6 - β1)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨m1, m2, m3⟩ := hM
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  set s := β6 + γ6 - β1 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ * s = 1 := ⟨1 / s, by field_simp⟩
  have hκ0 : 0 < κ := by
    by_contra h; push Not at h; nlinarith
  set V0 := k20V3 a c d α1 s with hV0
  have hV : V0 = α1 • p - s • r := by rw [hV0, k20V3]
  have hα0 : 0 < α1 := by linarith
  have hr0 : r ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hdetV : det3 p q V0 = -s * det3 p q r := by
    rw [hV]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hΔ : det3 p q V0 ≠ 0 := by
    rw [hdetV]; exact mul_ne_zero (by linarith) hdet
  have hm1 : ⟪p, q⟫ = ⟪p, r⟫ := by
    have : ⟪p, b - c⟫ = ⟪p, q⟫ - ⟪p, r⟫ := by
      rw [← inner_sub_right]; congr 1; rw [hq, hr]; abel
    linarith
  have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have hrp : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have hrq : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  have hRT : ⟪q, r⟫ < ⟪r, r⟫ := by
    have e : b' - d = α1 • p + β1 • r := by rw [hb', hp, hr]; module
    have e2 : b - c = q - r := by rw [hq, hr]; abel
    rw [e, e2] at m3
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_sub_right] at m3
    have h0 : α1 * (⟪p, q⟫ - ⟪p, r⟫) = 0 := by rw [hm1]; ring
    nlinarith [m3, h0, hqp, hrp]
  -- inner products with the view
  have iP : ⟪p, V0⟫ = α1 * ⟪p, p⟫ - s * ⟪p, r⟫ := by
    rw [hV]; simp only [inner_sub_right, inner_smul_right]
  have iR : ⟪r, V0⟫ = α1 * ⟪p, r⟫ - s * ⟪r, r⟫ := by
    rw [hV]; simp only [inner_sub_right, inner_smul_right, hrp]
  have iQ : ⟪q, V0⟫ = α1 * ⟪p, q⟫ - s * ⟪q, r⟫ := by
    rw [hV]; simp only [inner_sub_right, inner_smul_right, hqp]
  have hlit' : 0 < (α1 - 1) * ⟪p, V0⟫ + β1 * ⟪r, V0⟫ := by
    have e : b' - a = (α1 - 1) • p + β1 • r := by rw [hb', hp, hr]; module
    rw [e, inner_add_left, inner_smul_left, inner_smul_left] at hlit
    simpa only [RCLike.conj_to_real] using hlit
  -- z(a) > z(d): <p, V0> > 0
  have zP : 0 < ⟪p, V0⟫ := by
    by_contra hneg
    push Not at hneg
    have hZ : 0 < ⟪r, V0⟫ := by
      have : (α1 - 1) * ⟪p, V0⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      by_contra hz; push Not at hz
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ β1) hz
      linarith
    have hcs := real_inner_mul_inner_self_le p r
    rw [iR] at hZ
    rw [iP] at hneg
    have hm : 0 < ⟪p, r⟫ := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg hs0.le (real_inner_self_nonneg (x := r)), mul_nonpos_of_nonneg_of_nonpos hα0.le h]
    nlinarith [mul_pos hm hZ, mul_nonneg hs0.le hm.le, real_inner_self_nonneg (x := p), real_inner_self_nonneg (x := r)]
  have zQR : 0 < ⟪c' - b', V0⟫ := by
    have e : c' - b' = β1 • (q - r) := by rw [hc', hb', hq, hr]; module
    rw [e, inner_smul_left, inner_sub_left, iQ, iR]
    simp only [RCLike.conj_to_real]
    rw [hm1]
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < β1) hs0) (sub_pos.2 hRT)]
  -- the points
  have eO : fpoint p q V0 d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q V0 d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q V0 d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC' : fpoint p q V0 d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have hks : κ • (s • r) = r := by rw [smul_smul, hκ, one_smul]
  have eC : fpoint p q V0 d (α1 * κ, 0, -κ) = c := by
    simp only [fpoint, fcomb]
    have : d + ((α1 * κ) • p + (0:ℝ) • q + (-κ) • V0) = d + κ • (s • r) := by rw [hV]; module
    rw [this, hks, hr]; abel
  have eB' : fpoint p q V0 d (α1 * (1 + β1 * κ), 0, -(β1 * κ)) = b' := by
    simp only [fpoint, fcomb]
    have : d + ((α1 * (1 + β1 * κ)) • p + (0:ℝ) • q + (-(β1 * κ)) • V0) = d + α1 • p + β1 • (κ • (s • r)) := by
      rw [hV]; module
    rw [this, hks, hb', hp, hr]
  set w := κ * (β1 - β6) + 1 with hw
  have hws : w * s = γ6 := by
    rw [hw]; have : κ * (β1 - β6) * s + s = (β1 - β6) * (κ * s) + s := by ring
    rw [add_mul, one_mul, this, hκ, hs]; ring
  have eA' : fpoint p q V0 d (α1 * w, β6, -w) = a' := by
    simp only [fpoint, fcomb]
    have : d + ((α1 * w) • p + β6 • q + (-w) • V0) = d + β6 • q + (w * s) • r := by rw [hV]; module
    rw [this, hws, ha', hq, hr]
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, V0⟫ → ⟪X, V0⟫ < ⟪Y, V0⟫ := by
    intro X Y h; rw [inner_sub_left] at h; linarith
  refine ⟨V0, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k20_r3_frame (V8 a a' b b' c c' d) p q V0 d hΔ hα1 hβ1 hβ6 hβ61 hκ0 hw ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k20R3Cyc_0, eB]; simp [V8]
    · simp only [k20R3Cyc_1, eO]; simp [V8]
    · simp only [k20R3Cyc_2, eA]; simp [V8]
    · simp only [k20R3Cyc_3, eB']; simp [V8]
    · simp only [k20R3Cyc_4, eC']; simp [V8]
  · intro y hy
    rw [eB, eO, eA, eB', eC', eC, eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eO, eA]
    apply inner_lt
    have : a - d = p := hp.symm
    rw [this]; exact zP
  · rw [eA, eB']
    apply inner_lt
    exact hlit
  · rw [eB', eC']
    exact inner_lt _ _ zQR

end C2
end Type08Sp
end Minimality
