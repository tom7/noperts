module

public import Minimality.Type08S.C2K46ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- Cell A view: `R = ⟪c-d,a'-d⟫ (b'-d) - ⟪c-d,b'-d⟫ (a'-d)`. -/
noncomputable def k89_RA (a' b' c d : ℝ³) : ℝ³ := ⟪c - d, a' - d⟫ • (b' - d) - ⟪c - d, b' - d⟫ • (a' - d)

/-- Cell A frame points on the wall (`α1=β1=β6=γ6=e`): `P=c-d`, `Q=a'-d`, `R=kap(b'-d)-lam(a'-d)`. -/
theorem k89_ptsA {a a' b b' c c' d : ℝ³} {e kap lam ρ w s : ℝ}
    (hC : K6mCoords a a' b b' c c' d e e e e) (he : 1 < e) (hkap : 0 < kap)
    (hρ : ρ = lam / kap) (hw : w = 1 / kap) (hs : s = 1 / e) :
    det3 (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) ≠ 0 ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (0, 0, 0) = d ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (1, 0, 0) = c ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (0, 1, 0) = a' ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (0, ρ, w) = b' ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (-1, ρ * s, w * s) = a ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (-1, s, 0) = b ∧
    fpoint (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) d (-2 * e, 1 + ρ, w) = c' := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have e0 : e ≠ 0 := by linarith
  have k0 : kap ≠ 0 := hkap.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : det3 (c - d) (a' - d) (kap • (b' - d) - lam • (a' - d)) =
        -(kap * e ^ 2) * det3 (a - d) (b - d) (c - d) := by
      rw [ha', hb']
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [h]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero k0 (pow_ne_zero 2 e0))) hdet
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp, hb', ha', hρ, hw]; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, hb', ha', hρ, hw, hs]; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, ha', hs]; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, hb', ha', hc', hρ, hw]; match_scalars <;> field_simp <;> ring
end Minimality.Type08Sp.C2
