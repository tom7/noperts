module

public import Minimality.Type08S.L2.K89A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

/-- Cell B view: `R = (qq-qr) p + (qr-pq) q - (qq-pq) r` (p,q,r = a-d,b-d,c-d). -/
noncomputable def k89_RB (a b c d : ℝ³) : ℝ³ :=
  (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) • (a - d) + (⟪b - d, c - d⟫ - ⟪a - d, b - d⟫) • (b - d)
    - (⟪b - d, b - d⟫ - ⟪a - d, b - d⟫) • (c - d)

theorem k89_ptsB {a a' b b' c c' d : ℝ³} {e Aq Bq β w : ℝ}
    (hC : K6mCoords a a' b b' c c' d e e e e) (he : 1 < e) (hA : 0 < Aq)
    (hβ : β = Bq / Aq) (hw : w = 1 / Aq) :
    det3 (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) ≠ 0 ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (0, 0, 0) = d ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (1, 0, 0) = b ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (0, 1, 0) = c ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (-β, 1 + β, w) = a ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (e, e, 0) = a' ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (-e * β, e * (2 + β), e * w) = b' ∧
    fpoint (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) d (e * (1 - β), e * (1 + β), e * w) = c' := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have k0 : Aq ≠ 0 := hA.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : det3 (b - d) (c - d) (Aq • (a - d) + Bq • (b - d) - (Aq + Bq) • (c - d)) =
        Aq * det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [h]; exact mul_ne_zero k0 hdet
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp, hβ, hw]; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, ha']; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, hb', hβ, hw]; match_scalars <;> field_simp <;> ring
  · rw [k17f_fp, hc', hβ, hw]; match_scalars <;> field_simp <;> ring
end Minimality.Type08Sp.C2
