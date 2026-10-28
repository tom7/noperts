module

public import Minimality.Type08S.GT_Wrap15

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 16: `gt_far_T4'` with no residual (T4 `r2 = b2` closed by `t4_eq`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem _root_.Minimality.T4Cfg.T2_a_neg_of_le {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ}
    {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (h : T4Cfg E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4) (hr : b2 ≤ r2) :
    FT2.a < 0 := by
  have h1 := h.T2_B; have h2 := h.T2_R; simp only [Fc.ev] at h1 h2
  have hS := h.S3_pos; have hd := h.delta_T2
  have key : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) < 0 := by
    have : FT2.a * (r1 * b2 - r2 * b1) + FT2.d * (b2 - r2) =
        b2 * (FT2.a * r1 + FT2.b * r2 + FT2.c * 0 + FT2.d) -
          r2 * (FT2.a * b1 + FT2.b * b2 + FT2.c * 0 + FT2.d) := by ring
    rw [this, h1]
    have := mul_neg_of_pos_of_neg h.hb2 h2
    linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg hh hS.le, mul_nonneg (show 0 ≤ -FT2.d by linarith) (show 0 ≤ r2 - b2 by linarith)]

/-- **The far triple tie, T4** (`z_w < tie <= z_v`; `z_v = 0` is S2): Rupert, no residual. -/
theorem gt_far_T4' (N : Norm08 a a' b b' c c' d)
    (hfc : N.F.abc'.f c < N.F.abc'.f a') (hfc' : N.F.a'bc.f c' < N.F.a'bc.f a)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫) (hzv0 : ⟪c, b - d⟫ ≤ ⟪b, b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, ua, a3, t, FH, FQac, FT1, FT2, FT3, FT4, P, hE⟩ :=
    t4_pic N.F N.hd hfc hfc' htouch hzw0 hzv0
  have Fr := t4_frame N.F N.hd
  by_cases hnb : NotBeyondW E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 A 0
  · exact t4_sminus N.F N.hd P hE hnb
  · have hwb : WeakBeyond E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
    · rcases lt_or_ge za zv with hzz | hzz
      · exact t4_c N.F N.hd P hE hwb hrb hzz
      · exact t4_b0 N.F N.hd P hE hwb hrb hzz
    · have hzz : zv < za := by
        rcases P.cfg.hzv.lt_or_eq with hz | hz
        · have cfg := P.cfg.toCfg hz
          exact cfg.T2_a_neg_iff.mp (cfg.T2_a_neg_of_le hrb.ge)
        · have := P.hmp
          rw [← hz] at this ⊢
          linarith
      exact t4_eq N.F N.hd P hE hwb hrb hzz
    · have hzz : zv < za := by
        rcases P.cfg.hzv.lt_or_eq with hz | hz
        · have cfg := P.cfg.toCfg hz
          exact cfg.T2_a_neg_iff.mp (cfg.T2_a_neg_of hrb)
        · have := P.hmp
          rw [← hz] at this ⊢
          linarith
      exact t4_a0 N.F N.hd P hE hwb hrb hzz

end Type08Sp
end Minimality
