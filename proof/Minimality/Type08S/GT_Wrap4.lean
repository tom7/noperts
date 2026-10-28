module

public import Minimality.Type08S.GT_Wrap3

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 4: T4, strictly not beyond (Lemma S-), from the face lattice
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

namespace T4Cfg0
variable {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
  (h : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4)
include h

theorem H_cd : FH.c = 0 ∧ FH.d = 0 := by
  have h1 := h.H_V; have h2 := h.H_W; simp only [Fc.ev] at h1 h2
  have hzw := h.hzw
  have hc : FH.c = 0 := by
    have : FH.c * (zv - zw) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by linarith)
  refine ⟨hc, ?_⟩
  rw [hc] at h1; linarith

theorem H_a_neg : FH.a < 0 := by
  have h1 := h.H_G; simp only [Fc.ev] at h1
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1
  have := h.hA
  by_contra hh; push Not at hh
  nlinarith

theorem S3_pos : 0 < r1 * b2 - r2 * b1 := by
  have h1 := h.H_B; have h2 := h.H_R; simp only [Fc.ev] at h1 h2
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1 h2
  have ha := h.H_a_neg; have hb2 := h.hb2
  have e : FH.a * (r1 * b2 - r2 * b1) = b2 * (FH.a * r1 + FH.b * r2 + 0 * 0 + 0) -
      r2 * (FH.a * b1 + FH.b * b2 + 0 * 0 + 0) := by ring
  have hneg : FH.a * (r1 * b2 - r2 * b1) < 0 := by
    rw [e, h1]; have := mul_neg_of_pos_of_neg hb2 h2; linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hh]

end T4Cfg0

open HFrame in
/-- **T4, strictly not beyond** (Lemma S−), assembled from the face lattice. -/
theorem t4_sminus (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hnb : NotBeyondW E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2 A 0) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg
  have hS3 := cfg.S3_pos
  have hb2 := cfg.hb2
  have hA := cfg.hA
  have hr2 := cfg.hr2
  have hDr := cfg.hDr
  refine Fr.close_sminus_t4 (σ := -1) (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) (by simp) P.Φb ?_ P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hua0 cfg.hua1 P.ht0 P.ht1
    cfg.hzv P.hzw0 P.hm P.hmp ?_ ?_ ?_ ?_ hnb
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [P.Φa']; simp
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end Type08Sp
end Minimality
