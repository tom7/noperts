module

public import Minimality.Type08S.GT_Wrap1

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 2: N2, strictly not beyond (Lemma S-), from the face lattice
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

namespace N2Cfg0
variable {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
  (h : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3)
include h

theorem H_cd : FH.c = 0 ∧ FH.d = 0 := by
  have h1 := h.H_C; have h2 := h.H_W; simp only [Fc.ev] at h1 h2
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

/-- `a` is on the side of `g` of the line `p b`. -/
theorem U1_pos : 0 < b2 * a1 - b1 * a2 := by
  have h1 := h.H_B; have h2 := h.H_A; simp only [Fc.ev] at h1 h2
  obtain ⟨hc, hd⟩ := h.H_cd
  rw [hc, hd] at h1 h2
  have ha := h.H_a_neg; have hb2 := h.hb2
  have e : FH.a * (b2 * a1 - b1 * a2) = b2 * (FH.a * a1 + FH.b * a2 + 0 * a3 + 0) -
      a2 * (FH.a * b1 + FH.b * b2 + 0 * 0 + 0) := by ring
  have hneg : FH.a * (b2 * a1 - b1 * a2) < 0 := by
    rw [e, h1]; have := mul_neg_of_pos_of_neg hb2 h2; linarith
  by_contra hh; push Not at hh
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hh]

end N2Cfg0

open HFrame in
/-- **N2, strictly not beyond** (Lemma S−), assembled from the face lattice. -/
theorem n2_sminus (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ} {FH FQab FQac FT1 FT2 FT3 : Fc}
    (P : N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      FH FQab FQac FT1 FT2 FT3)
    (hE : E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫)
    (hnb : NotBeyondW E ⟪F.a'b'c.N, F.a'b'c.N⟫ b1 b2 r1 r2 A 0) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := n2_frame F
  have cfg := P.cfg
  have hS3 := cfg.S3_pos
  have hU1 := cfg.U1_pos
  have hb2 := cfg.hb2
  have hA := cfg.hA
  have hr2 := cfg.hr2
  have ha2 := cfg.ha2
  have hDr := cfg.hDr
  have hTa1 := cfg.hTa1
  have hTa2 := cfg.hTa2
  refine Fr.close_sminus_n2 (σ := -1) (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (cP := c) (mP := d) (fP := b) (rP := c') (gP := b') (wP := a') (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) P.Φc P.Φd P.Φb P.Φc' P.Φb' P.Φa' P.Φa cfg.hs0 cfg.hs1 cfg.hzv P.hzw0 P.hm
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnb
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end Type08Sp
end Minimality
