module

public import Minimality.Type08S.GT_Wrap6

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 7: the dichotomy beyond / not beyond, and T4 `r2 < b2`, `za' < zv`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

/-- Not strictly-not-beyond is weakly beyond (frame form, `g = (E, 0)`). -/
theorem weak_of_not_nb {E M b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M)
    (h : ¬ NotBeyondW E M b1 b2 r1 r2 E 0) : WeakBeyond E M b1 b2 r1 r2 := by
  simp only [NotBeyondW, not_or, not_lt] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h4
  · simpa using h3
  · simpa using h2
  · exact h1

open HFrame in
/-- **T4, weakly beyond, `r2 < b2`, `za' < zv`** (cycle `(2, b, c', a)`; no convexity hypothesis). -/
theorem t4_c (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    {E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (P : T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t
      FH FQac FT1 FT2 FT3 FT4)
    (hE : E = ⟪hfE b c (b - d), hfE b c (b - d)⟫)
    (hwb : WeakBeyond E ⟪F.a'bc.N, F.a'bc.N⟫ b1 b2 r1 r2) (hrb : r2 < b2) (hzz : za < zv) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  subst hE
  have Fr := t4_frame F hd
  have cfg := P.cfg
  have hb1 : 0 < b1 := weakBeyond_B2 Fr.hee Fr.hNN cfg.hb2 hwb hrb
  refine Fr.propH_t4_c (V := insert d ({a, a', b, b', c, c'} : Finset ℝ³))
    (bP := b) (aP' := a') (fP := c') (rP := b') (gP := c) (wP := d) (aP := a) ?_ (by simp) (by simp)
    (by simp) (by simp) P.Φb P.Φa' P.Φc' P.Φb' P.Φc P.Φd P.Φa cfg.hA cfg.hua0 cfg.hua1 P.ht0 P.ht1
    cfg.hzv P.hzw0 P.hm P.hmp hzz cfg.hb2 hrb hb1 cfg.hr2
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  tauto

end Type08Sp
end Minimality
