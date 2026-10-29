module

public import Minimality.Type08S.SCc

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Sign test for frame vectors, strict part. -/
theorem tiltSign_pos (hF : Fr e1 e2 e3) {a1 a2 a3 b1 b2 b3 dx dy : ℝ}
    (h : 0 < a1 * b2 - a2 * b1) :
    TiltSign (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (pc e1 e2 e3 0 0 1)
      (pc e1 e2 e3 dx dy 0) := by
  left; rw [det3_pc hF]; linarith

/-- Sign test for frame vectors, tie part. -/
theorem tiltSign_tie (hF : Fr e1 e2 e3) {a1 a2 a3 b1 b2 b3 dx dy : ℝ}
    (h0 : a1 * b2 - a2 * b1 = 0)
    (h : 0 < (a2 * b3 - a3 * b2) * dx + (a3 * b1 - a1 * b3) * dy) :
    TiltSign (pc e1 e2 e3 a1 a2 a3) (pc e1 e2 e3 b1 b2 b3) (pc e1 e2 e3 0 0 1)
      (pc e1 e2 e3 dx dy 0) := by
  right; rw [det3_pc hF, det3_pc hF]; constructor <;> linarith

/-- **Hidden middle over the `F`-side** `x'f`: a point over the open segment `(0,L)` of the line
`Y = 0` that is strictly above the line `x' f` (certificate in the triangle `x' f g`).
Independent of the tilt. -/
theorem triCert_midF (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    {σ L zp zf Xg Yg zg Xd zd s : ℝ} (hL : 0 < L) (hYg : 0 < Yg) (hX0 : 0 < Xd) (hXL : Xd < L)
    (h1 : o + pc e1 e2 e3 0 0 zp ∈ V) (h2 : o + pc e1 e2 e3 L 0 zf ∈ V)
    (h3 : o + pc e1 e2 e3 Xg Yg zg ∈ V)
    (hab : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd)) :
    TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) (o + pc e1 e2 e3 Xd 0 zd) := by
  refine ⟨_, h1, _, h2, _, h3, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [add_sub_add_left_eq_sub, pc_sub]
    first
    | exact tiltSign_pos hF (by nlinarith)
    | exact tiltSign_tie hF (by ring) (by nlinarith)

/-- **Hidden middle over the `G`-side** `g x`: the point over `λ (Xg, Yg)` (`0 < λ < 1`) strictly
below the chord from `x` (depth `zx`) to `g`, for large `s` (certificate in the triangle `g x f`). -/
theorem triCert_midG (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    {σ L zx zf Xg Yg zg lam za s : ℝ} (hL : 0 < L) (hYg : 0 < Yg) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < Xg + s * Yg)
    (h1 : o + pc e1 e2 e3 Xg Yg zg ∈ V) (h2 : o + pc e1 e2 e3 0 0 zx ∈ V)
    (h3 : o + pc e1 e2 e3 L 0 zf ∈ V)
    (hab : σ * (za - ((1 - lam) * zx + lam * zg)) < 0) :
    TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0)
      (o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za) := by
  refine ⟨_, h1, _, h2, _, h3, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [add_sub_add_left_eq_sub, pc_sub]
    first
    | exact tiltSign_pos hF (by nlinarith [mul_pos hL hYg, mul_pos (mul_pos hL hYg) hl0, mul_pos (mul_pos hL hYg) (sub_pos.2 hl1)])
    | exact tiltSign_tie hF (by ring) (by nlinarith [mul_pos hs (neg_pos.2 hab)])

/-- **Interior vertex**: strictly inside the screen triangle `(x', f, g)`. -/
theorem triCert_int (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    {σ L zp zf Xg Yg zg Xa Ya za s : ℝ} 
    (h1 : o + pc e1 e2 e3 0 0 zp ∈ V) (h2 : o + pc e1 e2 e3 L 0 zf ∈ V)
    (h3 : o + pc e1 e2 e3 Xg Yg zg ∈ V)
    (hT : 0 < L * Yg) (hc1 : 0 < L * Ya) (hc2 : 0 < (Xg - L) * Ya - Yg * (Xa - L))
    (hc3 : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)) :
    TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) (o + pc e1 e2 e3 Xa Ya za) := by
  refine ⟨_, h1, _, h2, _, h3, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [add_sub_add_left_eq_sub, pc_sub]
    exact tiltSign_pos hF (by nlinarith)

end Type08Sp
end Minimality
