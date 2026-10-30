module

public import Minimality.Type08S.P2H5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H6: the N2 interior vertex `a` anywhere in the screen quadrilateral (D5 fix)

`triCert_quad`: a point strictly inside the screen quadrilateral `(x', f, r, g)` (pkB's `PicN2` items) is hidden at
the tilted views for large `s`: strictly inside the triangle `(x', f, g)` or `(f, r, g)`, or on the open diagonal
`f̄ ḡ` (then the tie row of one of the two triangles is decided by the tilt; `hnc`: `a` is not on the 3-D line `f g`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem triCert_quad (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    {σ L zp zf Xr Yr zr Xg Yg zg Xa Ya za : ℝ} (hσ : σ ≠ 0)
    (h1 : o + pc e1 e2 e3 0 0 zp ∈ V) (h2 : o + pc e1 e2 e3 L 0 zf ∈ V)
    (h3 : o + pc e1 e2 e3 Xr Yr zr ∈ V) (h4 : o + pc e1 e2 e3 Xg Yg zg ∈ V)
    (hL : 0 < L) (hYg : 0 < Yg) (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr))
    (ha1 : 0 < Ya) (ha2 : 0 < (Xr - L) * Ya - Yr * (Xa - L))
    (ha3 : 0 < (Xg - Xr) * (Ya - Yr) - (Yg - Yr) * (Xa - Xr))
    (ha4 : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg))
    (hnc : ¬ ((Xg - L) * Ya - Yg * (Xa - L) = 0 ∧ Yg * (za - zf) - (zg - zf) * Ya = 0)) :
    ∀ᶠ s : ℝ in atTop,
      TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) (o + pc e1 e2 e3 Xa Ya za) := by
  set D := (Xg - L) * Ya - Yg * (Xa - L) with hD
  set W := Yg * (za - zf) - (zg - zf) * Ya with hW
  set M := (zg - zf) * (Xa - L) - (Xg - L) * (za - zf) with hM
  -- the two triangles
  have T1 : ∀ s : ℝ, (0 < D ∨ (D = 0 ∧ 0 < σ * s * W - σ * M)) →
      TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) (o + pc e1 e2 e3 Xa Ya za) := by
    intro s hs
    refine ⟨_, h1, _, h2, _, h4, ?_, ?_, ?_, ?_⟩ <;>
      simp only [add_sub_add_left_eq_sub, pc_sub]
    · exact tiltSign_pos hF (by nlinarith)
    · exact tiltSign_pos hF (by nlinarith)
    · rcases hs with hs | ⟨hs0, hs⟩
      · exact tiltSign_pos hF (by rw [hD] at hs; linarith)
      · refine tiltSign_tie hF (by rw [hD] at hs0; linarith) ?_
        rw [hW, hM] at hs; linarith
    · exact tiltSign_pos hF (by nlinarith)
  have T2 : ∀ s : ℝ, (D < 0 ∨ (D = 0 ∧ 0 < -(σ * s * W - σ * M))) →
      TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) (o + pc e1 e2 e3 Xa Ya za) := by
    intro s hs
    refine ⟨_, h2, _, h3, _, h4, ?_, ?_, ?_, ?_⟩ <;>
      simp only [add_sub_add_left_eq_sub, pc_sub]
    · exact tiltSign_pos hF (by nlinarith)
    · exact tiltSign_pos hF (by nlinarith)
    · exact tiltSign_pos hF (by nlinarith)
    · rcases hs with hs | ⟨hs0, hs⟩
      · exact tiltSign_pos hF (by rw [hD] at hs; linarith)
      · refine tiltSign_tie hF (by rw [hD] at hs0; linarith) ?_
        rw [hW, hM] at hs; linarith
  rcases lt_trichotomy D 0 with hDn | hD0 | hDp
  · exact Eventually.of_forall fun s => T2 s (Or.inl hDn)
  · have hW0 : W ≠ 0 := fun h => hnc ⟨hD0, h⟩
    rcases lt_or_gt_of_ne (mul_ne_zero hσ hW0) with hn | hp
    · filter_upwards [ev_aff (-(σ * W)) (σ * M) (by linarith)] with s hs
      exact T2 s (Or.inr ⟨hD0, by nlinarith⟩)
    · filter_upwards [ev_aff (σ * W) (-(σ * M)) hp] with s hs
      exact T1 s (Or.inr ⟨hD0, by nlinarith⟩)
  · exact Eventually.of_forall fun s => T1 s (Or.inl hDp)

end Type08Sp
end Minimality
