module

public import Minimality.Type24Circle

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.HDNApex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Screen inner product at the view `u` (copy of `LaplacianNH.scr`). -/
noncomputable def scr (u p q : V) : ℝ := ⟪p, q⟫ - ⟪p, u⟫ * ⟪q, u⟫ / ⟪u, u⟫

theorem scr_sub_left (u p p' q : V) : scr u (p - p') q = scr u p q - scr u p' q := by
  unfold scr; simp only [inner_sub_left]; ring

theorem scr_smul_left (u p q : V) (s : ℝ) : scr u (s • p) q = s * scr u p q := by
  unfold scr; simp only [inner_smul_left, RCLike.conj_to_real]; ring

/-- Apex-pair form of Lemma NH (no foot hypotheses needed): if `scr u eM eJ < 0 < scr u eJ eJ`
(NH gives both from the depths and `<eM,eJ> <= 0`), then for every point `x_1 + s eJ` of the
screen segment `1J` (`0 <= s`), the screen vector from it to `x_M` is NOT orthogonal to `eJ`:
no normal of the edge `1J` at an edge point (and no perpendicular through the foot) reaches `x_M`. -/
theorem scr_foot_ne {u eJ eM : V} (hneg : scr u eM eJ < 0) (hpos : 0 < scr u eJ eJ)
    {s : ℝ} (hs : 0 ≤ s) : scr u (eM - s • eJ) eJ < 0 := by
  rw [scr_sub_left, scr_smul_left]; nlinarith

end Minimality.HDNApex
