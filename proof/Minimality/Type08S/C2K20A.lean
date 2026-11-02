module

public import Minimality.RightPrism

@[expose] public section


/-!
# K20 / A: Theorem 8.1 generalized ("truncated right prism plus base points")

The bottom polygon `p` (ccw, `z = 0`) with a top point `liftPt (p j) (hz j)` above every vertex at its own height
`hz j > 0` (the tops need not be coplanar), inside a larger set `V`.  Same motion as `isRupert_rightPrism_gen`
(view `e_z + ε v`, spin `ψ` about the axis, tilt `κ`, translation `- λ v`), but `v` is given (generic for `p`) and
the extra points need certificates only for the motion actually used (`λ` large, any `κ`).  The four local
certificates are re-proved with arbitrary heights of the neighbours.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

section certs

variable (V : Finset ℝ³) (v : ℝ²) (ω τ : ℝ³)

theorem k20_cert_flat {q qm qp : ℝ²} {z zm zp : ℝ} (hm : liftPt qm zm ∈ V) (hp : liftPt qp zp ∈ V)
    (hE : 0 < cross2 (q - qm) (qp - q))
    (h1 : 0 < cross2 (qp - q) (proj_xy (cross ω (liftPt q z) + τ)))
    (h2 : 0 < cross2 (q - qm) (proj_xy (cross ω (liftPt q z) + τ))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v (qp - q) (zp - z) (liftPt (qm - q) (zm - z)) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (qp - q) (qm - q) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  have T2 := tt v (qp - q) (zp - z) _ (Or.inl h1)
  have T3 := tt v (q - qm) (z - zm) _ (Or.inl h2)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hm, _, hp, ?_, ?_, ?_⟩ <;> rw [liftPt_sub_liftPt] <;>
    (try rw [liftPt_sub_liftPt]) <;> assumption

theorem k20_cert_up {q qm : ℝ²} {z zm d : ℝ} (hm : liftPt qm zm ∈ V) (hu : liftPt q (z + d) ∈ V)
    (h0 : 0 < d * cross2 (qm - q) v)
    (h1 : 0 < d * cross2 (proj_xy (cross ω (liftPt q z) + τ)) v)
    (h2 : 0 < cross2 (q - qm) (proj_xy (cross ω (liftPt q z) + τ))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v 0 d (liftPt (qm - q) (zm - z)) (Or.inr ⟨by simp [cross2],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h0⟩)
  have T2 := tt v 0 d (cross ω (liftPt q z) + τ) (Or.inr ⟨by simp [cross2],
    by simpa [cross2] using h1⟩)
  have T3 := tt v (q - qm) (z - zm) _ (Or.inl h2)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hm, _, hu, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, add_sub_cancel_left]; exact t1
  · rw [liftPt_sub_liftPt, sub_self, add_sub_cancel_left]; exact t2
  · rw [liftPt_sub_liftPt]; exact t3

theorem k20_cert_down {q qp : ℝ²} {z zp d : ℝ} (hu : liftPt q (z + d) ∈ V) (hp : liftPt qp zp ∈ V)
    (h0 : 0 < -(d * cross2 (qp - q) v))
    (h1 : 0 < cross2 (qp - q) (proj_xy (cross ω (liftPt q z) + τ)))
    (h2 : 0 < -(d * cross2 (proj_xy (cross ω (liftPt q z) + τ)) v)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v (qp - q) (zp - z) (liftPt 0 d) (Or.inr ⟨by simp [cross2, proj_xy_liftPt],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h0⟩)
  have T2 := tt v (qp - q) (zp - z) _ (Or.inl h1)
  have T3 := tt v 0 (-d) (cross ω (liftPt q z) + τ) (Or.inr ⟨by simp [cross2],
    by simpa [cross2] using h2⟩)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hu, _, hp, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, add_sub_cancel_left]; exact t1
  · rw [liftPt_sub_liftPt]; exact t2
  · rw [liftPt_sub_liftPt, sub_self, show z - (z + d) = -d by ring]; exact t3

/-- A hidden point `(q, z)`, strictly inside the triangle `(qm, zm) (q, z + d) (qp, zp)`. -/
theorem k20_cert_hidden {q qm qp : ℝ²} {z zm zp d : ℝ} (hm : liftPt qm zm ∈ V)
    (h0 : liftPt q (z + d) ∈ V) (hp : liftPt qp zp ∈ V)
    (hE : 0 < cross2 (q - qm) (qp - q))
    (h1 : 0 < d * cross2 (q - qm) v) (h2 : 0 < d * cross2 (qp - q) v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T0 := tt v (q - qm) (z + d - zm) (liftPt (qp - qm) (zp - zm)) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (q - qm) (qp - qm) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  have T1 := tt v (q - qm) (z + d - zm) (liftPt (q - qm) (z - zm)) (Or.inr ⟨by
    rw [proj_xy_liftPt, cross2_self], by
      rw [proj_xy_liftPt, liftPt_two]
      have : (z + d - zm) * cross2 (q - qm) v - (z - zm) * cross2 (q - qm) v = d * cross2 (q - qm) v := by ring
      rw [this]; exact h1⟩)
  have T2 := tt v (qp - q) (zp - (z + d)) (liftPt 0 (-d)) (Or.inr ⟨by simp [cross2, proj_xy_liftPt],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h2⟩)
  have T3 := tt v (qm - qp) (zm - zp) (liftPt (q - qp) (z - zp)) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (qm - qp) (q - qp) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  filter_upwards [T0, T1, T2, T3] with ε t0 t1 t2 t3
  refine Or.inr ⟨_, hm, _, h0, _, hp, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt]; exact t0
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt]; exact t1
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, show z - (z + d) = -d by ring]; exact t2
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt]; exact t3

end certs

end C2
end Type08Sp
end Minimality
