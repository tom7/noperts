module

public import Minimality.Type08S.C2K24MTaA
public import Minimality.Type08S.C2K17F1A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality
namespace Type08Sp
namespace C2

/-- Gram form of `⟪fvec u, fvec v⟫` for frame coefficient triples `u v` (lexgen certificates). -/
def certG (u v : ℝ × ℝ × ℝ) (pp pq pr qq qr rr : ℝ) : ℝ :=
  u.1 * v.1 * pp + (u.1 * v.2.1 + u.2.1 * v.1) * pq + (u.1 * v.2.2 + u.2.2 * v.1) * pr +
    u.2.1 * v.2.1 * qq + (u.2.1 * v.2.2 + u.2.2 * v.2.1) * qr + u.2.2 * v.2.2 * rr

theorem cert_ip_lin (p q r : ℝ³) (u v : ℝ × ℝ × ℝ) :
    ⟪u.1 • p + u.2.1 • q + u.2.2 • r, v.1 • p + v.2.1 • q + v.2.2 • r⟫ =
      certG u v ⟪p, p⟫ ⟪p, q⟫ ⟪p, r⟫ ⟪q, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
  have h1 : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm _ _
  have h2 : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  have h3 : ⟪r, q⟫ = ⟪q, r⟫ := real_inner_comm _ _
  simp only [certG, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, h1, h2, h3]
  ring

theorem cert_vec {p q r d X Y : ℝ³} {x y : ℝ × ℝ × ℝ} (hX : fpoint p q r d x = X) (hY : fpoint p q r d y = Y) :
    X - Y = (x - y).1 • p + (x - y).2.1 • q + (x - y).2.2 • r := by
  subst hX hY
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
  simp only [k17f_fp, Prod.mk_sub_mk]; module

theorem cert_vec_r (p q r : ℝ³) : r = (0, 0, 1).1 • p + ((0:ℝ), (0:ℝ), (1:ℝ)).2.1 • q + ((0:ℝ), (0:ℝ), (1:ℝ)).2.2 • r := by
  simp

/-- `⟪X - Y, Z - W⟫` in the Gram entries of the frame. -/
theorem cert_ipd {p q r d X Y Z W : ℝ³} {x y z w : ℝ × ℝ × ℝ} (hX : fpoint p q r d x = X)
    (hY : fpoint p q r d y = Y) (hZ : fpoint p q r d z = Z) (hW : fpoint p q r d w = W) :
    ⟪X - Y, Z - W⟫ = certG (x - y) (z - w) ⟪p, p⟫ ⟪p, q⟫ ⟪p, r⟫ ⟪q, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
  rw [cert_vec hX hY, cert_vec hZ hW, cert_ip_lin]

/-- `⟪X - Y, r⟫` (r the third frame vector). -/
theorem cert_ipd_r {p q r d X Y : ℝ³} {x y : ℝ × ℝ × ℝ} (hX : fpoint p q r d x = X)
    (hY : fpoint p q r d y = Y) :
    ⟪X - Y, r⟫ = certG (x - y) (0, 0, 1) ⟪p, p⟫ ⟪p, q⟫ ⟪p, r⟫ ⟪q, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
  rw [cert_vec hX hY, ← cert_ip_lin]; congr 1; simp

theorem cert_ip_r_d {p q r d X Y : ℝ³} {x y : ℝ × ℝ × ℝ} (hX : fpoint p q r d x = X)
    (hY : fpoint p q r d y = Y) :
    ⟪r, X - Y⟫ = certG (x - y) (0, 0, 1) ⟪p, p⟫ ⟪p, q⟫ ⟪p, r⟫ ⟪q, q⟫ ⟪q, r⟫ ⟪r, r⟫ := by
  rw [real_inner_comm]; exact cert_ipd_r hX hY

/-- The Gram matrix of a frame with `det3 p q r ≠ 0` is positive definite (principal minors). -/
theorem cert_gram_pd {p q r : ℝ³} (h : det3 p q r ≠ 0) :
    0 < ⟪p, p⟫ ∧ 0 < ⟪q, q⟫ ∧ 0 < ⟪r, r⟫ ∧ 0 < ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 ∧
      0 < ⟪p, p⟫ * ⟪r, r⟫ - ⟪p, r⟫ ^ 2 ∧ 0 < ⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2 ∧
      0 < ⟪p, p⟫ * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) - ⟪p, q⟫ * (⟪p, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ * ⟪p, r⟫) +
        ⟪p, r⟫ * (⟪p, q⟫ * ⟪q, r⟫ - ⟪q, q⟫ * ⟪p, r⟫) := by
  have h1 : det3 q r p ≠ 0 := by
    intro h0; apply h; simp only [det3_expand] at h0 ⊢; linarith
  have h2 : det3 r p q ≠ 0 := by
    intro h0; apply h; simp only [det3_expand] at h0 ⊢; linarith
  have hqr := k24mta_cs h
  have hrp := k24mta_cs h1
  have hpq := k24mta_cs h2
  have hrp' : ⟪r, p⟫ = ⟪p, r⟫ := real_inner_comm _ _
  rw [hrp'] at hrp
  have hp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 (k17f_r0 h1)
  have hq : 0 < ⟪q, q⟫ := real_inner_self_pos.2 (k17f_r0 h2)
  have hr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 (k17f_r0 h)
  have hdet : ⟪p, p⟫ * (⟪q, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ ^ 2) - ⟪p, q⟫ * (⟪p, q⟫ * ⟪r, r⟫ - ⟪q, r⟫ * ⟪p, r⟫) +
      ⟪p, r⟫ * (⟪p, q⟫ * ⟪q, r⟫ - ⟪q, q⟫ * ⟪p, r⟫) = det3 p q r ^ 2 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, det3_expand]
    ring
  refine ⟨hp, hq, hr, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  rw [hdet]; positivity

-- syntax test: linear_combination on a strict inequality
example (x y : ℝ) (h1 : 0 < x * y) (h2 : 0 ≤ y) (e : x = 2 * y) : 0 < 3 * x * y + 2 * (x - 2 * y) * y + y := by
  linear_combination 3 * h1 + h2 - (2 * y) * e

end C2
end Type08Sp
end Minimality
