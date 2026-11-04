module

public import Minimality.Type08S.C2K46ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2
noncomputable section

noncomputable def k89c_cb (p q r : ℝ³) (X : ℝ × ℝ × ℝ) : ℝ³ := X.1 • p + X.2.1 • q + X.2.2 • r

def k89c_sub (x y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (x.1 - y.1, x.2.1 - y.2.1, x.2.2 - y.2.2)
def k89c_add (x y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)
def k89c_cr (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
def k89c_d3 (x y z : ℝ × ℝ × ℝ) : ℝ :=
  (x.2.1 * y.2.2 - x.2.2 * y.2.1) * z.1 + (x.2.2 * y.1 - x.1 * y.2.2) * z.2.1 +
    (x.1 * y.2.1 - x.2.1 * y.1) * z.2.2

def k89c_e (t : ℝ) : ℝ := (t + 1) / (3 - t)
def k89c_u (t : ℝ) : ℝ := (t - 1) / (2 * t)

def k89c_P (t : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (0, 0, 0)
  | 1 => (1, 0, 0)
  | 2 => (0, 1, 0)
  | 3 => (0, 0, 1)
  | 4 => (0, k89c_e t, k89c_e t)
  | 5 => (k89c_e t, 0, k89c_e t)
  | _ => (k89c_e t, k89c_e t, 0)

def k89c_o1 (t : ℝ) : ℝ := -8*t*(46200*t^6 - 209061*t^5 + 155509*t^4 + 225824*t^3 - 155376*t^2 + 21917*t + 539)
def k89c_o2 (t : ℝ) : ℝ := 8*t*(92400*t^6 - 601797*t^5 + 1329072*t^4 - 1181858*t^3 + 407736*t^2 - 44625*t - 784)
def k89c_o3 (t : ℝ) : ℝ := 4*t*(9*t - 7)*(26400*t^5 - 145667*t^4 + 233785*t^3 - 103439*t^2 + 13131*t + 182)
def k89c_ta1 (t : ℝ) : ℝ := -8*t*(t + 1)*(3*t - 1)*(5*t - 3)*(9*t - 7)*(11*t - 21)*(25*t - 7)
def k89c_ta3 (t : ℝ) : ℝ := -(t + 1)*(5*t - 3)*(25*t - 7)*(924*t^4 - 1173*t^3 - 1452*t^2 + 497*t + 28)

def k89c_om (t : ℝ) : ℝ × ℝ × ℝ := (k89c_o1 t, k89c_o2 t, k89c_o3 t)
def k89c_ta (t : ℝ) : ℝ × ℝ × ℝ := (k89c_ta1 t, 0, k89c_ta3 t)
def k89c_g (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((1 + k89c_u t) * x.1 - k89c_u t * (x.1 + x.2.1 + x.2.2),
   (1 + k89c_u t) * x.2.1 - k89c_u t * (x.1 + x.2.1 + x.2.2),
   (1 + k89c_u t) * x.2.2 - k89c_u t * (x.1 + x.2.1 + x.2.2))
def k89c_vel (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  k89c_add (k89c_cr (k89c_om t) (k89c_g t x)) (k89c_ta t)
def k89c_w0 : ℝ × ℝ × ℝ := (2, -8, 7)

noncomputable def k89c_omv (p q r : ℝ³) (μ t : ℝ) : ℝ³ :=
  (1 / μ) • (k89c_o1 t • cross q r + k89c_o2 t • cross r p + k89c_o3 t • cross p q)

theorem k89c_cc (u v x : ℝ³) : cross (cross u v) x = ⟪u, x⟫ • v - ⟪v, x⟫ • u := by
  ext i; fin_cases i <;>
    simp [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

theorem k89c_sub_cb (p q r : ℝ³) (X Y : ℝ × ℝ × ℝ) :
    k89c_cb p q r X - k89c_cb p q r Y = k89c_cb p q r (k89c_sub X Y) := by
  simp only [k89c_cb, k89c_sub, sub_smul]; abel

theorem k89c_add_cb (p q r : ℝ³) (X Y : ℝ × ℝ × ℝ) :
    k89c_cb p q r X + k89c_cb p q r Y = k89c_cb p q r (k89c_add X Y) := by
  simp only [k89c_cb, k89c_add, add_smul]; abel

theorem k89c_det_cb (p q r : ℝ³) (X Y Z : ℝ × ℝ × ℝ) :
    det3 (k89c_cb p q r X) (k89c_cb p q r Y) (k89c_cb p q r Z) = det3 p q r * k89c_d3 X Y Z := by
  simp only [det3_expand, k89c_cb, k89c_d3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem k89c_det_smul (a b c : ℝ³) (σ : ℝ) : det3 a b (σ • c) = σ * det3 a b c := by
  simp [det3, inner_smul_right]

theorem k89c_vel_cb {p q r : ℝ³} {μ t u : ℝ} (hμ : 0 < μ) (hu : u = k89c_u t)
    (hpp : ⟪p, p⟫ = μ) (hqq : ⟪q, q⟫ = μ) (hrr : ⟪r, r⟫ = μ)
    (hpq : ⟪p, q⟫ = -μ * u) (hpr : ⟪p, r⟫ = -μ * u) (hqr : ⟪q, r⟫ = -μ * u) (X : ℝ × ℝ × ℝ) :
    cross (k89c_omv p q r μ t) (k89c_cb p q r X) = k89c_cb p q r (k89c_cr (k89c_om t) (k89c_g t X)) := by
  have hqp : ⟪q, p⟫ = -μ * u := by rw [real_inner_comm]; exact hpq
  have hrp : ⟪r, p⟫ = -μ * u := by rw [real_inner_comm]; exact hpr
  have hrq : ⟪r, q⟫ = -μ * u := by rw [real_inner_comm]; exact hqr
  have ip : ∀ s : ℝ³, ⟪s, k89c_cb p q r X⟫ = X.1 * ⟪s, p⟫ + X.2.1 * ⟪s, q⟫ + X.2.2 * ⟪s, r⟫ := by
    intro s; simp [k89c_cb, inner_add_right, inner_smul_right]
  have h : cross (k89c_omv p q r μ t) (k89c_cb p q r X) = (1/μ) • (k89c_o1 t • cross (cross q r) (k89c_cb p q r X) + k89c_o2 t • cross (cross r p) (k89c_cb p q r X) + k89c_o3 t • cross (cross p q) (k89c_cb p q r X)) := by
    simp only [k89c_omv, cross_smul_l, cross_add_l]
  rw [h, k89c_cc, k89c_cc, k89c_cc]
  simp only [ip, hpp, hqq, hrr, hpq, hpr, hqr, hqp, hrp, hrq]
  subst hu
  have hμ' : μ ≠ 0 := hμ.ne'
  ext i; fin_cases i <;>
    simp [k89c_cb, k89c_cr, k89c_g, k89c_om, k89c_u] <;> field_simp <;> ring

def k89c_w (p q r : ℝ³) (σ : ℝ) : ℝ³ := σ • k89c_cb p q r k89c_w0
def k89c_tau (p q r d : ℝ³) (μ t : ℝ) : ℝ³ :=
  k89c_cb p q r (k89c_ta t) - cross (k89c_omv p q r μ t) d

theorem k89c_sub_pt (p q r d : ℝ³) (X Y : ℝ × ℝ × ℝ) :
    (d + k89c_cb p q r Y) - (d + k89c_cb p q r X) = k89c_cb p q r (k89c_sub Y X) := by
  rw [add_sub_add_left_eq_sub, k89c_sub_cb]

theorem k89c_vel_abs {p q r : ℝ³} {μ t u : ℝ} (d : ℝ³) (hμ : 0 < μ) (hu : u = k89c_u t)
    (hpp : ⟪p, p⟫ = μ) (hqq : ⟪q, q⟫ = μ) (hrr : ⟪r, r⟫ = μ)
    (hpq : ⟪p, q⟫ = -μ * u) (hpr : ⟪p, r⟫ = -μ * u) (hqr : ⟪q, r⟫ = -μ * u) (X : ℝ × ℝ × ℝ) :
    cross (k89c_omv p q r μ t) (d + k89c_cb p q r X) + k89c_tau p q r d μ t
      = k89c_cb p q r (k89c_vel t X) := by
  rw [cross_add_r, k89c_vel_cb hμ hu hpp hqq hrr hpq hpr hqr, k89c_vel, ← k89c_add_cb, k89c_tau]
  have : k89c_cb p q r (k89c_ta t) = k89c_cb p q r (k89c_ta t) := rfl
  abel

theorem k89c_det_w (p q r : ℝ³) (σ : ℝ) (hσD : 0 < σ * det3 p q r) (A B : ℝ × ℝ × ℝ)
    (h : 0 < k89c_d3 A B k89c_w0) :
    0 < det3 (k89c_cb p q r A) (k89c_cb p q r B) (k89c_w p q r σ) := by
  rw [k89c_w, k89c_det_smul, k89c_det_cb]
  have : σ * (det3 p q r * k89c_d3 A B k89c_w0) = (σ * det3 p q r) * k89c_d3 A B k89c_w0 := by ring
  rw [this]; exact mul_pos hσD h

theorem k89c_rim {V : Finset ℝ³} {p q r d : ℝ³} {μ t u σ : ℝ} (hμ : 0 < μ) (hu : u = k89c_u t)
    (hpp : ⟪p, p⟫ = μ) (hqq : ⟪q, q⟫ = μ) (hrr : ⟪r, r⟫ = μ)
    (hpq : ⟪p, q⟫ = -μ * u) (hpr : ⟪p, r⟫ = -μ * u) (hqr : ⟪q, r⟫ = -μ * u)
    (hσD : 0 < σ * det3 p q r) {X Y0 Y1 : ℝ × ℝ × ℝ} {x y0 y1 : ℝ³}
    (hx : x = d + k89c_cb p q r X) (hy0 : y0 = d + k89c_cb p q r Y0) (hy1 : y1 = d + k89c_cb p q r Y1)
    (hy0V : y0 ∈ V) (hy1V : y1 ∈ V)
    (h1 : 0 < k89c_d3 (k89c_sub Y1 X) (k89c_sub Y0 X) k89c_w0)
    (h2 : 0 < k89c_d3 (k89c_sub Y1 X) (k89c_vel t X) k89c_w0)
    (h3 : 0 < k89c_d3 (k89c_sub X Y0) (k89c_vel t X) k89c_w0) :
    TiltCert V (k89c_w p q r σ) (k89c_omv p q r μ t) (k89c_tau p q r d μ t) x := by
  left
  refine ⟨y0, hy0V, y1, hy1V, ?_, ?_, ?_⟩
  · rw [hx, hy0, hy1, k89c_sub_pt, k89c_sub_pt]; exact k89c_det_w p q r σ hσD _ _ h1
  · rw [hx, hy1, k89c_sub_pt, k89c_vel_abs d hμ hu hpp hqq hrr hpq hpr hqr]
    exact k89c_det_w p q r σ hσD _ _ h2
  · rw [hx, hy0, k89c_sub_pt p q r d Y0 X, k89c_vel_abs d hμ hu hpp hqq hrr hpq hpr hqr]
    exact k89c_det_w p q r σ hσD _ _ h3

theorem k89c_tri {V : Finset ℝ³} {p q r d : ℝ³} {μ t σ : ℝ}
    (hσD : 0 < σ * det3 p q r) {X A B C : ℝ × ℝ × ℝ} {x a b c : ℝ³}
    (hx : x = d + k89c_cb p q r X) (ha : a = d + k89c_cb p q r A) (hb : b = d + k89c_cb p q r B)
    (hc : c = d + k89c_cb p q r C) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (h1 : 0 < k89c_d3 (k89c_sub B A) (k89c_sub C A) k89c_w0)
    (h2 : 0 < k89c_d3 (k89c_sub B A) (k89c_sub X A) k89c_w0)
    (h3 : 0 < k89c_d3 (k89c_sub C B) (k89c_sub X B) k89c_w0)
    (h4 : 0 < k89c_d3 (k89c_sub A C) (k89c_sub X C) k89c_w0) :
    TiltCert V (k89c_w p q r σ) (k89c_omv p q r μ t) (k89c_tau p q r d μ t) x := by
  right
  refine ⟨a, haV, b, hbV, c, hcV, ?_, ?_, ?_, ?_⟩
  · rw [hb, ha, hc, k89c_sub_pt, k89c_sub_pt]; exact k89c_det_w p q r σ hσD _ _ h1
  · rw [hx, hb, ha, k89c_sub_pt, k89c_sub_pt]; exact k89c_det_w p q r σ hσD _ _ h2
  · rw [hx, hb, hc, k89c_sub_pt, k89c_sub_pt]; exact k89c_det_w p q r σ hσD _ _ h3
  · rw [hx, ha, hc, k89c_sub_pt, k89c_sub_pt]; exact k89c_det_w p q r σ hσD _ _ h4

end
end Minimality.Type08Sp.C2
