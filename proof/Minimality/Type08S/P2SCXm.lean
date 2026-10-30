module

public import Minimality.Type08S.SCn
public import Minimality.Type08S.SCs

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X, master (package 8): the three-scale motion of sp08f §3 as one instantiation of `sc5_core`

Motion in the frame (all s-dependent parts are `1/s`):
`V_λ = 1 + N (z - zx) - θ Y`,  `V_Y = θ X - (ρ (z - zx) + b)/s`, `θ = θ0 - η0/s`,
i.e. `ω = (ρ/s, N, θ0 - η0/s)`, `τ = (1 - N zx, (ρ zx - b)/s, 0)`.
Here `N = M κ` (scale `M`), `ρ = σ k` with `k ≈ M + c` (scale `M`, row `1/s`), `b = 1/2`.
Each corner row of `sc5_core` is then exactly `A + C/s` (`rA`, `rC`).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Order-0 part of the row `a·V_Y(X1, z) + c·V_X(Y1, z)` (`u = z - zx`). -/
def rA (a c X1 Y1 u θ0 N : ℝ) : ℝ := a * θ0 * X1 + c * (1 + N * u - θ0 * Y1)
/-- Order-`1/s` part of the same row. -/
def rC (a c X1 Y1 u η0 ρ b : ℝ) : ℝ := -a * (η0 * X1 + ρ * u + b) + c * η0 * Y1
/-- Lexicographic positivity of `A + C/s` for large `s`. -/
def QQ (A C : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 < C)

theorem ev_QQ {A C : ℝ} (h : QQ A C) : ∀ᶠ s : ℝ in atTop, 0 < A + C / s := by
  rcases h with h | ⟨rfl, hC⟩
  · exact (ev_of_eq (P := fun s => A + C / s) 0 A C (Or.inr ⟨rfl, h⟩) (fun s hs => by ring))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simpa using div_pos hC hs

theorem eval_row (a c X1 Y1 z1 θ0 η0 N ρ b zx s : ℝ) (hs : 0 < s) :
    a * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) X1 z1 +
      c * VX N (θ0 - η0 / s) (1 - N * zx) Y1 z1 =
    rA a c X1 Y1 (z1 - zx) θ0 N + rC a c X1 Y1 (z1 - zx) η0 ρ b / s := by
  simp only [VX, VY, rA, rC]; field_simp; ring

theorem ev_row {a c X1 Y1 z1 θ0 η0 N ρ b zx : ℝ}
    (h : QQ (rA a c X1 Y1 (z1 - zx) θ0 N) (rC a c X1 Y1 (z1 - zx) η0 ρ b)) :
    ∀ᶠ s : ℝ in atTop, 0 < a * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) X1 z1 +
      c * VX N (θ0 - η0 / s) (1 - N * zx) Y1 z1 := by
  filter_upwards [ev_QQ h, eventually_gt_atTop (0 : ℝ)] with s h1 h2
  rw [eval_row a c X1 Y1 z1 θ0 η0 N ρ b zx s h2]; exact h1

/-- **Master lemma for SC-X.**  The ten corner rows of `sc5_core` for the three-scale motion, as
`QQ` conditions on the order-0 / order-`1/s` coefficients (`q2`, `q3` are the `s`-free ν-rows). -/
theorem scx_master (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg θ0 η0 N ρ b : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr)
    (q1 : QQ (rA 1 0 0 0 (zp - zx) θ0 N) (rC 1 0 0 0 (zp - zx) η0 ρ b))
    (q2 : 0 < σ * (zx - zp) * (1 - b + (N - ρ) * (zp - zx)))
    (q3 : 0 < σ * (zx - zp) * (1 - b))
    (q4 : QQ (rA (-Xg) Yg 0 0 0 θ0 N) (rC (-Xg) Yg 0 0 0 η0 ρ b))
    (q5 : QQ (rA (Xr - L) (-Yr) L 0 (zf - zx) θ0 N) (rC (Xr - L) (-Yr) L 0 (zf - zx) η0 ρ b))
    (q6 : QQ (rA 1 0 L 0 (zf - zx) θ0 N) (rC 1 0 L 0 (zf - zx) η0 ρ b))
    (q7 : QQ (rA (Xg - Xr) (-(Yg - Yr)) Xr Yr (zr - zx) θ0 N)
      (rC (Xg - Xr) (-(Yg - Yr)) Xr Yr (zr - zx) η0 ρ b))
    (q8 : QQ (rA (Xr - L) (-Yr) Xr Yr (zr - zx) θ0 N) (rC (Xr - L) (-Yr) Xr Yr (zr - zx) η0 ρ b))
    (q9 : QQ (rA (-Xg) Yg Xg Yg (zg - zx) θ0 N) (rC (-Xg) Yg Xg Yg (zg - zx) η0 ρ b))
    (q10 : QQ (rA (Xg - Xr) (-(Yg - Yr)) Xg Yg (zg - zx) θ0 N)
      (rC (Xg - Xr) (-(Yg - Yr)) Xg Yg (zg - zx) η0 ρ b))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have e0 := ev_of_eq (P := fun s => Xg + s * Yg) Yg Xg 0 (Or.inl hYg) (fun s hs => by ring)
  have e1 := ev_row (a := 1) (c := 0) (X1 := 0) (Y1 := 0) (z1 := zp) (zx := zx) q1
  have e4 := ev_row (a := -Xg) (c := Yg) (X1 := 0) (Y1 := 0) (z1 := zx) (zx := zx)
    (by simpa using q4)
  have e5 := ev_row (a := Xr - L) (c := -Yr) (X1 := L) (Y1 := 0) (z1 := zf) (zx := zx) q5
  have e6 := ev_row (a := 1) (c := 0) (X1 := L) (Y1 := 0) (z1 := zf) (zx := zx) q6
  have e7 := ev_row (a := Xg - Xr) (c := -(Yg - Yr)) (X1 := Xr) (Y1 := Yr) (z1 := zr) (zx := zx) q7
  have e8 := ev_row (a := Xr - L) (c := -Yr) (X1 := Xr) (Y1 := Yr) (z1 := zr) (zx := zx) q8
  have e9 := ev_row (a := -Xg) (c := Yg) (X1 := Xg) (Y1 := Yg) (z1 := zg) (zx := zx) q9
  have e10 := ev_row (a := Xg - Xr) (c := -(Yg - Yr)) (X1 := Xg) (Y1 := Yg) (z1 := zg) (zx := zx) q10
  have e2 : ∀ᶠ s : ℝ in atTop, 0 < σ * (zx - zp) * (s * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) 0 zp +
      VX N (θ0 - η0 / s) (1 - N * zx) 0 zp) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have : s * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) 0 zp +
      VX N (θ0 - η0 / s) (1 - N * zx) 0 zp = 1 - b + (N - ρ) * (zp - zx) := by
      simp only [VX, VY]; field_simp; ring
    rw [this]; exact q2
  have e3 : ∀ᶠ s : ℝ in atTop, 0 < σ * (zx - zp) * (s * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) 0 zx +
      VX N (θ0 - η0 / s) (1 - N * zx) 0 zx) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have : s * VY (ρ / s) (θ0 - η0 / s) ((ρ * zx - b) / s) 0 zx +
      VX N (θ0 - η0 / s) (1 - N * zx) 0 zx = 1 - b := by
      simp only [VX, VY]; field_simp; ring
    rw [this]; exact q3
  obtain ⟨s, hs, hEs⟩ := (((e0.and ((e1.and e2).and (e3.and e4))).and
    ((e5.and e6).and (e7.and e8))).and (e9.and e10)).and hE |>.exists
  obtain ⟨⟨⟨h0, ⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩, h9, h10⟩ := hs
  exact sc5_core hF o E (σ := σ) (s := s) (w1 := ρ / s) (w2 := N) (w3 := θ0 - η0 / s)
    (t1 := 1 - N * zx) (t2 := (ρ * zx - b) / s) hL hzx hcr hYr hcg h0
    (by simpa using h1) h2 h3 (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by linarith) (by simpa using h8) (by simpa using h9) (by linarith) hEs



theorem ev_lin {α β : ℝ} (hα : 0 < α) : ∀ᶠ M : ℝ in atTop, 0 < α * M + β := by
  filter_upwards [eventually_gt_atTop (|β| / α)] with M hM
  have := (div_lt_iff₀ hα).1 hM
  nlinarith [neg_abs_le β]

/-- **Wrapper**: `b = 1/2`, `ρ = σ k` with `k σ (zx - zp) ≥ max 1 (N (zx - zp) + 1)`; rows `q1`–`q4` and the
`E`-certificates are discharged. -/
theorem scx_wrap (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg θ0 η0 N k : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr)
    (hk1 : 1 ≤ k * (σ * (zx - zp))) (hk2 : N * (zx - zp) + 1 ≤ k * (σ * (zx - zp)))
    (q5 : QQ (rA (Xr - L) (-Yr) L 0 (zf - zx) θ0 N)
      (rC (Xr - L) (-Yr) L 0 (zf - zx) η0 (σ * k) (1 / 2)))
    (q6 : QQ (rA 1 0 L 0 (zf - zx) θ0 N) (rC 1 0 L 0 (zf - zx) η0 (σ * k) (1 / 2)))
    (q7 : QQ (rA (Xg - Xr) (-(Yg - Yr)) Xr Yr (zr - zx) θ0 N)
      (rC (Xg - Xr) (-(Yg - Yr)) Xr Yr (zr - zx) η0 (σ * k) (1 / 2)))
    (q8 : QQ (rA (Xr - L) (-Yr) Xr Yr (zr - zx) θ0 N)
      (rC (Xr - L) (-Yr) Xr Yr (zr - zx) η0 (σ * k) (1 / 2)))
    (q9 : QQ (rA (-Xg) Yg Xg Yg (zg - zx) θ0 N) (rC (-Xg) Yg Xg Yg (zg - zx) η0 (σ * k) (1 / 2)))
    (q10 : QQ (rA (Xg - Xr) (-(Yg - Yr)) Xg Yg (zg - zx) θ0 N)
      (rC (Xg - Xr) (-(Yg - Yr)) Xg Yg (zg - zx) η0 (σ * k) (1 / 2)))
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  refine scx_master hF o E (θ0 := θ0) (η0 := η0) (N := N) (ρ := σ * k) (b := 1 / 2)
    hL hzx hcr hYr hYg hcg ?_ ?_ ?_ ?_ q5 q6 q7 q8 q9 q10 hE
  · right
    refine ⟨by simp [rA], ?_⟩
    simp only [rC]; nlinarith
  · have : (N - σ * k) * (zp - zx) = k * (σ * (zx - zp)) - N * (zx - zp) := by ring
    rw [this]; nlinarith
  · nlinarith
  · left; simp only [rA]; nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.scx_wrap
