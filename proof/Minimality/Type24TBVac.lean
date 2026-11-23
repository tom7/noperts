module

public import Minimality.SVCTieGeo
public import Minimality.Type24SAT.K24.Par2546
public import Minimality.Type24SAT.K24.Wire24

@[expose] public section

/-!
# Three tied vertices of an edge-on facet are impossible (Task TB24B, `hvac`)

If `⟪N t, w⟫ = 0` and three vertices `a b c` of facet `t` have equal depth `⟪·, w⟫`, then
`x b - x a`, `x c - x a` are orthogonal to `N t` and `w`, hence `cross = 0`: collinear.  For type 24
no three vertices of a facet are collinear (`fne24`, `par2546_quad`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.T24 Minimality.T24.SAT Minimality.T24.Par

namespace Minimality.SVC.Geo

theorem tbg_cross_smul (u v : ℝ³) (a1 b1 a2 b2 : ℝ) :
    cross (a1 • u + b1 • v) (a2 • u + b2 • v) = (a1 * b2 - b1 * a2) • cross u v := by
  ext i
  fin_cases i <;>
  · simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    ring

/-- Two vectors orthogonal to `N ≠ 0` and `w ≠ 0` with `N ⟂ w` are parallel. -/
theorem tbg_cross_zero {N w u v : ℝ³} (hN : N ≠ 0) (hw : w ≠ 0) (hNw : ⟪N, w⟫ = 0)
    (huN : ⟪u, N⟫ = 0) (hvN : ⟪v, N⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    cross u v = 0 := by
  obtain ⟨k1, h1⟩ := tbg_cross_par hw huw hvw
  obtain ⟨k2, h2⟩ := tbg_cross_par hN huN hvN
  have h := congrArg (fun y => ⟪y, N⟫) (h1.symm.trans h2)
  simp only [real_inner_smul_left] at h
  rw [real_inner_comm N w, hNw] at h
  have hNN : 0 < ⟪N, N⟫ := real_inner_self_pos.mpr hN
  have : k2 = 0 := by
    have : k2 * ⟪N, N⟫ = 0 := by linarith [real_inner_comm N w]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hNN.ne'
  rw [h2, this, zero_smul]

theorem tbg_N_ne {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x)
    (t : Fin m) {a v : Fin n} (ha : a ∈ S t) (hv : v ∉ S t) : F.N t ≠ 0 := by
  intro h0
  have := F.inner_sub t v a
  rw [h0, inner_zero_left, F.zero t a ha] at this
  linarith [F.neg t v hv]

/-- Three tied vertices of an edge-on facet are collinear. -/
theorem tbg_vac {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x)
    (t : Fin m) {a b c v : Fin n} (ha : a ∈ S t) (hb : b ∈ S t) (hc : c ∈ S t) (hv : v ∉ S t)
    {w : ℝ³} (hw : w ≠ 0) (hNw : ⟪F.N t, w⟫ = 0)
    (hab : ⟪x a, w⟫ = ⟪x b, w⟫) (hbc : ⟪x b, w⟫ = ⟪x c, w⟫) :
    cross (x b - x a) (x c - x a) = 0 := by
  have hu : ⟪F.N t, x b - x a⟫ = 0 := by rw [F.inner_sub, F.zero t a ha, F.zero t b hb]; ring
  have hv' : ⟪F.N t, x c - x a⟫ = 0 := by rw [F.inner_sub, F.zero t a ha, F.zero t c hc]; ring
  refine tbg_cross_zero (tbg_N_ne F t ha hv) hw hNw ?_ ?_ ?_ ?_
  · rw [real_inner_comm]; exact hu
  · rw [real_inner_comm]; exact hv'
  · rw [inner_sub_left]; linarith
  · rw [inner_sub_left]; linarith

section T24

variable {x : Fin 7 → ℝ³}

theorem cross_ne_of_Bk (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v : Fin 7)
    (hv : v ∉ s0x_S24 t) (i j k : Fin 7) (hi : fA t = i) (hj : fB t = j) (hk : fC t = k) :
    cross (x j - x i) (x k - x i) ≠ 0 := by
  intro h0
  apply fne24 F t v i j k hv hi hj hk
  show det3 (x j - x i) (x k - x i) (x v - x i) = 0
  simp only [det3, h0, inner_zero_left]

theorem cross_ne_F0 (F : S0xFac 9 s0x_S24 x) : cross (x 1 - x 0) (x 2 - x 0) ≠ 0 :=
  cross_ne_of_Bk F 0 6 (by decide) 0 1 2 (by decide) (by decide) (by decide)

theorem cross_ne_F1 (F : S0xFac 9 s0x_S24 x) : cross (x 1 - x 0) (x 6 - x 0) ≠ 0 :=
  cross_ne_of_Bk F 1 2 (by decide) 0 1 6 (by decide) (by decide) (by decide)

theorem cross_ne_F7 (F : S0xFac 9 s0x_S24 x) : cross (x 3 - x 2) (x 6 - x 2) ≠ 0 :=
  cross_ne_of_Bk F 7 0 (by decide) 2 3 6 (by decide) (by decide) (by decide)

theorem cross_ne_F3 (F : S0xFac 9 s0x_S24 x) :
    cross (x 3 - x 0) (x 4 - x 0) ≠ 0 :=
  cross_ne_of_Bk F 3 1 (by decide) 0 3 4 (by decide) (by decide) (by decide)

/-- The four triples of the quadrilateral facet `0345` (type 24) are not collinear. -/
theorem cross_ne_quad (F : S0xFac 9 s0x_S24 x) :
    cross (x 3 - x 0) (x 4 - x 0) ≠ 0 ∧ cross (x 3 - x 0) (x 5 - x 0) ≠ 0 ∧
    cross (x 4 - x 0) (x 5 - x 0) ≠ 0 ∧ cross (x 4 - x 3) (x 5 - x 3) ≠ 0 := by
  obtain ⟨al, be, hal, hbe, hab, h3⟩ := par2546_quad F
  have hx3 : x 3 = x 0 + (al • (x 5 - x 0) + be • (x 4 - x 0)) := by rw [← h3]; abel
  have hD := cross_ne_F3 F
  have e1 : cross (x 3 - x 0) (x 4 - x 0) = (-al) • cross (x 4 - x 0) (x 5 - x 0) := by
    have h := tbg_cross_smul (x 4 - x 0) (x 5 - x 0) be al 1 0
    simp only [one_smul, zero_smul, add_zero] at h
    have e : x 3 - x 0 = be • (x 4 - x 0) + al • (x 5 - x 0) := by rw [h3]; abel
    rw [e, h]; congr 1; ring
  have hc45 : cross (x 4 - x 0) (x 5 - x 0) ≠ 0 := by
    intro h0; apply hD; rw [e1, h0, smul_zero]
  have e2 : cross (x 3 - x 0) (x 5 - x 0) = be • cross (x 4 - x 0) (x 5 - x 0) := by
    have h := tbg_cross_smul (x 4 - x 0) (x 5 - x 0) be al 0 1
    simp only [one_smul, zero_smul, zero_add] at h
    have e : x 3 - x 0 = be • (x 4 - x 0) + al • (x 5 - x 0) := by rw [h3]; abel
    rw [e, h]; congr 1; ring
  have e3 : cross (x 4 - x 3) (x 5 - x 3) = (1 - al - be) • cross (x 4 - x 0) (x 5 - x 0) := by
    have := tbg_cross_smul (x 4 - x 0) (x 5 - x 0) (1 - be) (-al) (-be) (1 - al)
    have a1 : x 4 - x 3 = (1 - be) • (x 4 - x 0) + (-al) • (x 5 - x 0) := by rw [hx3]; module
    have a2 : x 5 - x 3 = (-be) • (x 4 - x 0) + (1 - al) • (x 5 - x 0) := by rw [hx3]; module
    rw [a1, a2, this]; congr 1; ring
  refine ⟨hD, ?_, hc45, ?_⟩
  · rw [e2]; exact smul_ne_zero hbe.ne' hc45
  · rw [e3]; exact smul_ne_zero (by linarith) hc45

end T24

end Minimality.SVC.Geo
