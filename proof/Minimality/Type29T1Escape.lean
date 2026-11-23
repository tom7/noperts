module

public import Minimality.Type29T1Close

@[expose] public section

/-!
# Type 29, `t = 1` K1a cell without the sample fact `s < 1 ∨ D234 < 1`: the escape and its view

`t1_closed` (Type29T1Close) needs `hsD : s < 1 ∨ D234 < 1`, which fails on part of the cell
(nopert229 T1FACTS: exact escape shape `(-43/20, 3/5, 7/20, -7/2, -33/20, 9/4, 31/20, 1)`).
`t1_escape`: on the escape (`¬ hsD`, `¬ LexAny29`) one has `s ≥ 1`, `D234 ≥ 1`, `g35 = g45 = 0`.
There the view `u023_356 = D023 (x1 - x4) - dG4 (x3 - x6)` (line of the facet planes 023 and 356)
closes. This file has the view data: the facet values at `u023_356` (`f*_u023_356`), the facings
(`t1e_facing_signs`; only 012 and 124 vary, with `m = b2 + h2`), the forced depth chain
`z3 < z6 < z4 < z1` (`t1e_forced_z`) and `z2 < z0` for `b0 + h0 ≤ m` (`t1e_z02_A`). The leaf
(`lexAny29_F023F356`, lexicographic depths, all `m`) and `t1_closed'` are in `Type29T1Res`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21

namespace Minimality.NF29

theorem t1l2_c234 (a0 a2 b2 h2 b0 h0 : ℝ) (ha0 : a0 < 0) (ha2 : a2 < 0)
    (hDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)))
    (hA : 0 < 1 - b0 - h0) : b2 + h2 < 1 := by
  nlinarith [mul_pos_of_neg_of_neg ha0 ha2]

theorem t1l2_c015 (a0 b0 h0 a2 b2 h2 : ℝ) (ha0 : a0 < 0) (hh0 : 0 < h0)
    (hDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)))
    (hdG4 : 0 < b0 * (1 - h2) - b2 * (1 - h0)) :
    0 < a0*b0*h2 - a0*b0 + a0*b2 + a0*h0*h2 - a0*h0 - a2*b0*h0 - a2*h0^2 + a2*h0 := by
  nlinarith [mul_pos hh0 (neg_pos.mpr ha0)]

variable {x : Fin 7 → ℝ³}

/-- `u = gamma d + alpha e3`, `gamma = D023`, `alpha = -dG4`, `d = x1 - x4`, `e3 = x3 - x6`. -/
noncomputable def u023_356 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  N.D023 • (x 1 - x 4) + (-N.dG4) • (x 3 - x 6)

local macro "uF_val " N:term:max f:ident : tactic =>
  `(tactic| (
    rw [($f $N).hN (x 3 + u023_356 $N x) (x 3), add_sub_cancel_left]
    dsimp only [u023_356]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← ($f $N).hN (x 1) (x 4), ← ($f $N).hN (x 3) (x 6)]
    dsimp only [dG, dG4, D02, DG4, DG5, D023, f012, f015, f023, f035, f124, f1456, f234, f346,
      f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]))

theorem f012_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f012.f (x 3 + N.u023_356 x) - N.f012.f (x 3) = N.D02 * (N.b0 - N.b2 + N.h0 - N.h2) * N.D ^ 2 := by
  uF_val N f012; rw [ht]; ring
theorem f015_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f015.f (x 3 + N.u023_356 x) - N.f015.f (x 3) =
      (N.a0*N.b0*N.h2 - N.a0*N.b0 + N.a0*N.b2 + N.a0*N.h0*N.h2 - N.a0*N.h0 - N.a2*N.b0*N.h0
        - N.a2*N.h0^2 + N.a2*N.h0) * N.D ^ 2 := by
  uF_val N f015; rw [ht]; ring
theorem f023_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f023.f (x 3 + N.u023_356 x) - N.f023.f (x 3) = 0 := by
  uF_val N f023; rw [ht]; ring
theorem f035_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f035.f (x 3 + N.u023_356 x) - N.f035.f (x 3) =
      (1 - N.b0 - N.h0) * (N.a0*N.b2 + N.a0*N.h2 - N.a0 - N.a2*N.b0 - N.a2*N.h0 + N.a2)
        * N.D ^ 2 := by
  uF_val N f035; rw [ht]; ring
theorem f124_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f124.f (x 3 + N.u023_356 x) - N.f124.f (x 3) = -(N.b2 + N.h2) * N.dG4 * N.D ^ 2 := by
  uF_val N f124; rw [ht]; ring
theorem f1456_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f1456.f (x 3 + N.u023_356 x) - N.f1456.f (x 3) = N.dG4 * N.D ^ 2 := by
  uF_val N f1456; rw [ht]; ring
theorem f234_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f234.f (x 3 + N.u023_356 x) - N.f234.f (x 3) = (N.b2 + N.h2 - 1) * N.DG4 * N.D ^ 2 := by
  uF_val N f234; rw [ht]; ring
theorem f346_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f346.f (x 3 + N.u023_356 x) - N.f346.f (x 3) = -N.D023 * N.D ^ 2 := by
  uF_val N f346; rw [ht]; ring
theorem f356_u023_356 (N : NF29 x) (ht : N.t = 1) :
    N.f356.f (x 3 + N.u023_356 x) - N.f356.f (x 3) = 0 := by
  uF_val N f356; rw [ht]; ring


/-! ### forced depths (metric slice g35 = g45 = 0) -/

theorem t1e_forced_depths {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (d e3 e4 : V) (h3 : ⟪d, e3⟫ = 0) (h4 : ⟪d, e4⟫ = 0) (γ α : ℝ) (hγ : 0 < γ) (hα : α < 0)
    (hd : d ≠ 0) (he3 : e3 ≠ 0) (hg : ⟪e3, e4⟫ < 0) :
    ⟪e3, γ • d + α • e3⟫ < 0 ∧ 0 < ⟪e4, γ • d + α • e3⟫ ∧ 0 < ⟪d, γ • d + α • e3⟫ := by
  have h3' : ⟪e3, d⟫ = 0 := by rw [real_inner_comm]; exact h3
  have h4' : ⟪e4, d⟫ = 0 := by rw [real_inner_comm]; exact h4
  have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd
  have hee : 0 < ⟪e3, e3⟫ := real_inner_self_pos.mpr he3
  have he43 : ⟪e4, e3⟫ < 0 := by rw [real_inner_comm]; exact hg
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_add_right, inner_smul_right, inner_smul_right, h3']; nlinarith
  · rw [inner_add_right, inner_smul_right, inner_smul_right, h4']; nlinarith
  · rw [inner_add_right, inner_smul_right, inner_smul_right, h3]; nlinarith

theorem t1e_forced_z (N : NF29 x) (ht : N.t = 1) (hdG4 : 0 < N.dG4)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) :
    ⟪x 3, N.u023_356 x⟫ < ⟪x 6, N.u023_356 x⟫ ∧ ⟪x 6, N.u023_356 x⟫ < ⟪x 4, N.u023_356 x⟫ ∧
      ⟪x 4, N.u023_356 x⟫ < ⟪x 1, N.u023_356 x⟫ := by
  have hp := t1_par N ht
  rw [hp, real_inner_smul_right] at h35 h45
  have h3 : ⟪x 1 - x 4, x 3 - x 6⟫ = 0 := by
    rw [real_inner_comm]; exact (mul_eq_zero.mp h35).resolve_left N.hs.ne'
  have h4 : ⟪x 1 - x 4, x 4 - x 6⟫ = 0 := by
    rw [real_inner_comm]; exact (mul_eq_zero.mp h45).resolve_left N.hs.ne'
  have hd : x 1 - x 4 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide))
  have he3 : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide))
  have := t1e_forced_depths (x 1 - x 4) (x 3 - x 6) (x 4 - x 6) h3 h4 N.D023 (-N.dG4)
    (D023_pos N) (by linarith) hd he3 hg34
  obtain ⟨a, b, c⟩ := this
  change ⟪x 3 - x 6, N.u023_356 x⟫ < 0 at a
  change 0 < ⟪x 4 - x 6, N.u023_356 x⟫ at b
  change 0 < ⟪x 1 - x 4, N.u023_356 x⟫ at c
  rw [inner_sub_left] at a b c
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ### facings -/

theorem t1e_facing_signs (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hdG4 : 0 < N.dG4)
    (hA : 0 < 1 - N.b0 - N.h0) (s012 s124 : SignType)
    (h012 : SignType.sign (N.D02 * (N.b0 - N.b2 + N.h0 - N.h2)) = s012)
    (h124 : SignType.sign (-(N.b2 + N.h2) * N.dG4) = s124) :
    ∀ t : Fin 9, SignType.sign ⟪(s0x_fac29 N.facets).N t, N.u023_356 x⟫ =
      ![s012, 1, 0, 1, s124, 1, -1, -1, 0] t := by
  intro t
  have hnb : ∀ t : Fin 9, ⟪(s0x_fac29 N.facets).N t, N.u023_356 x⟫ =
      (s0x_fac29 N.facets).f t (x 3 + N.u023_356 x) - (s0x_fac29 N.facets).f t (x 3) := by
    intro t; rw [(s0x_fac29 N.facets).hN t (x 3 + N.u023_356 x) (x 3), add_sub_cancel_left]
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hDG4 : 0 < N.DG4 := by have := N.hDG4; simp only [DG4, D02, dG4]; linarith
  have c1 := t1l2_c234 N.a0 N.a2 N.b2 N.h2 N.b0 N.h0 N.ha0 ha2 N.hDG5 hA
  have c2 := t1l2_c015 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.ha0 N.hh0 N.hDG5 hdG4
  rw [hnb t]
  fin_cases t
  · change SignType.sign (N.f012.f (x 3 + N.u023_356 x) - N.f012.f (x 3)) = s012
    rw [f012_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]; exact h012
  · change SignType.sign (N.f015.f (x 3 + N.u023_356 x) - N.f015.f (x 3)) = 1
    rw [f015_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]; exact sign_pos c2
  · change SignType.sign (N.f023.f (x 3 + N.u023_356 x) - N.f023.f (x 3)) = 0
    rw [f023_u023_356 N ht]; exact sign_zero
  · change SignType.sign (N.f035.f (x 3 + N.u023_356 x) - N.f035.f (x 3)) = 1
    rw [f035_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]
    refine sign_pos (mul_pos hA ?_)
    have := N.hE35; nlinarith
  · change SignType.sign (N.f124.f (x 3 + N.u023_356 x) - N.f124.f (x 3)) = s124
    rw [f124_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]; exact h124
  · change SignType.sign (N.f1456.f (x 3 + N.u023_356 x) - N.f1456.f (x 3)) = 1
    rw [f1456_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]; exact sign_pos hdG4
  · change SignType.sign (N.f234.f (x 3 + N.u023_356 x) - N.f234.f (x 3)) = -1
    rw [f234_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]
    exact sign_neg (mul_neg_of_neg_of_pos (by linarith) hDG4)
  · change SignType.sign (N.f346.f (x 3 + N.u023_356 x) - N.f346.f (x 3)) = -1
    rw [f346_u023_356 N ht, sign_mul, sign_pos hD2, mul_one]
    exact sign_neg (by linarith [D023_pos N])
  · change SignType.sign (N.f356.f (x 3 + N.u023_356 x) - N.f356.f (x 3)) = 0
    rw [f356_u023_356 N ht]; exact sign_zero

/-! ### the finite data: points and forced pairs (rims and checks in Type29T1Res) -/

def t1e_P5 : Fin 5 → Fin 7 := ![1, 2, 3, 4, 6]
def t1e_forced5 : List (Fin 5 × Fin 5) := [(4, 2), (3, 4), (0, 3)]
/-! ### case A (x0 on the rim) -/
/-- `Dp ≥ 0` in case A and on its wall `m = b0 + h0`. Only seven inequalities are needed (the
NF29 facts `a2 < 0`, `b2 < 0`, `h0, h2 > 0`, the facet inequalities and `D234 ≥ 1` of the first
version were not used; each of the seven is needed by this `nlinarith` call). -/
theorem t1l2_cA2 (a0 b0 h0 a2 b2 h2 s : ℝ) (ha0 : a0 < 0) (hb0 : 0 < b0)
    (hDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)))
    (hs : 1 ≤ s) (hA0 : 0 < 1 - b0 - h0)
    (hdG4 : 0 < b0 * (1 - h2) - b2 * (1 - h0)) (hA : b0 + h0 ≤ b2 + h2) :
    0 ≤ a2 - a0 + s * (h2 - h0) - (s - 1) * (b2 + h2 - b0 - h0) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hA)]
def t1e_P6 : Fin 6 → Fin 7 := ![1, 2, 3, 4, 6, 0]
def t1e_forced6 : List (Fin 6 × Fin 6) := [(4, 2), (3, 4), (0, 3), (5, 1)]
theorem t1e_vec_x02 (N : NF29 x) (ht : N.t = 1) :
    x 0 - x 2 = (N.a2 - N.a0 + N.s * (N.h2 - N.h0) - (N.s - 1) * (N.b2 + N.h2 - N.b0 - N.h0)) • (x 1 - x 4)
      + (N.h0 - N.h2) • (x 3 - x 6) + (N.b2 + N.h2 - N.b0 - N.h0) • (x 4 - x 6) := by
  nf29_simp N
  rw [ht]
  ext i
  simp only [nfV, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `z2 < z0` at `u023_356` for `b0 + h0 ≤ m` (case A and its wall). -/
theorem t1e_z02_A (N : NF29 x) (ht : N.t = 1) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hs1 : 1 ≤ N.s)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) (hmA : N.b0 + N.h0 ≤ N.b2 + N.h2) :
    ⟪x 2, N.u023_356 x⟫ < ⟪x 0, N.u023_356 x⟫ := by
  have hp := t1_par N ht
  rw [hp, real_inner_smul_right] at h35 h45
  have h3 : ⟪x 1 - x 4, x 3 - x 6⟫ = 0 := by
    rw [real_inner_comm]; exact (mul_eq_zero.mp h35).resolve_left N.hs.ne'
  have h4 : ⟪x 1 - x 4, x 4 - x 6⟫ = 0 := by
    rw [real_inner_comm]; exact (mul_eq_zero.mp h45).resolve_left N.hs.ne'
  have h3' : ⟪x 3 - x 6, x 1 - x 4⟫ = 0 := by rw [real_inner_comm]; exact h3
  have h4' : ⟪x 4 - x 6, x 1 - x 4⟫ = 0 := by rw [real_inner_comm]; exact h4
  have hd : x 1 - x 4 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide))
  have he3 : x 3 - x 6 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (N.inj h) (by decide))
  have hdd : 0 < ⟪x 1 - x 4, x 1 - x 4⟫ := real_inner_self_pos.mpr hd
  have hee : 0 < ⟪x 3 - x 6, x 3 - x 6⟫ := real_inner_self_pos.mpr he3
  have hdp := t1l2_cA2 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.ha0 hb0 N.hDG5 hs1 hA hdG4 hmA
  have hq : N.h0 - N.h2 < 0 := by linarith [N.hb2]
  have hr : 0 ≤ N.b2 + N.h2 - N.b0 - N.h0 := by linarith
  have hγ := D023_pos N
  rw [← sub_pos, ← inner_sub_left, t1e_vec_x02 N ht]
  dsimp only [u023_356]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h3,
    h3', h4']
  have hg : ⟪x 4 - x 6, x 3 - x 6⟫ < 0 := by rw [real_inner_comm]; exact hg34
  nlinarith [mul_nonneg hdp (mul_pos hγ hdd).le,
    mul_nonneg (mul_nonneg hr hdG4.le) (neg_pos.mpr hg).le,
    mul_pos (mul_pos (neg_pos.mpr hq) hdG4) hee]

/-! ### the escape of `t1_closed` (copied from nopert229 t1facts/T1Escape.lean) -/

/-- `t1_closed` without the sample fact `hsD`: the whole escape of the V46/W14 argument.
If the V46 leaf region holds and `LexAny29` fails, then `s ≥ 1`, `D234 ≥ 1` and `g35 = g45 = 0`. -/
theorem t1_escape (N : NF29 x) (ht : N.t = 1)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hU5 : 0 < N.DG4 - N.D023)
    (hg35 : ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0) (hg45 : ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0)
    (h012 : 0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0)
    (lam mu eta : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (heta : 0 < eta)
    (hfront : lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    1 ≤ N.s ∧ 1 ≤ N.D234 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧ ⟪x 4 - x 6, x 5 - x 6⟫ = 0 := by
  have hA46 := v46_fail N hdG4 h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0
    hmu1 heta hfront hnf
  obtain ⟨h35, h45⟩ := g35_g45_zero_of_V46 N ht hU5 hg35 hg45 hA46
  have hsD : ¬ (N.s < 1 ∨ N.D234 < 1) := fun hsD =>
    hnf (lexAny29_W14_of_V46 N ht hdG4 hA hU5 hsD hg35 hg45 hA46)
  push Not at hsD
  exact ⟨hsD.1, hsD.2, h35, h45⟩

end Minimality.NF29
