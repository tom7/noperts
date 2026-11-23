module

public import Minimality.Type29T1Close
public import Minimality.SVC

@[expose] public section

/-!
# Type 29, `t = 1` K1a cell without the sample fact `s < 1 ∨ D234 < 1`

`t1_closed` (Type29T1Close) needs `hsD : s < 1 ∨ D234 < 1`, which fails on part of the cell
(nopert229 T1FACTS: exact escape shape `(-43/20, 3/5, 7/20, -7/2, -33/20, 9/4, 31/20, 1)`).
`t1_escape`: on the escape (`¬ hsD`, `¬ LexAny29`) one has `s ≥ 1`, `D234 ≥ 1`, `g35 = g45 = 0`.
There the view `u023_356 = D023 (x1 - x4) - dG4 (x3 - x6)` (line of the facet planes 023 and 356)
closes by `single_view_closure` with the tilt `x0 - x1`, in three cases of `m = b2 + h2`:
`C : m < 0`, `B : 0 < m < b0 + h0`, `A : b0 + h0 < m` (leaves `lexAny29_F023F356_C/B/A`).
`t1_closed'` = `t1_closed` with `hsD` replaced by `hsD ∨ T1EscOK N`.

Not covered (hypotheses of `T1EscOK`): K1a (`a2 < 0 < b0`), the edge cases `m = 0` (facet 124
edge-on at the view) and `m = b0 + h0` (facet 012 edge-on), and depth ties at the view among the
vertices `1, 2, 3, 4, 6` (and `0` in case A); the forced chain is `z3 < z6 < z4 < z1` (and `z2 < z0`
in case A), so only ties with `z2` (and `z0`) are open, a codimension-1 metric set.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.SVC

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

/-- the tilt `x0 - x1` is positive on both edge-on facets 023 and 356 -/
theorem t1e_tilt_pos (N : NF29 x) (ht : N.t = 1) (hb0 : 0 < N.b0) :
    0 < N.f023.f (x 0) - N.f023.f (x 1) ∧ 0 < N.f356.f (x 0) - N.f356.f (x 1) := by
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  refine ⟨?_, ?_⟩
  · have h0 := N.f023.zero 0 (by decide)
    have h1 := N.f023.neg 1 (by decide)
    linarith
  · have hv : N.f356.f (x 0) - N.f356.f (x 1) = (N.b0 + N.h0) * N.s * N.D ^ 2 := by
      dsimp only [f356, Face16.ofPoly]
      nf29_simp N
      simp only [det3c, NF29.D]
      rw [ht]; ring
    rw [hv]
    exact mul_pos (mul_pos (by linarith [N.hh0]) N.hs) hD2

/-! ### the finite core (copied from T1Core) -/

def t1e_P5 : Fin 5 → Fin 7 := ![1, 2, 3, 4, 6]
def t1e_forced5 : List (Fin 5 × Fin 5) := [(4, 2), (3, 4), (0, 3)]
def t1e_RB : List (Rim 9 5) :=
  [{ k := 5, c := ![3, 4, 2, 1, 0], U := {0, 1, 2, 3, 5, 8}, Dn := {4, 6, 7},
     sd := ![0, 0, 1, 0, 0, 0, 0, 0, 1] }]
def t1e_RC : List (Rim 9 5) :=
  [{ k := 4, c := ![3, 4, 2, 1], U := {0, 1, 2, 3, 4, 5, 8}, Dn := {6, 7},
     sd := ![0, 0, 1, 0, 0, 0, 0, 0, 1] }]
theorem t1e_checkB : check s0x_S29 t1e_P5 ![1, 1, 0, 1, -1, 1, -1, -1, 0] t1e_forced5 [] t1e_RB = true := by
  decide +kernel
theorem t1e_checkC : check s0x_S29 t1e_P5 ![1, 1, 0, 1, 1, 1, -1, -1, 0] t1e_forced5 [] t1e_RC = true := by
  decide +kernel

theorem t1e_leaf_core (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0)
    (s012 s124 : SignType) (hs012 : s012 ≠ 0) (hs124 : s124 ≠ 0)
    (h012 : SignType.sign (N.D02 * (N.b0 - N.b2 + N.h0 - N.h2)) = s012)
    (h124 : SignType.sign (-(N.b2 + N.h2) * N.dG4) = s124)
    (R : List (Rim 9 5)) (hRsd : ∀ ρ ∈ R, ρ.sd = ![0, 0, 1, 0, 0, 0, 0, 0, 1])
    (hgen : ∀ i j : Fin 5, i ≠ j → ⟪x (t1e_P5 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P5 j), N.u023_356 x⟫)
    (hcheck : check s0x_S29 t1e_P5 ![s012, 1, 0, 1, s124, 1, -1, -1, 0] t1e_forced5 [] R = true) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  obtain ⟨z1, z2, z3⟩ := t1e_forced_z N ht hdG4 h35 h45 hg34
  obtain ⟨t1, t2⟩ := t1e_tilt_pos N ht hb0
  refine single_view_closure (s0x_fac29 N.facets) t1e_P5 (N.u023_356 x) _
    (t1e_facing_signs N ht ha2 hdG4 hA s012 s124 h012 h124) R ?_ t1e_forced5 ?_ [] (by simp) hgen hcheck
  · intro ρ hρ
    refine ⟨x 0 - x 1, fun t ht0 => ?_⟩
    rw [hRsd ρ hρ]
    have hd : ∀ t : Fin 9, ⟪(s0x_fac29 N.facets).N t, x 0 - x 1⟫ =
        (s0x_fac29 N.facets).f t (x 0) - (s0x_fac29 N.facets).f t (x 1) :=
      fun t => ((s0x_fac29 N.facets).hN t (x 0) (x 1)).symm
    rw [hd t]
    fin_cases t
    · exact absurd ht0 hs012
    · exact absurd ht0 (by simp)
    · change SignType.sign (N.f023.f (x 0) - N.f023.f (x 1)) = 1
      exact sign_pos t1
    · exact absurd ht0 (by simp)
    · exact absurd ht0 hs124
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · change SignType.sign (N.f356.f (x 0) - N.f356.f (x 1)) = 1
      exact sign_pos t2
  · intro ij hij
    simp only [t1e_forced5, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl
    · exact z1
    · exact z2
    · exact z3

/-- case C: `b2 + h2 < 0` (x1 inside the rim 4 6 3 2) -/
theorem lexAny29_F023F356_C (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) (hm : N.b2 + N.h2 < 0)
    (hgen : ∀ i j : Fin 5, i ≠ j → ⟪x (t1e_P5 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P5 j), N.u023_356 x⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  have hD02 : 0 < N.D02 := N.hDD
  refine t1e_leaf_core N ht ha2 hb0 hdG4 hA h35 h45 hg34 1 1 one_ne_zero one_ne_zero ?_ ?_ t1e_RC
    (by intro ρ hρ; simp [t1e_RC] at hρ; subst hρ; rfl) hgen t1e_checkC
  · exact sign_pos (mul_pos hD02 (by linarith [N.hh0]))
  · exact sign_pos (mul_pos (by linarith) hdG4)

/-- case B: `0 < b2 + h2 < b0 + h0` (rim 4 6 3 2 1) -/
theorem lexAny29_F023F356_B (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) (hm0 : 0 < N.b2 + N.h2)
    (hm1 : N.b2 + N.h2 < N.b0 + N.h0)
    (hgen : ∀ i j : Fin 5, i ≠ j → ⟪x (t1e_P5 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P5 j), N.u023_356 x⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  have hD02 : 0 < N.D02 := N.hDD
  refine t1e_leaf_core N ht ha2 hb0 hdG4 hA h35 h45 hg34 1 (-1) one_ne_zero (by decide) ?_ ?_ t1e_RB
    (by intro ρ hρ; simp [t1e_RB] at hρ; subst hρ; rfl) hgen t1e_checkB
  · exact sign_pos (mul_pos hD02 (by linarith))
  · exact sign_neg (mul_neg_of_neg_of_pos (by linarith) hdG4)

/-! ### case A (x0 on the rim) -/
/-- `Dp ≥ 0` in case A. Only seven inequalities are needed (the NF29 facts `a2 < 0`, `b2 < 0`,
`h0, h2 > 0`, the facet inequalities and `D234 ≥ 1` of the first version were not used; each of the
seven is needed by this `nlinarith` call). -/
theorem t1l2_cA2 (a0 b0 h0 a2 b2 h2 s : ℝ) (ha0 : a0 < 0) (hb0 : 0 < b0)
    (hDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2)))
    (hs : 1 ≤ s) (hA0 : 0 < 1 - b0 - h0)
    (hdG4 : 0 < b0 * (1 - h2) - b2 * (1 - h0)) (hA : b0 + h0 < b2 + h2) :
    0 ≤ a2 - a0 + s * (h2 - h0) - (s - 1) * (b2 + h2 - b0 - h0) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_pos.mpr hA).le]
def t1e_P6 : Fin 6 → Fin 7 := ![1, 2, 3, 4, 6, 0]
def t1e_forced6 : List (Fin 6 × Fin 6) := [(4, 2), (3, 4), (0, 3), (5, 1)]
def t1e_RA : List (Rim 9 6) :=
  [{ k := 6, c := ![3, 4, 2, 1, 5, 0], U := {1, 2, 3, 5, 8}, Dn := {0, 4, 6, 7},
     sd := ![0, 0, 1, 0, 0, 0, 0, 0, 1] }]
theorem t1e_checkA : check s0x_S29 t1e_P6 ![-1, 1, 0, 1, -1, 1, -1, -1, 0] t1e_forced6 [] t1e_RA = true := by
  decide +kernel

theorem t1e_vec_x02 (N : NF29 x) (ht : N.t = 1) :
    x 0 - x 2 = (N.a2 - N.a0 + N.s * (N.h2 - N.h0) - (N.s - 1) * (N.b2 + N.h2 - N.b0 - N.h0)) • (x 1 - x 4)
      + (N.h0 - N.h2) • (x 3 - x 6) + (N.b2 + N.h2 - N.b0 - N.h0) • (x 4 - x 6) := by
  nf29_simp N
  rw [ht]
  ext i
  simp only [nfV, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem t1e_z02_A (N : NF29 x) (ht : N.t = 1) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hs1 : 1 ≤ N.s)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) (hmA : N.b0 + N.h0 < N.b2 + N.h2) :
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
  have hr : 0 < N.b2 + N.h2 - N.b0 - N.h0 := by linarith
  have hγ := D023_pos N
  rw [← sub_pos, ← inner_sub_left, t1e_vec_x02 N ht]
  dsimp only [u023_356]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h3,
    h3', h4']
  have hg : ⟪x 4 - x 6, x 3 - x 6⟫ < 0 := by rw [real_inner_comm]; exact hg34
  nlinarith [mul_nonneg hdp (mul_pos hγ hdd).le, mul_pos (mul_pos hr hdG4) (neg_pos.mpr hg),
    mul_nonneg (mul_nonneg (neg_nonneg.mpr hq.le) hdG4.le) hee.le]

theorem lexAny29_F023F356_A (N : NF29 x) (ht : N.t = 1) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hs1 : 1 ≤ N.s)
    (h35 : ⟪x 3 - x 6, x 5 - x 6⟫ = 0) (h45 : ⟪x 4 - x 6, x 5 - x 6⟫ = 0)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ < 0) (hmA : N.b0 + N.h0 < N.b2 + N.h2)
    (hgen : ∀ i j : Fin 6, i ≠ j → ⟪x (t1e_P6 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P6 j), N.u023_356 x⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  obtain ⟨z1, z2, z3⟩ := t1e_forced_z N ht hdG4 h35 h45 hg34
  have z4 := t1e_z02_A N ht hb0 hdG4 hA hs1 h35 h45 hg34 hmA
  obtain ⟨t1, t2⟩ := t1e_tilt_pos N ht hb0
  have hD02 : 0 < N.D02 := N.hDD
  have hb2 := N.hb2
  refine single_view_closure (s0x_fac29 N.facets) t1e_P6 (N.u023_356 x) _
    (t1e_facing_signs N ht ha2 hdG4 hA (-1) (-1) ?_ ?_) t1e_RA ?_ t1e_forced6 ?_ [] (by simp) hgen t1e_checkA
  · exact sign_neg (mul_neg_of_pos_of_neg hD02 (by linarith [N.hh0]))
  · exact sign_neg (mul_neg_of_neg_of_pos (by linarith [N.hh0]) hdG4)
  · intro ρ hρ
    simp only [t1e_RA, List.mem_singleton] at hρ
    subst hρ
    refine ⟨x 0 - x 1, fun t ht0 => ?_⟩
    have hd : ∀ t : Fin 9, ⟪(s0x_fac29 N.facets).N t, x 0 - x 1⟫ =
        (s0x_fac29 N.facets).f t (x 0) - (s0x_fac29 N.facets).f t (x 1) :=
      fun t => ((s0x_fac29 N.facets).hN t (x 0) (x 1)).symm
    rw [hd t]
    fin_cases t
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · change SignType.sign (N.f023.f (x 0) - N.f023.f (x 1)) = 1
      exact sign_pos t1
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · exact absurd ht0 (by simp)
    · change SignType.sign (N.f356.f (x 0) - N.f356.f (x 1)) = 1
      exact sign_pos t2
  · intro ij hij
    simp only [t1e_forced6, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl | rfl
    · exact z1
    · exact z2
    · exact z3
    · exact z4


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

/-! ### `t1_closed'`: the `t = 1` cell without `hsD` -/

/-- Distinct depths on `1, 2, 3, 4, 6` and of `0` against them give distinct depths on `t1e_P6`. -/
theorem t1e_gen6 (N : NF29 x)
    (hgen : ∀ i j : Fin 5, i ≠ j → ⟪x (t1e_P5 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P5 j), N.u023_356 x⟫)
    (h0 : ∀ i : Fin 5, ⟪x 0, N.u023_356 x⟫ ≠ ⟪x (t1e_P5 i), N.u023_356 x⟫) :
    ∀ i j : Fin 6, i ≠ j → ⟪x (t1e_P6 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P6 j), N.u023_356 x⟫ := by
  have hP : ∀ i : Fin 5, t1e_P6 (Fin.castSucc i) = t1e_P5 i := by decide
  have hL : t1e_P6 (Fin.last 5) = 0 := rfl
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact absurd rfl hij
    | cast j => rw [hL, hP]; exact h0 j
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [hL, hP]; exact fun h => h0 i h.symm
    | cast j => rw [hP, hP]; exact hgen i j (fun h => hij (by rw [h]))

/-- The part of the escape `1 ≤ s, 1 ≤ D234` of `t1_closed` that `lexAny29_F023F356_A/B/C` close:
K1a, `m = b2 + h2` off the two edge-on values `0` and `b0 + h0`, and no depth tie at `u023_356`
among `1, 2, 3, 4, 6`, nor of `0` with them in case A (`b0 + h0 < m`). -/
def T1EscOK (N : NF29 x) : Prop :=
  N.a2 < 0 ∧ 0 < N.b0 ∧ N.b2 + N.h2 ≠ 0 ∧ N.b2 + N.h2 ≠ N.b0 + N.h0 ∧
    (∀ i j : Fin 5, i ≠ j → ⟪x (t1e_P5 i), N.u023_356 x⟫ ≠ ⟪x (t1e_P5 j), N.u023_356 x⟫) ∧
    (N.b0 + N.h0 < N.b2 + N.h2 →
      ∀ i : Fin 5, ⟪x 0, N.u023_356 x⟫ ≠ ⟪x (t1e_P5 i), N.u023_356 x⟫)

/-- **`t1_closed` without the sample fact `hsD`.** On the `t = 1` K1a cell with the V46 leaf region,
either `hsD` (old proof, `t1_closed`) or the escape conditions `T1EscOK` (then `t1_escape` gives
`s, D234 ≥ 1`, `g35 = g45 = 0`; `¬ Z` makes `g34 < 0`; the leaves `lexAny29_F023F356_A/B/C` close). -/
theorem t1_closed' (N : NF29 x) (ht : N.t = 1)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hU5 : 0 < N.DG4 - N.D023)
    (hesc : (N.s < 1 ∨ N.D234 < 1) ∨ N.T1EscOK)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0)
    (hZ : ¬ (⟪x 3 - x 6, x 4 - x 6⟫ = 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧
      ⟪x 4 - x 6, x 5 - x 6⟫ = 0))
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
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  rcases hesc with hsD | ⟨ha2, hb0, hm0, hm1, hgen, hgenA⟩
  · exact t1_closed N ht hdG4 hA hU5 hsD hg35 hg45 h012 h015 h035 h124 h1456 h234 h356
      lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront hnf
  obtain ⟨hs1, -, h35, h45⟩ := t1_escape N ht hdG4 hA hU5 hg35 hg45 h012 h015 h035 h124
    h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront hnf
  have hg34' : ⟪x 3 - x 6, x 4 - x 6⟫ < 0 :=
    lt_of_le_of_ne hg34 (fun h => hZ ⟨h, h35, h45⟩)
  rcases lt_or_gt_of_ne hm0 with hC | hpos
  · exact hnf (lexAny29_F023F356_C N ht ha2 hb0 hdG4 hA h35 h45 hg34' hC hgen)
  rcases lt_or_gt_of_ne hm1 with hB | hAc
  · exact hnf (lexAny29_F023F356_B N ht ha2 hb0 hdG4 hA h35 h45 hg34' hpos hB hgen)
  · exact hnf (lexAny29_F023F356_A N ht ha2 hb0 hdG4 hA hs1 h35 h45 hg34' hAc
      (t1e_gen6 N hgen (hgenA hAc)))

end Minimality.NF29
