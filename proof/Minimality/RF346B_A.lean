module

public import Minimality.R012
public import Minimality.R012F
public import Minimality.R012M
public import Minimality.Q45Tie

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012

variable {x : Fin 7 → ℝ³}

/-- The 5-rim `(1, 6, 3, 5, 2)`; the chord `2 → 1` of facet 012 is the edge from index `4` to index `0`
(vertex `0` is the middle over it). -/
def rimN : ZMod 5 → Fin 7
  | 0 => 1
  | 1 => 6
  | 2 => 3
  | 3 => 5
  | 4 => 2

theorem rf346b_inner_plane (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (A B : ℝ) :
    ⟪F.N t, A • (x 0 - x 1) + B • (x 2 - x 1)⟫ =
      A * (F.f t (x 0) - F.f t (x 1)) + B * (F.f t (x 2) - F.f t (x 1)) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]

/-- A view `u` in the plane of 012 with `N5 < 0`, `N1 > 0`, `N2 > 0` is `A (x0-x1) + B (x2-x1)` with
`A > 0`, `B < 0`, `A + B > 0` (the window `t = B/A ∈ (-1, 0)`). -/
theorem rf346b_coords (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h0 : ⟪F.N 0, u⟫ = 0)
    (h5 : ⟪F.N 5, u⟫ < 0) (h1 : 0 < ⟪F.N 1, u⟫) (h2 : 0 < ⟪F.N 2, u⟫) :
    ∃ A B : ℝ, 0 < A ∧ B < 0 ∧ 0 < A + B ∧ u = A • (x 0 - x 1) + B • (x 2 - x 1) := by
  obtain ⟨p, q, r, hu⟩ := exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) u (omega_ne_zero F)
  have hu' : u = p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1) := hu
  have e : ∀ t : Fin 9, ⟪F.N t, u⟫ = p * (F.f t (x 0) - F.f t (x 1)) + q * (F.f t (x 2) - F.f t (x 1))
      + r * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    rw [hu', inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
  have f0 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f5 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have f1 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have f2 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  rw [e] at h0 h5 h1 h2
  rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at h0
  rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at h5
  rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at h1
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at h2
  have hr : r = 0 := by
    have : r * F.f 0 (x 6) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h f0.ne
  subst hr
  have hp : 0 < p := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f5.le]
  have hq : q < 0 := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg hn (neg_nonneg.mpr f1.le)]
  have hpq : 0 < p + q := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f2.le]
  exact ⟨p, q, hp, hq, hpq, by rw [hu', zero_smul, add_zero]⟩

/-- `Ω * det3 (x2-x1, x6-x1, x_d - x1) > 0` for `d` off facet 126 (facet 5). -/
lemma rf346b_omega_V5d (F : S0xFac 9 s0x_S24 x) (d : Fin 7) (hd : d ∉ s0x_S24 5) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 1) (x 6 - x 1) (x d - x 1) := by
  have hc := cramer_facet_eq F 5 1 2 6 0 d (by decide) (by decide) (by decide)
  have hid : det3 (x 2 - x 1) (x 6 - x 1) (x 0 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [hid] at hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have f0 := F.neg 5 0 (by decide)
  have fd := F.neg 5 d hd
  have h1 : (Ω * det3 (x 2 - x 1) (x 6 - x 1) (x d - x 1)) * F.f 5 (x 0) = Ω ^ 2 * F.f 5 (x d) := by
    linear_combination (-Ω) * hc
  have h2 : (Ω * det3 (x 2 - x 1) (x 6 - x 1) (x d - x 1)) * F.f 5 (x 0) < 0 := by
    rw [h1]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hΩ) fd
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f0.le]

/-- `Ω * det3 (x2-x0, x5-x0, x3-x0) < 0` (facets 025, 235). -/
lemma rf346b_omega_E1 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0) < 0 := by
  have hA := omega_mul_det3_0256_pos_unconditional F
  have hB := cramer_facet_eq F 2 0 2 5 3 6 (by decide) (by decide) (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have e1 : det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) = - det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e1] at hA
  set E1 := det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0)
  set E2 := det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0)
  have f26 := F.neg 2 6 (by decide)
  have f23 := F.neg 2 3 (by decide)
  have hE2 : Ω * E2 < 0 := by nlinarith
  have h1 : (Ω * E1) * F.f 2 (x 6) = (Ω * E2) * F.f 2 (x 3) := by linear_combination Ω * hB
  have h1' : 0 < (Ω * E1) * F.f 2 (x 6) := by
    rw [h1]; exact mul_pos_of_neg_of_neg hE2 f23
  exact neg_of_mul_pos_of_neg' f26 h1'

/-- `Ω * det3 (x3-x2, x5-x2, x_d - x2) < 0` for `d` off facet 235 (facet 6). -/
lemma rf346b_omega_G6d (F : S0xFac 9 s0x_S24 x) (d : Fin 7) (hd : d ∉ s0x_S24 6) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 2) (x 5 - x 2) (x d - x 2) < 0 := by
  have hE := rf346b_omega_E1 F
  have hc := cramer_facet_eq F 6 2 3 5 0 d (by decide) (by decide) (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have e : det3 (x 3 - x 2) (x 5 - x 2) (x 0 - x 2) = det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e] at hc
  set E1 := det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0)
  have f0 := F.neg 6 0 (by decide)
  have fd := F.neg 6 d hd
  have h1 : (Ω * det3 (x 3 - x 2) (x 5 - x 2) (x d - x 2)) * F.f 6 (x 0) = (Ω * E1) * F.f 6 (x d) := by
    linear_combination (-Ω) * hc
  have h2 : 0 < (Ω * det3 (x 3 - x 2) (x 5 - x 2) (x d - x 2)) * F.f 6 (x 0) := by
    rw [h1]; exact mul_pos_of_neg_of_neg hE fd
  exact neg_of_mul_pos_of_neg' f0 h2

/-- `(-Ω) κ` of the four forced sub-quads of the rim `(1,6,3,5,2)`: signs `+ - + -` for deleting
the corners `1, 6, 3, 5`. -/
theorem rf346b_sub_kappa_sign (F : S0xFac 9 s0x_S24 x) :
    let p : ZMod 5 → ℝ³ := fun i => x (rimN i)
    let Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
    0 < (-Ω) * quadKappa (subquad p 0) ∧ (-Ω) * quadKappa (subquad p 1) < 0 ∧
    0 < (-Ω) * quadKappa (subquad p 2) ∧ (-Ω) * quadKappa (subquad p 3) < 0 := by
  intro p Ω
  have g6 := rf346b_omega_G6d F 6 (by decide)
  have g1 := rf346b_omega_G6d F 1 (by decide)
  have v5 := rf346b_omega_V5d F 5 (by decide)
  have v3 := rf346b_omega_V5d F 3 (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < (-Ω) * det3 (x 5 - x 6) (x 2 - x 3) (x 6 - x 3)
    have e : det3 (x 5 - x 6) (x 2 - x 3) (x 6 - x 3) = det3 (x 3 - x 2) (x 5 - x 2) (x 6 - x 2) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; linarith
  · change (-Ω) * det3 (x 2 - x 3) (x 1 - x 5) (x 3 - x 5) < 0
    have e : det3 (x 2 - x 3) (x 1 - x 5) (x 3 - x 5) = - det3 (x 3 - x 2) (x 5 - x 2) (x 1 - x 2) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; linarith
  · change 0 < (-Ω) * det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2)
    have e : det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2) = - det3 (x 2 - x 1) (x 6 - x 1) (x 5 - x 1) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; linarith
  · change (-Ω) * det3 (x 6 - x 2) (x 3 - x 1) (x 2 - x 1) < 0
    have e : det3 (x 6 - x 2) (x 3 - x 1) (x 2 - x 1) = det3 (x 2 - x 1) (x 6 - x 1) (x 3 - x 1) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e]; linarith

end Minimality.T24.R012
