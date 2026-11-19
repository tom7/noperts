module

public import Minimality.Cell0234
public import Minimality.OctaTools

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.T24.FrontDiag
open Minimality Minimality.H21 Minimality.RimCell

theorem ip3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- Two tests at an edge `PQ` seen from two facets (one up, one down at `u`) have the same
nonzero sign. -/
theorem fd_edge {u Na Nb e r t : ℝ³} (he : e ≠ 0) (hNa : 0 < ⟪Na, u⟫) (hNb : ⟪Nb, u⟫ < 0)
    (hae : ⟪Na, e⟫ = 0) (hbe : ⟪Nb, e⟫ = 0)
    (hr1 : ⟪Na, r⟫ ≤ 0) (hr2 : ⟪Nb, r⟫ ≤ 0) (hr3 : ⟪Na, r⟫ < 0 ∨ ⟪Nb, r⟫ < 0)
    (ht1 : ⟪Na, t⟫ ≤ 0) (ht2 : ⟪Nb, t⟫ ≤ 0) (ht3 : ⟪Na, t⟫ < 0 ∨ ⟪Nb, t⟫ < 0) :
    0 < det3 e r u * det3 e t u := by
  set g : ℝ³ := ⟪Na, u⟫ • Nb - ⟪Nb, u⟫ • Na with hg
  have hgu : ⟪g, u⟫ = 0 := by
    simp only [hg, inner_sub_left, real_inner_smul_left]; ring
  have hge : ⟪g, e⟫ = 0 := by
    simp only [hg, inner_sub_left, real_inner_smul_left, hae, hbe]; ring
  have hgr : ⟪g, r⟫ < 0 := by
    simp only [hg, inner_sub_left, real_inner_smul_left]
    rcases hr3 with h | h <;> nlinarith
  have hgt : ⟪g, t⟫ < 0 := by
    simp only [hg, inner_sub_left, real_inner_smul_left]
    rcases ht3 with h | h <;> nlinarith
  set n : ℝ³ := cross u e with hn
  have hdet : ∀ w : ℝ³, det3 e w u = ⟪n, w⟫ := by
    intro w; simp only [hn, det3_expand, ip3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hnn : 0 < ⟪n, n⟫ := by
    by_contra hcon
    have h0 : n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 := by
      rw [ip3] at hcon; refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2)]
    obtain ⟨h0, h1, h2⟩ := h0
    simp only [hn, cross_apply_zero, cross_apply_one, cross_apply_two] at h0 h1 h2
    have ha : ⟪Na, e⟫ = 0 := hae
    rw [ip3] at ha
    apply he
    have e0 : ⟪Na, u⟫ * e 0 = 0 := by
      rw [ip3]; linear_combination (Na 2) * h1 - (Na 1) * h2 + (u 0) * ha
    have e1 : ⟪Na, u⟫ * e 1 = 0 := by
      rw [ip3]; linear_combination (Na 0) * h2 - (Na 2) * h0 + (u 1) * ha
    have e2 : ⟪Na, u⟫ * e 2 = 0 := by
      rw [ip3]; linear_combination (Na 1) * h0 - (Na 0) * h1 + (u 2) * ha
    ext i; fin_cases i <;> simp
    · exact (mul_eq_zero.mp e0).resolve_left hNa.ne'
    · exact (mul_eq_zero.mp e1).resolve_left hNa.ne'
    · exact (mul_eq_zero.mp e2).resolve_left hNa.ne'
  have key : ∀ w : ℝ³, ⟪g, w⟫ * ⟪n, n⟫ = ⟪g, n⟫ * ⟪n, w⟫ := by
    intro w
    simp only [hn, ip3, cross_apply_zero, cross_apply_one, cross_apply_two]
    rw [ip3] at hgu hge
    have n0 : (u 1 * e 2 - u 2 * e 1) = (u 1 * e 2 - u 2 * e 1) := rfl
    linear_combination
      (-(w 0 * (u 1 * (u 0 * e 1 - u 1 * e 0) - u 2 * (u 2 * e 0 - u 0 * e 2))
        + w 1 * (u 2 * (u 1 * e 2 - u 2 * e 1) - u 0 * (u 0 * e 1 - u 1 * e 0))
        + w 2 * (u 0 * (u 2 * e 0 - u 0 * e 2) - u 1 * (u 1 * e 2 - u 2 * e 1)))) * hge
      + (w 0 * (e 1 * (u 0 * e 1 - u 1 * e 0) - e 2 * (u 2 * e 0 - u 0 * e 2))
        + w 1 * (e 2 * (u 1 * e 2 - u 2 * e 1) - e 0 * (u 0 * e 1 - u 1 * e 0))
        + w 2 * (e 0 * (u 2 * e 0 - u 0 * e 2) - e 1 * (u 1 * e 2 - u 2 * e 1))) * hgu
  rw [hdet r, hdet t]
  have k1 := key r
  have k2 := key t
  by_contra hcon
  push Not at hcon
  have h1 : ⟪g, r⟫ * ⟪g, t⟫ * (⟪n, n⟫ * ⟪n, n⟫) = (⟪g, n⟫ * ⟪g, n⟫) * (⟪n, r⟫ * ⟪n, t⟫) := by
    linear_combination (⟪g, t⟫ * ⟪n, n⟫) * k1 + (⟪g, n⟫ * ⟪n, r⟫) * k2
  have h2 : 0 < ⟪g, r⟫ * ⟪g, t⟫ * (⟪n, n⟫ * ⟪n, n⟫) := by
    have := mul_pos_of_neg_of_neg hgr hgt
    positivity
  have h3 : (⟪g, n⟫ * ⟪g, n⟫) * (⟪n, r⟫ * ⟪n, t⟫) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) hcon
  linarith

theorem fd_real {a1 a2 a3 a4 κ nu f1 f3 s q01 q03 q21 q23 : ℝ}
    (h4 : 0 < a4 * a3) (h1 : 0 < a1 * a4) (h2 : 0 < a2 * a1) (h3 : 0 < a3 * a2)
    (hsum : a1 - a2 + a3 - a4 = 0) (hnu : 0 < nu) (hNV : κ * nu = -a2 * f1 - a4 * f3)
    (hf1 : f1 ≤ 0) (hf3 : f3 ≤ 0) (hf : f1 < 0 ∨ f3 < 0)
    (hy : (a1 + a3) * (κ * s) = a1 * a2 * q01 + a1 * a4 * q03 + a3 * a2 * q21 + a3 * a4 * q23)
    (y01 : q01 ≤ 0) (y03 : q03 ≤ 0) (y21 : q21 ≤ 0) (y23 : q23 ≤ 0) : s ≤ 0 := by
  have p14 : 0 < a1 * a4 := h1
  have p12 : 0 < a1 * a2 := by nlinarith
  have p32 : 0 < a3 * a2 := h3
  have p34 : 0 < a3 * a4 := by nlinarith
  have hrhs : a1 * a2 * q01 + a1 * a4 * q03 + a3 * a2 * q21 + a3 * a4 * q23 ≤ 0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos p12.le y01, mul_nonpos_of_nonneg_of_nonpos p14.le y03,
      mul_nonpos_of_nonneg_of_nonpos p32.le y21, mul_nonpos_of_nonneg_of_nonpos p34.le y23]
  have hS : 0 < (a1 + a3) * κ := by
    have hpos : 0 < (a1 + a3) * (κ * nu) := by
      have e : (a1 + a3) * (κ * nu) = -(a1 + a3) * (a2 * f1 + a4 * f3) := by
        rw [hNV]; ring
      rw [e]
      rcases lt_or_gt_of_ne (show a1 ≠ 0 by rintro h; rw [h] at h1; simp at h1) with hneg | hposi
      · have a4n : a4 < 0 := by nlinarith
        have a3n : a3 < 0 := by nlinarith
        have a2n : a2 < 0 := by nlinarith
        rcases hf with h | h <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos a2n.le hf1,
          mul_nonneg_of_nonpos_of_nonpos a4n.le hf3, mul_pos_of_neg_of_neg a2n h,
          mul_pos_of_neg_of_neg a4n h]
      · have a4n : 0 < a4 := by nlinarith
        have a3n : 0 < a3 := by nlinarith
        have a2n : 0 < a2 := by nlinarith
        rcases hf with h | h <;> nlinarith [mul_nonneg a2n.le (neg_nonneg.mpr hf1),
          mul_nonneg a4n.le (neg_nonneg.mpr hf3), mul_pos a2n (neg_pos.mpr h),
          mul_pos a4n (neg_pos.mpr h)]
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hnu.le]
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hS hc]

theorem fd_vec (a1 a2 a3 a4 : ℝ) (P0 P1 P2 P3 : ℝ³) (hs : a1 + a3 = a2 + a4) :
    (a1 + a3) • (a1 • P0 - a2 • P1 + a3 • P2 - a4 • P3) =
      (a1 * a2) • (P0 - P1) + (a1 * a4) • (P0 - P3) + (a3 * a2) • (P2 - P1)
        + (a3 * a4) • (P2 - P3) := by
  ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (a1 * P0 i + a3 * P2 i) * hs

theorem fd_vec2 (a1 a2 a3 a4 : ℝ) (P0 P1 P2 P3 : ℝ³) (hs : a1 - a2 + a3 - a4 = 0) :
    a1 • P0 - a2 • P1 + a3 • P2 - a4 • P3 =
        (-a2) • (P1 - P0) + a3 • (P2 - P0) + (-a4) • (P3 - P0) := by
  ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (P0 i) * hs

/-- **Farkas core of Lemma FD**: four points whose shadows along `u` form a convex quadrilateral
(the tests `S_012, S_013, S_023, S_123` of one sign) and a functional `N` with `N u > 0` vanishing
on `P0, P2`, nonpositive (one strictly negative) on `P1, P3`: `u` is a nonnegative combination of
`P_i - P_j` (`i` even, `j` odd), so any `y` making the four forms nonpositive has `u . y <= 0`. -/
theorem fd_cone {P0 P1 P2 P3 u N y : ℝ³} (hu : u ≠ 0)
    (h4 : 0 < det3 (P1 - P0) (P2 - P0) u * det3 (P1 - P0) (P3 - P0) u)
    (h1 : 0 < det3 (P2 - P1) (P3 - P1) u * det3 (P1 - P0) (P2 - P0) u)
    (h2 : 0 < det3 (P2 - P0) (P3 - P0) u * det3 (P2 - P1) (P3 - P1) u)
    (h3 : 0 < det3 (P1 - P0) (P3 - P0) u * det3 (P2 - P0) (P3 - P0) u)
    (hN : 0 < ⟪N, u⟫) (hN2 : ⟪N, P2 - P0⟫ = 0) (hN1 : ⟪N, P1 - P0⟫ ≤ 0) (hN3 : ⟪N, P3 - P0⟫ ≤ 0)
    (hN13 : ⟪N, P1 - P0⟫ < 0 ∨ ⟪N, P3 - P0⟫ < 0)
    (y01 : ⟪P0 - P1, y⟫ ≤ 0) (y03 : ⟪P0 - P3, y⟫ ≤ 0) (y21 : ⟪P2 - P1, y⟫ ≤ 0)
    (y23 : ⟪P2 - P3, y⟫ ≤ 0) : ⟪u, y⟫ ≤ 0 := by
  have hsum := four_point_sum P0 P1 P2 P3 u
  have hV := four_point_parallel P0 P1 P2 P3 u hu
  generalize det3 (P2 - P1) (P3 - P1) u = a1 at *
  generalize det3 (P2 - P0) (P3 - P0) u = a2 at *
  generalize det3 (P1 - P0) (P3 - P0) u = a3 at *
  generalize det3 (P1 - P0) (P2 - P0) u = a4 at *
  generalize hκ : ⟪a1 • P0 - a2 • P1 + a3 • P2 - a4 • P3, u⟫ / ⟪u, u⟫ = κ at hV
  have hNV : κ * ⟪N, u⟫ = -a2 * ⟪N, P1 - P0⟫ - a4 * ⟪N, P3 - P0⟫ := by
    have := congrArg (fun v => ⟪N, v⟫) (hV.symm.trans (fd_vec2 a1 a2 a3 a4 P0 P1 P2 P3 hsum))
    simp only [real_inner_smul_right, inner_add_right, hN2] at this
    linarith
  have hy : (a1 + a3) * (κ * ⟪u, y⟫) = a1 * a2 * ⟪P0 - P1, y⟫ + a1 * a4 * ⟪P0 - P3, y⟫
      + a3 * a2 * ⟪P2 - P1, y⟫ + a3 * a4 * ⟪P2 - P3, y⟫ := by
    have := congrArg (fun v => ⟪v, y⟫) (fd_vec a1 a2 a3 a4 P0 P1 P2 P3 (by linarith))
    rw [hV] at this
    simp only [real_inner_smul_left, inner_add_left] at this
    linarith
  exact fd_real h4 h1 h2 h3 hsum hN hNV hN1 hN3 hN13 hy y01 y03 y21 y23


section Glue
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Tests at one rim edge have one sign (from the up and down facets of the edge). -/
theorem edge_pos (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³}
    (hu : CellAt F U Dn u) (k j j' : ZMod 4) (hj : j ≠ k) (hj1 : j ≠ k + 1) (hj' : j' ≠ k)
    (hj1' : j' ≠ k + 1) :
    0 < det3 (x (c (k + 1)) - x (c k)) (x (c j) - x (c k)) u *
      det3 (x (c (k + 1)) - x (c k)) (x (c j') - x (c k)) u := by
  obtain ⟨a, ha, b, hb, hka, hkb, hk1a, hk1b, hrest⟩ := hcyc k
  have hk1 : k + 1 ≠ k := (by decide : ∀ k : ZMod 4, k + 1 ≠ k) k
  have hxc : ∀ i i', i ≠ i' → x (c i) ≠ x (c i') := fun i i' h e => h (hc (hx e))
  have hne : x (c (k + 1)) - x (c k) ≠ 0 := sub_ne_zero.mpr (hxc _ _ hk1)
  have f0a := F.zero a (c k) hka
  have f0b := F.zero b (c k) hkb
  have f1a := F.zero a (c (k + 1)) hk1a
  have f1b := F.zero b (c (k + 1)) hk1b
  have side : ∀ i, i ≠ k → i ≠ k + 1 →
      ⟪F.N a, x (c i) - x (c k)⟫ ≤ 0 ∧ ⟪F.N b, x (c i) - x (c k)⟫ ≤ 0 ∧
        (⟪F.N a, x (c i) - x (c k)⟫ < 0 ∨ ⟪F.N b, x (c i) - x (c k)⟫ < 0) := by
    intro i hi hi1
    rw [F.inner_sub, F.inner_sub, f0a, f0b]
    refine ⟨by simpa using F.le a (c i), by simpa using F.le b (c i), ?_⟩
    rcases hrest (c i) (fun h => hi (hc h)) (fun h => hi1 (hc h)) with h | h
    · left; simpa using F.neg a (c i) h
    · right; simpa using F.neg b (c i) h
  obtain ⟨s1, s2, s3⟩ := side j hj hj1
  obtain ⟨t1, t2, t3⟩ := side j' hj' hj1'
  refine fd_edge hne (hu.1 a ha) (hu.2 b hb) ?_ ?_ s1 s2 s3 t1 t2 t3
  · rw [F.inner_sub, f0a, f1a]; ring
  · rw [F.inner_sub, f0b, f1b]; ring

/-- **Lemma FD, open cell.** In the open cell of a rim `c` of four vertices whose diagonal `c 0, c 2`
lies on a facet `t` facing the view (`t` up), every `y` with all four diagonal forms
`<x (c i) - x (c j), y>` (`i` even, `j` odd) nonpositive has `<u, y> <= 0`. -/
theorem fd_open (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³}
    (hu : CellAt F U Dn u) {t : Fin m} (ht : t ∈ U) (h0 : c 0 ∈ S t) (h2 : c 2 ∈ S t)
    (h13 : c 1 ∉ S t ∨ c 3 ∉ S t) {y : ℝ³}
    (hy : ∀ p : ZMod 4 × ZMod 4, p ∈ diagPairs → ⟪x (c p.1) - x (c p.2), y⟫ ≤ 0) :
    ⟪u, y⟫ ≤ 0 := by
  have hNu := hu.1 t ht
  have hu0 : u ≠ 0 := by rintro rfl; simp at hNu
  have e := fun k j j' hj hj1 hj' hj1' => edge_pos F hx hc hcyc hu k j j' hj hj1 hj' hj1'
  have d1 : ∀ A B C : ℝ³, det3 (C - B) (A - B) u = det3 (B - A) (C - A) u := fun A B C => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have E0 := e 0 2 3 (by decide) (by decide) (by decide) (by decide)
  have E1 := e 1 3 0 (by decide) (by decide) (by decide) (by decide)
  have E2 := e 2 0 1 (by decide) (by decide) (by decide) (by decide)
  have E3 := e 3 1 2 (by decide) (by decide) (by decide) (by decide)
  have r01 : (0 : ZMod 4) + 1 = 1 := by decide
  have r11 : (1 : ZMod 4) + 1 = 2 := by decide
  have r21 : (2 : ZMod 4) + 1 = 3 := by decide
  have r31 : (3 : ZMod 4) + 1 = 0 := by decide
  rw [r01] at E0
  rw [r11] at E1
  rw [r21] at E2
  rw [r31] at E3
  have q01 : ⟪x (c 0) - x (c 1), y⟫ ≤ 0 := hy (0, 1) (by decide)
  have q03 : ⟪x (c 0) - x (c 3), y⟫ ≤ 0 := hy (0, 3) (by decide)
  have q21 : ⟪x (c 2) - x (c 1), y⟫ ≤ 0 := hy (2, 1) (by decide)
  have q23 : ⟪x (c 2) - x (c 3), y⟫ ≤ 0 := hy (2, 3) (by decide)
  have fN0 : ⟪F.N t, x (c 2) - x (c 0)⟫ = 0 := by rw [F.inner_sub, F.zero t _ h0, F.zero t _ h2]; ring
  have fN1 : ⟪F.N t, x (c 1) - x (c 0)⟫ = F.f t (x (c 1)) := by
    rw [F.inner_sub, F.zero t _ h0]; ring
  have fN3 : ⟪F.N t, x (c 3) - x (c 0)⟫ = F.f t (x (c 3)) := by
    rw [F.inner_sub, F.zero t _ h0]; ring
  have f1 := F.le t (c 1)
  have f3 := F.le t (c 3)
  have f13 : F.f t (x (c 1)) < 0 ∨ F.f t (x (c 3)) < 0 := by
    rcases h13 with h | h
    · left; exact F.neg t _ h
    · right; exact F.neg t _ h
  rw [← fN1, ← fN3] at f13
  rw [← fN1] at f1
  rw [← fN3] at f3
  have d2 : ∀ P0 P1 P3 : ℝ³, det3 (P0 - P3) (P1 - P3) u = det3 (P1 - P0) (P3 - P0) u := fun _ _ _ => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have d3 : ∀ P0 P2 P3 : ℝ³, det3 (P0 - P3) (P2 - P3) u = det3 (P2 - P0) (P3 - P0) u := fun _ _ _ => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  generalize hP0 : x (c 0) = P0 at *
  generalize hP1 : x (c 1) = P1 at *
  generalize hP2 : x (c 2) = P2 at *
  generalize hP3 : x (c 3) = P3 at *
  rw [d1 P0 P1 P2] at E1
  rw [d1 P0 P2 P3, d1 P1 P2 P3] at E2
  rw [d2 P0 P1 P3, d3 P0 P2 P3] at E3
  exact fd_cone hu0 E0 E1 E2 E3 hNu fN0 f1 f3 f13 q01 q03 q21 q23

/-- **Lemma FD** (front diagonal), metric-free.  Rim `c` of four vertices of a closed cell
(`a` in the open cell, `g` a nonzero point of the closed cell): if the diagonal `c 0, c 2` lies on
a facet `t` that faces the view (`t` up) and `c 1`, `c 3` are not both on `t`, then some diagonal
form `<x (c i) - x (c j), g>` (`i` even, `j` odd) is positive. -/
theorem front_diag (F : S0xFac m S x) (hx : Function.Injective x) {c : ZMod 4 → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a g : ℝ³}
    (ha : CellAt F U Dn a) (hg : CellLe F U Dn g) (hg0 : g ≠ 0) {t : Fin m} (ht : t ∈ U)
    (h0 : c 0 ∈ S t) (h2 : c 2 ∈ S t) (h13 : c 1 ∉ S t ∨ c 3 ∉ S t) :
    ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g⟫ := by
  by_contra hcon
  push Not at hcon
  have hG : 0 < ⟪g, g⟫ := real_inner_self_pos.mpr hg0
  have key : ∀ ε : ℝ, 0 < ε → ⟪g, g⟫ + ε * ⟪a, g⟫ ≤ 0 := by
    intro ε hε
    have hu : CellAt F U Dn (g + ε • a) := by
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [inner_add_right, real_inner_smul_right]
        nlinarith [hg.1 t ht, ha.1 t ht]
      · rw [inner_add_right, real_inner_smul_right]
        nlinarith [hg.2 t ht, ha.2 t ht]
    have := fd_open F hx hc hcyc hu ht h0 h2 h13 (y := g) hcon
    rw [inner_add_left, real_inner_smul_left] at this
    linarith
  have hpos : 0 < |⟪a, g⟫| + 1 := by positivity
  have := key (⟪g, g⟫ / (2 * (|⟪a, g⟫| + 1))) (by positivity)
  have h3 : ⟪g, g⟫ / (2 * (|⟪a, g⟫| + 1)) * ⟪a, g⟫ ≥ -(⟪g, g⟫ / 2) := by
    have h4 : -(|⟪a, g⟫|) ≤ ⟪a, g⟫ := neg_abs_le _
    have h5 : ⟪g, g⟫ / (2 * (|⟪a, g⟫| + 1)) * (|⟪a, g⟫| + 1) = ⟪g, g⟫ / 2 := by
      field_simp
    nlinarith [div_pos hG (by positivity : (0:ℝ) < 2 * (|⟪a, g⟫| + 1))]
  linarith
end Glue


section Cells
open Minimality.T24.SAT Minimality.T24.Cell0234

private theorem injc0234 : Function.Injective c0234 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
private theorem injc0536 : Function.Injective c0536 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- **Lemma FD on the cell 0234**: at every nonzero point of the closed cell some diagonal form of the
cycle `0 2 3 4` is positive (diagonal `0 3` lies on the front facet `0345`), for every metric. -/
theorem front_diag_0234 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    {a g : ℝ³} (ha : CellAt F U0234 Dn0234 a) (hg : CellLe F U0234 Dn0234 g) (hg0 : g ≠ 0) :
    ∃ p ∈ diagPairs, 0 < ⟪x (c0234 p.1) - x (c0234 p.2), g⟫ :=
  front_diag F hx injc0234 cyc0234 ha hg hg0 (t := 3) (by decide) (by decide) (by decide)
    (Or.inl (by decide))

/-- **Lemma FD on the cell 0536**: cycle `0 6 3 5`, diagonal `0 3` on the front facet `0345`. -/
theorem front_diag_0536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    {a g : ℝ³} (ha : CellAt F U0536 Dn0536 a) (hg : CellLe F U0536 Dn0536 g) (hg0 : g ≠ 0) :
    ∃ p ∈ diagPairs, 0 < ⟪x (c0536 p.1) - x (c0536 p.2), g⟫ :=
  front_diag F hx injc0536 cyc0536 ha hg hg0 (t := 3) (by decide) (by decide) (by decide)
    (Or.inl (by decide))

/-- **Q4 on 0234 from one negative form**: one point `g` of the closed cell with
`z0 < z2`, `z0 < z4`, `z3 < z2` or `z3 < z4` (`z = <x i, g>`) gives `IsRupert`; the positive form
comes from Lemma FD (`g' = g`). -/
theorem isRupert_q4_0234_of_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0234 Dn0234 a)
    (hg : CellLe F U0234 Dn0234 g)
    (hn : ⟪x 0, g⟫ < ⟪x 2, g⟫ ∨ ⟪x 0, g⟫ < ⟪x 4, g⟫ ∨ ⟪x 3, g⟫ < ⟪x 2, g⟫ ∨
      ⟪x 3, g⟫ < ⟪x 4, g⟫) :
    IsRupert (Finset.univ.image x) := by
  have hn' : ∃ p ∈ diagPairs, ⟪x (c0234 p.1) - x (c0234 p.2), g⟫ < 0 := by
    rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨p, -, hp⟩ := hn'
    simp at hp
  exact isRupert_of_cell0234 F hx ha hg hg hn' (front_diag_0234 F hx ha hg hg0)

/-- **Q4 on 0536 from one negative form** (cycle `0 6 3 5`): `z0 < z6`, `z0 < z5`, `z3 < z6` or
`z3 < z5` at one point of the closed cell. -/
theorem isRupert_q4_0536_of_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0536 Dn0536 a)
    (hg : CellLe F U0536 Dn0536 g)
    (hn : ⟪x 0, g⟫ < ⟪x 6, g⟫ ∨ ⟪x 0, g⟫ < ⟪x 5, g⟫ ∨ ⟪x 3, g⟫ < ⟪x 6, g⟫ ∨
      ⟪x 3, g⟫ < ⟪x 5, g⟫) :
    IsRupert (Finset.univ.image x) := by
  have hn' : ∃ p ∈ diagPairs, ⟪x (c0536 p.1) - x (c0536 p.2), g⟫ < 0 := by
    rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨p, -, hp⟩ := hn'
    simp at hp
  exact isRupert_of_cell0536 F hx ha hg hg hn' (front_diag_0536 F hx ha hg hg0)

/-- `isRupert_q4_0234_of_cevian` without `h3` (`z2 < z3`): only `z0 < z4` is needed. -/
theorem isRupert_q4_0234_of_cevian' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0234 Dn0234 a)
    (hg : CellLe F U0234 Dn0234 g) (h4 : ⟪x 0, g⟫ < ⟪x 4, g⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_q4_0234_of_neg F hx ha hg (Or.inr (Or.inl h4))

/-- `isRupert_q4_0536_of_cevian` without `h3` (`z6 < z3`): only `z0 < z5` is needed. -/
theorem isRupert_q4_0536_of_cevian' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0536 Dn0536 a)
    (hg : CellLe F U0536 Dn0536 g) (h4 : ⟪x 0, g⟫ < ⟪x 5, g⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_q4_0536_of_neg F hx ha hg (Or.inr (Or.inl h4))

end Cells

end Minimality.T24.FrontDiag
