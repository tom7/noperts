module

public import Minimality.FaceChordLeaf
public import Minimality.Quad05Leaf
public import Minimality.Type21Ridge

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.FaceChord

namespace Minimality.RimFromSigns

/-- **V1 (algebraic identity): ridge separation identity for two adjacent facets.**
Along a shared edge `x Q - x P` of facets `t` and `t'`, the projection
`det3 (x Q - x P) (y - x P) u` is proportional to `⟪F.N t', u⟫ * F.f t y - ⟪F.N t, u⟫ * F.f t' y`. -/
theorem det3_ridge_facets {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t t' : Fin nf) (P Q : Fin N) (hP : P ∈ S t ∧ P ∈ S t')
    (hQ : Q ∈ S t ∧ Q ∈ S t') (u : ℝ³) (hu_cross : cross u (x Q - x P) ≠ 0)
    (hl : ⟪F.N t', u⟫ • F.N t - ⟪F.N t, u⟫ • F.N t' ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y : ℝ³,
      det3 (x Q - x P) (y - x P) u = κ * (⟪F.N t', u⟫ * F.f t y - ⟪F.N t, u⟫ * F.f t' y) := by
  set e := x Q - x P
  set l := ⟪F.N t', u⟫ • F.N t - ⟪F.N t, u⟫ • F.N t'
  have he_cross : cross e u ≠ 0 := by
    intro h
    apply hu_cross
    rw [show cross u e = - cross e u by ext j; fin_cases j <;> simp [cross] <;> ring, h, neg_zero]
  have hNt_e : ⟪F.N t, e⟫ = 0 := by
    have := (F.hN t (x Q) (x P)).symm
    rw [F.zero t Q hQ.1, F.zero t P hP.1, sub_self] at this
    exact this
  have hNt'_e : ⟪F.N t', e⟫ = 0 := by
    have := (F.hN t' (x Q) (x P)).symm
    rw [F.zero t' Q hQ.2, F.zero t' P hP.2, sub_self] at this
    exact this
  have hle : ⟪l, e⟫ = 0 := by
    dsimp [l]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hNt_e, hNt'_e, mul_zero, mul_zero, sub_zero]
  have hlu : ⟪l, u⟫ = 0 := by
    dsimp [l]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hne : ⟪cross u e, e⟫ = 0 := inner_cross_right u e
  have hnu : ⟪cross u e, u⟫ = 0 := inner_cross_left u e
  have hcl : cross l (cross u e) = 0 := cross_eq_zero_of_perp2 hle hlu hne hnu he_cross
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, cross u e = κ • l := ⟨_, eq_smul_of_cross_eq_zero hl hcl⟩
  have hκ_ne : κ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact hu_cross hκ
  refine ⟨κ, hκ_ne, fun y => ?_⟩
  rw [det3_e_u, hκ, real_inner_smul_left]
  have h1 : ⟪F.N t, y - x P⟫ = F.f t y := by
    have := F.hN t y (x P)
    rw [F.zero t P hP.1, sub_zero] at this
    exact this.symm
  have h2 : ⟪F.N t', y - x P⟫ = F.f t' y := by
    have := F.hN t' y (x P)
    rw [F.zero t' P hP.2, sub_zero] at this
    exact this.symm
  dsimp [l]
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h1, h2]

/-- **V1 edge-on variant: chord edge separation identity for an edge-on facet.**
When facet `t` is edge-on (`⟪F.N t, u⟫ = 0`), its normal `F.N t` is orthogonal
to both `u` and `x Q - x P`. If `cross u (x Q - x P) ≠ 0` and `F.N t ≠ 0`,
then `det3 (x Q - x P) (y - x P) u` is proportional to `F.f t y`. -/
theorem det3_edgeOn_facet {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∈ S t)
    (u : ℝ³) (hnu : ⟪F.N t, u⟫ = 0) (hu_cross : cross u (x Q - x P) ≠ 0)
    (hN0 : F.N t ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y : ℝ³,
      det3 (x Q - x P) (y - x P) u = κ * F.f t y := by
  set e := x Q - x P
  have he_cross : cross e u ≠ 0 := by
    intro h
    apply hu_cross
    rw [show cross u e = - cross e u by ext j; fin_cases j <;> simp [cross] <;> ring, h, neg_zero]
  have hNt_e : ⟪F.N t, e⟫ = 0 := by
    have := (F.hN t (x Q) (x P)).symm
    rw [F.zero t Q hQ, F.zero t P hP, sub_self] at this
    exact this
  have hne : ⟪cross u e, e⟫ = 0 := inner_cross_right u e
  have hnu' : ⟪cross u e, u⟫ = 0 := inner_cross_left u e
  have hcl : cross (F.N t) (cross u e) = 0 := cross_eq_zero_of_perp2 hNt_e hnu hne hnu' he_cross
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, cross u e = κ • F.N t := ⟨_, eq_smul_of_cross_eq_zero hN0 hcl⟩
  have hκ_ne : κ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hκ
    exact hu_cross hκ
  refine ⟨κ, hκ_ne, fun y => ?_⟩
  rw [det3_e_u, hκ, real_inner_smul_left]
  have h1 : ⟪F.N t, y - x P⟫ = F.f t y := by
    have := F.hN t y (x P)
    rw [F.zero t P hP, sub_zero] at this
    exact this.symm
  rw [h1]

/-- **V1 sign corollary: uniform strict sign off the edge.**
Across a ridge edge `P → Q` between opposite-facing facets `t` (down) and `t'` (up),
every vertex `y` not on both facets has the exact same strict orientation sign. -/
theorem det3_sign_ridge {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t t' : Fin nf) (P Q : Fin N) (hP : P ∈ S t ∧ P ∈ S t')
    (hQ : Q ∈ S t ∧ Q ∈ S t') (u : ℝ³) (h_opp : ⟪F.N t, u⟫ < 0 ∧ 0 < ⟪F.N t', u⟫)
    (hu_cross : cross u (x Q - x P) ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y : Fin N, (y ∉ S t ∨ y ∉ S t') →
      0 < σ * det3 (x Q - x P) (x y - x P) u := by
  set l := ⟪F.N t', u⟫ • F.N t - ⟪F.N t, u⟫ • F.N t'
  by_cases hl : l = 0
  · refine ⟨1, one_ne_zero, fun y hy => ?_⟩
    have h1 : ⟪F.N t, x y - x P⟫ = F.f t (x y) := by
      have := F.hN t (x y) (x P)
      rw [F.zero t P hP.1, sub_zero] at this
      exact this.symm
    have h2 : ⟪F.N t', x y - x P⟫ = F.f t' (x y) := by
      have := F.hN t' (x y) (x P)
      rw [F.zero t' P hP.2, sub_zero] at this
      exact this.symm
    have h_inner : ⟪l, x y - x P⟫ = 0 := by rw [hl, inner_zero_left]
    have h_expand : ⟪l, x y - x P⟫ = ⟪F.N t', u⟫ * F.f t (x y) - ⟪F.N t, u⟫ * F.f t' (x y) := by
      dsimp [l]
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
    have hterm : ⟪F.N t', u⟫ * F.f t (x y) - ⟪F.N t, u⟫ * F.f t' (x y) < 0 := by
      rcases hy with hy | hy'
      · have hf : F.f t (x y) < 0 := F.neg t y hy
        have hf' : F.f t' (x y) ≤ 0 := F.le t' y
        nlinarith [h_opp.1, h_opp.2]
      · have hf : F.f t (x y) ≤ 0 := F.le t y
        have hf' : F.f t' (x y) < 0 := F.neg t' y hy'
        nlinarith [h_opp.1, h_opp.2]
    linarith [h_inner, h_expand]
  · obtain ⟨κ, hκ_ne, hκ_eq⟩ := det3_ridge_facets F t t' P Q hP hQ u hu_cross hl
    refine ⟨-κ, neg_ne_zero.mpr hκ_ne, fun y hy => ?_⟩
    rw [hκ_eq (x y)]
    have hterm : ⟪F.N t', u⟫ * F.f t (x y) - ⟪F.N t, u⟫ * F.f t' (x y) < 0 := by
      rcases hy with hy | hy'
      · have hf : F.f t (x y) < 0 := F.neg t y hy
        have hf' : F.f t' (x y) ≤ 0 := F.le t' y
        nlinarith [h_opp.1, h_opp.2]
      · have hf : F.f t (x y) ≤ 0 := F.le t y
        have hf' : F.f t' (x y) < 0 := F.neg t' y hy'
        nlinarith [h_opp.1, h_opp.2]
    have : (-κ) * (κ * (⟪F.N t', u⟫ * F.f t (x y) - ⟪F.N t, u⟫ * F.f t' (x y))) =
        - (κ ^ 2) * (⟪F.N t', u⟫ * F.f t (x y) - ⟪F.N t, u⟫ * F.f t' (x y)) := by ring
    rw [this]
    have hsq : 0 < κ ^ 2 := sq_pos_of_ne_zero hκ_ne
    nlinarith

/-- **V1 edge-on sign corollary: uniform strict sign off an edge-on facet.** -/
theorem det3_sign_edgeOn {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) (P Q : Fin N) (hP : P ∈ S t) (hQ : Q ∈ S t)
    (u : ℝ³) (hnu : ⟪F.N t, u⟫ = 0) (hu_cross : cross u (x Q - x P) ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ y : Fin N, y ∉ S t →
      0 < σ * det3 (x Q - x P) (x y - x P) u := by
  by_cases hN0 : F.N t = 0
  · refine ⟨1, one_ne_zero, fun y hy => ?_⟩
    have h1 := F.zero t P hP
    have h2 := F.neg t y hy
    have h_inner : ⟪F.N t, x y - x P⟫ = 0 := by rw [hN0, inner_zero_left]
    have := (F.hN t (x y) (x P)).symm
    rw [h1, sub_zero, h_inner] at this
    linarith
  · obtain ⟨κ, hκ_ne, hκ_eq⟩ := det3_edgeOn_facet F t P Q hP hQ u hnu hu_cross hN0
    refine ⟨-κ, neg_ne_zero.mpr hκ_ne, fun y hy => ?_⟩
    rw [hκ_eq (x y)]
    have hf : F.f t (x y) < 0 := F.neg t y hy
    have : (-κ) * (κ * F.f t (x y)) = - (κ ^ 2) * F.f t (x y) := by ring
    rw [this]
    have hsq : 0 < κ ^ 2 := sq_pos_of_ne_zero hκ_ne
    nlinarith

/-- Circular permutation identity for the projected area of a triangle. -/
theorem det3_cycle_triangle (A B C u : ℝ³) :
    det3 (B - A) (C - A) u = det3 (C - B) (A - B) u := by
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- If `a * d > 0` and `b * d > 0`, then `a` and `b` have the same sign: `0 < a * b`. -/
theorem sign_prod {a b d : ℝ} (ha : 0 < a * d) (hb : 0 < b * d) : 0 < a * b := by
  have hpos : 0 < (a * d) * (b * d) := mul_pos ha hb
  have hd : d ≠ 0 := by intro h; rw [h, mul_zero] at ha; exact lt_irrefl 0 ha
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have heq : (a * d) * (b * d) = d ^ 2 * (a * b) := by ring
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos hd2.le

/-- If `a` and `b` have the same sign (`0 < a * b`) and `0 < b * d`, then `0 < a * d`. -/
theorem sign_transfer {a b d : ℝ} (hab : 0 < a * b) (hbd : 0 < b * d) : 0 < a * d := by
  have hpos : 0 < (a * b) * (b * d) := mul_pos hab hbd
  have hb : b ≠ 0 := by intro h; rw [h, mul_zero] at hab; exact lt_irrefl 0 hab
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have heq : (a * b) * (b * d) = b ^ 2 * (a * d) := by ring
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos hb2.le

end Minimality.RimFromSigns

namespace Minimality.T24.RimFromSigns
open Minimality.T24.SAT Minimality.RimFromSigns

/-- **V2 (type 24, Lemma R): rim convexity and vertex 1 inside from sign pattern S*.**
At view `u` with facet 3 (`0345`) edge-on (`⟪F.N 3, u⟫ = 0`) and the sign pattern S*
(negative on facets 0, 1, 2, 4, 5; positive on facets 6, 7, 8), the quad rim `6 4 5 2`
is strictly convex (`hcyc`) and vertex 1 projects strictly inside (`h1`) for some `ρ ≠ 0`. -/
theorem lemmaR_quad_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN5 : ⟪F.N 5, u⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u⟫) (hN7 : 0 < ⟪F.N 7, u⟫) (hN8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
          (quad (x 6) (x 4) (x 5) (x 2) j - quad (x 6) (x 4) (x 5) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 5) (x 2) (i + 1) - quad (x 6) (x 4) (x 5) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 5) (x 2) i) u) := by
  have hne_64 : cross u (x 4 - x 6) ≠ 0 := by
    intro hcr
    have he : x 4 - x 6 ≠ 0 := by
      intro h
      have h1 : F.f 1 (x 6) = 0 := F.zero 1 6 (by decide)
      have h2 : F.f 1 (x 4) < 0 := F.neg 1 4 (by decide)
      have : x 4 = x 6 := sub_eq_zero.mp h
      rw [this, h1] at h2
      exact lt_irrefl 0 h2
    have hcr' : cross (x 4 - x 6) u = 0 := by
      rw [show cross (x 4 - x 6) u = - cross u (x 4 - x 6) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
    obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x 4 - x 6) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
    have hz : ⟪F.N 4, x 4 - x 6⟫ = 0 := by
      have := (F.hN 4 (x 4) (x 6)).symm
      rw [F.zero 4 4 (by decide), F.zero 4 6 (by decide), sub_self] at this
      exact this
    have h0 : ⟪F.N 4, u⟫ = 0 := by
      rw [hk, real_inner_smul_right, hz, mul_zero]
    linarith [hN4]

  have hne_52 : cross u (x 2 - x 5) ≠ 0 := by
    intro hcr
    have he : x 2 - x 5 ≠ 0 := by
      intro h
      have h1 : F.f 0 (x 2) = 0 := F.zero 0 2 (by decide)
      have h2 : F.f 0 (x 5) < 0 := F.neg 0 5 (by decide)
      have : x 5 = x 2 := (sub_eq_zero.mp h).symm
      rw [this, h1] at h2
      exact lt_irrefl 0 h2
    have hcr' : cross (x 2 - x 5) u = 0 := by
      rw [show cross (x 2 - x 5) u = - cross u (x 2 - x 5) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
    obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x 2 - x 5) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
    have hz : ⟪F.N 2, x 2 - x 5⟫ = 0 := by
      have := (F.hN 2 (x 2) (x 5)).symm
      rw [F.zero 2 2 (by decide), F.zero 2 5 (by decide), sub_self] at this
      exact this
    have h0 : ⟪F.N 2, u⟫ = 0 := by
      rw [hk, real_inner_smul_right, hz, mul_zero]
    linarith [hN2]

  have hne_26 : cross u (x 6 - x 2) ≠ 0 := by
    intro hcr
    have he : x 6 - x 2 ≠ 0 := by
      intro h
      have h1 : F.f 0 (x 2) = 0 := F.zero 0 2 (by decide)
      have h2 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
      have : x 6 = x 2 := sub_eq_zero.mp h
      rw [this, h1] at h2
      exact lt_irrefl 0 h2
    have hcr' : cross (x 6 - x 2) u = 0 := by
      rw [show cross (x 6 - x 2) u = - cross u (x 6 - x 2) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
    obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x 6 - x 2) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
    have hz : ⟪F.N 5, x 6 - x 2⟫ = 0 := by
      have := (F.hN 5 (x 6) (x 2)).symm
      rw [F.zero 5 6 (by decide), F.zero 5 2 (by decide), sub_self] at this
      exact this
    have h0 : ⟪F.N 5, u⟫ = 0 := by
      rw [hk, real_inner_smul_right, hz, mul_zero]
    linarith [hN5]

  have hne_45 : cross u (x 5 - x 4) ≠ 0 := by
    intro hcr
    have he : x 5 - x 4 ≠ 0 := by
      intro h
      have h1 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
      have h2 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
      have : x 4 = x 5 := (sub_eq_zero.mp h).symm
      rw [this, h1] at h2
      exact lt_irrefl 0 h2
    have hcr' : cross (x 5 - x 4) u = 0 := by
      rw [show cross (x 5 - x 4) u = - cross u (x 5 - x 4) by ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
    obtain ⟨k, hk⟩ : ∃ k : ℝ, u = k • (x 5 - x 4) := ⟨_, eq_smul_of_cross_eq_zero he hcr'⟩
    have hf2 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
    have hf6 : F.f 6 (x 4) < 0 := F.neg 6 4 (by decide)
    have h2 : ⟪F.N 2, u⟫ = - k * F.f 2 (x 4) := by
      rw [hk, real_inner_smul_right]
      have hN2_sub : ⟪F.N 2, x 5 - x 4⟫ = - F.f 2 (x 4) := by
        have := (F.hN 2 (x 5) (x 4)).symm
        rw [F.zero 2 5 (by decide)] at this
        linarith
      rw [hN2_sub]
      ring
    have h6 : ⟪F.N 6, u⟫ = - k * F.f 6 (x 4) := by
      rw [hk, real_inner_smul_right]
      have hN6_sub : ⟪F.N 6, x 5 - x 4⟫ = - F.f 6 (x 4) := by
        have := (F.hN 6 (x 5) (x 4)).symm
        rw [F.zero 6 5 (by decide)] at this
        linarith
      rw [hN6_sub]
      ring
    have hk_neg : k < 0 := by
      rw [h2] at hN2
      nlinarith
    have hk_pos : 0 < k := by
      rw [h6] at hN6
      nlinarith
    linarith

  obtain ⟨σ₀, hσ₀_ne, hσ₀⟩ := det3_sign_ridge F 4 8 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN4, hN8⟩ hne_64
  obtain ⟨σ₁, hσ₁_ne, hσ₁⟩ := det3_sign_edgeOn F 3 4 5 (by decide) (by decide) u hN3 hne_45
  obtain ⟨σ₂, hσ₂_ne, hσ₂⟩ := det3_sign_ridge F 2 6 5 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN2, hN6⟩ hne_52
  obtain ⟨σ₃, hσ₃_ne, hσ₃⟩ := det3_sign_ridge F 5 7 2 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN5, hN7⟩ hne_26

  have hcyc01 : det3 (x 4 - x 6) (x 5 - x 6) u = det3 (x 5 - x 4) (x 6 - x 4) u :=
    det3_cycle_triangle (x 6) (x 4) (x 5) u
  have hcyc12 : det3 (x 5 - x 4) (x 2 - x 4) u = det3 (x 2 - x 5) (x 4 - x 5) u :=
    det3_cycle_triangle (x 4) (x 5) (x 2) u
  have hcyc23 : det3 (x 2 - x 5) (x 6 - x 5) u = det3 (x 6 - x 2) (x 5 - x 2) u :=
    det3_cycle_triangle (x 5) (x 2) (x 6) u

  have h0_5 : 0 < σ₀ * det3 (x 4 - x 6) (x 5 - x 6) u := hσ₀ 5 (Or.inl (by decide))
  have h1_6 : 0 < σ₁ * det3 (x 5 - x 4) (x 6 - x 4) u := hσ₁ 6 (by decide)
  have h1_6' : 0 < σ₁ * det3 (x 4 - x 6) (x 5 - x 6) u := by rw [hcyc01]; exact h1_6
  have hσ01 : 0 < σ₀ * σ₁ := sign_prod h0_5 h1_6'

  have h1_2 : 0 < σ₁ * det3 (x 5 - x 4) (x 2 - x 4) u := hσ₁ 2 (by decide)
  have h2_4 : 0 < σ₂ * det3 (x 2 - x 5) (x 4 - x 5) u := hσ₂ 4 (Or.inl (by decide))
  have h2_4' : 0 < σ₂ * det3 (x 5 - x 4) (x 2 - x 4) u := by rw [hcyc12]; exact h2_4
  have hσ12 : 0 < σ₁ * σ₂ := sign_prod h1_2 h2_4'
  have hσ02 : 0 < σ₀ * σ₂ := sign_transfer hσ01 hσ12

  have h2_6 : 0 < σ₂ * det3 (x 2 - x 5) (x 6 - x 5) u := hσ₂ 6 (Or.inl (by decide))
  have h3_5 : 0 < σ₃ * det3 (x 6 - x 2) (x 5 - x 2) u := hσ₃ 5 (Or.inl (by decide))
  have h3_5' : 0 < σ₃ * det3 (x 2 - x 5) (x 6 - x 5) u := by rw [hcyc23]; exact h3_5
  have hσ23 : 0 < σ₂ * σ₃ := sign_prod h2_6 h3_5'
  have hσ03 : 0 < σ₀ * σ₃ := sign_transfer hσ02 hσ23

  have h0_2 : 0 < σ₀ * det3 (x 4 - x 6) (x 2 - x 6) u := hσ₀ 2 (Or.inl (by decide))
  have h0_1 : 0 < σ₀ * det3 (x 4 - x 6) (x 1 - x 6) u := hσ₀ 1 (Or.inl (by decide))

  have h1_1 : 0 < σ₁ * det3 (x 5 - x 4) (x 1 - x 4) u := hσ₁ 1 (by decide)

  have h2_1 : 0 < σ₂ * det3 (x 2 - x 5) (x 1 - x 5) u := hσ₂ 1 (Or.inl (by decide))

  have h3_4 : 0 < σ₃ * det3 (x 6 - x 2) (x 4 - x 2) u := hσ₃ 4 (Or.inl (by decide))
  have h3_1 : 0 < σ₃ * det3 (x 6 - x 2) (x 1 - x 2) u := hσ₃ 1 (Or.inr (by decide))

  refine ⟨σ₀, hσ₀_ne, ?_, ?_⟩
  · intro i j hj1 hj2
    fin_cases i <;> fin_cases j
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact h0_5
    · exact h0_2
    · exact sign_transfer hσ01 h1_6
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ01 h1_2
    · exact sign_transfer hσ02 h2_6
    · exact sign_transfer hσ02 h2_4
    · exact False.elim (hj1 rfl)
    · exact False.elim (hj2 rfl)
    · exact False.elim (hj2 rfl)
    · exact sign_transfer hσ03 h3_4
    · exact sign_transfer hσ03 h3_5
    · exact False.elim (hj1 rfl)
  · intro i
    fin_cases i
    · exact h0_1
    · exact sign_transfer hσ01 h1_1
    · exact sign_transfer hσ02 h2_1
    · exact sign_transfer hσ03 h3_1

end Minimality.T24.RimFromSigns
