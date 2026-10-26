module

public import Minimality.Type29Facets
public import Minimality.Classify

@[expose] public section

/-!
# Type 29: from the face list to the octahedron with its cap

`type29_cap`: seven points in convex position realizing the faces of type 29
(`sevenTypeFaces 28`: `012, 015, 023, 035, 124, 1456, 234, 346, 356`) give the octahedron
`O = K − 6` with its facet functions (`OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5)`, faces
`012, 015, 023, 035, 124, 145, 234, 345`) and the cap `6` (`IsCap29`), the input of the normal
form `IsCap29.toNF29` and of the class theorems.

Seven of the eight facet functions are those of `K` (for `145`, that of the quadrilateral
`1456`, which vanishes at `6`). The face `345` of `O` is not a face of `K`: its function is
`−ψ(1) ψ`, `ψ = det4 (3, 4, 5, ·)`, and the signs of `ψ` come from orientation determinants
(`Classify.D`):
* `0` and `6` are on opposite sides of `345`: the faces `035` and `356` of `K` meet at the edge
  `35`, and `4` lies in their wedge (`psi06`); likewise `2` and `6` at the edge `34` with the
  faces `234`, `346` (`psi26`);
* `1` and `6` are on opposite sides of `345`: in the plane of `1456`, `6 = λ₁ 1 + λ₄ 4 + λ₅ 5`
  (Cramer) with `λ₄, λ₅ > 0` (Grassmann–Plücker at the edges `15`, `14` with the faces `015`,
  `124`), so `λ₁ ≥ 0` would put `6` in the triangle `145`, against convex position (`psi16`).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset Classify

/-! ### Facet functions and determinants -/

/-- An affine function vanishing at three non-collinear labelled points is a multiple of their
orientation determinant. -/
theorem facet_mul_det {x : Fin 7 → ℝ³} (φ : ℝ³ →ᵃ[ℝ] ℝ) {a b c : Fin 7} (ha : φ (x a) = 0)
    (hb : φ (x b) = 0) (hc : φ (x c) = 0) (hn : cross (x b - x a) (x c - x a) ≠ 0) :
    ∃ m κ : ℝ, 0 < m ∧ ∀ z, φ (x z) * m = κ * D x a b c z := by
  obtain ⟨L, hL⟩ := exists_normal_of_affine φ
  set n := cross (x b - x a) (x c - x a) with hndef
  refine ⟨⟪n, n⟫, ⟪L, n⟫, real_inner_self_pos.mpr hn, fun z => ?_⟩
  have hu : ⟪L, x b - x a⟫ = 0 := by rw [← hL, hb, ha, sub_zero]
  have hv : ⟪L, x c - x a⟫ = 0 := by rw [← hL, hc, ha, sub_zero]
  have hz : φ (x z) = ⟪L, x z - x a⟫ := by rw [← hL, ha, sub_zero]
  have := lagrange L (x b - x a) (x c - x a) (x z - x a)
  rw [hu, hv, zero_mul, zero_mul, sub_zero] at this
  rw [hz, D, det4, ← hndef]
  linarith

/-- Two points beneath a facet have orientation determinants of one sign with its triple. -/
theorem facet_same_sign {x : Fin 7 → ℝ³} (φ : ℝ³ →ᵃ[ℝ] ℝ) {a b c : Fin 7} (ha : φ (x a) = 0)
    (hb : φ (x b) = 0) (hc : φ (x c) = 0) (hn : cross (x b - x a) (x c - x a) ≠ 0) {z w : Fin 7}
    (hz : φ (x z) < 0) (hw : φ (x w) < 0) : 0 < D x a b c z * D x a b c w := by
  obtain ⟨m, κ, hm, h⟩ := facet_mul_det φ ha hb hc hn
  have hpos : 0 < (κ * D x a b c z) * (κ * D x a b c w) := by
    rw [← h z, ← h w]
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hz hm) (mul_neg_of_neg_of_pos hw hm)
  have e : (κ * D x a b c z) * (κ * D x a b c w) = κ ^ 2 * (D x a b c z * D x a b c w) := by ring
  by_contra hle
  push Not at hle
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) hle]

/-- A point on a facet (beneath which some point lies) is coplanar with its triple. -/
theorem facet_det_zero {x : Fin 7 → ℝ³} (φ : ℝ³ →ᵃ[ℝ] ℝ) {a b c : Fin 7} (ha : φ (x a) = 0)
    (hb : φ (x b) = 0) (hc : φ (x c) = 0) (hn : cross (x b - x a) (x c - x a) ≠ 0) {z w : Fin 7}
    (hz : φ (x z) = 0) (hw : φ (x w) < 0) : D x a b c z = 0 := by
  obtain ⟨m, κ, hm, h⟩ := facet_mul_det φ ha hb hc hn
  have h1 := h z
  rw [hz, zero_mul] at h1
  have hκ : κ ≠ 0 := by
    intro h0
    have h2 := h w
    rw [h0, zero_mul] at h2
    nlinarith
  exact (mul_eq_zero.mp h1.symm).resolve_left hκ

/-- A point beneath a facet is off the plane of its triple. -/
theorem facet_det_ne {x : Fin 7 → ℝ³} (φ : ℝ³ →ᵃ[ℝ] ℝ) {a b c : Fin 7} (ha : φ (x a) = 0)
    (hb : φ (x b) = 0) (hc : φ (x c) = 0) (hn : cross (x b - x a) (x c - x a) ≠ 0) {w : Fin 7}
    (hw : φ (x w) < 0) : D x a b c w ≠ 0 := by
  have := facet_same_sign φ ha hb hc hn hw hw
  intro h0
  rw [h0, zero_mul] at this
  exact lt_irrefl _ this

/-- In convex position no three labelled points are collinear. -/
theorem cross_ne_of_hvert {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hvert : ∀ v ∈ univ.image x, v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³))
    {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cross (x b - x a) (x c - x a) ≠ 0 := by
  intro h0
  have hba : x b - x a ≠ 0 := sub_ne_zero.mpr (hx.ne hab.symm)
  obtain ⟨p, hp, hph⟩ := exists_mem_convexHull_erase_of_collinear (img29 a) (img29 b) (img29 c)
    (hx.ne hab) (hx.ne hac) (hx.ne hbc) (eq_smul_of_cross_eq_zero hba h0)
  exact hvert p hp hph

/-- The facet function of `O = K − 6` given by a face `f` of `K` through `p, q, r`. -/
noncomputable def facetFnK {x : Fin 7 → ℝ³} (φ : ℝ³ →ᵃ[ℝ] ℝ) (f : Finset (Fin 7))
    (hφ : ∀ i, (i ∈ f → φ (x i) = 0) ∧ (i ∉ f → φ (x i) < 0)) (p q r : Fin 7) (hp : p ∈ f)
    (hq : q ∈ f) (hr : r ∈ f) (hO : ∀ j : Fin 7, j ≠ 6 → j ∉ f ∨ j = p ∨ j = q ∨ j = r) :
    FacetFn {x 0, x 4, x 1, x 3, x 2, x 5} (x p) (x q) (x r) where
  f := φ
  N := Classical.choose (exists_normal_of_affine φ)
  hN := Classical.choose_spec (exists_normal_of_affine φ)
  hP := (hφ p).1 hp
  hQ := (hφ q).1 hq
  hR := (hφ r).1 hr
  neg w hw h1 h2 h3 := by
    have key : ∀ j : Fin 7, j ≠ 6 → w = x j → φ w < 0 := by
      rintro j hj rfl
      rcases hO j hj with h | rfl | rfl | rfl
      · exact (hφ j).2 h
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h | h | h | h | h
    · exact key 0 (by decide) h
    · exact key 4 (by decide) h
    · exact key 1 (by decide) h
    · exact key 3 (by decide) h
    · exact key 2 (by decide) h
    · exact key 5 (by decide) h

/-- The facet function `c · det4 (3, 4, 5, ·)` of the face `345` of `O`. -/
noncomputable def facetFn345 {x : Fin 7 → ℝ³} (c : ℝ) (h0 : c * D x 3 4 5 0 < 0)
    (h1 : c * D x 3 4 5 1 < 0) (h2 : c * D x 3 4 5 2 < 0) :
    FacetFn {x 0, x 4, x 1, x 3, x 2, x 5} (x 4) (x 3) (x 5) where
  f z := c * det4 (x 3) (x 4) (x 5) z
  N := c • cross (x 4 - x 3) (x 5 - x 3)
  hN y z := by
    simp only [det4, real_inner_smul_left, ← mul_sub, ← inner_sub_right]
    congr 2
    abel
  hP := by rw [det4_eq]; ring
  hQ := by rw [det4_eq]; ring
  hR := by rw [det4_eq]; ring
  neg w hw h4 h3 h5 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | h | rfl | h | rfl | h
    · exact h0
    · exact absurd h h4
    · exact h1
    · exact absurd h h3
    · exact h2
    · exact absurd h h5

/-! ### The signs of `345` -/

/-- Each of `0, 2` lies on the other side of `345` than `6`, at an edge `35` (`34`) of `K`
whose two faces contain them. -/
theorem psi_edge {u v w1 w2 p q : ℝ} (huv : 0 < u * v) (hw : 0 < w1 * w2)
    (e : v = -w1) (hp : p = u) (hq : q = w2) : p * q < 0 := by
  rw [hp, hq]
  rw [e] at huv
  have h1 : 0 < (u * -w1) * (w1 * w2) := mul_pos huv hw
  have h2 : (u * -w1) * (w1 * w2) = -(u * w2) * (w1 * w1) := by ring
  rw [h2] at h1
  by_contra hle
  push Not at hle
  nlinarith [mul_self_nonneg w1]

/-- Two points on the other side than a third are on one side. -/
theorem same_side {a b c : ℝ} (h1 : a * c < 0) (h2 : b * c < 0) : -b * a < 0 := by
  have h := mul_pos_of_neg_of_neg h1 h2
  have e : (a * c) * (b * c) = (b * a) * c ^ 2 := by ring
  rw [e] at h
  by_contra hle
  push Not at hle
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : b * a ≤ 0) (sq_nonneg c)]

/-- **The cap and the octahedron of type 29.** Seven points in convex position realizing the
faces of type 29 give the facet functions of `O = K − 6` and the cap `6` beyond `345`. -/
theorem type29_cap {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hvert : ∀ v ∈ univ.image x, v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³))
    (hR : RealizesFaces x (sevenTypeFaces 28)) :
    ∃ F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5), IsCap29 F (x 6) := by
  have nc : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c → cross (x b - x a) (x c - x a) ≠ 0 :=
    fun a b c hab hac hbc => cross_ne_of_hvert hx hvert hab hac hbc
  obtain ⟨φ012, h012⟩ := hR {0, 1, 2} (by decide)
  obtain ⟨φ015, h015⟩ := hR {0, 1, 5} (by decide)
  obtain ⟨φ023, h023⟩ := hR {0, 2, 3} (by decide)
  obtain ⟨φ035, h035⟩ := hR {0, 3, 5} (by decide)
  obtain ⟨φ124, h124⟩ := hR {1, 2, 4} (by decide)
  obtain ⟨φQ, hQ⟩ := hR {1, 4, 5, 6} (by decide)
  obtain ⟨φ234, h234⟩ := hR {2, 3, 4} (by decide)
  obtain ⟨φ346, h346⟩ := hR {3, 4, 6} (by decide)
  obtain ⟨φ356, h356⟩ := hR {3, 5, 6} (by decide)
  -- `0, 6` and `2, 6` on opposite sides of `345`
  have s035 := facet_same_sign φ035 ((h035 0).1 (by decide)) ((h035 3).1 (by decide))
    ((h035 5).1 (by decide)) (nc 0 3 5 (by decide) (by decide) (by decide))
    (z := 4) (w := 6) ((h035 4).2 (by decide)) ((h035 6).2 (by decide))
  have s356 := facet_same_sign φ356 ((h356 3).1 (by decide)) ((h356 5).1 (by decide))
    ((h356 6).1 (by decide)) (nc 3 5 6 (by decide) (by decide) (by decide))
    (z := 0) (w := 4) ((h356 0).2 (by decide)) ((h356 4).2 (by decide))
  have s234 := facet_same_sign φ234 ((h234 2).1 (by decide)) ((h234 3).1 (by decide))
    ((h234 4).1 (by decide)) (nc 2 3 4 (by decide) (by decide) (by decide))
    (z := 5) (w := 6) ((h234 5).2 (by decide)) ((h234 6).2 (by decide))
  have s346 := facet_same_sign φ346 ((h346 3).1 (by decide)) ((h346 4).1 (by decide))
    ((h346 6).1 (by decide)) (nc 3 4 6 (by decide) (by decide) (by decide))
    (z := 2) (w := 5) ((h346 2).2 (by decide)) ((h346 5).2 (by decide))
  have psi06 : D x 3 4 5 0 * D x 3 4 5 6 < 0 :=
    psi_edge s035 s356 (by simp only [D, det4_eq]; ring) (by simp only [D, det4_eq]; ring)
      (by simp only [D, det4_eq]; ring)
  have psi26 : D x 3 4 5 2 * D x 3 4 5 6 < 0 := by
    have := psi_edge (p := -D x 3 4 5 2) (q := -D x 3 4 5 6) s234 s346
      (by simp only [D, det4_eq]; ring) (by simp only [D, det4_eq]; ring)
      (by simp only [D, det4_eq]; ring)
    linarith
  -- `1, 6` on opposite sides of `345`: `6` in the plane of `145`, beyond the edge `45`
  have n145 := nc 1 4 5 (by decide) (by decide) (by decide)
  have z1456 : D x 1 4 5 6 = 0 := facet_det_zero φQ ((hQ 1).1 (by decide)) ((hQ 4).1 (by decide))
    ((hQ 5).1 (by decide)) n145 (z := 6) (w := 3) ((hQ 6).1 (by decide)) ((hQ 3).2 (by decide))
  have d1453 : D x 1 4 5 3 ≠ 0 := facet_det_ne φQ ((hQ 1).1 (by decide)) ((hQ 4).1 (by decide))
    ((hQ 5).1 (by decide)) n145 ((hQ 3).2 (by decide))
  have s124 := facet_same_sign φ124 ((h124 1).1 (by decide)) ((h124 2).1 (by decide))
    ((h124 4).1 (by decide)) (nc 1 2 4 (by decide) (by decide) (by decide))
    (z := 5) (w := 6) ((h124 5).2 (by decide)) ((h124 6).2 (by decide))
  have s015 := facet_same_sign φ015 ((h015 0).1 (by decide)) ((h015 1).1 (by decide))
    ((h015 5).1 (by decide)) (nc 0 1 5 (by decide) (by decide) (by decide))
    (z := 4) (w := 6) ((h015 4).2 (by decide)) ((h015 6).2 (by decide))
  have gp14 := det4_gp x 1 4 2 3 5 6
  have gp15 := det4_gp x 1 5 0 3 4 6
  -- the barycentric weights of `6` in the triangle `145`
  set D0 := D x 1 4 5 3 with hD0
  have l4 : 0 < D x 1 6 5 3 * D0 := by
    have e1 : D x 1 6 5 3 = D x 1 5 3 6 := by simp only [D, det4_eq]; ring
    have e2 : D0 = D x 1 5 3 4 := by simp only [hD0, D, det4_eq]; ring
    have e3 : D x 1 5 4 6 = -D x 1 4 5 6 := by simp only [D, det4_eq]; ring
    have e4 : D x 1 5 0 4 = D x 0 1 5 4 := by simp only [D, det4_eq]; ring
    have e5 : D x 1 5 0 6 = D x 0 1 5 6 := by simp only [D, det4_eq]; ring
    rw [e3, z1456, e4, e5] at gp15
    rw [e1, e2]
    rw [e2] at d1453
    -- `[1504][1536] = [1506][1534]` with `[1504][1506] > 0`
    have hr : D x 0 1 5 4 * D x 1 5 3 6 = D x 0 1 5 6 * D x 1 5 3 4 := by linarith
    have hq : 0 < (D x 1 5 3 6 * D x 1 5 3 4) * (D x 0 1 5 4 * D x 0 1 5 6) := by
      have : (D x 1 5 3 6 * D x 1 5 3 4) * (D x 0 1 5 4 * D x 0 1 5 6) =
          (D x 0 1 5 6 * D x 1 5 3 4) ^ 2 := by
        linear_combination (D x 1 5 3 4 * D x 0 1 5 6) * hr
      rw [this]
      have : D x 0 1 5 6 ≠ 0 := by
        intro h; rw [h, mul_zero] at s015; exact lt_irrefl _ s015
      positivity
    exact pos_of_mul_pos_left hq s015.le
  have l5 : 0 < D x 1 4 6 3 * D0 := by
    have e1 : D x 1 4 6 3 = -D x 1 4 3 6 := by simp only [D, det4_eq]; ring
    have e2 : D0 = -D x 1 4 3 5 := by simp only [hD0, D, det4_eq]; ring
    have e4 : D x 1 4 2 5 = -D x 1 2 4 5 := by simp only [D, det4_eq]; ring
    have e5 : D x 1 4 2 6 = -D x 1 2 4 6 := by simp only [D, det4_eq]; ring
    rw [z1456, e4, e5] at gp14
    rw [e1, e2]
    rw [e2] at d1453
    have hr : D x 1 2 4 5 * D x 1 4 3 6 = D x 1 2 4 6 * D x 1 4 3 5 := by linarith
    have hq : 0 < (D x 1 4 3 6 * D x 1 4 3 5) * (D x 1 2 4 5 * D x 1 2 4 6) := by
      have : (D x 1 4 3 6 * D x 1 4 3 5) * (D x 1 2 4 5 * D x 1 2 4 6) =
          (D x 1 2 4 6 * D x 1 4 3 5) ^ 2 := by
        linear_combination (D x 1 4 3 5 * D x 1 2 4 6) * hr
      rw [this]
      have : D x 1 2 4 6 ≠ 0 := by
        intro h; rw [h, mul_zero] at s124; exact lt_irrefl _ s124
      have : D x 1 4 3 5 ≠ 0 := fun h => d1453 (by rw [h, neg_zero])
      positivity
    have := pos_of_mul_pos_left hq s124.le
    linarith
  have psi16 : D x 3 4 5 1 * D x 3 4 5 6 < 0 := by
    have e1 : D x 3 4 5 1 * D x 3 4 5 6 = D x 6 4 5 3 * D0 := by
      simp only [hD0, D, det4_eq]; ring
    rw [e1]
    by_contra hle
    push Not at hle
    -- then `6` is in the triangle `145`
    have hsum := det4_sum x 6 1 4 5 3
    rw [z1456, add_zero] at hsum
    have hD0' : D0 ≠ 0 := d1453
    have hw : ∀ u : ℝ, 0 ≤ u * D0 → 0 ≤ u / D0 := fun u hu => by
      have : u / D0 = u * D0 / (D0 * D0) := by field_simp
      rw [this]; exact div_nonneg hu (mul_self_nonneg D0)
    apply hvert (x 6) (img29 6)
    have hpt : x 6 = ∑ i : Fin 3, (![D x 6 4 5 3 / D0, D x 1 6 5 3 / D0, D x 1 4 6 3 / D0] i) •
        (![x 1, x 4, x 5] i) := by
      ext k
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      have hc := det4_cramer x 6 1 4 5 3 k
      rw [z1456, zero_mul, add_zero] at hc
      field_simp
      linarith
    have hmem : ∑ i : Fin 3, (![D x 6 4 5 3 / D0, D x 1 6 5 3 / D0, D x 1 4 6 3 / D0] i) •
        (![x 1, x 4, x 5] i) ∈ convexHull ℝ (((univ.image x).erase (x 6) : Finset ℝ³) : Set ℝ³) := ?_
    · rwa [← hpt] at hmem
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i
      · exact hw _ hle
      · exact hw _ l4.le
      · exact hw _ l5.le
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      linarith
    · apply subset_convexHull
      fin_cases i <;> simp [hx.eq_iff]
  have d1 : D x 3 4 5 1 ≠ 0 := by
    intro h; rw [h, zero_mul] at psi16; exact lt_irrefl _ psi16
  -- the facet function of `345`: `−ψ(1) ψ`
  have q0 : -D x 3 4 5 1 * D x 3 4 5 0 < 0 := same_side psi06 psi16
  have q1 : -D x 3 4 5 1 * D x 3 4 5 1 < 0 := by
    have := mul_self_pos.mpr d1; linarith
  have q2 : -D x 3 4 5 1 * D x 3 4 5 2 < 0 := same_side psi26 psi16
  let F : OctFacets (x 0) (x 4) (x 1) (x 3) (x 2) (x 5) :=
    { nodup := by
        have : [x 0, x 4, x 1, x 3, x 2, x 5] = [0, 4, 1, 3, 2, 5].map x := rfl
        rw [this]
        exact (List.nodup_map_iff hx).mpr (by decide)
      abc := facetFnK φ012 _ h012 0 1 2 (by decide) (by decide) (by decide) (by decide)
      abc' := facetFnK φ015 _ h015 0 1 5 (by decide) (by decide) (by decide) (by decide)
      ab'c := facetFnK φ023 _ h023 0 3 2 (by decide) (by decide) (by decide) (by decide)
      ab'c' := facetFnK φ035 _ h035 0 3 5 (by decide) (by decide) (by decide) (by decide)
      a'bc := facetFnK φ124 _ h124 4 1 2 (by decide) (by decide) (by decide) (by decide)
      a'bc' := facetFnK φQ _ hQ 4 1 5 (by decide) (by decide) (by decide) (by decide)
      a'b'c := facetFnK φ234 _ h234 4 3 2 (by decide) (by decide) (by decide) (by decide)
      a'b'c' := facetFn345 (-D x 3 4 5 1) q0 q1 q2 }
  refine ⟨F, ⟨(hQ 6).1 (by decide), ?_, (h012 6).2 (by decide), (h015 6).2 (by decide),
    (h023 6).2 (by decide), (h035 6).2 (by decide), (h124 6).2 (by decide),
    (h234 6).2 (by decide)⟩⟩
  show 0 < -D x 3 4 5 1 * det4 (x 3) (x 4) (x 5) (x 6)
  have : det4 (x 3) (x 4) (x 5) (x 6) = D x 3 4 5 6 := rfl
  rw [this]
  linarith

/-! ### The classes -/

/-- The third class coordinate `V` of Lemma 21.2. -/
def NF29.V {x : Fin 7 → ℝ³} (N : NF29 x) : ℝ :=
  N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)

/-- **The classes of the octahedron** (Lemma 21.2) by the signs of `(a2, b0, V)`: a class
boundary, K2, K1 (`a` or `b` form), K3a, K3b, K4a, K4b. -/
theorem NF29.classes {x : Fin 7 → ℝ³} (N : NF29 x) :
    (N.a2 = 0 ∨ N.b0 = 0 ∨ N.V = 0) ∨
    (N.a2 < 0 ∧ N.b0 < 0) ∨
    ((N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V)) ∨
    (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.V) ∨
    (0 < N.a2 ∧ N.b0 < 0 ∧ N.V < 0) ∨
    (0 < N.a2 ∧ 0 < N.b0 ∧ N.V < 0) ∨
    (0 < N.a2 ∧ 0 < N.b0 ∧ 0 < N.V) := by
  rcases lt_trichotomy N.a2 0 with ha | ha | ha <;>
  rcases lt_trichotomy N.b0 0 with hb | hb | hb <;>
  rcases lt_trichotomy N.V 0 with hv | hv | hv <;>
  simp only [ha, hb, hv, lt_irrefl, true_and, and_true, true_or, or_true, not_lt.mpr,
    le_of_lt]

end Minimality

end
