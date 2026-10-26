module

public import Minimality.TripleTie

@[expose] public section

/-!
# The triple tie at the special value of Lemma T′ (`FEWER-FACES-PROOFS.md` 24.14, 24.15, 26.8)

At the special value of Lemma T′ three faces are edge-on in one view `u0` and the shadow is
a triangle. When the three corners are at one depth (the triple tie), the readings of
Lemma T′ at the corners (`SpecialValue.lean`) can all fail; the paper closes this case by
the sector criterion (Theorem 24.1) at `u0`, the ties broken lexicographically by the tilt.
In Lean this is `isRupert_triShadow_lex` (`TripleTie.lean`) with explicit chains:

- `isRupert_levelTri_frame`: the *bare level triangle*. Both chains at the apex are single
  edges, every other point of the two apex sides lies strictly on the hidden side (a
  vertical companion over the apex included), every other point of the far side strictly
  on the other side. The cycle is the triangle of the three corners, whose lexicographic
  values are distinct for a suitable tilt (Proposition 26.8, second case; Lemma 24.14 (α)).
- `isRupert_levelTri_mid_frame`: the face on side 1 is two-sided with one middle on each
  side of the level chord, side 2 is bare, the far side hidden (Lemma 24.14 (β)): the
  sector is chosen by the angle of the shadow at the far corner of side 1.

The face-lattice facts of the paper ("the three corners do not span a face", the signs of
one-sided faces) come from one determinant identity: three affine functionals vanishing on a
common line have `det [fᵢ(rⱼ)] = 0` (`det3_affine_zero`), whence `wedge_pos` (two facets
through an edge and a third plane through it) and `sameSide_of_facet`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-! ### Three planes through a line -/

/-- Three linear forms killing a common nonzero vector have a vanishing determinant
against any three vectors (the determinant of the products factors through `det N = 0`). -/
theorem det3_zero_real (a1 b1 c1 a2 b2 c2 a3 b3 c3 x1 y1 z1 x2 y2 z2 x3 y3 z3 d0 d1 d2 : ℝ)
    (hd : d0 ≠ 0 ∨ d1 ≠ 0 ∨ d2 ≠ 0) (h1 : a1 * d0 + b1 * d1 + c1 * d2 = 0)
    (h2 : a2 * d0 + b2 * d1 + c2 * d2 = 0) (h3 : a3 * d0 + b3 * d1 + c3 * d2 = 0) :
    (a1 * x1 + b1 * y1 + c1 * z1) *
        ((a2 * x2 + b2 * y2 + c2 * z2) * (a3 * x3 + b3 * y3 + c3 * z3) -
          (a2 * x3 + b2 * y3 + c2 * z3) * (a3 * x2 + b3 * y2 + c3 * z2)) -
      (a1 * x2 + b1 * y2 + c1 * z2) *
        ((a2 * x1 + b2 * y1 + c2 * z1) * (a3 * x3 + b3 * y3 + c3 * z3) -
          (a2 * x3 + b2 * y3 + c2 * z3) * (a3 * x1 + b3 * y1 + c3 * z1)) +
      (a1 * x3 + b1 * y3 + c1 * z3) *
        ((a2 * x1 + b2 * y1 + c2 * z1) * (a3 * x2 + b3 * y2 + c3 * z2) -
          (a2 * x2 + b2 * y2 + c2 * z2) * (a3 * x1 + b3 * y1 + c3 * z1)) = 0 := by
  set dN := a1 * (b2 * c3 - c2 * b3) - b1 * (a2 * c3 - c2 * a3) + c1 * (a2 * b3 - b2 * a3) with hdN
  set dU := x1 * (y2 * z3 - z2 * y3) - y1 * (x2 * z3 - z2 * x3) + z1 * (x2 * y3 - y2 * x3) with hdU
  have hN : dN = 0 := by
    have e0 : dN * d0 = 0 := by
      rw [hdN]
      linear_combination (b2 * c3 - c2 * b3) * h1 + (b3 * c1 - c3 * b1) * h2 +
        (b1 * c2 - c1 * b2) * h3
    have e1 : dN * d1 = 0 := by
      rw [hdN]
      linear_combination (c2 * a3 - a2 * c3) * h1 + (c3 * a1 - a3 * c1) * h2 +
        (c1 * a2 - a1 * c2) * h3
    have e2 : dN * d2 = 0 := by
      rw [hdN]
      linear_combination (a2 * b3 - b2 * a3) * h1 + (a3 * b1 - b3 * a1) * h2 +
        (a1 * b2 - b1 * a2) * h3
    rcases hd with h | h | h
    · exact (mul_eq_zero.mp e0).resolve_right h
    · exact (mul_eq_zero.mp e1).resolve_right h
    · exact (mul_eq_zero.mp e2).resolve_right h
  linear_combination dU * hN

/-- An affine function in coordinates, vanishing at `p`, is a linear form in `x - p`. -/
theorem aff_sub_rep {f : ℝ³ → ℝ}
    (hf : ∃ K α β γ : ℝ, ∀ x : ℝ³, f x = K + α * x 0 + β * x 1 + γ * x 2)
    {p : ℝ³} (hp : f p = 0) :
    ∃ α β γ : ℝ, ∀ x : ℝ³, f x = α * (x 0 - p 0) + β * (x 1 - p 1) + γ * (x 2 - p 2) := by
  obtain ⟨K, α, β, γ, h⟩ := hf
  refine ⟨α, β, γ, fun x => ?_⟩
  have := h p; rw [h x]; linarith

/-- **Three planes through a line.** Three affine functions vanishing at two distinct points
`p`, `q` have a vanishing determinant `det [fᵢ(rⱼ)]` at any three points. -/
theorem det3_affine_zero {f1 f2 f3 : ℝ³ → ℝ}
    (hf1 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f1 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hf2 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f2 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hf3 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f3 x = K + α * x 0 + β * x 1 + γ * x 2)
    {p q : ℝ³} (hpq : p ≠ q) (h1p : f1 p = 0) (h1q : f1 q = 0) (h2p : f2 p = 0) (h2q : f2 q = 0)
    (h3p : f3 p = 0) (h3q : f3 q = 0) (r1 r2 r3 : ℝ³) :
    f1 r1 * (f2 r2 * f3 r3 - f2 r3 * f3 r2) - f1 r2 * (f2 r1 * f3 r3 - f2 r3 * f3 r1) +
      f1 r3 * (f2 r1 * f3 r2 - f2 r2 * f3 r1) = 0 := by
  obtain ⟨a1, b1, c1, e1⟩ := aff_sub_rep hf1 h1p
  obtain ⟨a2, b2, c2, e2⟩ := aff_sub_rep hf2 h2p
  obtain ⟨a3, b3, c3, e3⟩ := aff_sub_rep hf3 h3p
  have hd : q 0 - p 0 ≠ 0 ∨ q 1 - p 1 ≠ 0 ∨ q 2 - p 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    ext k; fin_cases k
    · simp; linarith [h.1]
    · simp; linarith [h.2.1]
    · simp; linarith [h.2.2]
  have k1 := e1 q; have k2 := e2 q; have k3 := e3 q
  rw [h1q] at k1; rw [h2q] at k2; rw [h3q] at k3
  rw [e1, e1, e1, e2, e2, e2, e3, e3, e3]
  exact det3_zero_real a1 b1 c1 a2 b2 c2 a3 b3 c3 _ _ _ _ _ _ _ _ _ _ _ _ hd k1.symm k2.symm k3.symm

/-- **Two facets through an edge and a third plane** (the dihedral wedge). Let `f1`, `f2`
(facets) and `h` vanish on the line `pq`; `r1` lies on `f1` strictly inside `f2`, `r2` on
`f2` strictly inside `f1`, both strictly on the side `h > 0`. Then every point strictly
inside both facets is strictly on the side `h > 0`. -/
theorem wedge_pos {f1 f2 h : ℝ³ → ℝ}
    (hf1 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f1 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hf2 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f2 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hh : ∃ K α β γ : ℝ, ∀ x : ℝ³, h x = K + α * x 0 + β * x 1 + γ * x 2)
    {p q r1 r2 y : ℝ³} (hpq : p ≠ q) (h1p : f1 p = 0) (h1q : f1 q = 0) (h2p : f2 p = 0)
    (h2q : f2 q = 0) (hhp : h p = 0) (hhq : h q = 0)
    (a1 : f1 r1 = 0) (b1 : f2 r1 < 0) (c1 : 0 < h r1)
    (a2 : f2 r2 = 0) (b2 : f1 r2 < 0) (c2 : 0 < h r2)
    (y1 : f1 y < 0) (y2 : f2 y < 0) : 0 < h y := by
  have D := det3_affine_zero hf1 hf2 hh hpq h1p h1q h2p h2q hhp hhq r1 r2 y
  rw [a1, a2] at D
  by_contra hy
  push Not at hy
  have t1 : 0 ≤ (f1 r2 * f2 r1) * (-h y) := mul_nonneg (by nlinarith) (by linarith)
  have t2 : 0 < (f1 r2 * f2 y) * h r1 := mul_pos (by nlinarith) c1
  have t3 : 0 < (f1 y * f2 r1) * h r2 := mul_pos (by nlinarith) c2
  nlinarith

/-- **Two points of a facet below a second facet through an edge lie on one side.** `f1`,
`f2`, `h` vanish on the line `pq`; `r1`, `r2` lie on `f1` strictly inside `f2`, and `y` is
off `f1` with `h y = 0`. Then `r1` and `r2` are not strictly on opposite sides of `h`. -/
theorem sameSide_of_facet {f1 f2 h : ℝ³ → ℝ}
    (hf1 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f1 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hf2 : ∃ K α β γ : ℝ, ∀ x : ℝ³, f2 x = K + α * x 0 + β * x 1 + γ * x 2)
    (hh : ∃ K α β γ : ℝ, ∀ x : ℝ³, h x = K + α * x 0 + β * x 1 + γ * x 2)
    {p q r1 r2 y : ℝ³} (hpq : p ≠ q) (h1p : f1 p = 0) (h1q : f1 q = 0) (h2p : f2 p = 0)
    (h2q : f2 q = 0) (hhp : h p = 0) (hhq : h q = 0)
    (a1 : f1 r1 = 0) (b1 : f2 r1 < 0) (a2 : f1 r2 = 0) (b2 : f2 r2 < 0)
    (y1 : f1 y ≠ 0) (y3 : h y = 0) (c1 : 0 < h r1) (c2 : h r2 < 0) : False := by
  have D := det3_affine_zero hf1 hf2 hh hpq h1p h1q h2p h2q hhp hhq r1 r2 y
  rw [a1, a2, y3] at D
  have : f1 y * (f2 r1 * h r2 - f2 r2 * h r1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact y1 h0
  · nlinarith

/-- Affine maps are affine in coordinates. -/
theorem affineMap_rep (f : ℝ³ →ᵃ[ℝ] ℝ) :
    ∃ K α β γ : ℝ, ∀ x : ℝ³, f x = K + α * x 0 + β * x 1 + γ * x 2 :=
  affine_xyz f

/-- A depth `σ (⟪x, e⟫ - k)` is affine in coordinates. -/
theorem depth_rep (σ k : ℝ) (e : ℝ³) :
    ∃ K α β γ : ℝ, ∀ x : ℝ³, σ * (⟪x, e⟫ - k) = K + α * x 0 + β * x 1 + γ * x 2 :=
  ⟨-σ * k, σ * e 0, σ * e 1, σ * e 2, fun x => by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring⟩

/-! ### The bare level triangle -/

/-- Two lines of the Gram matrix of `r1`, `r2` are not both equal (`r1 ≠ r2`). -/
theorem gram_ne_of_cross2 {r1 r2 : ℝ²} (hρ : 0 < cross2 r1 r2) :
    r1 0 * r1 0 + r1 1 * r1 1 ≠ r1 0 * r2 0 + r1 1 * r2 1 ∨
      r1 0 * r2 0 + r1 1 * r2 1 ≠ r2 0 * r2 0 + r2 1 * r2 1 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have lag : (cross2 r1 r2) ^ 2 + (r1 0 * r2 0 + r1 1 * r2 1) ^ 2 =
      (r1 0 * r1 0 + r1 1 * r1 1) * (r2 0 * r2 0 + r2 1 * r2 1) := by unfold cross2; ring
  have : (cross2 r1 r2) ^ 2 = 0 := by
    linear_combination lag + (r2 0 * r2 0 + r2 1 * r2 1) * h1 -
      (r1 0 * r2 0 + r1 1 * r2 1) * h2
  have := pow_pos hρ 2
  linarith

set_option maxHeartbeats 4000000 in
/-- **The bare level triangle** (Theorem 24.1 at a triple tie; Proposition 26.8, Lemma 24.14
(α)). In the oblique frame `(O, r1, r2)` the apex `(0, 0, c)` and the far corners `(1, 0, c)`,
`(0, 1, c)` are in `V`, at one depth `c`. Every other point of `V` lies in the shadow
triangle: strictly inside, or on a side at the apex (`a = 0` or `b = 0`, `a + b < 1`; a
vertical companion over the apex included) strictly on the side `s (z - c) < 0`, or strictly
inside the far side strictly on the side `s (z - c) > 0`. Then `V` is Rupert: in the sector
hiding both apex sides and showing the far side bare, the silhouette is the triangle of the
three corners, unimodal for a tilt that separates their tilt values. -/
theorem isRupert_levelTri_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V : Finset ℝ³)
    (c s : ℝ) (hs : s = 1 ∨ s = -1)
    (hv : oblPt O r1 r2 0 0 c ∈ V) (ha : oblPt O r1 r2 1 0 c ∈ V) (hb : oblPt O r1 r2 0 1 c ∈ V)
    (hV : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      ((a = 0 ∧ b = 0 ∧ z = c) ∨ (a = 1 ∧ b = 0 ∧ z = c) ∨ (a = 0 ∧ b = 1 ∧ z = c) ∨
        (a + b < 1 ∧ ((0 < a ∧ 0 < b) ∨ s * (z - c) < 0)) ∨
        (0 < a ∧ 0 < b ∧ a + b = 1 ∧ 0 < s * (z - c)))) : IsRupert V := by
  set n11 := r1 0 * r1 0 + r1 1 * r1 1 with hn11
  set n12 := r1 0 * r2 0 + r1 1 * r2 1 with hn12
  set n22 := r2 0 * r2 0 + r2 1 * r2 1 with hn22
  -- the tilt `(s α, s β)`: the far tilt values differ
  obtain ⟨β, hβ, hPQ⟩ : ∃ β : ℝ, 0 < β ∧ n11 + β * n12 ≠ n12 + β * n22 := by
    rcases gram_ne_of_cross2 hρ with h | h
    · by_cases h1 : n11 + 1 * n12 = n12 + 1 * n22
      · exact ⟨2, by norm_num, fun h2 => h (by linarith)⟩
      · exact ⟨1, one_pos, h1⟩
    · by_cases h1 : n11 + 1 * n12 = n12 + 1 * n22
      · exact ⟨2, by norm_num, fun h2 => h (by linarith)⟩
      · exact ⟨1, one_pos, h1⟩
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine isRupert_triShadow_lex O r1 r2 hρ (m := 1) (n := 1) le_rfl le_rfl s hs (-s) hns
    (α := 1) (β := β) one_pos hβ (fun l => (l : ℝ)) (fun _ => c) (fun l => (l : ℝ)) (fun _ => c)
    (by simp) (by simp) rfl (fun l hl => by push_cast; linarith)
    (fun l hl => by push_cast; linarith) V ?_ ?_ ?_ (s * n11 + s * β * n12) (s * n12 + s * β * n22)
    (by ring) (by ring) ?_
  · intro l hl
    interval_cases l
    · simpa using hv
    · simpa using ha
  · intro l hl
    interval_cases l
    · simpa using hv
    · simpa using hb
  · intro y hy
    obtain ⟨a, b, z, rfl, ha0, hb0, hc⟩ := hV y hy
    refine ⟨a, b, z, rfl, ha0, hb0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_one]
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hab, -⟩ |
          ⟨hpa, hpb, hab, hz⟩
      · left; left; norm_num
      · right; left; rfl
      · right; right; rfl
      · left; left; nlinarith
      · left; right
        refine ⟨by linarith, ?_⟩
        have : 0 < s * (z - c) * (1 + β) := mul_pos hz (by linarith)
        nlinarith
    · intro hb' l hl h1 h2
      have hl0 : l = 0 := by omega
      subst hl0
      simp only [Nat.cast_one, Nat.cast_zero, zero_add] at h1 h2 ⊢
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, hb1, rfl⟩ | ⟨hab, hpos | hz⟩ |
          ⟨hpa, hpb, hab, hz⟩
      · exact absurd rfl h1
      · exact absurd rfl h2
      · linarith
      · linarith [hpos.2]
      · nlinarith
      · linarith
    · intro ha' l hl h1 h2
      have hl0 : l = 0 := by omega
      subst hl0
      simp only [Nat.cast_one, Nat.cast_zero, zero_add] at h1 h2 ⊢
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨ha1, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨hab, hpos | hz⟩ |
          ⟨hpa, hpb, hab, hz⟩
      · exact absurd rfl h2
      · linarith
      · exact absurd rfl h1
      · linarith [hpos.1]
      · nlinarith
      · linarith
  · -- the mode: the far tilt values differ
    simp only [Nat.cast_one, one_mul, LexS]
    have hne : s * (s * n11 + s * β * n12) ≠ s * (s * n12 + s * β * n22) := by
      intro h; apply hPQ
      have e1 : s * (s * n11 + s * β * n12) = n11 + β * n12 := by
        linear_combination (n11 + β * n12) * hs2
      have e2 : s * (s * n12 + s * β * n22) = n12 + β * n22 := by
        linear_combination (n12 + β * n22) * hs2
      rw [← e1, ← e2]; exact h
    rcases lt_or_gt_of_ne hne with h | h
    · right; left
      exact ⟨trivial, trivial, Or.inr (Or.inr ⟨trivial, h⟩)⟩
    · left
      exact ⟨Or.inr trivial, Or.inl (Or.inr ⟨trivial, h⟩)⟩

/-! ### A two-sided face at the apex -/

set_option maxHeartbeats 8000000 in
/-- **The level triangle with a shown middle on side 1** (Lemma 24.14 (β), the frame). As
`isRupert_levelTri_frame`, but the side `b = 0` shows the chain apex, `M = (am, 0, zm)`,
`(1, 0, c)` (the middle `M` strictly on the side `s (z - c) > 0`), every other point of it
strictly inside the side and strictly on the side `s (z - c) < 0`; the points inside the side
`a = 0` are strictly on the side `t (z - c) > 0`; the far points strictly inside the far side
satisfy `0 < (z - c) (s β - t α)`. The run is the chain `C1`; the far corner `(0, 1, c)` is
not the top of the cycle when `s Q < s P` or `s Q < 0`, for the far tilt values `P`, `Q`. -/
theorem isRupert_levelTri_mid_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V : Finset ℝ³)
    (c s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (am zm : ℝ) (ham : 0 < am)
    (ham1 : am < 1) (hzm : 0 < s * (zm - c)) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hv : oblPt O r1 r2 0 0 c ∈ V) (hm : oblPt O r1 r2 am 0 zm ∈ V)
    (ha : oblPt O r1 r2 1 0 c ∈ V) (hb : oblPt O r1 r2 0 1 c ∈ V)
    (hV : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((a = 0 ∧ b = 0 ∧ z = c) ∨ (a = am ∧ b = 0 ∧ z = zm) ∨ (a = 1 ∧ b = 0 ∧ z = c) ∨
        (a = 0 ∧ b = 1 ∧ z = c) ∨ (0 < a ∧ 0 < b ∧ a + b < 1) ∨
        (0 < a ∧ a < 1 ∧ b = 0 ∧ s * (z - c) < 0) ∨ (a = 0 ∧ 0 < b ∧ b < 1 ∧ 0 < t * (z - c)) ∨
        (0 < a ∧ 0 < b ∧ a + b = 1 ∧ 0 < (z - c) * (s * β - t * α))))
    (hmode : s * (-t * α * (r1 0 * r2 0 + r1 1 * r2 1) + s * β * (r2 0 * r2 0 + r2 1 * r2 1)) <
        s * (-t * α * (r1 0 * r1 0 + r1 1 * r1 1) + s * β * (r1 0 * r2 0 + r1 1 * r2 1)) ∨
      s * (-t * α * (r1 0 * r2 0 + r1 1 * r2 1) + s * β * (r2 0 * r2 0 + r2 1 * r2 1)) < 0) :
    IsRupert V := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have ht2 : t * t = 1 := by rcases ht with rfl | rfl <;> norm_num
  set ca : ℕ → ℝ := fun l => if l = 0 then 0 else if l = 1 then am else 1 with hca
  set cz : ℕ → ℝ := fun l => if l = 1 then zm else c with hcz
  have c0 : ca 0 = 0 := by simp [hca]
  have c1 : ca 1 = am := by simp [hca]
  have c2 : ca 2 = 1 := by simp [hca]
  have z0 : cz 0 = c := by simp [hcz]
  have z1 : cz 1 = zm := by simp [hcz]
  have z2 : cz 2 = c := by simp [hcz]
  refine isRupert_triShadow_lex O r1 r2 hρ (m := 2) (n := 1) (by norm_num) le_rfl s hs t ht
    hα hβ ca cz (fun l => (l : ℝ)) (fun _ => c) c0 (by simp) (by rw [z0])
    (fun l hl => by interval_cases l <;> simp [hca] <;> linarith)
    (fun l hl => by push_cast; linarith) V ?_ ?_ ?_ _ _ rfl rfl ?_
  · intro l hl
    interval_cases l
    · rw [c0, z0]; exact hv
    · rw [c1, z1]; exact hm
    · rw [c2, z2]; exact ha
  · intro l hl
    interval_cases l
    · simpa using hv
    · simpa using hb
  · intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hV y hy
    have Zm := hzm
    refine ⟨a, b, z, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
        ⟨rfl, -⟩ | ⟨h, -⟩ <;> linarith
    · rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, h, -⟩ |
        ⟨-, -, rfl, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> linarith
    · rw [c2, z2]
      simp only [Nat.cast_one]
      rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨hpa, hpb, hab⟩ | ⟨hpa, hpa1, rfl, hz⟩ | ⟨rfl, hpb, hpb1, hz⟩ | ⟨hpa, hpb, hab, hz⟩
      · left; left; norm_num
      · left; left; nlinarith
      · right; left; rfl
      · right; right; rfl
      · left; left; nlinarith
      · left; left; nlinarith
      · left; left; nlinarith
      · left; right
        refine ⟨by linarith, ?_⟩
        nlinarith
    · intro hb' l hl h1 h2
      subst hb'
      interval_cases l
      · rw [c0, c1, z0, z1] at *
        rcases hc with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨-, h, -⟩ |
            ⟨hpa, hpb, hab⟩ | ⟨hpa, hpa1, -, hz⟩ | ⟨-, hpb, -⟩ | ⟨hpa, hpb, hab, hz⟩
        · exact absurd rfl h1
        · exact absurd rfl h2
        · nlinarith
        · linarith
        · linarith
        · nlinarith
        · linarith
        · linarith
      · rw [c1, c2, z1, z2] at *
        rcases hc with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨-, h, -⟩ |
            ⟨hpa, hpb, hab⟩ | ⟨hpa, hpa1, -, hz⟩ | ⟨-, hpb, -⟩ | ⟨hpa, hpb, hab, hz⟩
        · nlinarith
        · exact absurd rfl h1
        · exact absurd rfl h2
        · linarith
        · linarith
        · nlinarith
        · linarith
        · linarith
    · intro ha' l hl h1 h2
      have hl0 : l = 0 := by omega
      subst hl0
      simp only [Nat.cast_one, Nat.cast_zero, zero_add] at h1 h2 ⊢
      rcases hc with ⟨-, rfl, rfl⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨-, rfl, rfl⟩ |
          ⟨hpa, hpb, hab⟩ | ⟨hpa, -⟩ | ⟨-, hpb, hpb1, hz⟩ | ⟨hpa, -⟩
      · subst ha'; exact absurd rfl h2
      · linarith
      · linarith
      · subst ha'; exact absurd rfl h1
      · linarith
      · linarith
      · nlinarith
      · linarith
  · simp only [c2, Nat.cast_one, one_mul, z2, z0, LexS]
    left
    refine ⟨Or.inr trivial, ?_⟩
    rcases hmode with h | h
    · exact Or.inl (Or.inr ⟨trivial, h⟩)
    · exact Or.inr ⟨trivial, Or.inr ⟨trivial, by simpa using h⟩⟩

set_option maxHeartbeats 8000000 in
/-- **Lemma 24.14 (β) in the frame.** The three corners at depth `c`; the side `b = 0` is a
two-sided face with exactly one point `(ap, 0, zp)` above and one `(an, 0, zn)` below the
level chord; the points inside the side `a = 0` are strictly on the side `t (z - c) > 0`, the
far points strictly inside the far side on the other side `t (z - c) < 0`. Then `V` is
Rupert, at every angle of the shadow: the sector `s = -t` works unless the angle at the far
corner `(1, 0)` is not acute and the one at `(0, 1)` not obtuse, and then `s = t` works. -/
theorem isRupert_levelTri_two_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V : Finset ℝ³)
    (c t : ℝ) (ht : t = 1 ∨ t = -1) (ap zp an zn : ℝ) (hap : 0 < ap) (hap1 : ap < 1)
    (han : 0 < an) (han1 : an < 1) (hzp : c < zp) (hzn : zn < c)
    (hv : oblPt O r1 r2 0 0 c ∈ V) (hmp : oblPt O r1 r2 ap 0 zp ∈ V)
    (hmn : oblPt O r1 r2 an 0 zn ∈ V)
    (ha : oblPt O r1 r2 1 0 c ∈ V) (hb : oblPt O r1 r2 0 1 c ∈ V)
    (hV : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((a = 0 ∧ b = 0 ∧ z = c) ∨ (a = ap ∧ b = 0 ∧ z = zp) ∨ (a = an ∧ b = 0 ∧ z = zn) ∨
        (a = 1 ∧ b = 0 ∧ z = c) ∨ (a = 0 ∧ b = 1 ∧ z = c) ∨ (0 < a ∧ 0 < b ∧ a + b < 1) ∨
        (a = 0 ∧ 0 < b ∧ b < 1 ∧ 0 < t * (z - c)) ∨
        (0 < a ∧ 0 < b ∧ a + b = 1 ∧ t * (z - c) < 0))) : IsRupert V := by
  set n11 := r1 0 * r1 0 + r1 1 * r1 1 with hn11
  set n12 := r1 0 * r2 0 + r1 1 * r2 1 with hn12
  set n22 := r2 0 * r2 0 + r2 1 * r2 1 with hn22
  have hn := (normSq_pos_of_cross2 hρ)
  have ht2 : t * t = 1 := by rcases ht with rfl | rfl <;> norm_num
  have hnt : -t = 1 ∨ -t = -1 := by rcases ht with rfl | rfl <;> norm_num
  -- the chain of sign `s` shows the middle `(am, zm)`; the other one is hidden
  have core : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ α β : ℝ, 0 < α → 0 < β →
      (∀ z : ℝ, t * (z - c) < 0 → 0 < (z - c) * (s * β - t * α)) →
      (s * (-t * α * n12 + s * β * n22) < s * (-t * α * n11 + s * β * n12) ∨
        s * (-t * α * n12 + s * β * n22) < 0) → IsRupert V := by
    intro s hs α β hα hβ hfar hmode
    have key : ∀ am zm a' z', 0 < am → am < 1 → 0 < s * (zm - c) → 0 < a' → a' < 1 →
        s * (z' - c) < 0 → oblPt O r1 r2 am 0 zm ∈ V →
        (∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
          ((a = 0 ∧ b = 0 ∧ z = c) ∨ (a = am ∧ b = 0 ∧ z = zm) ∨ (a = a' ∧ b = 0 ∧ z = z') ∨
            (a = 1 ∧ b = 0 ∧ z = c) ∨ (a = 0 ∧ b = 1 ∧ z = c) ∨ (0 < a ∧ 0 < b ∧ a + b < 1) ∨
            (a = 0 ∧ 0 < b ∧ b < 1 ∧ 0 < t * (z - c)) ∨
            (0 < a ∧ 0 < b ∧ a + b = 1 ∧ t * (z - c) < 0))) → IsRupert V := by
      intro am zm a' z' h1 h2 h3 h4 h5 h6 hmV hV'
      refine isRupert_levelTri_mid_frame O r1 r2 hρ V c s t hs ht am zm h1 h2 h3 hα hβ hv hmV ha hb
        (fun y hy => ?_) hmode
      obtain ⟨a, b, z, rfl, hc⟩ := hV' y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h | h | ⟨rfl, rfl, rfl⟩ | h | h | h | h | ⟨e1, e2, e3, e4⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h5, rfl, h6⟩)))))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e1, e2, e3, hfar z e4⟩))))))
    rcases hs with rfl | rfl
    · refine key ap zp an zn hap hap1 (by linarith) han han1 (by linarith) hmp (fun y hy => ?_)
      obtain ⟨a, b, z, rfl, hc⟩ := hV y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    · refine key an zn ap zp han han1 (by linarith) hap hap1 (by linarith) hmn (fun y hy => ?_)
      obtain ⟨a, b, z, rfl, hc⟩ := hV y hy
      refine ⟨a, b, z, rfl, ?_⟩
      rcases hc with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  -- the sector `s = -t`: the far value at `(1, 0)` above that at `(0, 1)`
  have neg : ∀ α β : ℝ, 0 < α → 0 < β → 0 < α * (n11 - n12) + β * (n12 - n22) → IsRupert V := by
    intro α β hα hβ h
    refine core (-t) hnt α β hα hβ (fun z hz => ?_) (Or.inl ?_)
    · have : 0 < -(t * (z - c)) * (α + β) := mul_pos (by linarith) (by linarith)
      nlinarith
    · have e1 : -t * (-t * α * n12 + -t * β * n22) = α * n12 + β * n22 := by
        linear_combination (α * n12 + β * n22) * ht2
      have e2 : -t * (-t * α * n11 + -t * β * n12) = α * n11 + β * n12 := by
        linear_combination (α * n11 + β * n12) * ht2
      rw [e1, e2]; linarith
  by_cases hA : n12 < n11
  · obtain ⟨ε, hε, h⟩ := exists_small_pos (f0 := n11 - n12) (f1 := n12 - n22) (by linarith)
    exact neg 1 ε one_pos hε (by linarith)
  by_cases hB : n22 < n12
  · obtain ⟨ε, hε, h⟩ := exists_small_pos (f0 := n12 - n22) (f1 := n11 - n12) (by linarith)
    exact neg ε 1 hε one_pos (by linarith)
  -- the sector `s = t`, with `α` large
  have h12 : 0 < n12 := by push Not at hA; linarith [hn.1]
  have hα : 0 < 1 + n22 / n12 := by have := div_pos hn.2 h12; linarith
  refine core t ht (1 + n22 / n12) 1 hα one_pos (fun z hz => ?_) (Or.inr ?_)
  · have e : (z - c) * (t * 1 - t * (1 + n22 / n12)) = -(t * (z - c)) * (n22 / n12) := by ring
    rw [e]; exact mul_pos (by linarith) (div_pos hn.2 h12)
  · have e : t * (-t * (1 + n22 / n12) * n12 + t * 1 * n22) = -n12 := by
      field_simp
      linear_combination (-n12 - n22 + n22) * ht2
    rw [e]; linarith

/-! ### Faces as point sets -/

set_option maxHeartbeats 4000000 in
/-- **The bare level triangle, faces as point sets.** The frame of `isRupert_levelTri_frame`
given by coordinates `a`, `b` on `V`: `F1` (`b = 0`), `F2` (`a = 0`), `F3` (`a + b = 1`) are
faces through the corners `p0 = F1 ∩ F2`, `p1 = F1 ∩ F3`, `p2 = F2 ∩ F3`, all at depth `c`;
the other points of `F1`, `F2` are strictly on the side `s (z - c) < 0`, those of `F3`
strictly on the other side. Then `V` is Rupert. -/
theorem isRupert_levelTri_faces (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V F1 F2 F3 : Finset ℝ³)
    (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : F1 ⊆ V) (h2V : F2 ⊆ V)
    (hb1 : ∀ p ∈ F1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ F1 → 0 < b p)
    (ha2 : ∀ p ∈ F2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ F2 → 0 < a p)
    (h3 : ∀ p ∈ F3, a p + b p = 1) (h3' : ∀ p ∈ V, p ∉ F3 → a p + b p < 1)
    (p0 p1 p2 : ℝ³) (hp0 : p0 ∈ F1 ∧ p0 ∈ F2) (hp1 : p1 ∈ F1 ∧ p1 ∈ F3) (hp2 : p2 ∈ F2 ∧ p2 ∈ F3)
    (h12 : ∀ p ∈ F1, p ∈ F2 → p = p0) (h13 : ∀ p ∈ F1, p ∈ F3 → p = p1)
    (h23 : ∀ p ∈ F2, p ∈ F3 → p = p2)
    (c s : ℝ) (hs : s = 1 ∨ s = -1) (hc0 : p0 2 = c) (hc1 : p1 2 = c) (hc2 : p2 2 = c)
    (hF1 : ∀ p ∈ F1, p ≠ p0 → p ≠ p1 → s * (p 2 - c) < 0)
    (hF2 : ∀ p ∈ F2, p ≠ p0 → p ≠ p2 → s * (p 2 - c) < 0)
    (hF3 : ∀ p ∈ F3, p ≠ p1 → p ≠ p2 → 0 < s * (p 2 - c)) : IsRupert V := by
  have ha0 : ∀ p ∈ V, 0 ≤ a p := fun p hp => by
    by_cases h : p ∈ F2
    · rw [ha2 p h]
    · exact (ha2' p hp h).le
  have hb0 : ∀ p ∈ V, 0 ≤ b p := fun p hp => by
    by_cases h : p ∈ F1
    · rw [hb1 p h]
    · exact (hb1' p hp h).le
  have e0 : p0 = oblPt O r1 r2 0 0 c := by
    have := hy p0 (h1V hp0.1); rwa [ha2 p0 hp0.2, hb1 p0 hp0.1, hc0] at this
  have e1 : p1 = oblPt O r1 r2 1 0 c := by
    have := hy p1 (h1V hp1.1)
    have k := h3 p1 hp1.2; rw [hb1 p1 hp1.1] at k
    rwa [hb1 p1 hp1.1, show a p1 = 1 by linarith, hc1] at this
  have e2 : p2 = oblPt O r1 r2 0 1 c := by
    have := hy p2 (h2V hp2.1)
    have k := h3 p2 hp2.2; rw [ha2 p2 hp2.1] at k
    rwa [ha2 p2 hp2.1, show b p2 = 1 by linarith, hc2] at this
  refine isRupert_levelTri_frame O r1 r2 hρ V c s hs (e0 ▸ h1V hp0.1) (e1 ▸ h1V hp1.1)
    (e2 ▸ h2V hp2.1) (fun y hy' => ⟨a y, b y, y 2, hy y hy', ha0 y hy', hb0 y hy', ?_⟩)
  by_cases y1 : y ∈ F1
  · by_cases ey0 : y = p0
    · subst ey0; exact Or.inl ⟨ha2 y hp0.2, hb1 y y1, hc0⟩
    by_cases ey1 : y = p1
    · subst ey1
      have k := h3 y hp1.2; rw [hb1 y y1] at k
      exact Or.inr (Or.inl ⟨by linarith, hb1 y y1, hc1⟩)
    have n2 : y ∉ F2 := fun h => ey0 (h12 y y1 h)
    have n3 : y ∉ F3 := fun h => ey1 (h13 y y1 h)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3' y hy' n3, Or.inr (hF1 y y1 ey0 ey1)⟩)))
  by_cases y2 : y ∈ F2
  · by_cases ey2 : y = p2
    · subst ey2
      have k := h3 y hp2.2; rw [ha2 y y2] at k
      exact Or.inr (Or.inr (Or.inl ⟨ha2 y y2, by linarith, hc2⟩))
    have ey0 : y ≠ p0 := fun e => y1 (e ▸ hp0.1)
    have n3 : y ∉ F3 := fun h => ey2 (h23 y y2 h)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3' y hy' n3, Or.inr (hF2 y y2 ey0 ey2)⟩)))
  by_cases y3 : y ∈ F3
  · have ey1 : y ≠ p1 := fun e => y1 (e ▸ hp1.1)
    have ey2 : y ≠ p2 := fun e => y2 (e ▸ hp2.1)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha2' y hy' y2, hb1' y hy' y1, h3 y y3,
      hF3 y y3 ey1 ey2⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3' y hy' y3, Or.inl ⟨ha2' y hy' y2, hb1' y hy' y1⟩⟩)))

set_option maxHeartbeats 4000000 in
/-- **Lemma 24.14 (β), faces as point sets.** As `isRupert_levelTri_faces`, but `F1` is
two-sided: its vertices besides the corners are one point `mp` strictly above and one `mn`
strictly below the level `c`; the other points of `F2` are strictly on the side
`t (z - c) > 0`, those of `F3` strictly on the other side. -/
theorem isRupert_levelTri_two_faces (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    (V F1 F2 F3 : Finset ℝ³)
    (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : F1 ⊆ V) (h2V : F2 ⊆ V)
    (hb1 : ∀ p ∈ F1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ F1 → 0 < b p)
    (ha2 : ∀ p ∈ F2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ F2 → 0 < a p)
    (h3 : ∀ p ∈ F3, a p + b p = 1) (h3' : ∀ p ∈ V, p ∉ F3 → a p + b p < 1)
    (p0 p1 p2 : ℝ³) (hp0 : p0 ∈ F1 ∧ p0 ∈ F2) (hp1 : p1 ∈ F1 ∧ p1 ∈ F3) (hp2 : p2 ∈ F2 ∧ p2 ∈ F3)
    (h12 : ∀ p ∈ F1, p ∈ F2 → p = p0) (h13 : ∀ p ∈ F1, p ∈ F3 → p = p1)
    (h23 : ∀ p ∈ F2, p ∈ F3 → p = p2)
    (c t : ℝ) (ht : t = 1 ∨ t = -1) (hc0 : p0 2 = c) (hc1 : p1 2 = c) (hc2 : p2 2 = c)
    (mp mn : ℝ³) (hmp : mp ∈ F1) (hmn : mn ∈ F1) (hzp : c < mp 2) (hzn : mn 2 < c)
    (hF1 : ∀ p ∈ F1, p = p0 ∨ p = p1 ∨ p = mp ∨ p = mn)
    (hF2 : ∀ p ∈ F2, p ≠ p0 → p ≠ p2 → 0 < t * (p 2 - c))
    (hF3 : ∀ p ∈ F3, p ≠ p1 → p ≠ p2 → t * (p 2 - c) < 0) : IsRupert V := by
  have e0 : p0 = oblPt O r1 r2 0 0 c := by
    have := hy p0 (h1V hp0.1); rwa [ha2 p0 hp0.2, hb1 p0 hp0.1, hc0] at this
  have e1 : p1 = oblPt O r1 r2 1 0 c := by
    have := hy p1 (h1V hp1.1)
    have k := h3 p1 hp1.2; rw [hb1 p1 hp1.1] at k
    rwa [hb1 p1 hp1.1, show a p1 = 1 by linarith, hc1] at this
  have e2 : p2 = oblPt O r1 r2 0 1 c := by
    have := hy p2 (h2V hp2.1)
    have k := h3 p2 hp2.2; rw [ha2 p2 hp2.1] at k
    rwa [ha2 p2 hp2.1, show b p2 = 1 by linarith, hc2] at this
  -- the middles of `F1` are strictly inside its side
  have mid : ∀ m ∈ F1, m 2 ≠ c → 0 < a m ∧ a m < 1 := by
    intro m hm hz
    have n2 : m ∉ F2 := fun h => hz (by rw [h12 m hm h, hc0])
    have n3 : m ∉ F3 := fun h => hz (by rw [h13 m hm h, hc1])
    refine ⟨ha2' m (h1V hm) n2, ?_⟩
    have := h3' m (h1V hm) n3; rw [hb1 m hm] at this; linarith
  have kp := mid mp hmp hzp.ne'
  have kn := mid mn hmn hzn.ne
  have emp : mp = oblPt O r1 r2 (a mp) 0 (mp 2) := by
    have := hy mp (h1V hmp); rwa [hb1 mp hmp] at this
  have emn : mn = oblPt O r1 r2 (a mn) 0 (mn 2) := by
    have := hy mn (h1V hmn); rwa [hb1 mn hmn] at this
  refine isRupert_levelTri_two_frame O r1 r2 hρ V c t ht (a mp) (mp 2) (a mn) (mn 2) kp.1 kp.2
    kn.1 kn.2 hzp hzn (e0 ▸ h1V hp0.1) (emp ▸ h1V hmp) (emn ▸ h1V hmn) (e1 ▸ h1V hp1.1)
    (e2 ▸ h2V hp2.1) (fun y hy' => ⟨a y, b y, y 2, hy y hy', ?_⟩)
  by_cases y1 : y ∈ F1
  · rcases hF1 y y1 with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨ha2 y hp0.2, hb1 y y1, hc0⟩
    · have k := h3 y hp1.2; rw [hb1 y y1] at k
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, hb1 y y1, hc1⟩)))
    · exact Or.inr (Or.inl ⟨rfl, hb1 y y1, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hb1 y y1, rfl⟩))
  by_cases y2 : y ∈ F2
  · by_cases ey2 : y = p2
    · subst ey2
      have k := h3 y hp2.2; rw [ha2 y y2] at k
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha2 y y2, by linarith, hc2⟩))))
    have ey0 : y ≠ p0 := fun e => y1 (e ▸ hp0.1)
    have n3 : y ∉ F3 := fun h => ey2 (h23 y y2 h)
    have k := h3' y hy' n3; rw [ha2 y y2] at k
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨ha2 y y2, hb1' y hy' y1, by linarith, hF2 y y2 ey0 ey2⟩))))))
  by_cases y3 : y ∈ F3
  · have ey1 : y ≠ p1 := fun e => y1 (e ▸ hp1.1)
    have ey2 : y ≠ p2 := fun e => y2 (e ▸ hp2.1)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨ha2' y hy' y2, hb1' y hy' y1, h3 y y3, hF3 y y3 ey1 ey2⟩))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨ha2' y hy' y2, hb1' y hy' y1, h3' y hy' y3⟩)))))

end Minimality

end
