module

public import Minimality.TriQuad
public import Minimality.QuadFacets

@[expose] public section

/-!
# From facets to the oblique frame (Corollary T1)

The bridge from two quadrilateral facets of a 7-point set sharing one vertex to
`isRupert_twoQuads_frame`.  First, planar: four points in a plane, no three
collinear and none in the triangle of the others, are the vertices of a convex
quadrilateral in one of six labelled orders (`convex_four`).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- The orientation of three points of the plane. -/
def orient2 (x0 y0 x1 y1 x2 y2 : ℝ) : ℝ := (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)

theorem convQuad_of_orient {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ}
    (h012 : 0 < orient2 x0 y0 x1 y1 x2 y2) (h013 : 0 < orient2 x0 y0 x1 y1 x3 y3)
    (h023 : 0 < orient2 x0 y0 x2 y2 x3 y3) (h123 : 0 < orient2 x1 y1 x2 y2 x3 y3) :
    ConvQuad x0 y0 x1 y1 x2 y2 x3 y3 := by
  unfold orient2 at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- No point among four lies in the triangle of the other three. -/
def NotInTri (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) : Prop :=
  ¬ ∃ t0 t1 t2 : ℝ, 0 ≤ t0 ∧ 0 ≤ t1 ∧ 0 ≤ t2 ∧ t0 + t1 + t2 = 1 ∧
    x3 = t0 * x0 + t1 * x1 + t2 * x2 ∧ y3 = t0 * y0 + t1 * y1 + t2 * y2

/-- If the orientations say that `3` is inside the triangle `0, 1, 2`, it is. -/
theorem inTri_of_orient {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ} (h : orient2 x0 y0 x1 y1 x2 y2 ≠ 0)
    (h0 : 0 ≤ orient2 x1 y1 x2 y2 x3 y3 / orient2 x0 y0 x1 y1 x2 y2)
    (h1 : 0 ≤ -orient2 x0 y0 x2 y2 x3 y3 / orient2 x0 y0 x1 y1 x2 y2)
    (h2 : 0 ≤ orient2 x0 y0 x1 y1 x3 y3 / orient2 x0 y0 x1 y1 x2 y2) :
    ¬ NotInTri x0 y0 x1 y1 x2 y2 x3 y3 := by
  intro hn
  apply hn
  refine ⟨_, _, _, h0, h1, h2, ?_, ?_, ?_⟩ <;> field_simp <;> unfold orient2 at * <;> ring

theorem orient2_identity (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) :
    orient2 x1 y1 x2 y2 x3 y3 - orient2 x0 y0 x2 y2 x3 y3 + orient2 x0 y0 x1 y1 x3 y3 -
      orient2 x0 y0 x1 y1 x2 y2 = 0 := by
  unfold orient2; ring

set_option maxHeartbeats 4000000 in
/-- **Four points in convex position.**  No three collinear and none in the
triangle of the others: a convex quadrilateral in one of the six labelled
orders starting at `0`. -/
theorem convex_four {x0 y0 x1 y1 x2 y2 x3 y3 : ℝ}
    (hA : orient2 x0 y0 x1 y1 x2 y2 ≠ 0) (hB : orient2 x0 y0 x1 y1 x3 y3 ≠ 0)
    (hC : orient2 x0 y0 x2 y2 x3 y3 ≠ 0) (hD : orient2 x1 y1 x2 y2 x3 y3 ≠ 0)
    (hn3 : NotInTri x0 y0 x1 y1 x2 y2 x3 y3) (hn2 : NotInTri x0 y0 x1 y1 x3 y3 x2 y2)
    (hn1 : NotInTri x0 y0 x2 y2 x3 y3 x1 y1) (hn0 : NotInTri x1 y1 x2 y2 x3 y3 x0 y0) :
    ConvQuad x0 y0 x1 y1 x2 y2 x3 y3 ∨ ConvQuad x0 y0 x3 y3 x2 y2 x1 y1 ∨
    ConvQuad x0 y0 x2 y2 x1 y1 x3 y3 ∨ ConvQuad x0 y0 x3 y3 x1 y1 x2 y2 ∨
    ConvQuad x0 y0 x1 y1 x3 y3 x2 y2 ∨ ConvQuad x0 y0 x2 y2 x3 y3 x1 y1 := by
  have hid := orient2_identity x0 y0 x1 y1 x2 y2 x3 y3
  -- the permuted orientations
  have p021 : orient2 x0 y0 x2 y2 x1 y1 = -orient2 x0 y0 x1 y1 x2 y2 := by unfold orient2; ring
  have p032 : orient2 x0 y0 x3 y3 x2 y2 = -orient2 x0 y0 x2 y2 x3 y3 := by unfold orient2; ring
  have p031 : orient2 x0 y0 x3 y3 x1 y1 = -orient2 x0 y0 x1 y1 x3 y3 := by unfold orient2; ring
  have p321 : orient2 x3 y3 x2 y2 x1 y1 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p213 : orient2 x2 y2 x1 y1 x3 y3 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p132 : orient2 x1 y1 x3 y3 x2 y2 = -orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p231 : orient2 x2 y2 x3 y3 x1 y1 = orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  have p230 : orient2 x2 y2 x3 y3 x0 y0 = orient2 x0 y0 x2 y2 x3 y3 := by unfold orient2; ring
  have p130 : orient2 x1 y1 x3 y3 x0 y0 = orient2 x0 y0 x1 y1 x3 y3 := by unfold orient2; ring
  have p120 : orient2 x1 y1 x2 y2 x0 y0 = orient2 x0 y0 x1 y1 x2 y2 := by unfold orient2; ring
  have p312 : orient2 x3 y3 x1 y1 x2 y2 = orient2 x1 y1 x2 y2 x3 y3 := by unfold orient2; ring
  rcases lt_or_gt_of_ne hA with a | a <;> rcases lt_or_gt_of_ne hB with b | b <;>
    rcases lt_or_gt_of_ne hC with c | c <;> rcases lt_or_gt_of_ne hD with d | d
  all_goals first
    | exact Or.inl (convQuad_of_orient (by linarith) (by linarith) (by linarith) (by linarith))
    | exact Or.inr (Or.inl (convQuad_of_orient (by rw [p032]; linarith) (by rw [p031]; linarith)
        (by rw [p021]; linarith) (by rw [p321]; linarith)))
    | exact Or.inr (Or.inr (Or.inl (convQuad_of_orient (by rw [p021]; linarith) (by linarith)
        (by linarith) (by rw [p213]; linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (convQuad_of_orient (by rw [p031]; linarith)
        (by rw [p032]; linarith) (by linarith) (by rw [p312]; linarith)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (convQuad_of_orient (by linarith) (by linarith)
        (by rw [p032]; linarith) (by rw [p132]; linarith))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (convQuad_of_orient (by linarith)
        (by rw [p021]; linarith) (by rw [p031]; linarith) (by rw [p231]; linarith))))))
    | exact absurd hn3 (inTri_of_orient hA (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
    | exact absurd hn2 (inTri_of_orient hB (by rw [p132]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p032]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
    | exact absurd hn1 (inTri_of_orient hC (by rw [p231]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p031]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
        (by rw [p021]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))))
    | exact absurd hn0 (inTri_of_orient hD (by rw [p230]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))) (by rw [p130]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith)))
        (by rw [p120]; (first | exact div_nonneg (by linarith) (by linarith) | exact div_nonneg_of_nonpos (by linarith) (by linarith))))

/-! ### Lifting planar facts to `ℝ³` -/

theorem oblPt_comb (O r1 r2 : ℝ²) {t0 t1 t2 : ℝ} (hs : t0 + t1 + t2 = 1)
    (a0 b0 z0 a1 b1 z1 a2 b2 z2 : ℝ) :
    oblPt O r1 r2 (t0 * a0 + t1 * a1 + t2 * a2) (t0 * b0 + t1 * b1 + t2 * b2)
      (t0 * z0 + t1 * z1 + t2 * z2) =
    t0 • oblPt O r1 r2 a0 b0 z0 + t1 • oblPt O r1 r2 a1 b1 z1 + t2 • oblPt O r1 r2 a2 b2 z2 := by
  ext j; fin_cases j <;> simp [oblPt]
  · linear_combination (-(O 0)) * hs
  · linear_combination (-(O 1)) * hs

theorem comb_mem_convexHull {S : Set ℝ³} {p0 p1 p2 : ℝ³} (h0 : p0 ∈ S) (h1 : p1 ∈ S) (h2 : p2 ∈ S)
    {t0 t1 t2 : ℝ} (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hs : t0 + t1 + t2 = 1) :
    t0 • p0 + t1 • p1 + t2 • p2 ∈ convexHull ℝ S := by
  have hc := convex_convexHull ℝ S
  by_cases h : t0 + t1 = 0
  · have e0 : t0 = 0 := by linarith
    have e1 : t1 = 0 := by linarith
    have e2 : t2 = 1 := by linarith
    subst e0 e1 e2; simpa using subset_convexHull ℝ S h2
  · have hpos : 0 < t0 + t1 := lt_of_le_of_ne (by linarith) (Ne.symm h)
    have hq : (t0 / (t0 + t1)) • p0 + (t1 / (t0 + t1)) • p1 ∈ convexHull ℝ S :=
      hc (subset_convexHull ℝ S h0) (subset_convexHull ℝ S h1) (div_nonneg ht0 hpos.le)
        (div_nonneg ht1 hpos.le) (by field_simp)
    have := hc hq (subset_convexHull ℝ S h2) hpos.le ht2 hs
    convert this using 1
    simp only [smul_add, smul_smul]
    congr 2 <;> field_simp

/-- Three points of the first ray's plane with zero orientation are collinear. -/
theorem orient_ne_of_frame1 {O r1 r2 : ℝ²} {ai zi aj zj ak zk : ℝ} (hij : ai ≠ aj)
    (h : ∀ c : ℝ, oblPt O r1 r2 ak 0 zk - oblPt O r1 r2 ai 0 zi ≠
      c • (oblPt O r1 r2 aj 0 zj - oblPt O r1 r2 ai 0 zi)) :
    orient2 ai zi aj zj ak zk ≠ 0 := by
  intro h0
  have hd : aj - ai ≠ 0 := sub_ne_zero.mpr hij.symm
  apply h ((ak - ai) / (aj - ai))
  unfold orient2 at h0
  ext j; fin_cases j <;> simp [oblPt] <;> field_simp
  linear_combination h0

/-- The same on the second ray's plane. -/
theorem orient_ne_of_frame2 {O r1 r2 : ℝ²} {bi zi bj zj bk zk : ℝ} (hij : bi ≠ bj)
    (h : ∀ c : ℝ, oblPt O r1 r2 0 bk zk - oblPt O r1 r2 0 bi zi ≠
      c • (oblPt O r1 r2 0 bj zj - oblPt O r1 r2 0 bi zi)) :
    orient2 bi zi bj zj bk zk ≠ 0 := by
  intro h0
  have hd : bj - bi ≠ 0 := sub_ne_zero.mpr hij.symm
  apply h ((bk - bi) / (bj - bi))
  unfold orient2 at h0
  ext j; fin_cases j <;> simp [oblPt] <;> field_simp
  linear_combination h0

/-- A point of the first ray's plane inside the triangle of three others lies
in their convex hull in `ℝ³`. -/
theorem notInTri_of_frame1 {O r1 r2 : ℝ²} {S : Set ℝ³} {a0 z0 a1 z1 a2 z2 a3 z3 : ℝ}
    (hnot : oblPt O r1 r2 a3 0 z3 ∉ convexHull ℝ S) (h0 : oblPt O r1 r2 a0 0 z0 ∈ S)
    (h1 : oblPt O r1 r2 a1 0 z1 ∈ S) (h2 : oblPt O r1 r2 a2 0 z2 ∈ S) :
    NotInTri a0 z0 a1 z1 a2 z2 a3 z3 := by
  rintro ⟨t0, t1, t2, ht0, ht1, ht2, hs, ea, ez'⟩
  apply hnot
  have e := oblPt_comb O r1 r2 hs a0 0 z0 a1 0 z1 a2 0 z2
  simp only [mul_zero, add_zero] at e
  rw [ea, ez', e]
  exact comb_mem_convexHull h0 h1 h2 ht0 ht1 ht2 hs

theorem notInTri_of_frame2 {O r1 r2 : ℝ²} {S : Set ℝ³} {b0 z0 b1 z1 b2 z2 b3 z3 : ℝ}
    (hnot : oblPt O r1 r2 0 b3 z3 ∉ convexHull ℝ S) (h0 : oblPt O r1 r2 0 b0 z0 ∈ S)
    (h1 : oblPt O r1 r2 0 b1 z1 ∈ S) (h2 : oblPt O r1 r2 0 b2 z2 ∈ S) :
    NotInTri b0 z0 b1 z1 b2 z2 b3 z3 := by
  rintro ⟨t0, t1, t2, ht0, ht1, ht2, hs, eb, ez'⟩
  apply hnot
  have e := oblPt_comb O r1 r2 hs 0 b0 z0 0 b1 z1 0 b2 z2
  simp only [mul_zero, add_zero] at e
  rw [eb, ez', e]
  exact comb_mem_convexHull h0 h1 h2 ht0 ht1 ht2 hs

set_option maxHeartbeats 4000000 in
/-- **Two quadrilateral facets sharing the vertex `0`, the line of their planes
vertical.**  `0123` and `0456` are facets whose planes contain the vertical line
through `y 0`; the points are extreme, no three collinear, no two vertically
aligned, with distinct heights: Rupert. -/
theorem isRupert_twoQuads_vertical (y : Fin 7 → ℝ³)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 0) = 0 ∧ f (y 0 + ez) = 0 ∧ f (y 1) = 0 ∧ f (y 2) = 0 ∧
      f (y 3) = 0 ∧ f (y 4) < 0 ∧ f (y 5) < 0 ∧ f (y 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 0) = 0 ∧ f (y 0 + ez) = 0 ∧ f (y 4) = 0 ∧ f (y 5) = 0 ∧
      f (y 6) = 0 ∧ f (y 1) < 0 ∧ f (y 2) < 0 ∧ f (y 3) < 0)
    (hext : ∀ i, y i ∉ convexHull ℝ (y '' {j | j ≠ i}))
    (hcol : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → ∀ c : ℝ, y k - y i ≠ c • (y j - y i))
    (hpar : ∀ i j : Fin 7, i ≠ j → y i 0 ≠ y j 0 ∨ y i 1 ≠ y j 1)
    (hZ : Function.Injective fun i => y i 2) : IsRupert (Finset.univ.image y) := by
  obtain ⟨f1, e10, e1z, e11, e12, e13, n14, n15, n16⟩ := hF1
  obtain ⟨f2, e20, e2z, e24, e25, e26, n21, n22, n23⟩ := hF2
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  -- the planes are vertical
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1z e10; simp [ez] at e1z; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2z e20; simp [ez] at e2z; linarith
  have g1 : ∀ i, f1 (y i) = α1 * (y i 0 - y 0 0) + β1 * (y i 1 - y 0 1) := by
    intro i; have := e10; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ i, f2 (y i) = α2 * (y i 0 - y 0 0) + β2 * (y i 1 - y 0 1) := by
    intro i; have := e20; rw [h2, hγ2] at this ⊢; linarith
  -- the frame
  set O : ℝ² := !₂[y 0 0, y 0 1] with hO
  set r1 : ℝ² := !₂[y 1 0 - y 0 0, y 1 1 - y 0 1] with hr1
  set r2 : ℝ² := !₂[y 4 0 - y 0 0, y 4 1 - y 0 1] with hr2
  have q11 := g1 1; have q14 := g1 4; have q21 := g2 1; have q24 := g2 4
  rw [e11] at q11; rw [e24] at q24
  replace q11 := q11.symm
  replace q24 := q24.symm
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : (α1 * (y 4 0 - y 0 0) + β1 * (y 4 1 - y 0 1)) * (y 1 0 - y 0 0) = 0 := by
      linear_combination (y 4 0 - y 0 0) * q11 + β1 * hρ0
    have k1 : (α1 * (y 4 0 - y 0 0) + β1 * (y 4 1 - y 0 1)) * (y 1 1 - y 0 1) = 0 := by
      linear_combination (y 4 1 - y 0 1) * q11 - α1 * hρ0
    have hn : α1 * (y 4 0 - y 0 0) + β1 * (y 4 1 - y 0 1) ≠ 0 := by rw [← q14]; exact n14.ne
    have r10 := (mul_eq_zero.mp k0).resolve_left hn
    have r11 := (mul_eq_zero.mp k1).resolve_left hn
    rw [r10, r11] at q21; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : Fin 7 → ℝ := fun i => cross2 !₂[y i 0 - y 0 0, y i 1 - y 0 1] r2 / ρ with ha
  set b : Fin 7 → ℝ := fun i => cross2 r1 !₂[y i 0 - y 0 0, y i 1 - y 0 1] / ρ with hb
  have hxy : ∀ i, y i 0 - y 0 0 = a i * r1 0 + b i * r2 0 ∧ y i 1 - y 0 1 = a i * r1 1 + b i * r2 1 := by
    intro i
    obtain ⟨c0, c1⟩ := cramer2 !₂[y i 0 - y 0 0, y i 1 - y 0 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ i, y i = oblPt O r1 r2 (a i) (b i) (y i 2) := by
    intro i; obtain ⟨c0, c1⟩ := hxy i
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  -- the facet functionals in the frame
  have G1 : ∀ i, f1 (y i) = b i * (α1 * r2 0 + β1 * r2 1) := by
    intro i; rw [g1 i, (hxy i).1, (hxy i).2]
    have : α1 * r1 0 + β1 * r1 1 = 0 := by simp only [hr1]; simp; linarith
    linear_combination a i * this
  have G2 : ∀ i, f2 (y i) = a i * (α2 * r1 0 + β2 * r1 1) := by
    intro i; rw [g2 i, (hxy i).1, (hxy i).2]
    have : α2 * r2 0 + β2 * r2 1 = 0 := by simp only [hr2]; simp; linarith
    linear_combination b i * this
  have hd1 : α1 * r2 0 + β1 * r2 1 < 0 := by simp only [hr2]; simp; linarith
  have hd2 : α2 * r1 0 + β2 * r1 1 < 0 := by simp only [hr1]; simp; linarith
  have hb0 : ∀ i, f1 (y i) = 0 → b i = 0 := fun i h => by
    rw [G1] at h; exact (mul_eq_zero.mp h).resolve_right hd1.ne
  have ha0 : ∀ i, f2 (y i) = 0 → a i = 0 := fun i h => by
    rw [G2] at h; exact (mul_eq_zero.mp h).resolve_right hd2.ne
  have hapos : ∀ i, f2 (y i) < 0 → 0 < a i := fun i h => by
    rw [G2] at h; nlinarith
  have hbpos : ∀ i, f1 (y i) < 0 → 0 < b i := fun i h => by
    rw [G1] at h; nlinarith
  have ha00 : a 0 = 0 := by simp [ha, cross2]
  have hb00 : b 0 = 0 := by simp [hb, cross2]
  have b1 := hb0 1 e11; have b2 := hb0 2 e12; have b3 := hb0 3 e13
  have a4 := ha0 4 e24; have a5 := ha0 5 e25; have a6 := ha0 6 e26
  have pa1 := hapos 1 n21; have pa2 := hapos 2 n22; have pa3 := hapos 3 n23
  have pb4 := hbpos 4 n14; have pb5 := hbpos 5 n15; have pb6 := hbpos 6 n16
  -- the points in the frame
  have E0 : y 0 = oblPt O r1 r2 0 0 (y 0 2) := by conv_lhs => rw [hy 0, ha00, hb00]
  have E1 : ∀ i, b i = 0 → y i = oblPt O r1 r2 (a i) 0 (y i 2) := fun i h => by
    conv_lhs => rw [hy i, h]
  have E2 : ∀ i, a i = 0 → y i = oblPt O r1 r2 0 (b i) (y i 2) := fun i h => by
    conv_lhs => rw [hy i, h]
  -- distinct coordinates along each ray
  have dA : ∀ i j, i ≠ j → b i = 0 → b j = 0 → a i ≠ a j := by
    intro i j hij hbi hbj e
    obtain ⟨c0, c1⟩ := hxy i; obtain ⟨d0, d1⟩ := hxy j
    rw [hbi, e] at c0 c1; rw [hbj] at d0 d1
    rcases hpar i j hij with h | h <;> apply h <;> linarith
  have dB : ∀ i j, i ≠ j → a i = 0 → a j = 0 → b i ≠ b j := by
    intro i j hij hai haj e
    obtain ⟨c0, c1⟩ := hxy i; obtain ⟨d0, d1⟩ := hxy j
    rw [hai, e] at c0 c1; rw [haj] at d0 d1
    rcases hpar i j hij with h | h <;> apply h <;> linarith
  -- the two quadrilaterals are convex in their planes
  have hQ1 : ConvQuad6 (y 0 2) (a 1) (y 1 2) (a 2) (y 2 2) (a 3) (y 3 2) := by
    have col : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → b i = 0 → b j = 0 → b k = 0 →
        a i ≠ a j → orient2 (a i) (y i 2) (a j) (y j 2) (a k) (y k 2) ≠ 0 := by
      intro i j k hij hik hjk hbi hbj hbk hne
      apply orient_ne_of_frame1 hne
      intro c; rw [← E1 i hbi, ← E1 j hbj, ← E1 k hbk]; exact hcol i j k hij hik hjk c
    have nt : ∀ i j k l : Fin 7, j ≠ i → k ≠ i → l ≠ i → b i = 0 → b j = 0 → b k = 0 →
        b l = 0 → NotInTri (a j) (y j 2) (a k) (y k 2) (a l) (y l 2) (a i) (y i 2) := by
      intro i j k l hj hk hl hbi hbj hbk hbl
      apply notInTri_of_frame1 (S := y '' {m | m ≠ i})
      · rw [← E1 i hbi]; exact hext i
      · rw [← E1 j hbj]; exact ⟨j, hj, rfl⟩
      · rw [← E1 k hbk]; exact ⟨k, hk, rfl⟩
      · rw [← E1 l hbl]; exact ⟨l, hl, rfl⟩
    have := convex_four (col 0 1 2 (by decide) (by decide) (by decide) hb00 b1 b2 (by rw [ha00]; exact pa1.ne))
      (col 0 1 3 (by decide) (by decide) (by decide) hb00 b1 b3 (by rw [ha00]; exact pa1.ne))
      (col 0 2 3 (by decide) (by decide) (by decide) hb00 b2 b3 (by rw [ha00]; exact pa2.ne))
      (col 1 2 3 (by decide) (by decide) (by decide) b1 b2 b3 (dA 1 2 (by decide) b1 b2))
      (nt 3 0 1 2 (by decide) (by decide) (by decide) b3 hb00 b1 b2)
      (nt 2 0 1 3 (by decide) (by decide) (by decide) b2 hb00 b1 b3)
      (nt 1 0 2 3 (by decide) (by decide) (by decide) b1 hb00 b2 b3)
      (nt 0 1 2 3 (by decide) (by decide) (by decide) hb00 b1 b2 b3)
    rw [ha00] at this; exact this
  have hQ2 : ConvQuad6 (y 0 2) (b 4) (y 4 2) (b 5) (y 5 2) (b 6) (y 6 2) := by
    have col : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → a i = 0 → a j = 0 → a k = 0 →
        b i ≠ b j → orient2 (b i) (y i 2) (b j) (y j 2) (b k) (y k 2) ≠ 0 := by
      intro i j k hij hik hjk hai haj hak hne
      apply orient_ne_of_frame2 hne
      intro c; rw [← E2 i hai, ← E2 j haj, ← E2 k hak]; exact hcol i j k hij hik hjk c
    have nt : ∀ i j k l : Fin 7, j ≠ i → k ≠ i → l ≠ i → a i = 0 → a j = 0 → a k = 0 →
        a l = 0 → NotInTri (b j) (y j 2) (b k) (y k 2) (b l) (y l 2) (b i) (y i 2) := by
      intro i j k l hj hk hl hai haj hak hal
      apply notInTri_of_frame2 (S := y '' {m | m ≠ i})
      · rw [← E2 i hai]; exact hext i
      · rw [← E2 j haj]; exact ⟨j, hj, rfl⟩
      · rw [← E2 k hak]; exact ⟨k, hk, rfl⟩
      · rw [← E2 l hal]; exact ⟨l, hl, rfl⟩
    have := convex_four (col 0 4 5 (by decide) (by decide) (by decide) ha00 a4 a5 (by rw [hb00]; exact pb4.ne))
      (col 0 4 6 (by decide) (by decide) (by decide) ha00 a4 a6 (by rw [hb00]; exact pb4.ne))
      (col 0 5 6 (by decide) (by decide) (by decide) ha00 a5 a6 (by rw [hb00]; exact pb5.ne))
      (col 4 5 6 (by decide) (by decide) (by decide) a4 a5 a6 (dB 4 5 (by decide) a4 a5))
      (nt 6 0 4 5 (by decide) (by decide) (by decide) a6 ha00 a4 a5)
      (nt 5 0 4 6 (by decide) (by decide) (by decide) a5 ha00 a4 a6)
      (nt 4 0 5 6 (by decide) (by decide) (by decide) a4 ha00 a5 a6)
      (nt 0 4 5 6 (by decide) (by decide) (by decide) ha00 a4 a5 a6)
    rw [hb00] at this; exact this
  -- the point set in the frame
  have himg : Finset.univ.image y = {y 0, y 1, y 2, y 3, y 4, y 5, y 6} := by
    ext p; simp [Fin.exists_fin_succ, eq_comm]
  rw [himg]
  nth_rewrite 1 [E0]
  rw [E1 1 b1, E1 2 b2, E1 3 b3, E2 4 a4, E2 5 a5, E2 6 a6]
  have hz7 : Function.Injective ![y 0 2, y 1 2, y 2 2, y 3 2, y 4 2, y 5 2, y 6 2] := by
    have : ![y 0 2, y 1 2, y 2 2, y 3 2, y 4 2, y 5 2, y 6 2] = fun i => y i 2 := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact hZ
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · -- negative orientation: exchange the two rays
    have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    have hz7' : Function.Injective ![y 0 2, y 4 2, y 5 2, y 6 2, y 1 2, y 2 2, y 3 2] := by
      have : ![y 0 2, y 4 2, y 5 2, y 6 2, y 1 2, y 2 2, y 3 2] =
          (fun i => y i 2) ∘ ![0, 4, 5, 6, 1, 2, 3] := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact hZ.comp (by decide)
    have key := isRupert_twoQuads_frame O r2 r1 hpos' pb4 pb5 pb6 pa1 pa2 pa3 hQ2 hQ1
      (dB 4 5 (by decide) a4 a5) (dB 4 6 (by decide) a4 a6) (dB 5 6 (by decide) a5 a6)
      (dA 1 2 (by decide) b1 b2) (dA 1 3 (by decide) b1 b3) (dA 2 3 (by decide) b2 b3) hz7'
    simp only [swap] at key
    convert key using 1
    ext p; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact isRupert_twoQuads_frame O r1 r2 hpos pa1 pa2 pa3 pb4 pb5 pb6 hQ1 hQ2
      (dA 1 2 (by decide) b1 b2) (dA 1 3 (by decide) b1 b3) (dA 2 3 (by decide) b2 b3)
      (dB 4 5 (by decide) a4 a5) (dB 4 6 (by decide) a4 a6) (dB 5 6 (by decide) a5 a6) hz7


/-- An affine function vanishing at `p` and `p + e` vanishes on the line. -/
theorem affine_zero_line (f : ℝ³ →ᵃ[ℝ] ℝ) {p e : ℝ³} (h0 : f p = 0) (h1 : f (p + e) = 0) (c : ℝ) :
    f (p + c • e) = 0 := by
  have k1 : f (p + e) = f.linear e + f p := by
    rw [show p + e = e +ᵥ p by rw [vadd_eq_add, add_comm]]; exact f.map_vadd p e
  have kc : f (p + c • e) = f.linear (c • e) + f p := by
    rw [show p + c • e = c • e +ᵥ p by rw [vadd_eq_add, add_comm]]; exact f.map_vadd p (c • e)
  rw [kc, map_smul, smul_eq_mul]
  rw [h0, h1] at k1
  rw [h0]
  have : f.linear e = 0 := by linarith
  rw [this]; ring

set_option maxHeartbeats 4000000 in
/-- **Corollary T1 for two quadrilateral facets sharing a vertex.**  `0123` and
`0456` are facets of the seven extreme points `x`, `e ≠ 0` spans the line of
their planes, no three points are collinear, no segment is parallel to `e`, and
the depths along `e` are distinct: Rupert. -/
theorem isRupert_twoQuads (x : Fin 7 → ℝ³) (e : ℝ³) (he : e ≠ 0)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 0) = 0 ∧ f (x 0 + e) = 0 ∧ f (x 1) = 0 ∧ f (x 2) = 0 ∧
      f (x 3) = 0 ∧ f (x 4) < 0 ∧ f (x 5) < 0 ∧ f (x 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 0) = 0 ∧ f (x 0 + e) = 0 ∧ f (x 4) = 0 ∧ f (x 5) = 0 ∧
      f (x 6) = 0 ∧ f (x 1) < 0 ∧ f (x 2) < 0 ∧ f (x 3) < 0)
    (hext : ∀ i, x i ∉ convexHull ℝ (x '' {j | j ≠ i}))
    (hcol : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → ∀ c : ℝ, x k - x i ≠ c • (x j - x i))
    (hpar : ∀ i j : Fin 7, i ≠ j → ∀ c : ℝ, x j - x i ≠ c • e)
    (hZ : Function.Injective fun i => ⟪x i, e⟫) : IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  rw [Finset.image_image]
  have hgz : ∀ p, g p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • e := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  -- facets transported by the inverse rotation
  have tr : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 0) = 0 → f (x 0 + e) = 0 →
      ∃ f' : ℝ³ →ᵃ[ℝ] ℝ, (∀ i, f' (g (x i)) = f (x i)) ∧ f' (g (x 0) + ez) = 0 := by
    intro f h0 h1
    refine ⟨f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap, fun i => by simp [hgI], ?_⟩
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g (x 0) + ez) =
        f (x 0 + r⁻¹ • e) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 h1 _
  obtain ⟨f1, e10, e1e, e11, e12, e13, n14, n15, n16⟩ := hF1
  obtain ⟨f2, e20, e2e, e24, e25, e26, n21, n22, n23⟩ := hF2
  obtain ⟨f1', hf1', hz1⟩ := tr f1 e10 e1e
  obtain ⟨f2', hf2', hz2⟩ := tr f2 e20 e2e
  refine isRupert_twoQuads_vertical (fun i => g (x i)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨f1', by rw [hf1']; exact e10, hz1, by rw [hf1']; exact e11, by rw [hf1']; exact e12,
      by rw [hf1']; exact e13, by rw [hf1']; exact n14, by rw [hf1']; exact n15,
      by rw [hf1']; exact n16⟩
  · exact ⟨f2', by rw [hf2']; exact e20, hz2, by rw [hf2']; exact e24, by rw [hf2']; exact e25,
      by rw [hf2']; exact e26, by rw [hf2']; exact n21, by rw [hf2']; exact n22,
      by rw [hf2']; exact n23⟩
  · intro i hmem
    apply hext i
    have himg : ((fun j => g (x j)) '' {j | j ≠ i}) = g '' (x '' {j | j ≠ i}) := by
      rw [Set.image_image]
    rw [himg, ← LinearMap.image_convexHull] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    rwa [← hginj hpe]
  · intro i j k hij hik hjk c h
    apply hcol i j k hij hik hjk c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · intro i j hij
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar i j hij ((g (x j - x i)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · intro i j hij
    apply hZ
    simp only [hgz] at hij
    simpa [hr.ne'] using hij

/-! ### Facet-level statement -/

/-- General position for Corollary T1 at two facets `Q1`, `Q2` meeting in `v`:
for the line of their planes (any direction `e ≠ 0` along which supporting
functionals of both vanish from `v`), no segment of `V` is parallel to it and the
depths along it are distinct. -/
def TriGen (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      Set.InjOn (fun p : ℝ³ => ⟪p, e⟫) (V : Set ℝ³)

set_option maxHeartbeats 4000000 in
/-- **Two quadrilateral facets sharing one vertex** (Corollary T1 of
`FEWER-FACES-PROOFS.md` §7): seven extreme points in general position with two
quadrilateral facets meeting in a single vertex (so covering all seven points)
are Rupert, given `TriGen` at the line of the two planes. -/
theorem isRupert_of_two_quad_facets_vertex (V : Finset ℝ³) (hV : V.card = 7)
    (hext : ∀ y ∈ V, y ∉ convexHull ℝ ((V.erase y : Finset ℝ³) : Set ℝ³)) (hgen : GenPos V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4)
    (h1f : IsFacet V Q1) (h2f : IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : TriGen V Q1 Q2 v) : IsRupert V := by
  classical
  -- the two quadrilaterals cover `V`
  have hcov : Q1 ∪ Q2 = V := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset h1V h2V)
    have := Finset.card_union_add_card_inter Q1 Q2
    rw [hint, Finset.card_singleton, h1c, h2c] at this
    rw [hV]; omega
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  -- an enumeration with `v` first
  obtain ⟨e0, he0, himg0, hQ0⟩ := exists_enum_four_first V Q1 hV h1V h1c
  obtain ⟨k, hk⟩ : ∃ k : Fin 7, e0 k = v := by
    have : v ∈ Finset.univ.image e0 := himg0 ▸ h1V hv1
    simpa using this
  have hk4 : k.val < 4 := (hQ0 k).mp (hk ▸ hv1)
  set σ : Equiv.Perm (Fin 7) := Equiv.swap 0 k with hσ
  set x : Fin 7 → ℝ³ := e0 ∘ σ with hx
  have hxinj : Function.Injective x := he0.comp σ.injective
  have himg : Finset.univ.image x = V := by
    rw [← himg0]; ext p; simp only [Finset.mem_image, Finset.mem_univ, true_and, hx,
      Function.comp_apply]
    exact ⟨fun ⟨i, h⟩ => ⟨σ i, h⟩, fun ⟨i, h⟩ => ⟨σ.symm i, by simp [h]⟩⟩
  have hx0 : x 0 = v := by simp [hx, hσ, hk]
  have hσ4 : ∀ i : Fin 7, (σ i).val < 4 ↔ i.val < 4 := by
    intro i
    rcases eq_or_ne i 0 with rfl | h0
    · rw [hσ, Equiv.swap_apply_left]; constructor <;> intro <;> omega
    rcases eq_or_ne i k with rfl | hik
    · rw [hσ, Equiv.swap_apply_right]; constructor <;> intro <;> omega
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne h0 hik]
  have hxQ1 : ∀ i : Fin 7, x i ∈ Q1 ↔ i.val < 4 := by
    intro i; rw [hx, Function.comp_apply, hQ0, hσ4]
  have hxV : ∀ i, x i ∈ V := fun i => himg ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hxQ2 : ∀ i : Fin 7, i.val ≥ 4 → x i ∈ Q2 := by
    intro i hi
    have h := hxV i; rw [← hcov] at h
    rcases Finset.mem_union.mp h with h | h
    · exact absurd ((hxQ1 i).mp h) (by omega)
    · exact h
  have hxnQ2 : ∀ i : Fin 7, i ≠ 0 → i.val < 4 → x i ∉ Q2 := by
    intro i hi0 hi4 h
    have : x i ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨(hxQ1 i).mpr hi4, h⟩
    rw [hint, Finset.mem_singleton, ← hx0] at this
    exact hi0 (hxinj this)
  -- the facet functionals and the line of the planes
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨K1, α1, β1, γ1, hf1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, hf2⟩ := affine_xyz f2
  set e : ℝ³ := !₂[β1 * γ2 - γ1 * β2, γ1 * α2 - α1 * γ2, α1 * β2 - β1 * α2] with he
  have dif : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (K α β γ : ℝ), (∀ p, f p = K + α * p 0 + β * p 1 + γ * p 2) →
      ∀ p q, f q - f p = α * (q 0 - p 0) + β * (q 1 - p 1) + γ * (q 2 - p 2) := by
    intro f K α β γ h p q; rw [h, h]; ring
  have e1 : f1 (v + e) = 0 := by
    have := dif f1 K1 α1 β1 γ1 hf1 v (v + e)
    rw [z1 v hv1] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have e2 : f2 (v + e) = 0 := by
    have := dif f2 K2 α2 β2 γ2 hf2 v (v + e)
    rw [z2 v hv2] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have hne : e ≠ 0 := by
    intro h0
    have c0 := congrArg (fun p : ℝ³ => p 0) h0
    have c1 := congrArg (fun p : ℝ³ => p 1) h0
    have c2 := congrArg (fun p : ℝ³ => p 2) h0
    simp [he] at c0 c1 c2
    -- `f1` is negative at `x 4`, `f2` vanishes at `x 1` too: the gradients would be parallel
    have d14 := dif f1 K1 α1 β1 γ1 hf1 v (x 4)
    have d21 := dif f2 K2 α2 β2 γ2 hf2 v (x 1)
    have d11 := dif f1 K1 α1 β1 γ1 hf1 v (x 1)
    rw [z1 v hv1, sub_zero] at d14
    rw [z1 v hv1, z1 (x 1) ((hxQ1 1).mpr (by decide)), sub_zero] at d11
    have hn2 : f2 (x 1) < 0 := n2 (x 1) (hxV 1) (hxnQ2 1 (by decide) (by decide))
    rw [z2 v hv2, sub_zero] at d21
    -- (n1 · d4) (n2 · d1) = (n1 · d1)(n2 · d4) + (cross terms) = 0
    have key : (f1 (x 4)) * (f2 (x 1)) = 0 := by
      rw [d14, d21]
      have := d11
      linear_combination (α2 * ((x 4) 0 - v 0) + β2 * ((x 4) 1 - v 1) + γ2 * ((x 4) 2 - v 2)) * this.symm +
        ((x 1 1 - v 1) * (x 4 0 - v 0) - (x 1 0 - v 0) * (x 4 1 - v 1)) * c2 +
        ((x 1 2 - v 2) * (x 4 1 - v 1) - (x 1 1 - v 1) * (x 4 2 - v 2)) * c0 +
        ((x 1 0 - v 0) * (x 4 2 - v 2) - (x 1 2 - v 2) * (x 4 0 - v 0)) * c1
    have hn1 : f1 (x 4) < 0 := n1 (x 4) (hxV 4) (by rw [hxQ1]; decide)
    nlinarith
  obtain ⟨hpar, hZ⟩ := hT f1 f2 z1 n1 z2 n2 e hne e1 e2
  rw [← himg]
  refine isRupert_twoQuads x e hne ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨f1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx0]; exact z1 v hv1
    · rw [hx0]; exact e1
    all_goals first
      | exact z1 _ ((hxQ1 _).mpr (by decide))
      | exact n1 _ (hxV _) (by rw [hxQ1]; decide)
  · refine ⟨f2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx0]; exact z2 v hv2
    · rw [hx0]; exact e2
    all_goals first
      | exact z2 _ (hxQ2 _ (by decide))
      | exact n2 _ (hxV _) (hxnQ2 _ (by decide) (by decide))
  · intro i hmem
    apply hext (x i) (hxV i)
    have : x '' {j | j ≠ i} = ((V.erase (x i) : Finset ℝ³) : Set ℝ³) := by
      ext p; simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_erase, Set.mem_sdiff,
        Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨hxV j, fun h => hj (hxinj h)⟩
      · rintro ⟨hp, hpi⟩
        rw [← himg] at hp; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
        exact ⟨j, fun h => hpi (h ▸ rfl), rfl⟩
    rwa [this] at hmem
  · intro i j k hij hik hjk c
    exact ((hgen (x i) (hxV i) (x k) (hxV k) (x i) (hxV i) (x j) (hxV j)
      (fun h => hik (hxinj h)) (fun h => hij (hxinj h)) (by
        intro h
        have : x k ∈ ({x i, x j} : Finset ℝ³) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h'
        · exact hik (hxinj h').symm
        · exact hjk (hxinj h').symm)).1 c)
  · intro i j hij c
    exact hpar (x i) (hxV i) (x j) (hxV j) (fun h => hij (hxinj h)) c
  · intro i j h
    exact hxinj (hZ (hxV i) (hxV j) h)

/-- `isRupert_of_two_quad_facets_vertex` for a solid hull, without assuming
that all seven points are extreme. -/
theorem isRupert_of_two_quad_facets_vertex_solid (V : Finset ℝ³) (hV : V.card = 7)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hgen : GenPos V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1c : Q1.card = 4) (h2c : Q2.card = 4)
    (h1f : IsFacet V Q1) (h2f : IsFacet V Q2) (v : ℝ³) (hint : Q1 ∩ Q2 = {v})
    (hT : TriGen V Q1 Q2 v) : IsRupert V := by
  classical
  by_cases hext : ∃ x ∈ V, x ∈ convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³)
  · obtain ⟨x, hx, hxh⟩ := hext
    have hhull : convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³) = convexHull ℝ (V : Set ℝ³) := by
      apply le_antisymm (convexHull_mono (by simp))
      refine convexHull_min (fun y hy => ?_) (convex_convexHull ℝ _)
      by_cases hyx : y = x
      · rw [hyx]; exact hxh
      · exact subset_convexHull ℝ _ (by simpa [hyx] using hy)
    refine isRupert_of_convexHull_eq hhull (isRupert_of_card_le_six _ ?_ ?_)
    · rw [Finset.card_erase_of_mem hx]; omega
    · rw [hhull]; exact hsol
  push Not at hext
  exact isRupert_of_two_quad_facets_vertex V hV hext hgen Q1 Q2 h1V h2V h1c h2c h1f h2f v hint hT

end Minimality

end
