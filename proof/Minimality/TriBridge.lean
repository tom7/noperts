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

/-! ### Lifting planar facts to `ℝ³` -/

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

/-! ### Facet-level statement -/

/-- No three of the points of `V` are collinear (the part of `GenPos` that
Lemma T and Corollary T1 use). -/
def NoThreeCollinear (V : Finset ℝ³) : Prop :=
  ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p)

/-- Seven points with a solid hull, one of them in the hull of the others: Rupert
(the hull is that of six points). -/
theorem isRupert_of_mem_convexHull_erase {V : Finset ℝ³} (hV : V.card = 7)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) {x : ℝ³} (hx : x ∈ V)
    (hxh : x ∈ convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³)) : IsRupert V := by
  have hhull : convexHull ℝ ((V.erase x : Finset ℝ³) : Set ℝ³) = convexHull ℝ (V : Set ℝ³) := by
    apply le_antisymm (convexHull_mono (by simp))
    refine convexHull_min (fun y hy => ?_) (convex_convexHull ℝ _)
    by_cases hyx : y = x
    · rw [hyx]; exact hxh
    · exact subset_convexHull ℝ _ (by simpa [hyx] using hy)
  refine isRupert_of_convexHull_eq hhull (isRupert_of_card_le_six _ ?_ ?_)
  · rw [Finset.card_erase_of_mem hx]; omega
  · rw [hhull]; exact hsol

/-- Of three distinct collinear points of `V`, the middle one lies in the hull of
the others. -/
theorem exists_mem_convexHull_erase_of_collinear {V : Finset ℝ³} {p q r : ℝ³} (hp : p ∈ V)
    (hq : q ∈ V) (hr : r ∈ V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {c : ℝ}
    (h : r - p = c • (q - p)) : ∃ y ∈ V, y ∈ convexHull ℝ ((V.erase y : Finset ℝ³) : Set ℝ³) := by
  have hr' : r = p + c • (q - p) := by rw [← h]; abel
  have mem : ∀ {y u w : ℝ³}, u ∈ V → w ∈ V → u ≠ y → w ≠ y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • u + b • w = y → y ∈ convexHull ℝ ((V.erase y : Finset ℝ³) : Set ℝ³) := by
    intro y u w hu hw huy hwy a b ha hb hab e
    exact segment_subset_convexHull (by simp [huy, hu]) (by simp [hwy, hw]) ⟨a, b, ha, hb, hab, e⟩
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- `p` lies between `q` and `r`
    refine ⟨p, hp, mem hq hr (Ne.symm hpq) (Ne.symm hpr) (-c / (1 - c)) (1 / (1 - c))
      (div_nonneg (by linarith) (by linarith)) (div_nonneg (by norm_num) (by linarith))
      (by rw [← add_div, neg_add_eq_sub, div_self (by linarith)]) ?_⟩
    rw [hr']
    have h1 : (1 - c) ≠ 0 := by linarith
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring
  · subst hc; rw [zero_smul, sub_eq_zero] at h; exact absurd h.symm hpr
  rcases lt_trichotomy c 1 with hc1 | hc1 | hc1
  · -- `r` lies between `p` and `q`
    refine ⟨r, hr, mem hp hq hpr hqr (1 - c) c (by linarith) hc.le (by ring) ?_⟩
    rw [hr']; module
  · subst hc1; rw [one_smul, sub_left_inj] at h; exact absurd h.symm hqr
  · -- `q` lies between `p` and `r`
    refine ⟨q, hq, mem hp hr hpq (Ne.symm hqr) (1 - 1 / c) (1 / c)
      (by rw [sub_nonneg, div_le_one (by linarith)]; linarith) (div_nonneg (by norm_num) (by linarith))
      (by ring) ?_⟩
    rw [hr']
    have h1 : c ≠ 0 := by linarith
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp; ring

/-- In seven points with a solid hull that are not Rupert, no three are
collinear. -/
theorem noThreeCollinear_of_not_isRupert {V : Finset ℝ³} (hV : V.card = 7)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hR : ¬ IsRupert V) :
    NoThreeCollinear V := by
  intro p hp q hq r hr hpq hpr hqr c h
  obtain ⟨y, hy, hyh⟩ := exists_mem_convexHull_erase_of_collinear hp hq hr hpq hpr hqr h
  exact hR (isRupert_of_mem_convexHull_erase hV hsol hy hyh)

/-- Strong general position at two facets `Q1`, `Q2` meeting in `v` (all depths
distinct; the theorems use the weaker `TriGenFar`, see `TriGen.far`):
for the line of their planes (any direction `e ≠ 0` along which supporting
functionals of both vanish from `v`), no segment of `V` is parallel to it and the
depths along it are distinct. -/
def TriGen (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      Set.InjOn (fun p : ℝ³ => ⟪p, e⟫) (V : Set ℝ³)

/-- General position for Lemma T at the line of the planes of two facets `Q1`,
`Q2` (through `v`): no segment between points of `V` is parallel to the line,
and the far ends of the two faces in the shadow (the point of `Q1` where `f2`
is least, the point of `Q2` where `f1` is least) have distinct depths along it.
Weaker than `TriGen` (`TriGen.far`). -/
def TriGenFar (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        ⟪p, e⟫ ≠ ⟪q, e⟫

theorem TriGen.far {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (h : TriGen V Q1 Q2 v) : TriGenFar V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hZ⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq _ _ hd => hpq (hZ (h1V hp) (h2V hq) hd)⟩

end Minimality

end
