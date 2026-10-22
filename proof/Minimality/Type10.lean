module

public import Minimality.TriFacetsEdge
public import Minimality.TieFrame
public import Minimality.ParallelOr
public import Minimality.TriFacetsChord
public import Minimality.EdgeChord

@[expose] public section

/-!
# Type 10 (the capped frustum) is Rupert

Theorem E of `FEWER-FACES-PROOFS.md` §7, by its algebraic proof: with the
facet functionals `fA, fB, fC, fD` of `1245, 1346, 2356, 023` and
`s = fB x0 / fB x2 + fA x0 / fA x3`, the view along the edge `14` has a
triangle shadow if `s < 1` (Lemma T over an edge), and the view along the line
of the planes of `023` and `1245` has one if `s ≥ 1` (Lemma T at a vertex),
by a Cramer identity for `x6` in the frame `x4; x0, x2, x3`.
At `s = 1` the edge `14` is parallel to the line of the second view (the plane
of `023` is parallel to it, `ParallelEdge.lean`), and the view along `14` has
`x0` on its far side: Lemma T′ over the edge (`isRupert_of_facets_edge_chord`),
given `EdgeFar` along `14` there (`FEWER-FACES-PROOFS.md` §23, item (ii)).

The first part of the file is general: Cramer's rule applied to affine
functionals, and the ratio of two affine functionals vanishing on the same
three non-collinear points.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-- The determinant of three vectors in coordinates. -/
def vol3 (a b c : ℝ³) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The cross product in coordinates. -/
noncomputable def crs3 (a b : ℝ³) : ℝ³ :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- **Cramer's rule for an affine functional**: the coordinates of `w - o` in
the frame `a - o, b - o, c - o`, applied to `f`. -/
theorem affine_cramer (f : ℝ³ →ᵃ[ℝ] ℝ) (o a b c w : ℝ³) :
    vol3 (a - o) (b - o) (c - o) * (f w - f o) =
      vol3 (w - o) (b - o) (c - o) * (f a - f o) + vol3 (a - o) (w - o) (c - o) * (f b - f o) +
      vol3 (a - o) (b - o) (w - o) * (f c - f o) := by
  obtain ⟨K, α, β, γ, h⟩ := affine_xyz f
  simp only [h, vol3, PiLp.sub_apply]
  ring

/-- `affine_cramer` in coordinates: the affine coordinates of `w` in the frame
`o; a, b, c` applied to `f`. -/
theorem affine_coord (f : ℝ³ →ᵃ[ℝ] ℝ) (o a b c w : ℝ³) (hΔ : vol3 (a - o) (b - o) (c - o) ≠ 0) :
    f w - f o = vol3 (w - o) (b - o) (c - o) / vol3 (a - o) (b - o) (c - o) * (f a - f o) +
      vol3 (a - o) (w - o) (c - o) / vol3 (a - o) (b - o) (c - o) * (f b - f o) +
      vol3 (a - o) (b - o) (w - o) / vol3 (a - o) (b - o) (c - o) * (f c - f o) := by
  have := affine_cramer f o a b c w
  field_simp
  linear_combination this

/-- An affine functional vanishing at `p, q, r` is proportional to the
determinant with `q - p, r - p`. -/
theorem affine_vanish3 (f : ℝ³ →ᵃ[ℝ] ℝ) {p q r : ℝ³} (hp : f p = 0) (hq : f q = 0) (hr : f r = 0)
    (y w : ℝ³) : vol3 (q - p) (r - p) (w - p) * f y = vol3 (q - p) (r - p) (y - p) * f w := by
  have := affine_cramer f p q r w y
  rw [hp, hq, hr] at this
  simp only [sub_zero, mul_zero, zero_add] at this
  linarith

/-- Three points `p ≠ q`, `r` off the line `p q` give a nonzero determinant
with the cross product. -/
theorem vol3_crs3_pos {p q r : ℝ³} (hpq : p ≠ q) (hcol : ∀ c : ℝ, r - p ≠ c • (q - p)) :
    0 < vol3 (q - p) (r - p) (crs3 (q - p) (r - p)) := by
  set u := q - p with hu
  set v := r - p with hv
  have e : vol3 u v (crs3 u v) = (u 1 * v 2 - u 2 * v 1) ^ 2 + (u 2 * v 0 - u 0 * v 2) ^ 2 +
      (u 0 * v 1 - u 1 * v 0) ^ 2 := by
    simp only [vol3, crs3]; simp; ring
  rw [e]
  by_contra hle
  push Not at hle
  have q0 := sq_nonneg (u 1 * v 2 - u 2 * v 1)
  have q1 := sq_nonneg (u 2 * v 0 - u 0 * v 2)
  have q2 := sq_nonneg (u 0 * v 1 - u 1 * v 0)
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have hu0 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≠ 0 := by
    intro h
    apply hpq
    have r0 := sq_nonneg (u 0); have r1 := sq_nonneg (u 1); have r2 := sq_nonneg (u 2)
    have a0 : u 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have a1 : u 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have a2 : u 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have : u = 0 := by ext i; fin_cases i <;> simp [a0, a1, a2]
    rw [hu] at this; exact (sub_eq_zero.mp this).symm
  apply hcol ((u 0 * v 0 + u 1 * v 1 + u 2 * v 2) / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2))
  ext i; fin_cases i <;> simp <;> field_simp
  · linear_combination (-u 1) * h2 + u 2 * h1
  · linear_combination u 0 * h2 - u 2 * h0
  · linear_combination (-u 0) * h1 + u 1 * h0

/-- **Two affine functionals vanishing on the same three non-collinear points
are proportional**: `f y * g w = f w * g y`. -/
theorem vanish3_ratio (f g : ℝ³ →ᵃ[ℝ] ℝ) {p q r : ℝ³} (hpq : p ≠ q)
    (hcol : ∀ c : ℝ, r - p ≠ c • (q - p))
    (fp : f p = 0) (fq : f q = 0) (fr : f r = 0) (gp : g p = 0) (gq : g q = 0) (gr : g r = 0)
    (y w : ℝ³) : f y * g w = f w * g y := by
  set w0 := p + crs3 (q - p) (r - p)
  have hD := vol3_crs3_pos hpq hcol
  have e0 : w0 - p = crs3 (q - p) (r - p) := by simp [w0]
  have fy := affine_vanish3 f fp fq fr y w0
  have fw := affine_vanish3 f fp fq fr w w0
  have gy := affine_vanish3 g gp gq gr y w0
  have gw := affine_vanish3 g gp gq gr w w0
  rw [e0] at fy fw gy gw
  set D := vol3 (q - p) (r - p) (crs3 (q - p) (r - p))
  have : D * D * (f y * g w) = D * D * (f w * g y) := by
    have k1 : D * D * (f y * g w) = (D * f y) * (D * g w) := by ring
    have k2 : D * D * (f w * g y) = (D * f w) * (D * g y) := by ring
    rw [k1, k2, fy, fw, gy, gw]; ring
  exact mul_left_cancel₀ (mul_pos hD hD).ne' this

/-- The face with index set `P` of the labelled points `x`, from a functional
vanishing exactly on it. -/
theorem isFacet_of_index (x : Fin 7 → ℝ³) (P : Finset (Fin 7)) (f : ℝ³ →ᵃ[ℝ] ℝ)
    (h : ∀ i, (i ∈ P → f (x i) = 0) ∧ (i ∉ P → f (x i) < 0)) :
    IsFacet (univ.image x) (P.image x) := by
  refine ⟨f, fun y hy => ?_, fun y hy hyP => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy; exact (h i).1 hi
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact (h i).2 (fun hi => hyP (Finset.mem_image_of_mem x hi))

set_option maxHeartbeats 4000000 in
/-- **Theorem E (type 10, the capped frustum).** Seven labelled points in general
position with facets `1245, 1346, 2356` (the side quadrilaterals) and `023` (a
cap triangle), given by functionals negative off them, are Rupert, given no
other segment parallel to `14` and a settled tie of the far depths there
(`EdgeTieR`) and `TriGenTri` at the line of the planes of `023` and `1245`
(at the special value where the deciding number is 1, `EdgeFar` along `14`
instead, for Lemma T′ over that edge). -/
theorem isRupert_type10 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x))
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (fA fB fC fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hZ1 : EdgeTieR (univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4) ∨
      EdgeFarP (univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))
    (hT2 : (TriGenTri (univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) ∨
        TriGenFarP (univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2)) ∧
      (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1 →
        EdgeFar (univ.image x) (({1, 2, 4, 5} : Finset (Fin 7)).image x)
          (({1, 3, 4, 6} : Finset (Fin 7)).image x) (x 1) (x 4))) :
    IsRupert (univ.image x) := by
  classical
  set V := univ.image x with hV
  have hxV : ∀ i, x i ∈ V := fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have memQ : ∀ (P : Finset (Fin 7)) i, x i ∈ P.image x ↔ i ∈ P := fun P i => hx.mem_finset_image
  have inter : ∀ P R : Finset (Fin 7), P.image x ∩ R.image x = (P ∩ R).image x :=
    fun P R => (Finset.image_inter P R hx).symm
  -- three distinct points are not collinear
  have ncol : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → ∀ c : ℝ, x k - x i ≠ c • (x j - x i) := by
    intro i j k hij hik hjk c
    exact hgen (x i) (hxV i) (x j) (hxV j) (x k) (hxV k) (fun h => hij (hx h))
      (fun h => hik (hx h)) (fun h => hjk (hx h)) c
  -- the ratio of a facet functional equals that of the given one
  have ratio : ∀ (f g : ℝ³ →ᵃ[ℝ] ℝ) (i j k : Fin 7), i ≠ j → i ≠ k → j ≠ k →
      f (x i) = 0 → f (x j) = 0 → f (x k) = 0 → g (x i) = 0 → g (x j) = 0 → g (x k) = 0 →
      ∀ y w, f w ≠ 0 → g w ≠ 0 → f y / f w = g y / g w := by
    intro f g i j k hij hik hjk fi fj fk gi gj gk y w hfw hgw
    rw [div_eq_div_iff hfw hgw]
    have := vanish3_ratio f g (fun h => hij (hx h)) (ncol i j k hij hik hjk) fi fj fk gi gj gk y w
    linarith
  set QA := ({1, 2, 4, 5} : Finset (Fin 7)).image x
  set QB := ({1, 3, 4, 6} : Finset (Fin 7)).image x
  set QD := ({0, 2, 3} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  rcases lt_or_ge (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3)) 1 with hlt | hgt
  · -- the view along the edge `14`
    refine isRupert_of_facets_edge_tieR_or V hgen QA QB (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fB hB) (x 1) (x 4) (fun h => by have := hx h; omega) ?_
      ⟨x 2, (memQ _ 2).mpr (by decide), by rw [memQ]; decide⟩
      ⟨x 3, (memQ _ 3).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_ hsol
    · rw [inter, show ({1, 2, 4, 5} ∩ {1, 3, 4, 6} : Finset (Fin 7)) = {1, 4} by decide]
      simp [Finset.image_insert]
    refine ⟨x 2, (memQ _ 2).mpr (by decide), x 3, (memQ _ 3).mpr (by decide),
      by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 0 := by fin_cases i <;> simp_all
    subst hi
    have e2 : f2 (x 0) / f2 (x 2) = fB (x 0) / fB (x 2) :=
      ratio f2 fB 1 3 4 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 4).mpr (by decide))) ((hB 1).1 (by decide)) ((hB 3).1 (by decide))
        ((hB 4).1 (by decide)) _ _ (n2 _ (hxV 2) (by rw [memQ]; decide)).ne
        ((hB 2).2 (by decide)).ne
    have e1 : f1 (x 0) / f1 (x 3) = fA (x 0) / fA (x 3) :=
      ratio f1 fA 1 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 1).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 1).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hA 3).2 (by decide)).ne
    rw [e1, e2]; exact hlt
  · -- the view along the line of the planes of `023` and `1245`
    -- Cramer for `x6` in the frame `x4; x0, x2, x3`
    have EA := affine_cramer fA (x 4) (x 0) (x 2) (x 3) (x 6)
    have EB := affine_cramer fB (x 4) (x 0) (x 2) (x 3) (x 6)
    have EC := affine_cramer fC (x 4) (x 0) (x 2) (x 3) (x 6)
    have ED := affine_cramer fD (x 4) (x 0) (x 2) (x 3) (x 6)
    set Δ := vol3 (x 0 - x 4) (x 2 - x 4) (x 3 - x 4)
    set Δ1 := vol3 (x 6 - x 4) (x 2 - x 4) (x 3 - x 4)
    set Δ2 := vol3 (x 0 - x 4) (x 6 - x 4) (x 3 - x 4)
    set Δ3 := vol3 (x 0 - x 4) (x 2 - x 4) (x 6 - x 4)
    have a2 := (hA 2).1 (by decide); have a4 := (hA 4).1 (by decide)
    have a0 := (hA 0).2 (by decide); have a3 := (hA 3).2 (by decide)
    have b3 := (hB 3).1 (by decide); have b4 := (hB 4).1 (by decide); have b6 := (hB 6).1 (by decide)
    have b0 := (hB 0).2 (by decide); have b2 := (hB 2).2 (by decide)
    have c2 := (hC 2).1 (by decide); have c3 := (hC 3).1 (by decide); have c6 := (hC 6).1 (by decide)
    have c0 := (hC 0).2 (by decide); have c4 := (hC 4).2 (by decide)
    have d0 := (hD 0).1 (by decide); have d2 := (hD 2).1 (by decide); have d3 := (hD 3).1 (by decide)
    have d4 := (hD 4).2 (by decide); have d6 := (hD 6).2 (by decide)
    rw [a2, a4] at EA; rw [b3, b4, b6] at EB; rw [c2, c3, c6] at EC; rw [d0, d2, d3] at ED
    -- `Δ ≠ 0`: `x4` is off the plane of `023`
    have hΔ : Δ ≠ 0 := by
      intro h0
      have k := affine_vanish3 fD d0 d2 d3 (x 4) (x 0 + crs3 (x 2 - x 0) (x 3 - x 0))
      have pos := vol3_crs3_pos (p := x 0) (q := x 2) (r := x 3) (fun h => by have := hx h; omega)
        (ncol 0 2 3 (by decide) (by decide) (by decide))
      have e : vol3 (x 2 - x 0) (x 3 - x 0) (x 4 - x 0) = -Δ := by
        simp only [Δ, vol3, PiLp.sub_apply]; ring
      rw [add_sub_cancel_left, e, h0, neg_zero, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos d4
      linarith
    have g1 : fD (x 6) * Δ * fC (x 4) + Δ1 * fC (x 0) * fD (x 4) = 0 := by
      linear_combination fC (x 4) * ED - fD (x 4) * EC
    have g2 : fA (x 6) * fD (x 4) * Δ * fB (x 2) + fD (x 6) * fA (x 3) * Δ * fB (x 2) -
        fA (x 3) * fD (x 4) * Δ * fB (x 2) -
        Δ1 * (fB (x 0) * fA (x 3) * fD (x 4) + fA (x 0) * fD (x 4) * fB (x 2) -
          fA (x 3) * fD (x 4) * fB (x 2)) = 0 := by
      linear_combination fD (x 4) * fB (x 2) * EA + fA (x 3) * fB (x 2) * ED +
        fA (x 3) * fD (x 4) * EB
    have nd4 := d4.ne; have nc4 := c4.ne; have na3 := a3.ne; have nb2 := b2.ne
    set r := Δ1 / Δ
    have hl : fD (x 6) / fD (x 4) = -r * (fC (x 0) / fC (x 4)) := by
      simp only [r]; field_simp; linear_combination g1
    have hk : fA (x 6) / fA (x 3) + fD (x 6) / fD (x 4) =
        1 + r * (fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) - 1) := by
      simp only [r]; field_simp; linear_combination g2
    have hlpos : 0 < fD (x 6) / fD (x 4) := div_pos_of_neg_of_neg d6 d4
    have hκ : 0 < fC (x 0) / fC (x 4) := div_pos_of_neg_of_neg c0 c4
    have hr : r < 0 := by
      by_contra h; push Not at h
      have : -r * (fC (x 0) / fC (x 4)) ≤ 0 := by nlinarith
      linarith
    have hiv : QD ∩ QA = {x 2} := by
      rw [inter, show ({0, 2, 3} ∩ {1, 2, 4, 5} : Finset (Fin 7)) = {2} by decide]
      simp
    rcases hgt.lt_or_eq with hgt' | hgeq
    · -- `s > 1`: the point off both planes strictly inside; Lemma T (the tie allowed)
      refine isRupert_of_facets_vertex_tie_or V hgen QD QA (sub _) (sub _)
        (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fA hA) (x 2) hiv
        ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.1.imp (fun h => h.tie (sub _) (sub _) hiv
          (Or.inl (by show (({0, 2, 3} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide))) id)
        ⟨x 3, (memQ _ 3).mpr (by decide), x 4, (memQ _ 4).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2 : f2 (x 6) / f2 (x 3) = fA (x 6) / fA (x 3) :=
        ratio f2 fA 1 2 4 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
          (z2 _ ((memQ _ 4).mpr (by decide))) ((hA 1).1 (by decide)) ((hA 2).1 (by decide))
          ((hA 4).1 (by decide)) _ _ (n2 _ (hxV 3) (by rw [memQ]; decide)).ne
          ((hA 3).2 (by decide)).ne
      have e1 : f1 (x 6) / f1 (x 4) = fD (x 6) / fD (x 4) :=
        ratio f1 fD 0 2 3 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
          (z1 _ ((memQ _ 3).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
          ((hD 3).1 (by decide)) _ _ (n1 _ (hxV 4) (by rw [memQ]; decide)).ne
          ((hD 4).2 (by decide)).ne
      rw [e1, e2]
      rw [hk]; nlinarith
    · -- `s = 1`: the view along the edge `14` has `x0` on its far side; Lemma T′ over the edge
      refine isRupert_of_facets_edge_chord V hgen QA QB (sub _) (sub _) (isFacet_of_index x _ fA hA)
        (isFacet_of_index x _ fB hB) (x 1) (x 4) (fun h => by have := hx h; omega) ?_
        (hT2.2 hgeq.symm) (x 2) (x 3) ((memQ _ 2).mpr (by decide)) ((memQ _ 3).mpr (by decide))
        (by rw [memQ]; decide) (by rw [memQ]; decide) (x 0) (hxV 0) (by rw [memQ]; decide)
        (by rw [memQ]; decide) ?_
      · rw [inter, show ({1, 2, 4, 5} ∩ {1, 3, 4, 6} : Finset (Fin 7)) = {1, 4} by decide]
        simp [Finset.image_insert]
      intro f1 f2 z1 n1 z2 n2
      have e2 : f2 (x 0) / f2 (x 2) = fB (x 0) / fB (x 2) :=
        ratio f2 fB 1 3 4 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
          (z2 _ ((memQ _ 4).mpr (by decide))) ((hB 1).1 (by decide)) ((hB 3).1 (by decide))
          ((hB 4).1 (by decide)) _ _ (n2 _ (hxV 2) (by rw [memQ]; decide)).ne
          ((hB 2).2 (by decide)).ne
      have e1 : f1 (x 0) / f1 (x 3) = fA (x 0) / fA (x 3) :=
        ratio f1 fA 1 2 4 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 1).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
          (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 1).1 (by decide)) ((hA 2).1 (by decide))
          ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
          ((hA 3).2 (by decide)).ne
      refine ⟨fun y hy hy1 hy2 hne => ?_, by rw [e1, e2]; exact hgeq.symm.le⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 0 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      exact absurd (by rw [hi]) hne

end Minimality

end
