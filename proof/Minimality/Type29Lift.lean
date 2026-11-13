module

public import Minimality.Type29Lemmas

@[expose] public section

/-!
# Type 29: the far-end lift of Lemma 3 (b) of Theorem P of §12

At the view along the octahedron quad edge `4 → 1` with `t > 1` the cap `6` is the
far end of the quadrilateral `1456` and `5` its middle, so `K`'s reduced polygon is
not `O`'s: its rim is `v, 2, 3, 6` (or the triangle `v, 2, 6` when `3` is hidden).
`isRupert_lift_far` proves Lemma 3 (b) in that case, in the labelling
`x → y = 4 → 1`, `x' = 0`, `y' = 3`, `p, p' = 2, 5`, `d = 6`:

* the shadow tests of `K` come from those of `O` (`quad_edge_testsσ`, in either
  orientation `σ`), the facets through the cap (`cap_testsσ`), the coordinates
  `d = y + s (x − y) + t (p' − y)`, and for the hidden vertex `x'` the barycentric
  argument `inside_line_pos`;
* the claim of Lemma 9.3 uses the face `x y' p` (`234`), a down face through `x y'`;
* `K` is not bad (step 3 of the proof): the up face `y' p' d` (`356`, the
  combination of the facets `x y' p'`, `x' y' p'` through the cap) bounds `z p`,
  `lift_far_not_bad_core` (a statement about reals);
* the closing (`isRupert_closing_quad`, `isRupert_tri_view`, with either
  orientation in `isRupert_closing_quadσ`, `isRupert_tri_viewσ`) is that of
  Lemma 9.3: `K_y`'s rim is unimodal, or `K_x`'s.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Tools -/

theorem EdgeMiddle.swap {u v w A B : ℝ³} {h : ℝ} {m : ℝ³} (H : EdgeMiddle u v w A B h m) :
    EdgeMiddle u v w B A h m := by
  obtain ⟨c, s, δ, hc, hs0, hs1, hδ, hm⟩ := H
  refine ⟨c, 1 - s, δ, hc, by linarith, by linarith, hδ, ?_⟩
  rcases hm with hm | hm
  · right; rw [hm]; module
  · left; rw [hm]; module

/-- Reversing an edge of the shadow reverses its test. -/
theorem det3_rev (A B w u : ℝ³) : det3 (A - B) (w - B) u = -det3 (B - A) (w - A) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- The barycentric identity for the affine function `det3 (D − P) (· − P) u` on the
screen (the view along `u`). -/
theorem det3_bary (A B C X D P u : ℝ³) :
    det3 (B - A) (C - A) u * det3 (D - P) (X - P) u =
      det3 (B - X) (C - X) u * det3 (D - P) (A - P) u +
      det3 (X - A) (C - A) u * det3 (D - P) (B - P) u +
      det3 (B - A) (X - A) u * det3 (D - P) (C - P) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **A point inside a quadrilateral is on the positive side of a line through a
vertex** that has the three other vertices on its positive side (weakly at the two
neighbours).  Orientation `σ = ±1`; only the two edges at `a0` are used. -/
theorem inside_line_pos {a0 a1 a2 a3 X D u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h023 : 0 < σ * det3 (a2 - a0) (a3 - a0) u) (h012 : 0 < σ * det3 (a1 - a0) (a2 - a0) u)
    (hX01 : 0 < σ * det3 (a1 - a0) (X - a0) u) (hX30 : 0 < σ * det3 (a0 - a3) (X - a3) u)
    (hL1 : 0 ≤ σ * det3 (D - a0) (a1 - a0) u) (hL2 : 0 < σ * det3 (D - a0) (a2 - a0) u)
    (hL3 : 0 ≤ σ * det3 (D - a0) (a3 - a0) u) :
    0 < σ * det3 (D - a0) (X - a0) u := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hL0 : det3 (D - a0) (a0 - a0) u = 0 := by simp only [det3_expand, PiLp.sub_apply]; ring
  rcases le_or_gt 0 (σ * det3 (a2 - a0) (X - a0) u) with hc | hc
  · have e := det3_bary a0 a2 a3 X D a0 u
    rw [hL0, mul_zero, zero_add] at e
    have i1 : det3 (X - a0) (a3 - a0) u = det3 (a0 - a3) (X - a3) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [i1] at e
    have e' : (σ * det3 (a2 - a0) (a3 - a0) u) * (σ * det3 (D - a0) (X - a0) u) =
        (σ * det3 (a0 - a3) (X - a3) u) * (σ * det3 (D - a0) (a2 - a0) u) +
        (σ * det3 (a2 - a0) (X - a0) u) * (σ * det3 (D - a0) (a3 - a0) u) := by
      linear_combination (σ * σ) * e
    have : 0 < (σ * det3 (a2 - a0) (a3 - a0) u) * (σ * det3 (D - a0) (X - a0) u) := by
      rw [e']; nlinarith [mul_pos hX30 hL2, mul_nonneg hc hL3]
    exact pos_of_mul_pos_pos this h023
  · have e := det3_bary a0 a1 a2 X D a0 u
    rw [hL0, mul_zero, zero_add] at e
    have i1 : det3 (X - a0) (a2 - a0) u = -det3 (a2 - a0) (X - a0) u := by
      rw [det3_swap12]
    rw [i1] at e
    have e' : (σ * det3 (a1 - a0) (a2 - a0) u) * (σ * det3 (D - a0) (X - a0) u) =
        (-(σ * det3 (a2 - a0) (X - a0) u)) * (σ * det3 (D - a0) (a1 - a0) u) +
        (σ * det3 (a1 - a0) (X - a0) u) * (σ * det3 (D - a0) (a2 - a0) u) := by
      linear_combination (σ * σ) * e
    have : 0 < (σ * det3 (a1 - a0) (a2 - a0) u) * (σ * det3 (D - a0) (X - a0) u) := by
      rw [e']; nlinarith [mul_pos hX01 hL2, mul_nonneg (neg_nonneg.mpr hc.le) hL1]
    exact pos_of_mul_pos_pos this h012

/-! ### The shadow tests of the octahedron and at the cap, in either orientation -/

/-- The four edge tests of the shadow `y, p, y', p'` at a quad edge `x → y`, for the
orientation `σ` of the shadow. -/
theorem quad_edge_testsσ {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * det3 (p - y) (p' - y) (y - x) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y → w ≠ p → w ≠ x →
      0 < σ * det3 (p - y) (w - y) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p → w ≠ y' →
      0 < σ * det3 (y' - p) (w - p) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y' → w ≠ p' →
      0 < σ * det3 (p' - y') (w - y') (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p' → w ≠ y → w ≠ x →
      0 < σ * det3 (y - p') (w - p') (y - x)) := by
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have e : ({x, x', y, y', p', p} : Finset ℝ³) = {x, x', y, y', p, p'} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
    rw [e] at E1 E2 E3 E4
    refine ⟨-1, Or.inr rfl, by linarith, fun w hw h1 h2 h3 => ?_, fun w hw h1 h2 => ?_,
      fun w hw h1 h2 => ?_, fun w hw h1 h2 h3 => ?_⟩
    · have := E4 w hw h2 h1 h3; rw [det3_rev] at this; linarith
    · have := E3 w hw h2 h1; rw [det3_rev] at this; linarith
    · have := E2 w hw h2 h1; rw [det3_rev] at this; linarith
    · have := E1 w hw h2 h1 h3; rw [det3_rev] at this; linarith
  · obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hpos
    refine ⟨1, Or.inl rfl, by linarith, fun w hw h1 h2 h3 => ?_, fun w hw h1 h2 => ?_,
      fun w hw h1 h2 => ?_, fun w hw h1 h2 h3 => ?_⟩ <;> rw [one_mul]
    exacts [E1 w hw h1 h2 h3, E2 w hw h1 h2, E3 w hw h1 h2, E4 w hw h1 h2 h3]

/-! ### The closing of Lemma 9.3 for a 4-cycle, and a triangle -/

/-- The closing at an edge view whose reduced polygon is a triangle `y, A, B`
(counterclockwise; automatically unimodal with distinct depths). -/
theorem isRupert_tri_view (V M : Finset ℝ³) {x y A B : ℝ³} (hxy : x ≠ y)
    (hxV : x ∈ V) (hyV : y ∈ V) (hAV : A ∈ V) (hBV : B ∈ V)
    (hyM : y ∉ M) (hAM : A ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (B - y) (y - x)) (t2 : 0 < det3 (B - A) (y - A) (y - x))
    (t3 : 0 < det3 (y - B) (A - B) (y - x))
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ x → z ≠ y → z ≠ A → z ≠ B →
      0 < det3 (A - y) (z - y) (y - x) ∧ 0 < det3 (B - A) (z - A) (y - x) ∧
      0 < det3 (y - B) (z - B) (y - x))
    (hinj : ⟪y, y - x⟫ ≠ ⟪A, y - x⟫ ∧ ⟪y, y - x⟫ ≠ ⟪B, y - x⟫ ∧ ⟪A, y - x⟫ ≠ ⟪B, y - x⟫)
    (hM : ∀ m ∈ M, EdgeMiddle (y - x) y x A B 1 m) (hnd : NoHDNAt (V.erase x) (y - x)) :
    IsRupert V := by
  classical
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  refine isRupert_of_edgeView V M (y - x) hu (k := 3) le_rfl (tri y A B) 0 x 1 hxV
    (by simp only [tri_0, one_smul]; abel) one_ne_zero ?_ ?_ ?_ ?_ ?_ hnd ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hyV, hAV, hBV]
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hyM, hAM, hBM]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1, b2, tri_0, tri_1, tri_2]
    exacts [t1, t2, t3]
  · intro z hz hzM hzw hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2
    simp only [tri_0, tri_1, tri_2] at h0 h1 h2
    obtain ⟨r1, r2, r3⟩ := hrest z hz hzM hzw h0 h1 h2
    rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
    exacts [r1, r2, r3]
  · rw [tri_inner]
    exact isCyclicUnimodal_three (tri_injective hinj.1 hinj.2.1 hinj.2.2)
  · rw [zmod3_zero_add_one, zmod3_zero_sub_one]
    simpa only [tri_0, tri_1, tri_2] using hM

/-! ### Step 3: the lift is not bad -/

/-! ### Lemma 3 (b) with the cap as the far end -/

end Minimality

end
