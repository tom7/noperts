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

/-- The tests of the shadow edges `y → p` (vertical facet `x y p`) and `p → y'` (facets
`x y' p`, `x' y' p`) at a point beneath those facets, in the orientation `σ` (given by
the shadow's tests at `p'` and at `y`). -/
theorem cap_testsσ {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hor : 0 < σ * det3 (p - y) (p' - y) (y - x))
    (hE2 : 0 < σ * det3 (y' - p) (y - p) (y - x)) {m : ℝ³}
    (h1 : F.abc.f m < 0)
    (h3 : F.ab'c.f m ≤ 0 ∧ F.a'b'c.f m ≤ 0 ∧ (F.ab'c.f m < 0 ∨ F.a'b'c.f m < 0)) :
    0 < σ * det3 (p - y) (m - y) (y - x) ∧ 0 < σ * det3 (y' - p) (m - p) (y - x) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have hp' := F.abc.neg p' (by simp) (Ne.symm hxp') (Ne.symm hyp') (Ne.symm hpp')
  have hHx := F.a'b'c.neg x (by simp) hxx' hxy' hxp
  have hGy := F.ab'c.neg y (by simp) (Ne.symm hxy) hyy' hyp
  rcases hσ with rfl | rfl
  · rw [one_mul] at hor hE2 ⊢; rw [one_mul]
    exact ⟨vert_edge_pos_pt F.abc hp' hor h1, far_edge_pos_pt F.ab'c F.a'b'c hHx hGy hq₁ hE2 h3⟩
  · simp only [neg_mul, one_mul, neg_pos] at hor hE2 ⊢
    have v := vert_edge_pos_pt' F.abc (r := p') hp'
      (by rw [show det3 (y - p) (p' - p) (y - x) = -det3 (p - y) (p' - y) (y - x) by
        simp only [det3_expand, PiLp.sub_apply]; ring]; linarith) h1
    have f := far_edge_pos_pt F.ab'c.p23 F.a'b'c.p23 hHx hGy hq₁
      (by rw [det3_rev]; linarith) h3
    rw [det3_rev] at v f
    constructor <;> linarith

/-! ### The closing of Lemma 9.3 for a 4-cycle, and a triangle -/

/-- **The closing of Lemma 9.3 at an edge view**, for any 4-cycle: the shadow of the
points other than the middles `M` and the hidden end is the counterclockwise
quadrilateral of the images of `y, A, y', B` (`x`, `y` both project to its first
corner), the claim of Lemma 9.3 holds through a face `G` containing `x`, `y'` and one
far end, and the edge is not bad: then `K_y`'s rim or `K_x`'s is unimodal, and with
distinct depths and no horizontal double normal, Theorem 8.9 with Theorem 7.3 gives a
passage. -/
theorem isRupert_closing_quad (V M : Finset ℝ³) {x y y' A B : ℝ³}
    (hne : x ≠ y ∧ x ≠ y' ∧ x ≠ A ∧ x ≠ B ∧ y ≠ y' ∧ y ≠ A ∧ y ≠ B ∧ y' ≠ A ∧ y' ≠ B ∧ A ≠ B)
    (hxV : x ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V) (hAV : A ∈ V) (hBV : B ∈ V)
    (hxM : x ∉ M) (hyM : y ∉ M) (hy'M : y' ∉ M) (hAM : A ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (y' - y) (y - x)) (t2 : 0 < det3 (A - y) (B - y) (y - x))
    (t3 : 0 < det3 (y' - A) (B - A) (y - x)) (t4 : 0 < det3 (y' - A) (y - A) (y - x))
    (t5 : 0 < det3 (B - y') (y - y') (y - x)) (t6 : 0 < det3 (B - y') (A - y') (y - x))
    (t7 : 0 < det3 (y - B) (A - B) (y - x)) (t8 : 0 < det3 (y - B) (y' - B) (y - x))
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ x → z ≠ y → z ≠ y' → z ≠ A → z ≠ B →
      0 < det3 (A - y) (z - y) (y - x) ∧ 0 < det3 (y' - A) (z - A) (y - x) ∧
      0 < det3 (B - y') (z - y') (y - x) ∧ 0 < det3 (y - B) (z - B) (y - x))
    {G : ℝ³ → ℝ} {N : ℝ³} (hG : ∀ s t, G s - G t = ⟪N, s - t⟫) (hGx : G x = 0)
    (hGy' : G y' = 0) (hGy : G y < 0) (hface : (G A = 0 ∧ G B < 0) ∨ (G B = 0 ∧ G A < 0))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪A, y - x⟫ ⟪B, y - x⟫)
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = A ∨ s = B) → (t = y' ∨ t = A ∨ t = B) →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hMy : ∀ m ∈ M, EdgeMiddle (y - x) y x A B 1 m)
    (hMx : ∀ m ∈ M, EdgeMiddle (y - x) x y A B (-1) m)
    (hnd : NoHDNAt (V.erase x) (y - x) ∧ NoHDNAt (V.erase y) (y - x)) : IsRupert V := by
  classical
  obtain ⟨hxy, hxy', hxA, hxB, hyy', hyA, hyB, hy'A, hy'B, hAB⟩ := hne
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have dA : ∀ z, det3 (A - x) (z - x) (y - x) = det3 (A - y) (z - y) (y - x) :=
    fun z => det3_shift_xy A z x y
  have dB : ∀ z, det3 (x - B) (z - B) (y - x) = det3 (y - B) (z - B) (y - x) :=
    fun z => det3_shift_p' B z x y
  have dx1 : det3 (y' - A) (x - A) (y - x) = det3 (y' - A) (y - A) (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have dx2 : det3 (B - y') (x - y') (y - x) = det3 (B - y') (y - y') (y - x) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hAy'u : ⟪A, y - x⟫ ≠ ⟪y', y - x⟫ := hinj A y' (by simp) (by simp) (Ne.symm hy'A)
  have hABu : ⟪A, y - x⟫ ≠ ⟪B, y - x⟫ := hinj A B (by simp) (by simp) hAB
  have hy'Bu : ⟪y', y - x⟫ ≠ ⟪B, y - x⟫ := hinj y' B (by simp) (by simp) hy'B
  have hinjq : ∀ z : ℝ³, (z = x ∨ z = y) → z ≠ A → z ≠ y' → z ≠ B → Function.Injective
      (quad ⟪z, y - x⟫ ⟪A, y - x⟫ ⟪y', y - x⟫ ⟪B, y - x⟫) := by
    intro z hz h1 h2 h3
    have hs : z = x ∨ z = y ∨ z = y' ∨ z = A ∨ z = B := by
      rcases hz with h | h
      exacts [Or.inl h, Or.inr (Or.inl h)]
    exact quad_injective (hinj z A hs (by simp) h1) (hinj z y' hs (by simp) h2)
      (hinj z B hs (by simp) h3) hAy'u hABu hy'Bu
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪A, y - x⟫ ⟪y', y - x⟫ ⟪B, y - x⟫)
  · -- `K_y`
    refine isRupert_of_edgeView V M (y - x) hu (k := 4) (by norm_num) (quad y A y' B) 0 x 1
      hxV (by simp only [quad_0, one_smul]; abel) one_ne_zero ?_ ?_ ?_ ?_ ?_ hnd.1 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [hyV, hAV, hy'V, hBV]
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [hyM, hAM, hy'M, hBM]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      exacts [t1, t2, t3, t4, t5, t6, t7, t8]
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzw h0 h2 h1 h3
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      exacts [r1, r2, r3, r4]
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq y (Or.inr rfl) hyA hyy' hyB) hN
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      simpa only [quad_0, quad_1, quad_3] using hMy
  · -- `K_x`, by the closing of Lemma 9.3
    have hS₂ : 0 < det3 (y' - x) (B - x) (y - x) := by
      rw [show det3 (y' - x) (B - x) (y - x) = det3 (y - B) (y' - B) (y - x) by
        simp only [det3_expand, PiLp.sub_apply]; ring]; exact t8
    have hS₃ : 0 < det3 (A - x) (B - x) (y - x) := by rw [dA]; exact t2
    have hS₄ : 0 < det3 (A - x) (y' - x) (y - x) := by rw [dA]; exact t1
    have hlow := quad_lower_of_face hG hxy hGx hGy' hGy hS₂ hS₄ hface
    have hN' := nws4_closing_x t3 hS₂ hS₃ hS₄ hlow hN hgood hABu
    refine isRupert_of_edgeView V M (y - x) hu (k := 4) (by norm_num) (quad x A y' B) 0 y (-1)
      hyV (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd.2 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [hxV, hAV, hy'V, hBV]
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [hxM, hAM, hy'M, hBM]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [dA]; exact t1
      · rw [dA]; exact t2
      · exact t3
      · rw [dx1]; exact t4
      · rw [dx2]; exact t5
      · exact t6
      · rw [dB]; exact t7
      · rw [dB]; exact t8
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM h0 hzw h2 h1 h3
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [dA]; exact r1
      · exact r2
      · exact r3
      · rw [dB]; exact r4
    · rw [quad_inner]; exact isCyclicUnimodal_of_NWS4 (hinjq x (Or.inl rfl) hxA hxy' hxB) hN'
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      simpa only [quad_0, quad_1, quad_3] using hMx

/-- `isRupert_closing_quad` in either orientation `σ` of the cycle `y, A, y', B`. -/
theorem isRupert_closing_quadσ (V M : Finset ℝ³) {x y y' A B : ℝ³} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hne : x ≠ y ∧ x ≠ y' ∧ x ≠ A ∧ x ≠ B ∧ y ≠ y' ∧ y ≠ A ∧ y ≠ B ∧ y' ≠ A ∧ y' ≠ B ∧ A ≠ B)
    (hxV : x ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V) (hAV : A ∈ V) (hBV : B ∈ V)
    (hxM : x ∉ M) (hyM : y ∉ M) (hy'M : y' ∉ M) (hAM : A ∉ M) (hBM : B ∉ M)
    (t1 : 0 < σ * det3 (A - y) (y' - y) (y - x)) (t2 : 0 < σ * det3 (A - y) (B - y) (y - x))
    (t3 : 0 < σ * det3 (y' - A) (B - A) (y - x)) (t4 : 0 < σ * det3 (y' - A) (y - A) (y - x))
    (t5 : 0 < σ * det3 (B - y') (y - y') (y - x)) (t6 : 0 < σ * det3 (B - y') (A - y') (y - x))
    (t7 : 0 < σ * det3 (y - B) (A - B) (y - x)) (t8 : 0 < σ * det3 (y - B) (y' - B) (y - x))
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ x → z ≠ y → z ≠ y' → z ≠ A → z ≠ B →
      0 < σ * det3 (A - y) (z - y) (y - x) ∧ 0 < σ * det3 (y' - A) (z - A) (y - x) ∧
      0 < σ * det3 (B - y') (z - y') (y - x) ∧ 0 < σ * det3 (y - B) (z - B) (y - x))
    {G : ℝ³ → ℝ} {N : ℝ³} (hG : ∀ s t, G s - G t = ⟪N, s - t⟫) (hGx : G x = 0)
    (hGy' : G y' = 0) (hGy : G y < 0) (hface : (G A = 0 ∧ G B < 0) ∨ (G B = 0 ∧ G A < 0))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪A, y - x⟫ ⟪B, y - x⟫)
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = A ∨ s = B) → (t = y' ∨ t = A ∨ t = B) →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hMy : ∀ m ∈ M, EdgeMiddle (y - x) y x A B 1 m)
    (hMx : ∀ m ∈ M, EdgeMiddle (y - x) x y A B (-1) m)
    (hnd : NoHDNAt (V.erase x) (y - x) ∧ NoHDNAt (V.erase y) (y - x)) : IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at t1 t2 t3 t4 t5 t6 t7 t8 hrest
    exact isRupert_closing_quad V M hne hxV hyV hy'V hAV hBV hxM hyM hy'M hAM hBM
      t1 t2 t3 t4 t5 t6 t7 t8 hrest hG hGx hGy' hGy hface hgood hinj hMy hMx hnd
  · simp only [neg_mul, one_mul, neg_pos] at t1 t2 t3 t4 t5 t6 t7 t8 hrest
    obtain ⟨hxy, hxy', hxA, hxB, hyy', hyA, hyB, hy'A, hy'B, hAB⟩ := hne
    have r : ∀ P Q R : ℝ³, det3 (Q - P) (R - P) (y - x) = det3 (R - Q) (P - Q) (y - x) := by
      intro P Q R; simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_closing_quad V M (A := B) (B := A)
      ⟨hxy, hxy', hxB, hxA, hyy', hyB, hyA, hy'B, hy'A, Ne.symm hAB⟩ hxV hyV hy'V hBV hAV
      hxM hyM hy'M hBM hAM ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hG hGx hGy' hGy hface.symm
      (by rwa [min_comm]) ?_ (fun m hm => (hMy m hm).swap) (fun m hm => (hMx m hm).swap) hnd
    · rw [show det3 (B - y) (y' - y) (y - x) = -det3 (B - y') (y - y') (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (B - y) (A - y) (y - x) = -det3 (A - y) (B - y) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (y' - B) (A - B) (y - x) = -det3 (B - y') (A - y') (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (y' - B) (y - B) (y - x) = -det3 (y - B) (y' - B) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (A - y') (y - y') (y - x) = -det3 (y' - A) (y - A) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (A - y') (B - y') (y - x) = -det3 (y' - A) (B - A) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (y - A) (B - A) (y - x) = -det3 (y - B) (A - B) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (y - A) (y' - A) (y - x) = -det3 (A - y) (y' - y) (y - x) by simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · intro z hz hzM h1 h2 h3 h4 h5
      obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM h1 h2 h3 h5 h4
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show det3 (B - y) (z - y) (y - x) = -det3 (y - B) (z - B) (y - x) by
          rw [det3_rev]]; linarith
      · rw [show det3 (y' - B) (z - B) (y - x) = -det3 (B - y') (z - y') (y - x) by
          rw [det3_rev]]; linarith
      · rw [show det3 (A - y') (z - y') (y - x) = -det3 (y' - A) (z - A) (y - x) by
          rw [det3_rev]]; linarith
      · rw [show det3 (y - A) (z - A) (y - x) = -det3 (A - y) (z - y) (y - x) by
          rw [det3_rev]]; linarith
    · intro s t hs ht hst
      exact hinj s t (by rcases hs with h | h | h | h | h <;> simp only [h, true_or, or_true])
        (by rcases ht with h | h | h <;> simp only [h, true_or, or_true]) hst

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

/-- `isRupert_tri_view` in either orientation `σ` of the triangle `y, A, B`. -/
theorem isRupert_tri_viewσ (V M : Finset ℝ³) {x y A B : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hxy : x ≠ y) (hxV : x ∈ V) (hyV : y ∈ V) (hAV : A ∈ V) (hBV : B ∈ V)
    (hyM : y ∉ M) (hAM : A ∉ M) (hBM : B ∉ M)
    (t1 : 0 < σ * det3 (A - y) (B - y) (y - x)) (t2 : 0 < σ * det3 (B - A) (y - A) (y - x))
    (t3 : 0 < σ * det3 (y - B) (A - B) (y - x))
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ x → z ≠ y → z ≠ A → z ≠ B →
      0 < σ * det3 (A - y) (z - y) (y - x) ∧ 0 < σ * det3 (B - A) (z - A) (y - x) ∧
      0 < σ * det3 (y - B) (z - B) (y - x))
    (hinj : ⟪y, y - x⟫ ≠ ⟪A, y - x⟫ ∧ ⟪y, y - x⟫ ≠ ⟪B, y - x⟫ ∧ ⟪A, y - x⟫ ≠ ⟪B, y - x⟫)
    (hM : ∀ m ∈ M, EdgeMiddle (y - x) y x A B 1 m) (hnd : NoHDNAt (V.erase x) (y - x)) :
    IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at t1 t2 t3 hrest
    exact isRupert_tri_view V M hxy hxV hyV hAV hBV hyM hAM hBM t1 t2 t3 hrest hinj hM hnd
  · simp only [neg_mul, one_mul, neg_pos] at t1 t2 t3 hrest
    refine isRupert_tri_view V M (A := B) (B := A) hxy hxV hyV hBV hAV hyM hBM hAM ?_ ?_ ?_ ?_
      ⟨hinj.2.1, hinj.1, Ne.symm hinj.2.2⟩ (fun m hm => (hM m hm).swap) hnd
    · rw [det3_swap12]; linarith
    · rw [show det3 (A - B) (y - B) (y - x) = -det3 (y - B) (A - B) (y - x) by
        simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · rw [show det3 (y - A) (B - A) (y - x) = -det3 (B - A) (y - A) (y - x) by
        simp only [det3_expand, PiLp.sub_apply]; ring]; linarith
    · intro z hz hzM h1 h2 h3 h4
      obtain ⟨r1, r2, r3⟩ := hrest z hz hzM h1 h2 h4 h3
      refine ⟨?_, ?_, ?_⟩
      · rw [show det3 (B - y) (z - y) (y - x) = -det3 (y - B) (z - B) (y - x) by
          rw [det3_rev]]; linarith
      · rw [show det3 (A - B) (z - B) (y - x) = -det3 (B - A) (z - A) (y - x) by
          rw [det3_rev]]; linarith
      · rw [show det3 (y - A) (z - A) (y - x) = -det3 (A - y) (z - y) (y - x) by
          rw [det3_rev]]; linarith

/-! ### Step 3: the lift is not bad -/

/-- **Step 3 of Lemma 3 (b), in reals.**  The data: the coordinates of the cap
(`F4`: `t (z p' − z y) = z d − z y + s U`), the up face `y' p' d` with affine function
`h` (`F1`: `s ⟪N, u⟫ = (1 − t) h y`, from `h d = 0`), and the four-point identity of
`p` in the frame `y; y', d` mod the view, applied to `h` (`F2`) and to the depth `z`
(`F3`), with the orientations `O3 = [y y' d]`, `D2 = [y p y']`,
`κ = O3 + D1 + D2 = [y' d p]` of one sign `σ`.  If `O` is not bad
(`¬ max (z y, z y') ≤ min (z p, z p')`), then `K` is not bad either. -/
theorem lift_far_not_bad_core {σ s t U O3 D1 D2 lam zy zy' zd zp zp' hy hp Nu : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hs : 0 < s) (ht : 1 < t) (hU : 0 < U) (hO3 : 0 < σ * O3)
    (hD2 : 0 < σ * D2) (hκ : 0 < σ * (O3 + D1 + D2)) (hhp : hp < 0) (hhy : hy < 0)
    (F1 : s * Nu = (1 - t) * hy)
    (F2 : D1 * (0 - hy) + D2 * (0 - hy) + O3 * (hp - hy) = lam * Nu)
    (F3 : D1 * (zy' - zy) + D2 * (zd - zy) + O3 * (zp - zy) = lam * U)
    (F4 : t * (zp' - zy) = zd - zy + s * U)
    (hgoodO : ¬ max zy zy' ≤ min zp zp') : ¬ max zy zy' ≤ min zp zd := by
  intro hbad
  simp only [max_le_iff, le_min_iff] at hbad hgoodO
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  have hp' : zp' < max zy zy' := by
    by_contra hc; push Not at hc
    rw [max_le_iff] at hc
    exact hgoodO (by obtain ⟨c1, c2⟩ := hc; constructor <;> constructor <;> linarith)
  have hp'y : zy < zp' := by nlinarith
  have hp'y' : zp' < zy' := by
    rcases le_total zy zy' with h | h
    · rwa [max_eq_right h] at hp'
    · rw [max_eq_left h] at hp'; linarith
  have E : (σ * lam * (1 - t) + s * (σ * (O3 + D1 + D2))) * hy = s * (σ * O3) * hp := by
    linear_combination (-(σ * s)) * F2 + (-(σ * lam)) * F1
  have hA : 0 < σ * lam * (1 - t) + s * (σ * (O3 + D1 + D2)) :=
    pos_of_mul_neg_neg (by rw [E]; exact mul_neg_of_pos_of_neg (mul_pos hs hO3) hhp) hhy
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hC : (t - 1) * (σ * lam) * U < s * (σ * (O3 + D1 + D2)) * U := by
    have : (t - 1) * (σ * lam) < s * (σ * (O3 + D1 + D2)) := by linarith
    exact mul_lt_mul_of_pos_right this hU
  have hB : (t - 1) * (σ * D1 * (zy' - zy) + σ * D2 * (zd - zy) + σ * O3 * (zp - zy)) =
      (t - 1) * (σ * lam) * U := by linear_combination (t - 1) * σ * F3
  have k1 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ t - 1 by linarith) hO3.le)
    (show (0 : ℝ) ≤ zp - zy' by linarith)
  have k2 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ t - 1 by linarith) hD2.le)
    (show (0 : ℝ) ≤ zd - zy' by linarith)
  have k3 := mul_neg_of_pos_of_neg hκ
    (show t * (zp' - zy') + (zy' - zd) < 0 by nlinarith)
  have k4 : σ * (O3 + D1 + D2) * (t * (zp' - zy)) = σ * (O3 + D1 + D2) * (zd - zy + s * U) := by
    rw [F4]
  nlinarith

/-! ### Lemma 3 (b) with the cap as the far end -/

set_option maxHeartbeats 1000000 in
/-- **Lemma 3 (b) of Theorem P of §12, the case `t > 1`.**  Let `x → y` be a quad
edge of the octahedron `O` (`x'` hidden; in type 29, `4 → 1` with `x' = 0`, `y' = 3`,
`p, p' = 2, 5`) that is not bad, and let the cap `d` (`6`) lie on the plane `x y p'`
at `d = y + s (x − y) + t (p' − y)` with `s > 0`, `t > 1` (so `d` is the far end of the
quadrilateral `x y p' d` along `x y`, and `p'` its middle), strictly beneath the facets
`x y p`, `x y' p`, `x' y' p`, `x' y' p'` and strictly beyond `x y' p'`.  Then `K`'s
reduced polygon at the view along `x y` has the rim `v, p, y', d` (or the triangle
`v, p, d` if `y'` is hidden), and `K`'s test has a unimodal closing: with distinct
depths along `y − x` (this excludes `K`'s touching `z p = z d`), `y'` off the plane
through `d p` along the view (`hcorner`), and no horizontal double normal at the view,
`K = O ∪ {d}` is Rupert. -/
theorem isRupert_lift_far {x x' y y' p p' d : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgoodO : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    {s t : ℝ} (hs : 0 < s) (ht : 1 < t) (hcoord : d = y + s • (x - y) + t • (p' - y))
    (hd1 : F.abc.f d < 0) (hd3 : F.ab'c.f d < 0) (hd4 : F.a'b'c.f d < 0)
    (hd5 : 0 < F.ab'c'.f d) (hd6 : F.a'b'c'.f d < 0)
    (hdO : d ≠ x ∧ d ≠ x' ∧ d ≠ y ∧ d ≠ y' ∧ d ≠ p ∧ d ≠ p')
    (hcorner : det3 (d - y') (p - y') (y - x) ≠ 0)
    (hinj : ∀ s t, (s = x ∨ s = y ∨ s = y' ∨ s = p ∨ s = d) → (t = y' ∨ t = p ∨ t = d) →
      s ≠ t → ⟪s, y - x⟫ ≠ ⟪t, y - x⟫)
    (hnd : NoHDNAt ((insert d ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert d ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert d {x, x', y, y', p, p'}) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hdx, hdx', hdy, hdy', hdp, hdp'⟩ := hdO
  set V : Finset ℝ³ := insert d {x, x', y, y', p, p'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  obtain ⟨σ, hσ, hor, E1, E2, E3, E4⟩ := quad_edge_testsσ F hq₁ hq₂
  have e1y' := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
  have e1x' := E1 x' mx' hx'y hx'p (Ne.symm hxx')
  have e2y := E2 y my hyp hyy'
  have e2x' := E2 x' mx' hx'p hx'y'
  have e3y := E3 y my hyy' hyp'
  have e3x' := E3 x' mx' hx'y' hx'p'
  have e3p := E3 p mp (Ne.symm hy'p) hpp'
  have e4p := E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
  have e4y' := E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  have e4x' := E4 x' mx' hx'p' hx'y (Ne.symm hxx')
  obtain ⟨c1, c2⟩ := cap_testsσ F hq₁ hσ hor e2y hd1 ⟨hd3.le, hd4.le, Or.inl hd3⟩
  have ht0 : 0 < t := by linarith
  -- the coordinates of the cap in the tests
  have I4 : ∀ X, det3 (y - d) (X - d) (y - x) = t * det3 (y - p') (X - p') (y - x) := by
    intro X; rw [hcoord]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have I3 : ∀ X, det3 (d - y') (X - y') (y - x) =
      (1 - t) * det3 (y - y') (X - y') (y - x) + t * det3 (p' - y') (X - y') (y - x) := by
    intro X; rw [hcoord]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have zero : ∀ X Y : ℝ³, det3 (X - Y) (X - Y) (y - x) = 0 := by
    intro X Y; simp only [det3_expand, PiLp.sub_apply]; ring
  have t5 : 0 < σ * det3 (d - y') (y - y') (y - x) := by
    rw [I3, zero, mul_zero, zero_add]; nlinarith
  have t7 : 0 < σ * det3 (y - d) (p - d) (y - x) := by rw [I4]; nlinarith
  have t8 : 0 < σ * det3 (y - d) (y' - d) (y - x) := by rw [I4]; nlinarith
  have t8x : 0 < σ * det3 (y - d) (x' - d) (y - x) := by rw [I4]; nlinarith
  -- the middle `p'`
  have hp'eq : p' = y + t⁻¹ • (d - y) + (s * t⁻¹) • (y - x) := by
    have h1 : t • (p' - y) = d - y + s • (y - x) := by rw [hcoord]; module
    calc p' = y + t⁻¹ • (t • (p' - y)) := by
          rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]; abel
      _ = _ := by rw [h1]; module
  have hti : 0 < t⁻¹ := inv_pos.mpr ht0
  have hti1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hMy : ∀ m ∈ ({p'} : Finset ℝ³), EdgeMiddle (y - x) y x p d 1 m := by
    intro m hm; rw [mem_singleton.mp hm]
    refine ⟨y, 1 - t⁻¹, s * t⁻¹, Or.inl rfl, by linarith, by linarith,
      (mul_pos hs hti).ne', Or.inr ?_⟩
    rw [hp'eq]; module
  have hMx : ∀ m ∈ ({p'} : Finset ℝ³), EdgeMiddle (y - x) x y p d (-1) m := by
    intro m hm; rw [mem_singleton.mp hm]
    refine ⟨x, 1 - t⁻¹, 1 - t⁻¹ + s * t⁻¹, Or.inl rfl, by linarith, by linarith,
      by nlinarith [mul_pos hs hti], Or.inr ?_⟩
    rw [hp'eq]; module
  have hinj' : ⟪y, y - x⟫ ≠ ⟪p, y - x⟫ ∧ ⟪y, y - x⟫ ≠ ⟪d, y - x⟫ ∧ ⟪p, y - x⟫ ≠ ⟪d, y - x⟫ :=
    ⟨hinj y p (by simp) (by simp) hyp, hinj y d (by simp) (by simp) (Ne.symm hdy),
      hinj p d (by simp) (by simp) (Ne.symm hdp)⟩
  have hp'M : ∀ z, z ≠ p' → z ∉ ({p'} : Finset ℝ³) := fun z hz h => hz (mem_singleton.mp h)
  have hdV : d ∈ V := by simp [V]
  rcases lt_or_gt_of_ne (show σ * det3 (d - y') (p - y') (y - x) ≠ 0 from
    mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hcorner) with hκn | hκp
  · -- `y'` hidden: the triangle `v, p, d`
    have hL2 : 0 < σ * det3 (d - p) (p' - p) (y - x) := by
      rw [show det3 (d - p) (p' - p) (y - x) = (t - 1) * det3 (p - y) (p' - y) (y - x) by
        rw [hcoord]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring]
      nlinarith
    have idc : det3 (d - p) (y - p) (y - x) = det3 (p - y) (d - y) (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have idk : det3 (d - p) (y' - p) (y - x) = -det3 (d - y') (p - y') (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_tri_viewσ V {p'} hσ hxy (by simp [V]) (by simp [V]) (by simp [V]) hdV
      (hp'M y hyp') (hp'M p hpp') (hp'M d hdp') c1 (by rw [idc]; exact c1) t7 ?_ hinj' hMy hnd.1
    intro z hz hzM hzx hzy hzp hzd
    rcases hmemV z hz with h | h | h | h | h | h | h
    · exact absurd h hzd
    · exact absurd h hzx
    · subst h
      refine ⟨e1x', ?_, t8x⟩
      refine inside_line_pos (a1 := y') (a2 := p') (a3 := y) hσ ?_ ?_ e2x' e1x' ?_ hL2 ?_
      · rw [show det3 (p' - p) (y - p) (y - x) = det3 (p - y) (p' - y) (y - x) by
          simp only [det3_expand, PiLp.sub_apply]; ring]; exact hor
      · rw [show det3 (y' - p) (p' - p) (y - x) = det3 (p' - y') (p - y') (y - x) by
          simp only [det3_expand, PiLp.sub_apply]; ring]; exact e3p
      · rw [idk]; linarith
      · rw [idc]; exact c1.le
    · exact absurd h hzy
    · subst h
      exact ⟨e1y', by rw [idk]; linarith, t8⟩
    · exact absurd h hzp
    · exact absurd (mem_singleton.mpr h) hzM
  · -- `y'` a corner: the quadrilateral `v, p, y', d`
    -- the up face `y' p' d`
    set α := -F.a'b'c'.f d with hα
    set β := F.ab'c'.f d with hβ
    have hα0 : 0 < α := by rw [hα]; linarith
    set h : ℝ³ → ℝ := fun X => α * F.ab'c'.f X + β * F.a'b'c'.f X with hh
    set Nh : ℝ³ := α • F.ab'c'.N + β • F.a'b'c'.N
    have hhN : ∀ X Y, h X - h Y = ⟪Nh, X - Y⟫ := by
      intro X Y
      simp only [hh, Nh, inner_add_left, real_inner_smul_left, ← F.ab'c'.hN, ← F.a'b'c'.hN]
      ring
    have hy'0 : h y' = 0 := by simp only [hh, F.ab'c'.hQ, F.a'b'c'.hQ]; ring
    have hd0 : h d = 0 := by simp only [hh, hα, hβ]; ring
    have hp'0 : h p' = 0 := by simp only [hh, F.ab'c'.hR, F.a'b'c'.hR]; ring
    have hhp : h p < 0 := by
      have a1 := F.ab'c'.neg p (by simp) (Ne.symm hxp) (Ne.symm hy'p) hpp'
      have a2 := F.a'b'c'.neg p (by simp) (Ne.symm hx'p) (Ne.symm hy'p) hpp'
      simp only [hh]; nlinarith
    have hhy : h y < 0 := by
      have a1 := F.ab'c'.neg y (by simp) (Ne.symm hxy) hyy' hyp'
      have a2 := F.a'b'c'.neg y (by simp) (Ne.symm hx'y) hyy' hyp'
      simp only [hh]; nlinarith
    -- the four-point identity of `p` in the frame `y; y', d`
    have h4 := det3_four_proj (y' - y) (d - y) (p - y) (y - x)
    have F3 := congrArg (fun v => ⟪v, y - x⟫) h4
    have F2 := congrArg (fun v => ⟪Nh, v⟫) h4
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at F3
    simp only [inner_add_right, real_inner_smul_right] at F2
    rw [← hhN y' y, ← hhN d y, ← hhN p y, hy'0, hd0] at F2
    have F1 : s * ⟪Nh, y - x⟫ = (1 - t) * h y := by
      have e := hhN d y
      have e2 : ⟪Nh, p' - y⟫ = -h y := by rw [← hhN, hp'0]; ring
      rw [hd0, show d - y = (-s) • (y - x) + t • (p' - y) by rw [hcoord]; module,
        inner_add_right, real_inner_smul_right, real_inner_smul_right, e2] at e
      linarith
    have F4 : t * (⟪p', y - x⟫ - ⟪y, y - x⟫) =
        ⟪d, y - x⟫ - ⟪y, y - x⟫ + s * ⟪y - x, y - x⟫ := by
      rw [hcoord]
      simp only [inner_add_left, real_inner_smul_left, inner_sub_left]; ring
    have hUx : ⟪y - x, y - x⟫ = ⟪y, y - x⟫ - ⟪x, y - x⟫ := inner_sub_left _ _ _
    have hU : 0 < ⟪y - x, y - x⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    have iO3 : det3 (y' - y) (d - y) (y - x) = det3 (d - y') (y - y') (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have iD2 : det3 (p - y) (y' - y) (y - x) = det3 (p - y) (y' - y) (y - x) := rfl
    have iκ : det3 (y' - y) (d - y) (y - x) + det3 (d - y) (p - y) (y - x) +
        det3 (p - y) (y' - y) (y - x) = det3 (d - y') (p - y') (y - x) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪d, y - x⟫ :=
      lift_far_not_bad_core (O3 := det3 (y' - y) (d - y) (y - x))
        (D1 := det3 (d - y) (p - y) (y - x)) (D2 := det3 (p - y) (y' - y) (y - x))
        (lam := det3 (y' - y) (d - y) (p - y)) (zp' := ⟪p', y - x⟫) hσ hs ht hU
        (by rw [iO3]; exact t5) e1y' (by rw [iκ]; exact hκp) hhp hhy F1
        (by linear_combination F2)
        (by linear_combination F3 - det3 (y' - y) (d - y) (p - y) * hUx)
        F4 hgoodO
    refine isRupert_closing_quadσ V {p'} hσ
      ⟨hxy, hxy', hxp, Ne.symm hdx, hyy', hyp, Ne.symm hdy, hy'p, Ne.symm hdy', Ne.symm hdp⟩
      (by simp [V]) (by simp [V]) (by simp [V]) (by simp [V]) hdV
      (hp'M x hxp') (hp'M y hyp') (hp'M y' hy'p') (hp'M p hpp') (hp'M d hdp')
      e1y' c1 c2 e2y t5 hκp t7 t8 ?_ F.ab'c.hN F.ab'c.hP F.ab'c.hQ
      (F.ab'c.neg y (by simp) (Ne.symm hxy) hyy' hyp) (Or.inl ⟨F.ab'c.hR, hd3⟩) hgood hinj
      hMy hMx hnd
    intro z hz hzM hzx hzy hzy' hzp hzd
    rcases hmemV z hz with h | h | h | h | h | h | h
    · exact absurd h hzd
    · exact absurd h hzx
    · subst h
      refine ⟨e1x', e2x', ?_, t8x⟩
      refine inside_line_pos (a1 := p') (a2 := y) (a3 := p) hσ ?_ e3y e3x' e2x' ?_ t5 hκp.le
      · rw [show det3 (y - y') (p - y') (y - x) = det3 (p - y) (y' - y) (y - x) by
          simp only [det3_expand, PiLp.sub_apply]; ring]; exact e1y'
      · rw [I3, zero, mul_zero, add_zero,
          show det3 (y - y') (p' - y') (y - x) = -det3 (p' - y') (y - y') (y - x) by
            rw [det3_swap12]]
        nlinarith
    · exact absurd h hzy
    · exact absurd h hzy'
    · exact absurd h hzp
    · exact absurd (mem_singleton.mpr h) hzM

end Minimality

end
