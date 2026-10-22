module

public import Minimality.RobustAxis

@[expose] public section

/-!
# Lemma E with ties, and general position up to single ties (`FEWER-FACES-PROOFS.md` §14, §18)

Lemma E (`edgePair_not_both`, `EdgePair.lean`) says that at an edge crossing along `v w` whose
closings have the 4-corner rims `(v, a, c, b)`, `(w, a, c, b)`, with `[a b c v] [a b c w] ≤ 0`,
the two rims are not both depth-separated, so with distinct depths one closing is unimodal.
Here ties are allowed: unless the three far depths are equal, one rim has diagonals that are
not even *weakly* separated (`edgePair_nws`), hence is robustly unimodal (§18.0), whatever its
other ties (`edgePair_robust`; Lemma 18.4 for edge pairs, with a stronger conclusion).  The
proof is the depth chain of Lemma E: over the crossing of the diagonals, `d_v ≤ e ≤ d_w` in
depth, with `e` strictly inside `[a, b]` and `d_v`, `d_w` strictly inside `[v, c]`, `[w, c]`
(the diagonals of a strictly convex quadrilateral cross at interior points, `segMeet_strict`).
So `(v, a, c, b)` can fail only with `{a, b}` weakly above `{v, c}`, `(w, a, c, b)` only with
`{w, c}` weakly above `{a, b}`, and both give `a = c = b` (`edgePair_nws_core`).

* `NWS4.isRobustUnimodal`: a 4-cycle whose diagonals are not weakly separated is robustly
  unimodal, whatever its ties.
* **Lemma E with ties**: `edgePair_nws_core`, `edgePair_nws`, `edgePair_robust`; the Rupert forms
  `isRupert_quad_rim_int_robust`, `isRupert_edgePair_closing_nws`, **`isRupert_edgePair_robust`**
  (Corollary 14.1: only `¬ (z_a = z_c = z_b)`), `isRupert_edgeTri_robust` (a triangle closing:
  only `¬ (z_v = z_a = z_b)`), `isRupert_quad_uniform_nws`, `isRupert_edgePair_uniform_robust`
  (with the uniform tilt of Lemma 16.27).
* **The octahedral quads of tiers Q and H with ties** (Lemma 9.3 / Lemma 2 of §12):
  `nws4_closing_x_tie`, `isRupert_quad_edge_lift_core_tie`, `isRupert_quad_edge_lift_tie`: the
  closing of Lemma 9.3 is `NWS4`, so the only depth condition left is that the far ends are not
  both at the depth of `y'` (two ties).
* `nws4_of_planar_quad_tie`: a planar 4-corner rim is `NWS4` unless three corners are at one
  depth.
* **General position up to single ties**: `OneTieAt V u` (at most one tied pair at the view
  `u`), `GenPosTie V` (no two segments parallel, and `OneTieAt` at the view along each segment;
  both failures have codimension 2), `GenPos.genPosTie`, `GenPosTie.ne_smul`,
  `GenPosTie.noTriple`, `GenPosTie.touch_oct`, `OneTieAt.rim`.
* **Robust unimodality by perturbation** (Lemma 18.4 (α) for an explicit family):
  `isRobustUnimodal_of_perturb`: a rim with at most one tied pair is robustly unimodal if it is
  unimodal with distinct depths and, along some direction separating the tied pair, every small
  perturbation with distinct depths is unimodal (used for the five-corner rim of type 21's
  `Y`, `type21_Y_robust`); `isRobustUnimodal_of_nhds`: the same from an open criterion (a
  condition holding near the sequence that makes every distinct sequence unimodal; the
  pentagons of type 16's `Ω`); `IsRobustUnimodal.neg`, `eventually_lt_near`,
  `eventually_entry_lt`, `OneTieAt.rim5`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Robust 4-cycles -/

/-- **A 4-cycle whose diagonals are not weakly separated is robustly unimodal**: it has no
three equal entries and no level edge inside a monotone run (either would make the diagonals
weakly separated). -/
theorem NWS4.isRobustUnimodal {z₀ z₁ z₂ z₃ : ℝ} (h : NWS4 (quad z₀ z₁ z₂ z₃)) :
    IsRobustUnimodal (quad z₀ z₁ z₂ z₃) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at h
  obtain ⟨h1, h2⟩ := h
  refine isRobustUnimodal_quad ?_ ?_ ?_
  · unfold QuadTie
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;>
      rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
      linarith [hc.1, hc.2]
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    rintro ⟨⟨k1, k2⟩, k3, k4⟩
    rcases h1 with h1 | h1 | h1 | h1 <;> linarith
  · rw [max_lt_iff, lt_min_iff, lt_min_iff]
    rintro ⟨⟨k1, k2⟩, k3, k4⟩
    rcases h2 with h2 | h2 | h2 | h2 <;> linarith

/-! ### Lemma E with ties: the depth core -/

/-- **Lemma E with ties, depth core.**  The far depths `a, c, b`, the axle ends `v`, `w`, and
three depths on the diagonals: `E` strictly inside `[a, b]` (or equal to both ends), `Dv`
strictly inside `[v, c]`, `Dw` strictly inside `[w, c]`, with `Dv ≤ E ≤ Dw`.  Unless
`a = c = b`, one of the 4-cycles `(v, a, c, b)`, `(w, a, c, b)` has diagonals that are not
weakly separated (`NWS4`).  Indeed `(v, a, c, b)` can only fail with `{a, b}` weakly above
`{v, c}` (the reverse would force `max (a, b) = E = Dv = min (v, c)`, hence `a = b = v = c`),
`(w, a, c, b)` only with `{w, c}` weakly above `{a, b}`; both together give
`c ≤ min (a, b) ≤ max (a, b) ≤ c`. -/
theorem edgePair_nws_core {v w a b c E Dv Dw : ℝ} (h1 : Dv ≤ E) (h2 : E ≤ Dw)
    (hE : (a < E ∧ E < b) ∨ (b < E ∧ E < a) ∨ (a = E ∧ E = b))
    (hv : (v < Dv ∧ Dv < c) ∨ (c < Dv ∧ Dv < v) ∨ (v = Dv ∧ Dv = c))
    (hw : (w < Dw ∧ Dw < c) ∨ (c < Dw ∧ Dw < w) ∨ (w = Dw ∧ Dw = c))
    (h3 : ¬ (a = c ∧ c = b)) :
    NWS4 (quad v a c b) ∨ NWS4 (quad w a c b) := by
  -- `{a, b}` is not weakly below `{v, c}`
  have H1 : ¬ (a ≤ v ∧ b ≤ v ∧ a ≤ c ∧ b ≤ c) := by
    rintro ⟨k1, k2, k3, k4⟩
    rcases hE with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases hv with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
      first | linarith | exact h3 ⟨by linarith, by linarith⟩
  -- `{a, b}` is not weakly above `{w, c}`
  have H2 : ¬ (w ≤ a ∧ w ≤ b ∧ c ≤ a ∧ c ≤ b) := by
    rintro ⟨k1, k2, k3, k4⟩
    rcases hE with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases hw with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
      first | linarith | exact h3 ⟨by linarith, by linarith⟩
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  by_cases hup : v ≤ a ∧ v ≤ b ∧ c ≤ a ∧ c ≤ b
  · obtain ⟨k1, k2, k3, k4⟩ := hup
    right
    refine ⟨?_, ?_⟩
    · by_contra hc
      simp only [not_or, not_lt] at hc
      exact h3 ⟨le_antisymm hc.2.2.1 k3, le_antisymm k4 hc.2.2.2⟩
    · by_contra hc
      simp only [not_or, not_lt] at hc
      exact H2 ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · left
    refine ⟨?_, ?_⟩
    · by_contra hc
      simp only [not_or, not_lt] at hc
      exact H1 ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    · by_contra hc
      simp only [not_or, not_lt] at hc
      exact hup ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-! ### Lemma E with ties, Euclidean form -/

/-- **The diagonals of a strictly convex quadrilateral cross at interior points**: a crossing
of the projections of `[p, q]` and `[r, s]` (`SegMeet`) with the four triangles nondegenerate
has both parameters strictly between `0` and `1`. -/
theorem segMeet_strict {p q r s u : ℝ³} (hm : SegMeet p q r s u)
    (hr : det3 (q - p) (r - p) u ≠ 0) (hs : det3 (q - p) (s - p) u ≠ 0)
    (hp : det3 (s - r) (p - r) u ≠ 0) (hq : det3 (s - r) (q - r) u ≠ 0) :
    ∃ l t μ : ℝ, 0 < l ∧ l < 1 ∧ 0 < t ∧ t < 1 ∧
      (r + t • (s - r)) - (p + l • (q - p)) = μ • u := by
  obtain ⟨l, t, μ, hl0, hl1, ht0, ht1, h⟩ := hm
  have e1 : (1 - t) * det3 (q - p) (r - p) u + t * det3 (q - p) (s - p) u = 0 := by
    have := congrArg (fun X => det3 (q - p) X u) h
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at this ⊢
    linear_combination this
  have e2 : (1 - l) * det3 (s - r) (p - r) u + l * det3 (s - r) (q - r) u = 0 := by
    have := congrArg (fun X => det3 (s - r) X u) h
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at this ⊢
    linear_combination -this
  refine ⟨l, t, μ, lt_of_le_of_ne hl0 ?_, lt_of_le_of_ne hl1 ?_, lt_of_le_of_ne ht0 ?_,
    lt_of_le_of_ne ht1 ?_, h⟩
  · rintro rfl; apply hp; linarith
  · rintro rfl; apply hq; linarith
  · rintro rfl; apply hr; linarith
  · rintro rfl; apply hs; linarith

theorem between_of_param {x y t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (x < x + t * (y - x) ∧ x + t * (y - x) < y) ∨ (y < x + t * (y - x) ∧ x + t * (y - x) < x) ∨
      (x = x + t * (y - x) ∧ x + t * (y - x) = y) := by
  rcases lt_trichotomy x y with h | rfl | h
  · left; constructor <;> nlinarith
  · right; right; constructor <;> ring
  · right; left; constructor <;> nlinarith

/-- **Lemma E with ties** (§14 with §18.4).  An edge crossing along `v w` (view `u = w − v`)
whose shadow is the strictly convex counterclockwise quadrilateral `(q, P a, P c, P b)`
(`q₁`–`q₄`), with `v`, `w` weakly on opposite sides of the plane `abc` (Lemma E (iii), or a
planar closing).  Unless the three far depths are equal, one of the rims `(v, a, c, b)`,
`(w, a, c, b)` has diagonals that are not weakly separated, so it is robustly unimodal
(`NWS4.isRobustUnimodal`): any other tie is allowed. -/
theorem edgePair_nws {v w a b c : ℝ³}
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫)) :
    NWS4 (quad ⟪v, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) ∨
      NWS4 (quad ⟪w, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) := by
  have i1 : det3 (c - v) (a - v) (w - v) = -det3 (a - v) (c - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (c - v) (b - v) (w - v) = det3 (b - c) (v - c) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i3 : det3 (b - a) (v - a) (w - v) = det3 (v - b) (a - b) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hsm : SegMeet v c a b (w - v) := by
    refine segMeet_of_sides ?_ ?_
    · rw [i1, i2]; nlinarith
    · rw [i3, i4]; nlinarith
  have hL : det3 (b - a) (c - a) (w - v) ≠ 0 := by rw [i4]; linarith
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := segMeet_strict hsm (by rw [i1]; linarith)
    (by rw [i2]; linarith) (by rw [i3]; linarith) (by rw [i4]; linarith)
  obtain ⟨hμ0, hμ1⟩ := edgePair_param hs1.le h hL hE
  set u := w - v with hu
  have hu0 : u ≠ 0 := by
    intro h0; apply hL; rw [h0]; simp only [det3, inner_zero_right]
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu0
  have hw : ⟪w, u⟫ = ⟪v, u⟫ + ⟪u, u⟫ := by
    conv_rhs => rw [hu]
    rw [inner_sub_left]; ring
  have i5 := congrArg (fun x => ⟪x, u⟫) h
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at i5
  refine edgePair_nws_core (E := ⟪a, u⟫ + t * (⟪b, u⟫ - ⟪a, u⟫))
    (Dv := ⟪v, u⟫ + s * (⟪c, u⟫ - ⟪v, u⟫)) (Dw := ⟪w, u⟫ + s * (⟪c, u⟫ - ⟪w, u⟫)) ?_ ?_
    (between_of_param ht0 ht1) (between_of_param hs0 hs1) (between_of_param hs0 hs1) h3
  · nlinarith [mul_nonneg hμ0 huu.le]
  · rw [hw]; nlinarith [mul_nonneg (show 0 ≤ 1 - s - μ by linarith) huu.le]

/-- **Lemma E with ties, robust form**: one of the two closings is robustly unimodal. -/
theorem edgePair_robust {v w a b c : ℝ³}
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫)) :
    IsRobustUnimodal (quad ⟪v, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) ∨
      IsRobustUnimodal (quad ⟪w, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) :=
  (edgePair_nws q₁ q₂ q₃ q₄ hE h3).imp NWS4.isRobustUnimodal NWS4.isRobustUnimodal

/-! ### Corollary 14.1 with ties -/

/-- **A 4-corner edge-view rim with ties** (`isRupert_quad_rim_int` with Theorem 18.3): as
there, with robustly unimodal depths in place of distinct depths and `NWS4`. -/
theorem isRupert_quad_rim_int_robust (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {w y y' A B : ℝ³}
    (h : ℝ) (hh : h ≠ 0) (hw : w = y - h • u) (hwV : w ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V)
    (hAV : A ∈ V) (hBV : B ∈ V) (hyM : y ∉ M) (hAM : A ∉ M) (hy'M : y' ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (y' - y) u) (t2 : 0 < det3 (A - y) (B - y) u)
    (t3 : 0 < det3 (y' - A) (B - A) u) (t4 : 0 < det3 (y' - A) (y - A) u)
    (t5 : 0 < det3 (B - y') (y - y') u) (t6 : 0 < det3 (B - y') (A - y') u)
    (t7 : 0 < det3 (y - B) (A - B) u) (t8 : 0 < det3 (y - B) (y' - B) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y → z ≠ A → z ≠ y' → z ≠ B →
      0 < det3 (A - y) (z - y) u ∧ 0 < det3 (y' - A) (z - A) u ∧
      0 < det3 (B - y') (z - y') u ∧ 0 < det3 (y - B) (z - B) u)
    (hz : IsRobustUnimodal (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y w A B h m) (hnd : NoHDNAt (V.erase w) u) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_robust V M u hu (k := 4) (by norm_num) (quad y A y' B) 0 w h hwV
    (by simp only [quad_0]; exact hw) hh ?_ ?_ ?_ ?_ ?_ hnd ?_
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
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzw (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact hz
  · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
    simpa only [quad_0, quad_1, quad_3] using hM

/-- **One closing with ties** (`isRupert_edgePair_closing` with `NWS4` in place of distinct
depths and non-separated diagonals). -/
theorem isRupert_edgePair_closing_nws (V M : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ}
    (hh : h ≠ 0) (ho : o = y - h • u) (hu : u ≠ 0) (hoV : o ∈ V) (hyV : y ∈ V) (haV : a ∈ V)
    (hbV : b ∈ V) (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hN : NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y o a b h m) (hnd : NoHDNAt (V.erase o) u) : IsRupert V := by
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  exact isRupert_quad_rim_int_robust V M u hu h hh ho hoV hyV hcV haV hbV hyM haM hcM hbM q₁
    (by rw [i2]; exact q₄) q₂ (by rw [i4]; exact q₁) q₃ (by rw [i6]; exact q₂) q₄
    (by rw [i8]; exact q₃) hrest hN.isRobustUnimodal hM hnd

/-- **Corollary 14.1 with ties** (`isRupert_edgePair` with Lemma E with ties): as
`isRupert_edgePair`, with the distinct depths on both rims replaced by "the three far depths
are not all equal". -/
theorem isRupert_edgePair_robust {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  classical
  set M := V.filter (fun z => EdgeMid v w a b z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c)
    with hM
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  have nM : ∀ z, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c → z ∉ M := by
    intro z hz hzM
    obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := mem_filter.mp hzM
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have rest : ∀ z ∈ V, z ∉ M → z ≠ v → z ≠ w → z ≠ a → z ≠ c → z ≠ b →
      EdgeHidden (w - v) v a c b z := by
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz with e | e | e | e | e | hmid | hid
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact absurd (mem_filter.mpr ⟨hz, hmid, h1, h2, h3, h5, h4⟩) hzM
    · exact hid
  rcases edgePair_nws q₁ q₂ q₃ q₄ hE h3 with hN | hN
  · -- `K_v`
    refine isRupert_edgePair_closing_nws V M (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hwV hvV haV hbV hcV (nM v (by tauto))
      (nM a (by tauto)) (nM b (by tauto)) (nM c (by tauto)) q₁ q₂ q₃ q₄ ?_ hN ?_ hnd₁
    · intro z hz hzM h1 h2 h3 h4 h5
      exact rest z hz hzM h2 h1 h3 h4 h5
    · intro m hm
      exact (mem_filter.mp hm).2.1.edgeMiddle_v
  · -- `K_w`
    refine isRupert_edgePair_closing_nws V M (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hvV hwV haV hbV hcV (nM w (by tauto)) (nM a (by tauto))
      (nM b (by tauto)) (nM c (by tauto)) (by rw [det3_vw_both]; exact q₁) q₂
      (by rw [det3_vw_right]; exact q₃) (by rw [det3_vw_left]; exact q₄) ?_ hN ?_ hnd₂
    · intro z hz hzM h1 h2 h3 h4 h5
      exact (rest z hz hzM h1 h2 h3 h4 h5).shift
    · intro m hm
      exact (mem_filter.mp hm).2.1.edgeMiddle_w

/-- **A triangle closing with ties** (`isRupert_edgeTri` with Theorem 18.3): only the three
depths of the rim not all equal. -/
theorem isRupert_edgeTri_robust {v w a b : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < det3 (a - v) (b - v) (w - v))
    (hz : ¬ (⟪v, w - v⟫ = ⟪a, w - v⟫ ∧ ⟪a, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHidden (w - v) v a b z)
    (hnd : NoHDNAt (V.erase w) (w - v)) : IsRupert V := by
  classical
  set M := V.filter (fun z => EdgeMid v w a b z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b) with hM
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at hT; simp only [det3, inner_zero_right, lt_irrefl] at hT
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  have i1 : det3 (b - a) (v - a) (w - v) = det3 (a - v) (b - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (v - b) (a - b) (w - v) = det3 (a - v) (b - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine isRupert_of_edgeView_robust V M (w - v) hu (k := 3) le_rfl (tri v a b) 0 w (-1) hwV
    (by rw [tri_0, neg_one_smul, sub_neg_eq_add]; abel) (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hvV, haV, hbV]
  · intro i hi
    obtain ⟨-, -, h1, -, h3, h4⟩ := mem_filter.mp hi
    rcases zmod3_cases i with rfl | rfl | rfl
    exacts [h1 rfl, h3 rfl, h4 rfl]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1, b2, tri_0, tri_1, tri_2, i1, i2]
    exacts [hT, hT, hT]
  · intro z hz hzM hzw hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2
    simp only [tri_0, tri_1, tri_2] at h0 h1 h2
    rcases hV z hz with e | e | e | e | hmid | ⟨r1, r2, r3⟩
    · exact absurd e h0
    · exact absurd e hzw
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd (mem_filter.mpr ⟨hz, hmid, h0, hzw, h1, h2⟩) hzM
    · rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
      exacts [r1, r2, r3]
  · rw [tri_inner]
    exact isRobustUnimodal_three hz
  · intro m hm
    rw [zmod3_zero_add_one, zmod3_zero_sub_one, tri_0, tri_1, tri_2]
    exact (mem_filter.mp hm).2.1.edgeMiddle_v

/-- **The closing by `x` with ties** (as `nws4_closing_x`, with the touching exclusion only:
the far ends `p`, `p'` not both at the depth of `y'`). -/
theorem nws4_closing_x_tie {x y y' p p' : ℝ³}
    (hS₁ : 0 < det3 (y' - p) (p' - p) (y - x)) (hS₂ : 0 < det3 (y' - x) (p' - x) (y - x))
    (hS₃ : 0 < det3 (p - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x))
    (hlow : det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ +
        det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫)
    (hN : ¬ NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
  set u := y - x
  have hsum := four_point_sum x p y' p' u
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hN ⊢
  simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
  have hY : ⟪p, u⟫ ≤ ⟪y, u⟫ ∧ ⟪p', u⟫ ≤ ⟪y, u⟫ ∧ ⟪p, u⟫ ≤ ⟪y', u⟫ ∧ ⟪p', u⟫ ≤ ⟪y', u⟫ := by
    by_contra hc
    apply hN
    constructor
    · simp only [not_and_or, not_le] at hc; exact hc
    · rcases hgood with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hx_lt : ⟪x, u⟫ < ⟪p, u⟫ ∨ ⟪x, u⟫ < ⟪p', u⟫ := by
    by_contra hc; push Not at hc
    obtain ⟨c1, c2⟩ := hc
    rcases le_total ⟪p, u⟫ ⟪p', u⟫ with hpp | hpp
    · nlinarith [mul_le_mul_of_nonneg_left c2 hS₁.le, mul_le_mul_of_nonneg_left hY4 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₂.le, mul_eq_zero_of_left hsum ⟪p', u⟫]
    · nlinarith [mul_le_mul_of_nonneg_left c1 hS₁.le, mul_le_mul_of_nonneg_left hY3 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₄.le, mul_eq_zero_of_left hsum ⟪p, u⟫]
  refine ⟨by rcases hx_lt with h | h; exacts [Or.inl h, Or.inr (Or.inl h)], ?_⟩
  by_contra hc
  simp only [not_or, not_lt] at hc
  obtain ⟨-, -, c3, c4⟩ := hc
  exact htouch ⟨by linarith, by linarith⟩

/-! ### Lemma 9.3 / Lemma 2 of §12 with ties (the octahedral quads of tiers Q and H) -/

/-- **Lemma 9.3 with ties, oriented core** (`isRupert_quad_edge_lift_core` with
Theorem 18.3). -/
theorem isRupert_quad_edge_lift_core_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (M : Finset ℝ³) (hMm : M ⊆ {m}) (hmid : m ∈ M → QuadMiddle x y p p' m)
    (hhid : m ∉ M → QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫))
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hmx, hmx', hmy, hmy', hmp, hmp'⟩ := hmO
  set V : Finset ℝ³ := insert m {x, x', y, y', p, p'} with hV
  have mx : x ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have hmemV : ∀ z ∈ V, z = m ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hnotM : ∀ z, z ≠ m → z ∉ M := fun z hz hzM => hz (mem_singleton.mp (hMm hzM))
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the middle, for either choice of `v`
  have hEM : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = y ∧ w = x ∧ hh = 1) ∨ (v = x ∧ w = y ∧ hh = -1)) →
      ∀ m' ∈ M, EdgeMiddle (y - x) v w p p' hh m' := by
    intro v w hh hvw m' hm'
    have hm'm : m' = m := mem_singleton.mp (hMm hm')
    subst hm'm
    obtain ⟨s, δ, hs0, hs1, hδ, hδ', hm⟩ := hmid hm'
    rcases hvw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases hm with hm | hm
      · exact ⟨v, s, δ, Or.inl rfl, hs0, hs1, hδ, Or.inl hm⟩
      · refine ⟨v, 1 - s, δ, Or.inl rfl, by linarith, by linarith, hδ, Or.inr ?_⟩
        rw [hm]; module
    · rcases hm with hm | hm
      · refine ⟨v, s, δ + 1 - s, Or.inl rfl, hs0, hs1, hδ', Or.inl ?_⟩
        rw [hm]; module
      · refine ⟨v, 1 - s, δ + 1 - s, Or.inl rfl, by linarith, by linarith, hδ', Or.inr ?_⟩
        rw [hm]; module
  -- the hidden point passes the edge tests
  have hH : m ∉ M → 0 < det3 (p - y) (m - y) (y - x) ∧ 0 < det3 (y' - p) (m - p) (y - x) ∧
      0 < det3 (p' - y') (m - y') (y - x) ∧ 0 < det3 (y - p') (m - p') (y - x) := by
    intro hmM
    obtain ⟨h1, h2, h3, h4⟩ := hhid hmM
    exact ⟨pos_of_mul_pos_pos (by rwa [mul_comm] at h1) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h2) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h3) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h4) hor⟩
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)
  · -- `K_y` is unimodal
    refine isRupert_of_edgeView_robust V M (y - x) hu (k := 4) (by norm_num) (quad y p y' p') 0 x 1
      (by simp [V]) (by simp only [quad_0, one_smul]; abel) one_ne_zero ?_ ?_ ?_ ?_ ?_
      hnd.1 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM y (Ne.symm hmy), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 y my hyp hyy'
      · exact E3 y my hyy' hyp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        exacts [t1, t2, t3, t4]
      · exact absurd h hzw
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h h0
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact hN.isRobustUnimodal
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM y x 1 (Or.inl ⟨rfl, rfl, rfl⟩)
  · -- `K_x` is unimodal (the closing by `x` of Lemma 9.3)
    have hS₁ := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) (y - x) := by
      rw [← det3_cyc x y' p']; exact E3 x mx hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) (y - x) := by
      rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hN' := nws4_closing_x_tie hS₁ hS₂ hS₃ hS₄ (quad_edge_lower F hS₁ hS₂ hS₃ hS₄) hN hgood
      htouch
    refine isRupert_of_edgeView_robust V M (y - x) hu (k := 4) (by norm_num) (quad x p y' p') 0 y (-1)
      (by simp [V]) (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd.2 ?_
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM x (Ne.symm hmx), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 x mx hxp hxy'
      · exact E3 x mx hxy' hxp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact t1
        · exact t2
        · exact t3
        · rw [det3_shift_p']; exact t4
      · exact absurd h h0
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h hzw
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact hN'.isRobustUnimodal
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM x y (-1) (Or.inr ⟨rfl, rfl, rfl⟩)

/-- **Lemma 2 of §12 with ties** (`isRupert_quad_edge_lift` with Theorem 18.3): the closing of
Lemma 9.3 has diagonals that are not weakly separated, hence robustly unimodal rim, whatever
its ties; the only depth condition left is that the far ends `p`, `p'` are not both at the
depth of `y'` (two ties, the touching of §9). -/
theorem isRupert_quad_edge_lift_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hm : QuadMiddle x y p p' m ∨ QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫))
    (hnd : NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase x) (y - x) ∧
      NoHDNAt ((insert m ({x, x', y, y', p, p'} : Finset ℝ³)).erase y) (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  -- the set `M` of middles
  obtain ⟨M, hMm, hmid, hhid⟩ : ∃ M : Finset ℝ³, M ⊆ {m} ∧ (m ∈ M → QuadMiddle x y p p' m) ∧
      (m ∉ M → QuadHidden x y y' p p' m) := by
    rcases hm with h | h
    · exact ⟨{m}, subset_rfl, fun _ => h, fun h' => absurd (mem_singleton_self m) h'⟩
    · exact ⟨∅, empty_subset _, fun h' => absurd h' (notMem_empty m), fun _ => h⟩
  have e : (insert m {x, x', y, y', p', p} : Finset ℝ³) = insert m {x, x', y, y', p, p'} := by
    rw [Finset.pair_comm p' p]
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := isRupert_quad_edge_lift_core_tie F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
      (by rwa [min_comm]) M hMm (fun h => (hmid h).swap) (fun h => (hhid h).swap)
      ⟨hmO.1, hmO.2.1, hmO.2.2.1, hmO.2.2.2.1, hmO.2.2.2.2.2, hmO.2.2.2.2.1⟩
      (fun h => htouch ⟨h.2, h.1⟩) (by rw [e]; exact hnd)
    rwa [e] at this
  · exact isRupert_quad_edge_lift_core_tie F hq₁ hq₂ hpos hgood M hMm hmid hhid hmO htouch hnd

/-! ### Corollary 14.1 with the uniform tilt and ties -/

/-- **`isRupert_quad_uniform` with ties**: the rim's diagonals not weakly separated. -/
theorem isRupert_quad_uniform_nws (V M : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ} (hh : h ≠ 0)
    (ho : o = y - h • u) (hu : u ≠ 0) (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hN : NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u)
    (hnd : NoHDNAt (V.erase o) u) : IsRupert V := by
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not the other axle end
  have hoy : y ≠ o := by
    intro e
    have h2 : y - h • u = y := by rw [ho] at e; exact e.symm
    have : h • u = 0 := by
      calc h • u = y - (y - h • u) := by abel
        _ = 0 := by rw [h2, sub_self]
    exact (smul_ne_zero hh hu) this
  have hoa : a ≠ o := by
    intro e
    have : det3 (a - y) (c - y) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hoc : c ≠ o := by
    intro e
    have : det3 (b - c) (y - c) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hob : b ≠ o := by
    intro e
    have : det3 (y - b) (a - b) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_uniform_robust V M {o} (V.erase o) u hu (k := 4) (by norm_num)
    (quad y a c b) ?_ ?_ ?_ ?_ ?_ hnd ?_ hM ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, haV, hcV, hbV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, haM, hcM, hbM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [q₁, by rw [i2]; exact q₄, q₂, by rw [i4]; exact q₁, q₃, by rw [i6]; exact q₂, q₄,
      by rw [i8]; exact q₃]
  · intro z hz hzM hzD hzx i
    have hzo : z ≠ o := fun e => hzD (by rw [e]; exact mem_singleton_self o)
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzo (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact hN.isRobustUnimodal
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_erase]
    exacts [⟨hoy, hyV⟩, ⟨hoa, haV⟩, ⟨hoc, hcV⟩, ⟨hob, hbV⟩]
  · intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨0, h, hh, by rw [quad_0]; exact ho⟩

/-- **Corollary 14.1 with the uniform tilt and ties** (`isRupert_edgePair_uniform` with Lemma E
with ties): only the three far depths not all equal. -/
theorem isRupert_edgePair_uniform_robust {v w a b c : ℝ³} (V M : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hvM : v ∉ M) (hwM : w ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z ∉ M → z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨
      EdgeHidden (w - v) v a c b z)
    (hM₁ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad v a c b i + s • (quad v a c b (i + 1) - quad v a c b i) + δ • (w - v))
    (hM₂ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad w a c b i + s • (quad w a c b (i + 1) - quad w a c b i) + δ • (w - v))
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  rcases edgePair_nws q₁ q₂ q₃ q₄ hE h3 with hN | hN
  · -- `K_v`
    refine isRupert_quad_uniform_nws V M (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hvV haV hbV hcV hvM haM hbM hcM q₁ q₂
      q₃ q₄ ?_ hN hM₁ hnd₁
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h2
    · exact absurd e h1
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid
  · -- `K_w`
    refine isRupert_quad_uniform_nws V M (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hwV haV hbV hcV hwM haM hbM hcM
      (by rw [det3_vw_both]; exact q₁) q₂ (by rw [det3_vw_right]; exact q₃)
      (by rw [det3_vw_left]; exact q₄) ?_ hN hM₂ hnd₂
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid.shift

/-! ### General position up to single ties -/

/-- **At most one tie at the view `u`**: two pairs of distinct points of `V` with equal depths
along `u` are the same pair. -/
def OneTieAt (V : Finset ℝ³) (u : ℝ³) : Prop :=
  ∀ s ∈ V, ∀ t ∈ V, ∀ s' ∈ V, ∀ t' ∈ V, s ≠ t → s' ≠ t' → ⟪s, u⟫ = ⟪t, u⟫ →
    ⟪s', u⟫ = ⟪t', u⟫ → (s = s' ∧ t = t') ∨ (s = t' ∧ t = s')

/-- **General position up to single ties** (the replacement of `GenPos` in the tie-tolerant
entry theorems): no two segments between points of `V` are parallel (the first clause of
`GenPos`), and at the view along each segment at most one pair of points has equal depths
(`GenPos` asks for none).  Both failures are of codimension 2: a segment parallel to another,
or a segment orthogonal to two others. -/
structure GenPosTie (V : Finset ℝ³) : Prop where
  par : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V, a ≠ b → c ≠ d → ({a, b} : Finset ℝ³) ≠ {c, d} →
    ∀ t : ℝ, b - a ≠ t • (d - c)
  tie : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → OneTieAt V (w - v)

/-- `GenPos` (no two segments parallel or orthogonal) gives `GenPosTie`: there are no ties at
all at the edge views. -/
theorem GenPos.genPosTie {V : Finset ℝ³} (h : GenPos V) : GenPosTie V where
  par a ha b hb c hc d hd hab hcd hne := (h a ha b hb c hc d hd hab hcd hne).1
  tie v hv w hw hvw s hs t ht s' hs' t' ht' hst _ e _ := by
    exfalso
    by_cases hp : ({s, t} : Finset ℝ³) = {v, w}
    · have hw' : w ∈ ({s, t} : Finset ℝ³) := hp ▸ (by simp)
      have hv' : v ∈ ({s, t} : Finset ℝ³) := hp ▸ (by simp)
      simp only [mem_insert, mem_singleton] at hw' hv'
      have hu : w - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvw)
      have key : ⟪w - v, w - v⟫ = 0 := by
        rcases hv' with rfl | rfl <;> rcases hw' with rfl | rfl
        · exact absurd rfl hvw
        · rw [inner_sub_left, e, sub_self]
        · rw [inner_sub_left, e, sub_self]
        · exact absurd rfl hvw
      exact hu (inner_self_eq_zero.mp key)
    · exact (h s hs t ht v hv w hw hst hvw hp).2 (by rw [inner_sub_left, e, sub_self])

/-- `GenPosTie`: two segments that are not the same pair are not parallel (as
`GenPos.ne_smul`). -/
theorem GenPosTie.ne_smul {V : Finset ℝ³} (hg : GenPosTie V) {s t x y : ℝ³} (hs : s ∈ V)
    (ht : t ∈ V) (hx : x ∈ V) (hy : y ∈ V) (hst : s ≠ t) (hxy : x ≠ y) (hty : t ≠ x ∧ t ≠ y)
    (r : ℝ) : t - s ≠ r • (y - x) := by
  have hpair : ({s, t} : Finset ℝ³) ≠ {x, y} := by
    intro heq
    have : t ∈ ({x, y} : Finset ℝ³) := heq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    tauto
  exact hg.par s hs t ht x hx y hy hst hxy hpair r

/-- `GenPosTie`: at an edge view, no three points have equal depths (two ties). -/
theorem GenPosTie.noTriple {V : Finset ℝ³} (hg : GenPosTie V) {v w s t r : ℝ³} (hv : v ∈ V)
    (hw : w ∈ V) (hs : s ∈ V) (ht : t ∈ V) (hr : r ∈ V) (hvw : v ≠ w) (hst : s ≠ t)
    (htr : t ≠ r) (hsr : s ≠ r) : ¬ (⟪s, w - v⟫ = ⟪t, w - v⟫ ∧ ⟪t, w - v⟫ = ⟪r, w - v⟫) := by
  rintro ⟨e1, e2⟩
  rcases hg.tie v hv w hw hvw s hs t ht t ht r hr hst htr e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hst h1
  · exact hsr h1

/-- `GenPosTie` at a quad edge `x → y` of an octahedron with one more point: the far ends
`p`, `p'` are not both at the depth of `y'` (the touching of §9). -/
theorem GenPosTie.touch_oct {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hg : GenPosTie (insert m ({x, x', y, y', p, p'} : Finset ℝ³))) :
    ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  rintro ⟨e1, e2⟩
  exact hg.noTriple (by simp) (by simp) (by simp) (by simp) (by simp) hxy (Ne.symm hy'p)
    hy'p' hpp' ⟨e1, e2.symm⟩

/-- **A planar 4-corner rim with ties** (`nws4_of_planar_quad`): a convex plane quadrilateral
`P₀ P₁ P₂ P₃` (`P₂ = P₀ + α (P₁ − P₀) + β (P₃ − P₀)`, `α, β > 0`, `α + β > 1`) has diagonals
that are not weakly separated unless `P₀`, `P₁`, `P₃` are at one depth. -/
theorem nws4_of_planar_quad_tie {P₀ P₁ P₂ P₃ u : ℝ³} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : 1 < α + β) (h : P₂ = P₀ + α • (P₁ - P₀) + β • (P₃ - P₀))
    (hne : ¬ (⟪P₀, u⟫ = ⟪P₁, u⟫ ∧ ⟪P₀, u⟫ = ⟪P₃, u⟫)) :
    NWS4 (quad ⟪P₀, u⟫ ⟪P₁, u⟫ ⟪P₂, u⟫ ⟪P₃, u⟫) := by
  by_cases h01 : ⟪P₀, u⟫ = ⟪P₁, u⟫
  · exact NWS4_quad_swap (nws4_of_planar_quad hβ hα (by linarith)
      (by rw [h]; abel) fun h03 => hne ⟨h01, h03⟩)
  · exact nws4_of_planar_quad hα hβ hαβ h h01

/-! ### Robust unimodality by perturbation (Lemma 18.4 (α) for an explicit family) -/

theorem IsRobustUnimodal.neg {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) :
    IsRobustUnimodal (fun i => -z i) where
  noPeaks B a b c d hab hbc hcd hdk h := by
    simp only [neg_lt_neg_iff] at h
    exact hz.noPeaks' B hab hbc hcd hdk ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple i j l hij hjl hil (neg_inj.mp e1) (neg_inj.mp e2)
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have := hz.noLevelRun B a b c d hab hbc hcd hdk (neg_inj.mp e)
    simp only [neg_lt_neg_iff]
    exact ⟨fun h => this.2 ⟨h.1, h.2⟩, fun h => this.1 ⟨h.1, h.2⟩⟩

/-- Strict comparisons of continuous functions persist near `0`. -/
theorem eventually_lt_near {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f 0 < g 0) : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), f ε < g ε :=
  ((hf.tendsto 0).eventually_lt (hg.tendsto 0) h).filter_mono nhdsWithin_le_nhds

/-- **Robust unimodality from a perturbation** (Lemma 18.4 (α) for an explicit family).  A
cyclic sequence `z` with at most one tied pair is robustly unimodal if it is unimodal when its
entries are distinct, and if, for its tied pair `a, b`, some direction `d` separates the pair
(`d a ≠ d b`) and every small perturbation `z + ε d` (`ε ≠ 0`) with distinct entries is
unimodal: then `z` is a limit of unimodal sequences from both sides of the tie. -/
theorem isRobustUnimodal_of_perturb {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hone : ∀ a b a' b', a ≠ b → a' ≠ b' → z a = z b → z a' = z b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (huni : Function.Injective z → IsCyclicUnimodal z)
    (hpert : ∀ a b, a ≠ b → z a = z b → ∃ d : ZMod k → ℝ, d a ≠ d b ∧
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (fun i => z i + ε * d i) →
        IsCyclicUnimodal (fun i => z i + ε * d i)) :
    IsRobustUnimodal z := by
  classical
  by_cases hinj : Function.Injective z
  · exact (huni hinj).isRobustUnimodal
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, z a = z b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨a, b, h1, h2⟩ := hinj
    exact ⟨a, b, h1, h2⟩
  obtain ⟨d, hd, hev⟩ := hpert a b hne hab
  set zs : ℝ → ZMod k → ℝ := fun ε i => z i + ε * d i with hzs
  have hlim0 : ∀ i, Tendsto (fun ε => zs ε i) (𝓝 (0 : ℝ)) (𝓝 (z i)) := by
    intro i
    have : Tendsto (fun ε : ℝ => z i + ε * d i) (𝓝 0) (𝓝 (z i + 0 * d i)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
    simpa using this
  -- eventually injective off `0`
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x y, z x ≠ z y → zs ε x ≠ zs ε y := by
    refine Filter.eventually_all.mpr fun x => Filter.eventually_all.mpr fun y => ?_
    by_cases hxy : z x = z y
    · exact Filter.Eventually.of_forall fun _ h => absurd hxy h
    · rcases lt_or_gt_of_ne hxy with h | h
      · exact ((hlim0 x).eventually_lt (hlim0 y) h).mono fun ε hε _ => hε.ne
      · exact ((hlim0 y).eventually_lt (hlim0 x) h).mono fun ε hε _ => hε.ne'
  have hinj' : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (zs ε) := by
    filter_upwards [hsep.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε h1 hε
    intro x y hxy
    by_contra hne'
    by_cases hz : z x = z y
    · have hε0 : ε ≠ 0 := hε
      have key : ε * (d x - d y) = 0 := by
        have : z x + ε * d x = z y + ε * d y := hxy
        linarith
      rcases hone a b x y hne hne' hab hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hd (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hε0))
      · exact hd (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hε0)).symm
    · exact h1 x y hz hxy
  have hrob : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), IsRobustUnimodal (zs ε) :=
    (hev.and hinj').mono fun ε h => (h.1 h.2).isRobustUnimodal
  have hone' : ∀ x y, x ≠ y → z x = z y → (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    intro x y hxy h
    rcases hone x y a b hxy hne h hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hgt : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have hlt : 𝓝[<] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_lt hx
  have lim : ∀ (l : Filter ℝ), l ≤ 𝓝[≠] (0 : ℝ) → ∀ i, Tendsto (fun ε => zs ε i) l (𝓝 (z i)) :=
    fun l hl i => (hlim0 i).mono_left (hl.trans nhdsWithin_le_nhds)
  -- on each side of `0` the tie is broken one way
  have side : ∀ ε, zs ε b - zs ε a = ε * (d b - d a) := by
    intro ε; simp only [hzs]; linarith [hab]
  rcases lt_or_gt_of_ne hd with hlt' | hgt'
  · -- `d a < d b`: `b` above `a` for `ε > 0`
    refine isRobustUnimodal_of_tendsto_single_tie (i := b) (j := a) (l := 𝓝[>] (0 : ℝ))
      (l' := 𝓝[<] (0 : ℝ)) (zs := zs) (zs' := zs) (fun x y hxy h => ?_) (lim _ hgt) (lim _ hlt)
      ?_ ?_
    · rcases hone' x y hxy h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · refine ((hrob.filter_mono hgt).and self_mem_nhdsWithin).frequently.mono fun ε h => ⟨h.1, ?_⟩
      have := side ε
      have h2 : (0 : ℝ) < ε := h.2
      nlinarith [mul_pos h2 (sub_pos.mpr hlt')]
    · refine ((hrob.filter_mono hlt).and self_mem_nhdsWithin).frequently.mono fun ε h => ⟨h.1, ?_⟩
      have := side ε
      have h2 : ε < 0 := h.2
      nlinarith [mul_pos (neg_pos.mpr h2) (sub_pos.mpr hlt')]
  · refine isRobustUnimodal_of_tendsto_single_tie (i := a) (j := b) (l := 𝓝[>] (0 : ℝ))
      (l' := 𝓝[<] (0 : ℝ)) (zs := zs) (zs' := zs) hone' (lim _ hgt) (lim _ hlt) ?_ ?_
    · refine ((hrob.filter_mono hgt).and self_mem_nhdsWithin).frequently.mono fun ε h => ⟨h.1, ?_⟩
      have := side ε
      have h2 : (0 : ℝ) < ε := h.2
      nlinarith [mul_pos h2 (sub_pos.mpr hgt')]
    · refine ((hrob.filter_mono hlt).and self_mem_nhdsWithin).frequently.mono fun ε h => ⟨h.1, ?_⟩
      have := side ε
      have h2 : ε < 0 := h.2
      nlinarith [mul_pos (neg_pos.mpr h2) (sub_pos.mpr hgt')]

/-- At most one tie at `u` among the points of `V` gives at most one tied pair of positions on
a rim of distinct points of `V`. -/
theorem OneTieAt.rim {V : Finset ℝ³} {u : ℝ³} (h : OneTieAt V u) {k : ℕ} {x : ZMod k → ℝ³}
    (hxV : ∀ i, x i ∈ V) (hx : Function.Injective x) :
    ∀ a b a' b', a ≠ b → a' ≠ b' → ⟪x a, u⟫ = ⟪x b, u⟫ → ⟪x a', u⟫ = ⟪x b', u⟫ →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  intro a b a' b' hab ha'b' e1 e2
  rcases h _ (hxV a) _ (hxV b) _ (hxV a') _ (hxV b') (hx.ne hab) (hx.ne ha'b') e1 e2 with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hx h1, hx h2⟩
  · exact Or.inr ⟨hx h1, hx h2⟩

/-- **Robust unimodality from an open criterion**: a cyclic sequence with at most one tied pair
is robustly unimodal if a condition `P` holds on a neighbourhood of it and every sequence with
distinct entries satisfying `P` is unimodal (for instance `P` a conjunction of strict
inequalities that excludes every two-peaked pattern). -/
theorem isRobustUnimodal_of_nhds {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hone : ∀ a b a' b', a ≠ b → a' ≠ b' → z a = z b → z a' = z b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (P : (ZMod k → ℝ) → Prop) (hP : ∀ᶠ y in 𝓝 z, P y)
    (huni : ∀ y, P y → Function.Injective y → IsCyclicUnimodal y) : IsRobustUnimodal z := by
  classical
  refine isRobustUnimodal_of_perturb hone (fun hinj => huni z hP.self_of_nhds hinj) ?_
  intro a b hab _
  refine ⟨fun i => if i = a then 1 else 0, by simp [Ne.symm hab], ?_⟩
  have hT : Tendsto (fun ε : ℝ => fun i => z i + ε * (if i = a then (1 : ℝ) else 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have : Tendsto (fun ε : ℝ => z i + ε * (if i = a then (1 : ℝ) else 0)) (𝓝 0)
        (𝓝 (z i + 0 * (if i = a then (1 : ℝ) else 0))) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  filter_upwards [hT.eventually hP] with ε hε hinj using huni _ hε hinj

/-- At most one tie at `u` on a five-corner rim of distinct points of `V`, in the form used by
`isRobustUnimodal_of_nhds`. -/
theorem OneTieAt.rim5 {V : Finset ℝ³} {u : ℝ³} (h : OneTieAt V u) {p₀ p₁ p₂ p₃ p₄ : ℝ³}
    (h₀ : p₀ ∈ V) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V) (h₄ : p₄ ∈ V)
    (hinj : Function.Injective (quint p₀ p₁ p₂ p₃ p₄)) :
    ∀ a b a' b', a ≠ b → a' ≠ b' →
      quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ a =
        quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ b →
      quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ a' =
        quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ b' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  have e : ∀ i, quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ i = ⟪quint p₀ p₁ p₂ p₃ p₄ i, u⟫ := by
    intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
  intro a b a' b' hab ha'b' e1 e2
  rw [e, e] at e1 e2
  exact h.rim (x := quint p₀ p₁ p₂ p₃ p₄)
    (fun i => by rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> assumption) hinj
    a b a' b' hab ha'b' e1 e2

/-- A strict comparison of two entries holds near a sequence where it holds. -/
theorem eventually_entry_lt {k : ℕ} {z : ZMod k → ℝ} {i j : ZMod k} (h : z i < z j) :
    ∀ᶠ y in 𝓝 z, y i < y j :=
  ((continuous_apply i).tendsto z).eventually_lt ((continuous_apply j).tendsto z) h

end Minimality

end
