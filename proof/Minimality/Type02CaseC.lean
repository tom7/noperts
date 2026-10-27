module

public import Minimality.RobustEdge
public import Minimality.SevenTypes

@[expose] public section

/-!
# Type 02, case (c): Lemma E at the edge `34` (`FEWER-FACES-PROOFS.md` Lemma 23.12, §24.6)

Type 02 has the faces `012`, `0134`, `0235`, `1246`, `256`, `3456`.  Lemma 23.12: at the edge
`34` the faces `0134`, `3456` are seen edge-on, and the rim of the closing at `3` (or at `4`) is
`(3, a, 2, b)`, with `a ∈ {0, 1}` and `b ∈ {5, 6}` the far ends.  Every one of the four rims is
a Lemma E pair (`isRupert_edgePair_robust`, `RobustEdge.lean`): for `(a, b) = (0, 5)` the rim is
the face `0235` and for `(1, 6)` the face `1246` (planar closings), and for `(0, 6)`, `(1, 5)`
the points `3`, `4` lie weakly on opposite sides of the plane `a 2 b`.  This holds at every
shape of the type, with no case-(c) hypothesis, so it closes the case-(c) triple tie of the view
of `0235`, `1246` as well (the paper uses it only there).

The exceptions are those of §24.6, with the vertical far edge as in Theorem B
(`isRupert_type02`): `Type02EdgeGen x` asks

* the horizontal-double-normal exclusion `NoHDNAt` for both reduced point sets of the closings at
  the view `x 4 - x 3` (a codimension-1 condition at a fixed view, §22 / Lemma 7.4);
* `(G1)`: `x 1 - x 0` and `x 6 - x 5` are not parallel to `x 4 - x 3` (a codimension-1
  condition each: a vertical far edge, closed in the paper by the limit machinery of 18.1, 18.2);
* the far depths are not all equal: for the far ends `(a, b)` of the two faces at the edge,
  `x a`, `x 2`, `x b` are not at one depth along `x 4 - x 3` (codimension 2; with `NoHDNAt` this
  is the "two ties" of §6).

`isRupert_type02_edge34` proves `IsRupert` from the six facets under `Type02EdgeGen`, and
`type02_edge34_false` is the form for the skeleton: `Type02EdgeGen x → False` for a realized
nopert of type 02.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

namespace Type02CaseC

/-- The `det3` of three vectors in the basis `E1, E2, E3`. -/
theorem det3_coord (A N E : ℝ³) (a1 b1 c1 a2 b2 c2 a3 b3 c3 : ℝ) :
    det3 (a1 • A + b1 • N + c1 • E) (a2 • A + b2 • N + c2 • E) (a3 • A + b3 • N + c3 • E) =
      det3 A N E * (a1 * (b2 * c3 - c2 * b3) - b1 * (a2 * c3 - c2 * a3) +
        c1 * (a2 * b3 - b2 * a3)) := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, RCLike.inner_apply, conj_trivial]
  simp
  ring

/-- `det3_coord` with the last vector the third basis vector. -/
theorem det3_coord_u (A N E : ℝ³) (a1 b1 c1 a2 b2 c2 : ℝ) :
    det3 (a1 • A + b1 • N + c1 • E) (a2 • A + b2 • N + c2 • E) E =
      det3 A N E * (a1 * b2 - a2 * b1) := by
  have h := det3_coord A N E a1 b1 c1 a2 b2 c2 0 0 1
  simp only [zero_smul, one_smul, zero_add] at h
  rw [h]; ring

/-- Swapping `a` and `b` in `EdgeMid`. -/
theorem edgeMid_symm {v w a b m : ℝ³} (h : EdgeMid v w a b m) : EdgeMid v w b a m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inl (by rw [h]; module))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inl (by rw [h]; module)⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inr (by rw [h]; module)))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inl (by rw [h]; module)))⟩

/-- The `det3` of the four-point test is symmetric under swapping `a` and `b`. -/
theorem hE_swap (a b c p : ℝ³) :
    det3 (a - b) (c - b) (p - b) = - det3 (b - a) (c - a) (p - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **Lemma E in coordinates, positive orientation**: the rim `(v, a, c, b)` with `a` on the
`E1` ray, `b` on the `E2` ray (each up to a multiple of the view `w - v`), and `c` beyond the
chord. -/
theorem rim_core (V : Finset ℝ³) {v w a b c E1 E2 : ℝ³}
    (hD : 0 < det3 E1 E2 (w - v)) {tA tB ζa ζb α β γ : ℝ}
    (ha : a = v + tA • E1 + ζa • (w - v)) (hb : b = v + tB • E2 + ζb • (w - v))
    (hc : c = v + α • E1 + β • E2 + γ • (w - v))
    (htA : 0 < tA) (htB : 0 < tB) (hα : 0 < α) (hβ : 0 < β)
    (hch : tA * tB < α * tB + β * tA)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  set u := w - v with hu
  have e1 : a - v = tA • E1 + (0 : ℝ) • E2 + ζa • u := by rw [ha]; module
  have e2 : c - v = α • E1 + β • E2 + γ • u := by rw [hc]; module
  have e4 : c - a = (α - tA) • E1 + β • E2 + (γ - ζa) • u := by rw [hc, ha]; module
  have e5 : b - a = (-tA) • E1 + tB • E2 + (ζb - ζa) • u := by rw [hb, ha]; module
  have e6 : b - c = (-α) • E1 + (tB - β) • E2 + (ζb - γ) • u := by rw [hb, hc]; module
  have e7 : v - c = (-α) • E1 + (-β) • E2 + (-γ) • u := by rw [hc]; module
  have e8 : v - b = (0 : ℝ) • E1 + (-tB) • E2 + (-ζb) • u := by rw [hb]; module
  have e9 : a - b = tA • E1 + (-tB) • E2 + (ζa - ζb) • u := by rw [hb, ha]; module
  have q₁ : 0 < det3 (a - v) (c - v) u := by
    rw [e1, e2, det3_coord_u]; nlinarith [mul_pos hD (mul_pos htA hβ)]
  have q₂ : 0 < det3 (c - a) (b - a) u := by
    rw [e4, e5, det3_coord_u]
    have : 0 < α * tB + β * tA - tA * tB := by linarith
    nlinarith [mul_pos hD this]
  have q₃ : 0 < det3 (b - c) (v - c) u := by
    rw [e6, e7, det3_coord_u]; nlinarith [mul_pos hD (mul_pos hα htB)]
  have q₄ : 0 < det3 (v - b) (a - b) u := by
    rw [e8, e9, det3_coord_u]; nlinarith [mul_pos hD (mul_pos htA htB)]
  exact isRupert_edgePair_robust V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄ hE h3
    (fun z hz => by
      rcases hV z hz with h | h | h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
        Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))])
    hnd₁ hnd₂

/-- **Lemma E in coordinates, either orientation.** -/
theorem rim_core' (V : Finset ℝ³) {v w a b c E1 E2 : ℝ³}
    (hD : det3 E1 E2 (w - v) ≠ 0) {tA tB ζa ζb α β γ : ℝ}
    (ha : a = v + tA • E1 + ζa • (w - v)) (hb : b = v + tB • E2 + ζb • (w - v))
    (hc : c = v + α • E1 + β • E2 + γ • (w - v))
    (htA : 0 < tA) (htB : 0 < tB) (hα : 0 < α) (hβ : 0 < β)
    (hch : tA * tB < α * tB + β * tA)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hD' : 0 < det3 E2 E1 (w - v) := by
      have : det3 E2 E1 (w - v) = - det3 E1 E2 (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    refine rim_core V (a := b) (b := a) hD' hb ha (by rw [hc]; module) htB htA hβ hα
      (by linarith) hvV hwV hbV haV hcV ?_ ?_ ?_ hnd₁ hnd₂
    · rw [hE_swap a b c v, hE_swap a b c w]; nlinarith [hE]
    · exact fun ⟨h1, h2⟩ => h3 ⟨h2.symm, h1.symm⟩
    · intro z hz
      rcases hV z hz with h | h | h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (edgeMid_symm h)))))]
  · exact rim_core V hpos ha hb hc htA htB hα hβ hch hvV hwV haV hbV hcV hE h3 hV hnd₁ hnd₂

/-! ### Coordinates in the frame `e0 = x0 - x3`, `e5 = x5 - x3`, `u = x4 - x3` -/

/-- Cramer's rule in `ℝ³`. -/
theorem cramer3 (e0 e5 u p : ℝ³) :
    det3 e0 e5 u • p = det3 p e5 u • e0 + det3 e0 p u • e5 + det3 e0 e5 p • u := by
  ext i; fin_cases i <;> simp [det3_expand] <;> ring

/-- If `det3 e0 e5 u ≠ 0`, every point has coordinates in the frame `q; e0, e5, u`. -/
theorem exists_coords {e0 e5 u : ℝ³} (hD : det3 e0 e5 u ≠ 0) (p q : ℝ³) :
    ∃ α β γ : ℝ, p = q + α • e0 + β • e5 + γ • u := by
  refine ⟨det3 (p - q) e5 u / det3 e0 e5 u, det3 e0 (p - q) u / det3 e0 e5 u,
    det3 e0 e5 (p - q) / det3 e0 e5 u, ?_⟩
  have h := cramer3 e0 e5 u (p - q)
  have h2 : p = q + (det3 e0 e5 u)⁻¹ • (det3 e0 e5 u • (p - q)) := by
    rw [smul_smul, inv_mul_cancel₀ hD, one_smul]; abel
  rw [h] at h2
  refine h2.trans ?_
  simp only [smul_add, smul_smul, div_eq_inv_mul]
  abel

/-- An affine function on a combination. -/
theorem aff_comb (f : ℝ³ →ᵃ[ℝ] ℝ) (q e0 e5 u : ℝ³) (α β γ : ℝ) :
    f (q + α • e0 + β • e5 + γ • u) =
      f q + α * f.linear e0 + β * f.linear e5 + γ * f.linear u := by
  have h : q + α • e0 + β • e5 + γ • u = (α • e0 + β • e5 + γ • u) +ᵥ q := by
    rw [vadd_eq_add]; abel
  rw [h, f.map_vadd]
  simp only [vadd_eq_add, map_add, map_smul, smul_eq_mul]
  ring

theorem lin_sub (f : ℝ³ →ᵃ[ℝ] ℝ) (p q : ℝ³) : f.linear (p - q) = f p - f q := by
  have := f.linearMap_vsub p q
  simpa using this

/-- **The frame is a basis**: three facets through the edge `34` and the points `0`, `5`
separate `e0`, `e5`, `u`. -/
theorem det_ne_zero (e0 e5 u : ℝ³) (L1 L2 L3 : ℝ³ →ₗ[ℝ] ℝ)
    (h10 : L1 e0 = 0) (h15 : L1 e5 ≠ 0) (h20 : L2 e0 ≠ 0)
    (h30 : L3 e0 = 0) (h35 : L3 e5 = 0) (h3u : L3 u ≠ 0) : det3 e0 e5 u ≠ 0 := by
  intro hD
  have key : ∀ p, det3 p e5 u • e0 + det3 e0 p u • e5 + det3 e0 e5 p • u = 0 := by
    intro p; rw [← cramer3, hD, zero_smul]
  have hC : ∀ p, det3 e0 e5 p = 0 := by
    intro p
    have := congrArg L3 (key p)
    simp only [map_add, map_smul, smul_eq_mul, h30, h35, mul_zero, zero_add, map_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h h3u
  have hcr : cross e0 e5 = 0 := by
    have := hC (cross e0 e5)
    exact inner_self_eq_zero.mp this
  have he0 : e0 ≠ 0 := by
    intro h; rw [h, map_zero] at h20; exact h20 rfl
  have := eq_smul_of_cross_eq_zero he0 hcr
  apply h15
  rw [this, map_smul, h10, smul_zero]

/-- The `det3` of differences of frame points. -/
theorem det3_pc (v A N E : ℝ³) (x0 y0 z0 x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) :
    det3 ((v + x1 • A + y1 • N + z1 • E) - (v + x0 • A + y0 • N + z0 • E))
        ((v + x2 • A + y2 • N + z2 • E) - (v + x0 • A + y0 • N + z0 • E))
        ((v + x3 • A + y3 • N + z3 • E) - (v + x0 • A + y0 • N + z0 • E)) =
      det3 A N E * ((x1 - x0) * ((y2 - y0) * (z3 - z0) - (z2 - z0) * (y3 - y0)) -
        (y1 - y0) * ((x2 - x0) * (z3 - z0) - (z2 - z0) * (x3 - x0)) +
        (z1 - z0) * ((x2 - x0) * (y3 - y0) - (y2 - y0) * (x3 - x0))) := by
  have h1 : (v + x1 • A + y1 • N + z1 • E) - (v + x0 • A + y0 • N + z0 • E) =
      (x1 - x0) • A + (y1 - y0) • N + (z1 - z0) • E := by module
  have h2 : (v + x2 • A + y2 • N + z2 • E) - (v + x0 • A + y0 • N + z0 • E) =
      (x2 - x0) • A + (y2 - y0) • N + (z2 - z0) • E := by module
  have h3 : (v + x3 • A + y3 • N + z3 • E) - (v + x0 • A + y0 • N + z0 • E) =
      (x3 - x0) • A + (y3 - y0) • N + (z3 - z0) • E := by module
  rw [h1, h2, h3, det3_coord]

/-- The four-point test `hE` of Lemma E in frame coordinates, for `v` and `w = v + u`. -/
theorem hE_coords (v A N E a b c : ℝ³) (xa ya za xb yb zb xc yc zc : ℝ)
    (ha : a = v + xa • A + ya • N + za • E) (hb : b = v + xb • A + yb • N + zb • E)
    (hc : c = v + xc • A + yc • N + zc • E) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (v + E - a) =
      (det3 A N E) ^ 2 *
        (((xb - xa) * ((yc - ya) * (0 - za) - (zc - za) * (0 - ya)) -
          (yb - ya) * ((xc - xa) * (0 - za) - (zc - za) * (0 - xa)) +
          (zb - za) * ((xc - xa) * (0 - ya) - (yc - ya) * (0 - xa))) *
        ((xb - xa) * ((yc - ya) * (1 - za) - (zc - za) * (0 - ya)) -
          (yb - ya) * ((xc - xa) * (1 - za) - (zc - za) * (0 - xa)) +
          (zb - za) * ((xc - xa) * (0 - ya) - (yc - ya) * (0 - xa)))) := by
  have hv : v = v + (0 : ℝ) • A + (0 : ℝ) • N + (0 : ℝ) • E := by module
  have hw : v + E = v + (0 : ℝ) • A + (0 : ℝ) • N + (1 : ℝ) • E := by module
  have e1 := det3_pc v A N E xa ya za xb yb zb xc yc zc 0 0 0
  have e2 := det3_pc v A N E xa ya za xb yb zb xc yc zc 0 0 1
  rw [← ha, ← hb, ← hc, ← hv] at e1
  rw [← ha, ← hb, ← hc, ← hw] at e2
  rw [e1, e2]; ring

/-! ### Middles -/

/-- A middle above the chord from `w`, on the face of `a`. -/
theorem mid_a_up {v w a m E1 : ℝ³} {s γ : ℝ} (ha : a = v + E1) (hs0 : 0 < s) (hs1 : s < 1)
    (hγ : 0 < γ - 1 + s) (hm : m = v + s • E1 + γ • (w - v)) (b : ℝ³) : EdgeMid v w a b m :=
  ⟨s, γ - 1 + s, hs0, hs1, hγ, Or.inr (Or.inr (Or.inl (by rw [hm, ha]; module)))⟩

/-- A middle above the chord from `w`, on the face of `b`. -/
theorem mid_b_up {v w b m E2 : ℝ³} {s γ : ℝ} (hb : b = v + E2) (hs0 : 0 < s) (hs1 : s < 1)
    (hγ : 0 < γ - 1 + s) (hm : m = v + s • E2 + γ • (w - v)) (a : ℝ³) : EdgeMid v w a b m :=
  ⟨1 - s, γ - 1 + s, by linarith, by linarith, hγ,
    Or.inr (Or.inr (Or.inr (by rw [hm, hb]; module)))⟩

/-- A middle below the chord from `v`, on the face of `a`. -/
theorem mid_a_low {v w a m E1 : ℝ³} {t ζ : ℝ} (ht : 1 < t) (hζ : 0 < ζ)
    (ha : a = v + t • E1 + ζ • (w - v)) (hm : m = v + E1) (b : ℝ³) : EdgeMid v w a b m := by
  have ht0 : 0 < t := by linarith
  refine ⟨1 / t, ζ / t, by positivity, by rw [div_lt_one ht0]; exact ht, by positivity,
    Or.inl ?_⟩
  rw [hm, ha]
  match_scalars <;> field_simp <;> ring

/-- A middle below the chord from `v`, on the face of `b`. -/
theorem mid_b_low {v w b m E2 : ℝ³} {t ζ : ℝ} (ht : 1 < t) (hζ : 0 < ζ)
    (hb : b = v + t • E2 + ζ • (w - v)) (hm : m = v + E2) (a : ℝ³) : EdgeMid v w a b m := by
  have ht0 : 0 < t := by linarith
  refine ⟨1 - 1 / t, ζ / t, ?_, ?_, by positivity, Or.inr (Or.inl ?_)⟩
  · have : 1 / t < 1 := by rw [div_lt_one ht0]; exact ht
    linarith
  · have : 0 < 1 / t := by positivity
    linarith
  rw [hm, hb]
  match_scalars <;> field_simp <;> ring

/-! ### The four-point test in the four cases -/

/-- Case `(a, b) = (0, 5)`: planar rim, `v` on the plane `a b c`. -/
theorem hE_A (v A N E a b c : ℝ³) (α β : ℝ)
    (ha : a = v + (1 : ℝ) • A + (0 : ℝ) • N + (0 : ℝ) • E)
    (hb : b = v + (0 : ℝ) • A + (1 : ℝ) • N + (0 : ℝ) • E)
    (hc : c = v + α • A + β • N + (0 : ℝ) • E) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (v + E - a) ≤ 0 := by
  rw [hE_coords v A N E a b c 1 0 0 0 1 0 α β 0 ha hb hc]
  apply le_of_eq; ring

/-- Case `(a, b) = (0, 6)`. -/
theorem hE_C (v A N E a b c : ℝ³) (α β t ζ : ℝ)
    (ha : a = v + (1 : ℝ) • A + (0 : ℝ) • N + (0 : ℝ) • E)
    (hb : b = v + (0 : ℝ) • A + t • N + ζ • E)
    (hc : c = v + α • A + β • N + (0 : ℝ) • E) (hζ : 0 < ζ) (hβ : 0 < β)
    (hS : ζ * β - β - t * (α - 1) ≤ 0) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (v + E - a) ≤ 0 := by
  rw [hE_coords v A N E a b c 1 0 0 0 t ζ α β 0 ha hb hc]
  calc _ = (det3 A N E) ^ 2 * ((ζ * β) * (ζ * β - β - t * (α - 1))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (mul_nonpos_of_nonneg_of_nonpos (mul_pos hζ hβ).le hS)

/-- Case `(a, b) = (1, 5)`. -/
theorem hE_D (v A N E a b c : ℝ³) (α β t ζ : ℝ)
    (ha : a = v + t • A + (0 : ℝ) • N + ζ • E)
    (hb : b = v + (0 : ℝ) • A + (1 : ℝ) • N + (0 : ℝ) • E)
    (hc : c = v + α • A + β • N + (0 : ℝ) • E) (hζ : 0 < ζ) (hα : 0 < α)
    (hS : ζ * α - α - t * (β - 1) ≤ 0) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (v + E - a) ≤ 0 := by
  rw [hE_coords v A N E a b c t 0 ζ 0 1 0 α β 0 ha hb hc]
  calc _ = (det3 A N E) ^ 2 * ((ζ * α) * (ζ * α - α - t * (β - 1))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (mul_nonpos_of_nonneg_of_nonpos (mul_pos hζ hα).le hS)

/-- Case `(a, b) = (1, 6)`: planar rim, `w` on the plane `a b c`. -/
theorem hE_B (v A N E a b c : ℝ³) (α β t ζ s η : ℝ)
    (ha : a = v + t • A + (0 : ℝ) • N + ζ • E)
    (hb : b = v + (0 : ℝ) • A + s • N + η • E)
    (hc : c = v + α • A + β • N + (0 : ℝ) • E)
    (hw : -t * β * (1 - ζ) - s * (α - t) * (1 - ζ) + s * t * ζ + (η - ζ) * t * β = 0) :
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (v + E - a) ≤ 0 := by
  rw [hE_coords v A N E a b c t 0 ζ 0 s η α β 0 ha hb hc]
  apply le_of_eq
  calc _ = (det3 A N E) ^ 2 * ((s * ζ * α + t * β * η) *
      (-t * β * (1 - ζ) - s * (α - t) * (1 - ζ) + s * t * ζ + (η - ζ) * t * β)) := by ring
    _ = 0 := by rw [hw]; ring

/-- Cover of the seven indices and the vertex classification of Lemma E. -/
theorem hV_mk (x : Fin 7 → ℝ³) (ia ib m1 m2 : Fin 7)
    (hcov : ∀ i : Fin 7, i = 3 ∨ i = 4 ∨ i = ia ∨ i = ib ∨ i = 2 ∨ i = m1 ∨ i = m2)
    (h1 : EdgeMid (x 3) (x 4) (x ia) (x ib) (x m1))
    (h2 : EdgeMid (x 3) (x 4) (x ia) (x ib) (x m2)) :
    ∀ z ∈ Finset.univ.image x, z = x 3 ∨ z = x 4 ∨ z = x ia ∨ z = x ib ∨ z = x 2 ∨
      EdgeMid (x 3) (x 4) (x ia) (x ib) z := by
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  rcases hcov i with h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))

end Type02CaseC

open Type02CaseC

/-- **The far end `a` of a face at the edge `34`, with the other point `m` of the face over the
open side**: in the shadow along `x 4 - x 3` the point `m` lies strictly between `x 3` and `a`
(Lemma 23.12: `a ∈ {0, 1}` is the far end of `0134`, `a ∈ {5, 6}` that of `3456`). -/
def Type02FarEnd (x : Fin 7 → ℝ³) (a m : Fin 7) : Prop :=
  ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ x m = x 3 + s • (x a - x 3) + δ • (x 4 - x 3)

/-- The depths of `x a`, `x 2`, `x b` along the edge `34` are all equal. -/
def Type02Tie (x : Fin 7 → ℝ³) (a b : Fin 7) : Prop :=
  ⟪x a, x 4 - x 3⟫ = ⟪x 2, x 4 - x 3⟫ ∧ ⟪x 2, x 4 - x 3⟫ = ⟪x b, x 4 - x 3⟫

/-- **The general position of Lemma 23.12 + §24.6 at the edge `34` of type 02.**
* `hdn4`, `hdn3`: no horizontal double normal at the view `x 4 - x 3` of the point sets
  `V \ {x 4}`, `V \ {x 3}` (the closings `K_3`, `K_4`; Lemma 7.4, codimension 1 at a fixed
  view);
* `g1`, `g2`: `(G1)`, the edges `01`, `56` are not parallel to `34` (a vertical far edge;
  codimension 1 each);
* `t05`, `t06`, `t15`, `t16`: the far depths `x a`, `x 2`, `x b` are not all equal, for the far
  ends `(a, b)` of the faces `0134`, `3456` (codimension 2; `Type02FarEnd x a m` says that `a` is
  the far end, with `m` the other point of its face). -/
structure Type02EdgeGen (x : Fin 7 → ℝ³) : Prop where
  hdn4 : NoHDNAt ((Finset.univ.image x).erase (x 4)) (x 4 - x 3)
  hdn3 : NoHDNAt ((Finset.univ.image x).erase (x 3)) (x 4 - x 3)
  g1 : ∀ c : ℝ, x 1 - x 0 ≠ c • (x 4 - x 3)
  g2 : ∀ c : ℝ, x 6 - x 5 ≠ c • (x 4 - x 3)
  t05 : Type02FarEnd x 0 1 → Type02FarEnd x 5 6 → ¬ Type02Tie x 0 5
  t06 : Type02FarEnd x 0 1 → Type02FarEnd x 6 5 → ¬ Type02Tie x 0 6
  t15 : Type02FarEnd x 1 0 → Type02FarEnd x 5 6 → ¬ Type02Tie x 1 5
  t16 : Type02FarEnd x 1 0 → Type02FarEnd x 6 5 → ¬ Type02Tie x 1 6

theorem pos_of_mul_neg' {a b : ℝ} (hb : b < 0) (h : a * b < 0) : 0 < a := by
  by_contra ha; push Not at ha
  have := mul_nonneg_of_nonpos_of_nonpos ha hb.le; linarith

set_option maxHeartbeats 2000000 in
theorem isRupert_type02_edge34 (x : Fin 7 → ℝ³)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 0) = 0 ∧ f (x 1) = 0 ∧ f (x 4) = 0 ∧
      f (x 2) < 0 ∧ f (x 5) < 0 ∧ f (x 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 5) = 0 ∧ f (x 6) = 0 ∧ f (x 4) = 0 ∧
      f (x 0) < 0 ∧ f (x 1) < 0 ∧ f (x 2) < 0)
    (hF3 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 0) = 0 ∧ f (x 2) = 0 ∧ f (x 5) = 0 ∧
      f (x 1) < 0 ∧ f (x 4) < 0 ∧ f (x 6) < 0)
    (hF4 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 4) = 0 ∧ f (x 1) = 0 ∧ f (x 2) = 0 ∧ f (x 6) = 0 ∧
      f (x 0) < 0 ∧ f (x 3) < 0 ∧ f (x 5) < 0)
    (hgen : Type02EdgeGen x) : IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨f1, a3, a0, a1, a4, a2, a5, a6⟩ := hF1
  obtain ⟨f2, b3, b5, b6, b4, b0, b1, b2⟩ := hF2
  obtain ⟨f3, c3, c0, c2, c5, c1, c4, c6⟩ := hF3
  obtain ⟨f4, d4, d1, d2, d6, d0, d3, d5⟩ := hF4
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ³, e0 = x 0 - x 3 := ⟨_, rfl⟩
  obtain ⟨e5, he5⟩ : ∃ e5 : ℝ³, e5 = x 5 - x 3 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ³, u = x 4 - x 3 := ⟨_, rfl⟩
  have hx0 : x 0 = x 3 + e0 := by rw [he0]; abel
  have hx5 : x 5 = x 3 + e5 := by rw [he5]; abel
  have hx4 : x 4 = x 3 + u := by rw [hu]; abel
  -- the values of the linear parts
  have l1e0 : f1.linear e0 = 0 := by rw [he0, lin_sub]; linarith
  have l1u : f1.linear u = 0 := by rw [hu, lin_sub]; linarith
  have l1e5 : f1.linear e5 < 0 := by rw [he5, lin_sub]; linarith
  have l2e5 : f2.linear e5 = 0 := by rw [he5, lin_sub]; linarith
  have l2u : f2.linear u = 0 := by rw [hu, lin_sub]; linarith
  have l2e0 : f2.linear e0 < 0 := by rw [he0, lin_sub]; linarith
  have l3e0 : f3.linear e0 = 0 := by rw [he0, lin_sub]; linarith
  have l3e5 : f3.linear e5 = 0 := by rw [he5, lin_sub]; linarith
  have l3u : f3.linear u < 0 := by rw [hu, lin_sub]; linarith
  have hD := det_ne_zero e0 e5 u f1.linear f2.linear f3.linear l1e0 l1e5.ne l2e0.ne
    l3e0 l3e5 l3u.ne
  obtain ⟨α1, β1, γ1, h1⟩ := exists_coords hD (x 1) (x 3)
  obtain ⟨α2, β2, γ2, h2⟩ := exists_coords hD (x 2) (x 3)
  obtain ⟨α6, β6, γ6, h6⟩ := exists_coords hD (x 6) (x 3)
  have F : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (p : ℝ³) (α β γ : ℝ), p = x 3 + α • e0 + β • e5 + γ • u →
      f p = f (x 3) + α * f.linear e0 + β * f.linear e5 + γ * f.linear u := by
    intro f p α β γ h; subst h; exact aff_comb f (x 3) e0 e5 u α β γ
  -- facet 0134: the second coordinate
  have A1 := F f1 (x 1) α1 β1 γ1 h1
  have A2 := F f1 (x 2) α2 β2 γ2 h2
  have A6 := F f1 (x 6) α6 β6 γ6 h6
  simp only [a3, a1, l1e0, l1u, mul_zero, add_zero, zero_add] at A1 A2 A6
  have hβ1 : β1 = 0 := by
    rcases mul_eq_zero.mp A1.symm with h | h
    · exact h
    · exact absurd h l1e5.ne
  have hβ2 : 0 < β2 := pos_of_mul_neg' l1e5 (by rw [← A2]; exact a2)
  have hβ6 : 0 < β6 := pos_of_mul_neg' l1e5 (by rw [← A6]; exact a6)
  -- facet 3456: the first coordinate
  have B1 := F f2 (x 1) α1 β1 γ1 h1
  have B2 := F f2 (x 2) α2 β2 γ2 h2
  have B6 := F f2 (x 6) α6 β6 γ6 h6
  simp only [b3, b6, l2e5, l2u, mul_zero, add_zero, zero_add] at B1 B2 B6
  have hα6 : α6 = 0 := by
    rcases mul_eq_zero.mp B6.symm with h | h
    · exact h
    · exact absurd h l2e0.ne
  have hα1 : 0 < α1 := pos_of_mul_neg' l2e0 (by rw [← B1]; exact b1)
  have hα2 : 0 < α2 := pos_of_mul_neg' l2e0 (by rw [← B2]; exact b2)
  -- facet 0235: the third coordinate
  have C1 := F f3 (x 1) α1 β1 γ1 h1
  have C2 := F f3 (x 2) α2 β2 γ2 h2
  have C6 := F f3 (x 6) α6 β6 γ6 h6
  simp only [c3, c2, l3e0, l3e5, mul_zero, add_zero, zero_add] at C1 C2 C6
  have hγ2 : γ2 = 0 := by
    rcases mul_eq_zero.mp C2.symm with h | h
    · exact h
    · exact absurd h l3u.ne
  have hγ1 : 0 < γ1 := pos_of_mul_neg' l3u (by rw [← C1]; exact c1)
  have hγ6 : 0 < γ6 := pos_of_mul_neg' l3u (by rw [← C6]; exact c6)
  subst hβ1 hα6 hγ2
  -- facet 1246: the plane `z = 1 - p0 x - p5 y`
  have hg : 0 < f4.linear u := by rw [hu, lin_sub]; linarith
  have l4g : f4 (x 3) = - f4.linear u := by rw [hu, lin_sub]; linarith
  have l4e0 : f4.linear e0 < f4.linear u := by rw [he0, hu, lin_sub, lin_sub]; linarith
  have l4e5 : f4.linear e5 < f4.linear u := by rw [he5, hu, lin_sub, lin_sub]; linarith
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℝ, f4.linear e0 = p0 * f4.linear u :=
    ⟨f4.linear e0 / f4.linear u, by field_simp⟩
  obtain ⟨p5, hp5⟩ : ∃ p5 : ℝ, f4.linear e5 = p5 * f4.linear u :=
    ⟨f4.linear e5 / f4.linear u, by field_simp⟩
  have hp0' : p0 < 1 := by
    by_contra h; push Not at h
    rw [hp0] at l4e0
    have := mul_nonneg (sub_nonneg.2 h) hg.le
    linarith only [this, l4e0]
  have hp5' : p5 < 1 := by
    by_contra h; push Not at h
    rw [hp5] at l4e5
    have := mul_nonneg (sub_nonneg.2 h) hg.le
    linarith only [this, l4e5]
  have D1 := F f4 (x 1) α1 0 γ1 (by rw [h1])
  have D2 := F f4 (x 2) α2 β2 0 h2
  have D6 := F f4 (x 6) 0 β6 γ6 h6
  rw [d1, l4g, hp0, hp5] at D1
  rw [d2, l4g, hp0, hp5] at D2
  rw [d6, l4g, hp0, hp5] at D6
  have N1 : γ1 = 1 - α1 * p0 := by
    have : f4.linear u * (γ1 - 1 + α1 * p0) = 0 := by linear_combination -D1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have N6 : γ6 = 1 - β6 * p5 := by
    have : f4.linear u * (γ6 - 1 + β6 * p5) = 0 := by linear_combination -D6
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have N2 : α2 * p0 + β2 * p5 = 1 := by
    have : f4.linear u * (α2 * p0 + β2 * p5 - 1) = 0 := by linear_combination -D2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have hu' : x 4 - x 3 = u := hu.symm
  have hD' : det3 e0 e5 (x 4 - x 3) ≠ 0 := by rw [hu']; exact hD
  have mem : ∀ i, x i ∈ Finset.univ.image x :=
    fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have e1 : x 1 = x 3 + α1 • e0 + γ1 • u := by rw [h1]; module
  have e6 : x 6 = x 3 + β6 • e5 + γ6 • u := by rw [h6]; module
  have e2 : x 2 = x 3 + α2 • e0 + β2 • e5 := by rw [h2]; module
  have hα1ne : α1 ≠ 1 := by
    intro h; apply hgen.g1 γ1
    rw [hu', e1, hx0, h]; module
  have hβ6ne : β6 ≠ 1 := by
    intro h; apply hgen.g2 γ6
    rw [hu', e6, hx5, h]; module
  have q1 : α1 * p0 < 1 := by rw [N1] at hγ1; linarith
  have q6 : β6 * p5 < 1 := by rw [N6] at hγ6; linarith
  -- the far-end witnesses
  have fe01 : α1 < 1 → Type02FarEnd x 0 1 := fun hlt =>
    ⟨α1, γ1, hα1, hlt, by rw [← he0, hu', e1]⟩
  have fe56 : β6 < 1 → Type02FarEnd x 5 6 := fun hlt =>
    ⟨β6, γ6, hβ6, hlt, by rw [← he5, hu', e6]⟩
  have fe10 : 1 < α1 → Type02FarEnd x 1 0 := fun hgt =>
    ⟨1 / α1, -γ1 / α1, by positivity, by rw [div_lt_one hα1]; exact hgt, by
      rw [e1, hx0, hu']
      match_scalars <;> field_simp <;> ring⟩
  have fe65 : 1 < β6 → Type02FarEnd x 6 5 := fun hgt =>
    ⟨1 / β6, -γ6 / β6, by positivity, by rw [div_lt_one hβ6]; exact hgt, by
      rw [e6, hx5, hu']
      match_scalars <;> field_simp <;> ring⟩
  have hc : x 2 = x 3 + α2 • e0 + β2 • e5 + (0 : ℝ) • (x 4 - x 3) := by rw [e2]; module
  have hγa : 0 < γ1 - 1 + α1 := by
    have : γ1 - 1 + α1 = α1 * (1 - p0) := by rw [N1]; ring
    rw [this]; exact mul_pos hα1 (sub_pos.2 hp0')
  have hγb : 0 < γ6 - 1 + β6 := by
    have : γ6 - 1 + β6 = β6 * (1 - p5) := by rw [N6]; ring
    rw [this]; exact mul_pos hβ6 (sub_pos.2 hp5')
  have m1 : x 1 = x 3 + α1 • e0 + γ1 • (x 4 - x 3) := by rw [hu']; exact e1
  have m6 : x 6 = x 3 + β6 • e5 + γ6 • (x 4 - x 3) := by rw [hu']; exact e6
  have m0 : x 0 = x 3 + (1 : ℝ) • e0 + (0 : ℝ) • (x 4 - x 3) := by rw [hx0]; module
  have m5 : x 5 = x 3 + (1 : ℝ) • e5 + (0 : ℝ) • (x 4 - x 3) := by rw [hx5]; module
  have ha0 : x 0 = x 3 + (1 : ℝ) • e0 + (0 : ℝ) • e5 + (0 : ℝ) • u := by rw [hx0]; module
  have hb5 : x 5 = x 3 + (0 : ℝ) • e0 + (1 : ℝ) • e5 + (0 : ℝ) • u := by rw [hx5]; module
  have hc2 : x 2 = x 3 + α2 • e0 + β2 • e5 + (0 : ℝ) • u := by rw [e2]; module
  have ha1 : x 1 = x 3 + α1 • e0 + (0 : ℝ) • e5 + γ1 • u := by rw [e1]; module
  have hb6 : x 6 = x 3 + (0 : ℝ) • e0 + β6 • e5 + γ6 • u := by rw [e6]; module
  rcases lt_or_gt_of_ne hα1ne with hlt | hgt <;> rcases lt_or_gt_of_ne hβ6ne with hlt6 | hgt6
  · -- (a, b) = (0, 5): planar rim `0235`
    have hch : (1 : ℝ) * 1 < α2 * 1 + β2 * 1 := by
      have := mul_lt_mul_of_pos_left hp0' hα2
      have := mul_lt_mul_of_pos_left hp5' hβ2
      linarith
    refine rim_core' _ hD' m0 m5 hc one_pos one_pos hα2 hβ2 hch (mem 3) (mem 4) (mem 0) (mem 5)
      (mem 2) ?_ (hgen.t05 (fe01 hlt) (fe56 hlt6)) ?_ hgen.hdn4 hgen.hdn3
    · rw [hx4]; exact hE_A (x 3) e0 e5 u (x 0) (x 5) (x 2) α2 β2 ha0 hb5 hc2
    · exact hV_mk x 0 5 1 6 (by decide)
        (mid_a_up hx0 hα1 hlt hγa m1 (x 5)) (mid_b_up hx5 hβ6 hlt6 hγb m6 (x 0))
  · -- (a, b) = (0, 6): Lemma E
    have hch : (1 : ℝ) * β6 < α2 * β6 + β2 * 1 := by
      have e : β6 = α2 * β6 * p0 + β2 * (β6 * p5) := by linear_combination (-β6) * N2
      have t1 := mul_lt_mul_of_pos_left hp0' (mul_pos hα2 hβ6)
      have t2 := mul_lt_mul_of_pos_left q6 hβ2
      linarith
    refine rim_core' _ hD' m0 m6 hc one_pos hβ6 hα2 hβ2 hch (mem 3) (mem 4) (mem 0)
      (mem 6) (mem 2) ?_ (hgen.t06 (fe01 hlt) (fe65 hgt6)) ?_ hgen.hdn4 hgen.hdn3
    · rw [hx4]
      refine hE_C (x 3) e0 e5 u (x 0) (x 6) (x 2) α2 β2 β6 γ6 ha0 hb6 hc2 hγ6 hβ2 ?_
      have : γ6 * β2 - β2 - β6 * (α2 - 1) = -(β6 * α2 * (1 - p0)) := by
        rw [N6]; linear_combination (-β6) * N2
      rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hβ6 hα2) (sub_pos.2 hp0')).le
    · exact hV_mk x 0 6 1 5 (by decide)
        (mid_a_up hx0 hα1 hlt hγa m1 (x 6)) (mid_b_low hgt6 hγ6 m6 hx5 (x 0))
  · -- (a, b) = (1, 5): Lemma E
    have hch : α1 * 1 < α2 * 1 + β2 * α1 := by
      have e : α1 = α2 * (α1 * p0) + β2 * α1 * p5 := by linear_combination (-α1) * N2
      have t1 := mul_lt_mul_of_pos_left q1 hα2
      have t2 := mul_lt_mul_of_pos_left hp5' (mul_pos hβ2 hα1)
      linarith
    refine rim_core' _ hD' m1 m5 hc hα1 one_pos hα2 hβ2 hch (mem 3) (mem 4) (mem 1)
      (mem 5) (mem 2) ?_ (hgen.t15 (fe10 hgt) (fe56 hlt6)) ?_ hgen.hdn4 hgen.hdn3
    · rw [hx4]
      refine hE_D (x 3) e0 e5 u (x 1) (x 5) (x 2) α2 β2 α1 γ1 ha1 hb5 hc2 hγ1 hα2 ?_
      have : γ1 * α2 - α2 - α1 * (β2 - 1) = -(α1 * β2 * (1 - p5)) := by
        rw [N1]; linear_combination (-α1) * N2
      rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hα1 hβ2) (sub_pos.2 hp5')).le
    · exact hV_mk x 1 5 0 6 (by decide)
        (mid_a_low hgt hγ1 m1 hx0 (x 5)) (mid_b_up hx5 hβ6 hlt6 hγb m6 (x 1))
  · -- (a, b) = (1, 6): planar rim `1246`
    have hch : α1 * β6 < α2 * β6 + β2 * α1 := by
      have e : α1 * β6 = α2 * β6 * (α1 * p0) + β2 * α1 * (β6 * p5) := by
        linear_combination (-(α1 * β6)) * N2
      have t1 := mul_lt_mul_of_pos_left q1 (mul_pos hα2 hβ6)
      have t2 := mul_lt_mul_of_pos_left q6 (mul_pos hβ2 hα1)
      linarith
    refine rim_core' _ hD' m1 m6 hc hα1 hβ6 hα2 hβ2 hch (mem 3) (mem 4) (mem 1)
      (mem 6) (mem 2) ?_ (hgen.t16 (fe10 hgt) (fe65 hgt6)) ?_ hgen.hdn4 hgen.hdn3
    · rw [hx4]
      refine hE_B (x 3) e0 e5 u (x 1) (x 6) (x 2) α2 β2 α1 γ1 β6 γ6 ha1 hb6 hc2 ?_
      rw [N1, N6]; linear_combination (-(α1 * β6)) * N2
    · exact hV_mk x 1 6 0 5 (by decide)
        (mid_a_low hgt hγ1 m1 hx0 (x 6)) (mid_b_low hgt6 hγ6 m6 hx5 (x 1))

/-- **Type 02, case (c): Lemma E at the edge `34`** (Lemma 23.12 and §24.6 of
`FEWER-FACES-PROOFS.md`), in the form for the skeleton `anySevenVertexNopertIsSimplicial`: a
7-point nopert whose labelling realizes the faces `0134`, `0235`, `1246`, `3456` of type 02
(`Minimality.sevenTypeFaces 1`) satisfies `¬ Type02EdgeGen x`.  Hypotheses of
`Type02EdgeGen`: the HDN exclusion at the view `x 4 - x 3` for both closings, `(G1)`, and the far
depths not all equal; each fails only in codimension 1 (HDN, `(G1)`) or 2 (ties) of the shapes of
the type, hence in codimension ≥ 3 inside the case-(c) family of the view of `0235`, `1246`. -/
theorem type02_edge34_false {x : Fin 7 → ℝ³} (hN : IsNopert (Finset.univ.image x))
    {fs : List (Finset (Fin 7))} (hR : Minimality.RealizesFaces x fs)
    (h1 : ({0, 1, 3, 4} : Finset (Fin 7)) ∈ fs) (h2 : ({0, 2, 3, 5} : Finset (Fin 7)) ∈ fs)
    (h3 : ({1, 2, 4, 6} : Finset (Fin 7)) ∈ fs) (h4 : ({3, 4, 5, 6} : Finset (Fin 7)) ∈ fs)
    (hgen : Type02EdgeGen x) : False := by
  obtain ⟨f1, hf1⟩ := hR _ h1
  obtain ⟨f2, hf2⟩ := hR _ h4
  obtain ⟨f3, hf3⟩ := hR _ h2
  obtain ⟨f4, hf4⟩ := hR _ h3
  refine hN.2 (isRupert_type02_edge34 x ?_ ?_ ?_ ?_ hgen)
  · exact ⟨f1, (hf1 3).1 (by decide), (hf1 0).1 (by decide), (hf1 1).1 (by decide),
      (hf1 4).1 (by decide), (hf1 2).2 (by decide), (hf1 5).2 (by decide),
      (hf1 6).2 (by decide)⟩
  · exact ⟨f2, (hf2 3).1 (by decide), (hf2 5).1 (by decide), (hf2 6).1 (by decide),
      (hf2 4).1 (by decide), (hf2 0).2 (by decide), (hf2 1).2 (by decide),
      (hf2 2).2 (by decide)⟩
  · exact ⟨f3, (hf3 3).1 (by decide), (hf3 0).1 (by decide), (hf3 2).1 (by decide),
      (hf3 5).1 (by decide), (hf3 1).2 (by decide), (hf3 4).2 (by decide),
      (hf3 6).2 (by decide)⟩
  · exact ⟨f4, (hf4 4).1 (by decide), (hf4 1).1 (by decide), (hf4 2).1 (by decide),
      (hf4 6).1 (by decide), (hf4 0).2 (by decide), (hf4 3).2 (by decide),
      (hf4 5).2 (by decide)⟩

/-- The skeleton form: `byGen1 (type02_edge34_byGen hx hN hR) …` with
`hR : RealizesFaces x (sevenTypeFaces 1)`. -/
theorem type02_edge34_byGen {x : Fin 7 → ℝ³} (hN : IsNopert (Finset.univ.image x))
    (hR : Minimality.RealizesFaces x (Minimality.sevenTypeFaces 1)) :
    Type02EdgeGen x → False :=
  type02_edge34_false hN hR (by decide) (by decide) (by decide) (by decide)

end Minimality

end
