module

public import Minimality.Oct9Gale
public import Minimality.UnimodalCert

@[expose] public section

/-!
# Type 08: the lemmas of `FEWER-FACES-PROOFS.md` §10

Type 08 is the octahedron `O = K − 2` with a *cap* `2` (here `d`): with `O`'s
opposite pairs `(a, a')`, `(b, b')`, `(c, c')`, the cap is the common point of the
planes of `abc'`, `ab'c`, `a'bc`, strictly beyond the face `abc` and strictly
beneath the other four faces (`IsCap`).  The three planes become `K`'s
quadrilaterals `Q_ab = (d, a, c', b)`, `Q_ac = (d, a, b', c)`, `Q_bc = (d, b, a', c)`.

The Gale calculus is that of `Oct9Gale.lean`: `galeD G.l G.m s t` is `[s t]`.

* Tools: affine functions with linear parts, `eq_of_affine3` (three affine
  functions with a nonsingular matrix on a frame separate points),
  `coords_of_affine3` (coordinates in a plane read off two affine functions).
* **Lemma 3** (single-plane form of Lemma 9.5) — `not_bad_of_crossing`
  (coefficient form) and `not_bad_of_inTri` (the projection along `p' − p` in
  determinant form).
* **Lemma 4** (the cap in the axis view) — `inTri_cap_BD`, `inTri_cap_AB` in
  determinant form `S X Y = det3 (X − c) (Y − c) e`, with the facts (i)–(iii)
  of its proof as hypotheses; `IsCap.axis_facts` proves (i)–(iii) for a cap and
  `axis_quad_signs` the convex quadrilateral `C D A B` around `O` (every octahedron).
* Lemma 9.7 in dependency form — `inTri_of_dep`.  With Lemmas 4 and 3:
  `type08_t4_not_bad` (the T4 edge of Theorem 10.1 is not bad).
* **Lemma 1 (a), (b)** (far ends at a QQ edge, Gale form) — `far_end_Qbc_iff`,
  `far_end_Qab_iff`, from `facet_lt_iff_of_dep` (Lemma 9.6 as an equivalence).
* **Lemma 1 (c)** (the rim is a planar convex quadrilateral, hence unimodal) —
  `nws4_of_planar_quad`, `IsCap.Qac_nws4`, with the convex coordinates of `Q_ac` in
  `IsCap.Qac_coords'` (of `Q_ab`, `Q_bc` by the `S3` symmetry `IsCap.perm₁₂`,
  `IsCap.perm₂₃`).
* **Lemma 2** (the cap is a middle) — `IsCap.middle_Qbc`.
* **Lemma 6** (a non-quad pair) — `type08_lemma6`.
* **Lemma 7** (the Gale chain) — `type08_lemma7`, from the sign table
  `type08_signs` of the labelling of Lemma 6.
The cases of Theorem 10.1 are in `Type08Cases.lean`, `Type08T4.lean`, and the
theorem in `Type08.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Tools -/

/-- An affine function with linear part `N` at a point given in a frame. -/
theorem affine_frame {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (o p q : ℝ³) (s t : ℝ) :
    f (o + s • (p - o) + t • (q - o)) = f o + s * (f p - f o) + t * (f q - f o) := by
  have h := hf (o + s • (p - o) + t • (q - o)) o
  rw [show o + s • (p - o) + t • (q - o) - o = s • (p - o) + t • (q - o) by abel,
    inner_add_right, real_inner_smul_right, real_inner_smul_right, ← hf, ← hf] at h
  linarith

/-- `det3 N₀ N₁ N₂ · det3 e₀ e₁ e₂` is the determinant of the inner products. -/
theorem det3_mul_det3 (N₀ N₁ N₂ e₀ e₁ e₂ : ℝ³) :
    det3 N₀ N₁ N₂ * det3 e₀ e₁ e₂ =
      ⟪N₀, e₀⟫ * (⟪N₁, e₁⟫ * ⟪N₂, e₂⟫ - ⟪N₁, e₂⟫ * ⟪N₂, e₁⟫) -
      ⟪N₀, e₁⟫ * (⟪N₁, e₀⟫ * ⟪N₂, e₂⟫ - ⟪N₁, e₂⟫ * ⟪N₂, e₀⟫) +
      ⟪N₀, e₂⟫ * (⟪N₁, e₀⟫ * ⟪N₂, e₁⟫ - ⟪N₁, e₁⟫ * ⟪N₂, e₀⟫) := by
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]
  ring

/-- A vector orthogonal to three independent vectors vanishes. -/
theorem eq_zero_of_inner3 {N₀ N₁ N₂ w : ℝ³} (hD : det3 N₀ N₁ N₂ ≠ 0) (h₀ : ⟪N₀, w⟫ = 0)
    (h₁ : ⟪N₁, w⟫ = 0) (h₂ : ⟪N₂, w⟫ = 0) : w = 0 := by
  have hc := congrArg (fun v => ⟪v, w⟫) (cramer N₀ N₁ N₂ w)
  simp only [real_inner_smul_left, inner_add_left, h₀, h₁, h₂, mul_zero, add_zero] at hc
  exact inner_self_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hD)

/-- Three affine functions whose matrix of values on a frame `o; e₀, e₁, e₂` is
nonsingular separate points. -/
theorem eq_of_affine3 {f₀ f₁ f₂ : ℝ³ → ℝ} {N₀ N₁ N₂ : ℝ³}
    (h₀ : ∀ y z, f₀ y - f₀ z = ⟪N₀, y - z⟫) (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) (o e₀ e₁ e₂ : ℝ³)
    (hdet : (f₀ e₀ - f₀ o) * ((f₁ e₁ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₁ - f₂ o)) -
      (f₀ e₁ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₂ - f₂ o) - (f₁ e₂ - f₁ o) * (f₂ e₀ - f₂ o)) +
      (f₀ e₂ - f₀ o) * ((f₁ e₀ - f₁ o) * (f₂ e₁ - f₂ o) - (f₁ e₁ - f₁ o) * (f₂ e₀ - f₂ o)) ≠ 0)
    {w w' : ℝ³} (hw₀ : f₀ w = f₀ w') (hw₁ : f₁ w = f₁ w') (hw₂ : f₂ w = f₂ w') : w = w' := by
  rw [h₀ e₀, h₀ e₁, h₀ e₂, h₁ e₀, h₁ e₁, h₁ e₂, h₂ e₀, h₂ e₁, h₂ e₂, ← det3_mul_det3] at hdet
  have hD : det3 N₀ N₁ N₂ ≠ 0 := left_ne_zero_of_mul hdet
  refine sub_eq_zero.mp (eq_zero_of_inner3 hD ?_ ?_ ?_)
  · rw [← h₀]; linarith
  · rw [← h₁]; linarith
  · rw [← h₂]; linarith

/-- **Coordinates in a plane.**  If `f₀` vanishes on the plane of `o, p, q, w`
(and not everywhere), `f₁` on the line `o q` and `f₂` on the line `o p`, then
`w = o + (f₁ w / f₁ p) (p − o) + (f₂ w / f₂ q) (q − o)`. -/
theorem coords_of_affine3 {f₀ f₁ f₂ : ℝ³ → ℝ} {N₀ N₁ N₂ : ℝ³}
    (h₀ : ∀ y z, f₀ y - f₀ z = ⟪N₀, y - z⟫) (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) {o p q w Z : ℝ³}
    (h₀o : f₀ o = 0) (h₀p : f₀ p = 0) (h₀q : f₀ q = 0) (h₀w : f₀ w = 0) (h₀Z : f₀ Z ≠ 0)
    (h₁o : f₁ o = 0) (h₁q : f₁ q = 0) (h₁p : f₁ p ≠ 0)
    (h₂o : f₂ o = 0) (h₂p : f₂ p = 0) (h₂q : f₂ q ≠ 0) :
    w = o + (f₁ w / f₁ p) • (p - o) + (f₂ w / f₂ q) • (q - o) := by
  refine eq_of_affine3 h₀ h₁ h₂ o p q Z ?_ ?_ ?_ ?_
  · rw [h₀o, h₀p, h₀q, h₁o, h₁q, h₂o, h₂p]
    simp only [sub_zero, zero_mul, zero_sub, mul_zero, sub_self, zero_add]
    exact mul_ne_zero h₀Z (mul_ne_zero h₁p h₂q)
  · rw [affine_frame h₀, h₀o, h₀p, h₀q, h₀w]; ring
  · rw [affine_frame h₁, h₁o, h₁q]; field_simp; ring
  · rw [affine_frame h₂, h₂o, h₂p]; field_simp; ring

/-! ### Lemma 3: the single-plane form of Lemma 9.5 -/

/-- **Lemma 3 of §10, coefficient form.**  Let `p`, `p'` lie strictly on
opposite sides of the plane `x y y'` (an affine `g` vanishing there), and let the
line through `p` along `p' − p` meet the triangle `y' x y` in its interior:
`p = β y' + γ x + δ y + t (p' − p)` with `β, γ, δ > 0` summing to 1.  Then the
edge `x → y` is not bad: `max (z y, z y') > min (z p, z p')` for
`z = ⟪·, y − x⟫`. -/
theorem not_bad_of_crossing {x y y' p p' : ℝ³} {g : ℝ³ → ℝ} {N : ℝ³}
    (hg : ∀ s t, g s - g t = ⟪N, s - t⟫) (hgx : g x = 0) (hgy : g y = 0) (hgy' : g y' = 0)
    (hpp' : g p * g p' < 0) (hxy : x ≠ y) {β γ δ t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (hsum : β + γ + δ = 1)
    (hO : p = β • y' + γ • x + δ • y + t • (p' - p)) :
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  intro hbad
  have hpx : p - x = β • (y' - x) + δ • (y - x) + t • (p' - p) := by
    conv_lhs => rw [hO]
    rw [show γ = 1 - β - δ by linarith]
    module
  -- the crossing point `m = p − t (p' − p)` is on the plane: `g p = t (g p' − g p)`
  have hm : g p = t * (g p' - g p) := by
    have h1 := hg p x
    rw [hgx, sub_zero, hpx, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, ← hg, ← hg, ← hg, hgx, hgy, hgy'] at h1
    linarith
  have ht0 : t < 0 := by
    by_contra h; push Not at h
    have e : g p * g p' * (1 + t) = t * (g p' * g p') := by linear_combination g p' * hm
    nlinarith [mul_self_nonneg (g p'), mul_nonneg h (mul_self_nonneg (g p'))]
  have ht1 : -1 < t := by
    by_contra h; push Not at h
    have e : g p * g p' * (1 + t) = t * (g p' * g p') := by linear_combination g p' * hm
    have hp'0 : g p' ≠ 0 := by intro h0; rw [h0, mul_zero] at hpp'; exact lt_irrefl _ hpp'
    have := mul_self_pos.mpr hp'0
    nlinarith
  set u := y - x with hu
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hxu : ⟪x, u⟫ = ⟪y, u⟫ - ⟪u, u⟫ := by
    rw [show (x : ℝ³) = y - u by rw [hu]; abel, inner_sub_left]
  have hz := congrArg (fun v => ⟪v, u⟫) hO
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at hz
  rw [hxu] at hz
  simp only [max_le_iff, le_min_iff] at hbad
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  have k1 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 1 + t by linarith) hβ.le)
    (sub_nonneg.mpr h2)
  have k2 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 1 + t by linarith)
    (show (0 : ℝ) ≤ 1 - β by linarith)) (sub_nonneg.mpr h1)
  have k3 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ -t by linarith) hβ.le) (sub_nonneg.mpr h4)
  have k4 := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ -t by linarith)
    (show (0 : ℝ) ≤ 1 - β by linarith)) (sub_nonneg.mpr h3)
  have key : (1 + t) * β * (⟪p, u⟫ - ⟪y', u⟫) + (1 + t) * (1 - β) * (⟪p, u⟫ - ⟪y, u⟫) +
      -t * β * (⟪p', u⟫ - ⟪y', u⟫) + -t * (1 - β) * (⟪p', u⟫ - ⟪y, u⟫) = -(γ * ⟪u, u⟫) := by
    linear_combination hz + ⟪y, u⟫ * hsum
  linarith [mul_pos hγ huu]

/-- The four-vector identity behind Cramer's rule in a projection along `e`. -/
theorem det3_four_proj (b c d e : ℝ³) :
    det3 c d e • b + det3 d b e • c + det3 b c e • d = det3 b c d • e := by
  ext i; fin_cases i <;>
    simp only [det3_expand, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;> ring

/-- **Lemma 3 of §10, projection form.**  Project along `p' − p`; if the image
of `p` lies in the interior of the triangle of the images of `y'`, `x`, `y`
(the three orientations `det3 (· − p) (· − p) (p' − p)` have one strict sign)
and `p`, `p'` lie strictly on opposite sides of the plane `x y y'`, the edge
`x → y` is not bad. -/
theorem not_bad_of_inTri {x y y' p p' : ℝ³} {g : ℝ³ → ℝ} {N : ℝ³}
    (hg : ∀ s t, g s - g t = ⟪N, s - t⟫) (hgx : g x = 0) (hgy : g y = 0) (hgy' : g y' = 0)
    (hpp' : g p * g p' < 0) (hxy : x ≠ y)
    (hS : (0 < det3 (x - p) (y - p) (p' - p) ∧ 0 < det3 (y - p) (y' - p) (p' - p) ∧
        0 < det3 (y' - p) (x - p) (p' - p)) ∨
      (det3 (x - p) (y - p) (p' - p) < 0 ∧ det3 (y - p) (y' - p) (p' - p) < 0 ∧
        det3 (y' - p) (x - p) (p' - p) < 0)) :
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫ := by
  set S1 := det3 (x - p) (y - p) (p' - p)
  set S2 := det3 (y - p) (y' - p) (p' - p)
  set S3 := det3 (y' - p) (x - p) (p' - p)
  have hid := det3_four_proj (y' - p) (x - p) (y - p) (p' - p)
  have hS0 : S1 + S2 + S3 ≠ 0 := by
    rcases hS with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> [exact (by linarith : 0 < S1 + S2 + S3).ne';
      exact (by linarith : S1 + S2 + S3 < 0).ne]
  have hpos : 0 < S1 / (S1 + S2 + S3) ∧ 0 < S2 / (S1 + S2 + S3) ∧ 0 < S3 / (S1 + S2 + S3) := by
    rcases hS with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨div_pos h1 (by linarith), div_pos h2 (by linarith), div_pos h3 (by linarith)⟩
    · exact ⟨div_pos_of_neg_of_neg h1 (by linarith), div_pos_of_neg_of_neg h2 (by linarith),
        div_pos_of_neg_of_neg h3 (by linarith)⟩
  refine not_bad_of_crossing hg hgx hgy hgy' hpp' hxy (β := S1 / (S1 + S2 + S3))
    (γ := S2 / (S1 + S2 + S3)) (δ := S3 / (S1 + S2 + S3))
    (t := -(det3 (y' - p) (x - p) (y - p) / (S1 + S2 + S3))) hpos.1 hpos.2.1 hpos.2.2
    (by field_simp) ?_
  -- `S1 (y' − p) + S2 (x − p) + S3 (y − p) = det3 (y'−p) (x−p) (y−p) (p' − p)`
  have hid' : (S1 + S2 + S3) • p = S1 • y' + S2 • x + S3 • y -
      det3 (y' - p) (x - p) (y - p) • (p' - p) := by
    rw [← hid]; simp only [S1, S2, S3, smul_sub, add_smul]; abel
  have hinv : (S1 + S2 + S3)⁻¹ * (S1 + S2 + S3) = 1 := inv_mul_cancel₀ hS0
  calc p = (S1 + S2 + S3)⁻¹ • ((S1 + S2 + S3) • p) := by rw [smul_smul, hinv, one_smul]
    _ = _ := by rw [hid']; simp only [div_eq_inv_mul, smul_sub, smul_add, smul_smul,
          neg_smul]; abel

/-! ### Lemma 4: the cap in the axis view -/

/-- The Plücker relation for orientations seen from `c` in a projection along `e`. -/
theorem det3_plucker_e (c e a b d a' : ℝ³) :
    det3 (a - c) (b - c) e * det3 (d - c) (a' - c) e =
      det3 (a - c) (d - c) e * det3 (b - c) (a' - c) e +
      det3 (a - c) (a' - c) e * det3 (d - c) (b - c) e := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **Lemma 4 of §10, `B C D` form.**  Project along `e` and write
`S X Y = det3 (X − c) (Y − c) e` (the orientation of the images of `X`, `Y` seen
from the image `O` of `c`).  Let `C, D, A, B` (the images of `a, b, a', b'`)
surround `O` counterclockwise, and let the image `C*` of the cap `d` satisfy (ii)
`C*`, `A` lie on opposite sides of the line `D O` and (iii) `C*`, `C` on the same
side of `O B`.  If `O ∈ int conv (B, C, D)`, then `O ∈ int conv (B, C*, D)`. -/
theorem inTri_cap_BD {c e a b a' b' d : ℝ³}
    (hba' : 0 < det3 (b - c) (a' - c) e)
    (hb'a : 0 < det3 (b' - c) (a - c) e)
    (hii : det3 (b - c) (d - c) e * det3 (b - c) (a' - c) e < 0)
    (hiii : 0 < det3 (b' - c) (d - c) e * det3 (b' - c) (a - c) e)
    (hBCD : 0 < det3 (b - c) (b' - c) e) :
    0 < det3 (b' - c) (d - c) e ∧ 0 < det3 (d - c) (b - c) e ∧ 0 < det3 (b - c) (b' - c) e := by
  refine ⟨pos_of_mul_pos_pos (by rwa [mul_comm] at hiii) hb'a, ?_, hBCD⟩
  rw [det3_swap12]
  have := neg_of_mul_neg_pos hii hba'
  linarith

/-- **Lemma 4 of §10, `A B C` form.**  As `inTri_cap_BD`, with also (i) `C*`, `B`
on opposite sides of the line `C O`: if `O ∈ int conv (A, B, C)`, then
`O ∈ int conv (A, B, C*)`. -/
theorem inTri_cap_AB {c e a b a' b' d : ℝ³}
    (hab : 0 < det3 (a - c) (b - c) e) (hba' : 0 < det3 (b - c) (a' - c) e)
    (ha'b' : 0 < det3 (a' - c) (b' - c) e) (hb'a : 0 < det3 (b' - c) (a - c) e)
    (hi : det3 (a - c) (d - c) e * det3 (a - c) (b' - c) e < 0)
    (hii : det3 (b - c) (d - c) e * det3 (b - c) (a' - c) e < 0)
    (hiii : 0 < det3 (b' - c) (d - c) e * det3 (b' - c) (a - c) e)
    (hABC : 0 < det3 (a - c) (a' - c) e) :
    0 < det3 (a' - c) (b' - c) e ∧ 0 < det3 (b' - c) (d - c) e ∧
      0 < det3 (d - c) (a' - c) e := by
  refine ⟨ha'b', pos_of_mul_pos_pos (by rwa [mul_comm] at hiii) hb'a, ?_⟩
  have had : 0 < det3 (a - c) (d - c) e :=
    pos_of_mul_neg_neg hi (by rw [det3_swap12]; linarith)
  have hdb : 0 < det3 (d - c) (b - c) e := by
    rw [det3_swap12]; have := neg_of_mul_neg_pos hii hba'; linarith
  have hpl := det3_plucker_e c e a b d a'
  have : 0 < det3 (a - c) (b - c) e * det3 (d - c) (a' - c) e := by
    rw [hpl]; positivity
  exact pos_of_mul_pos_pos this hab

/-- A linear relation among four vectors passes to `det3 (·) W e`. -/
theorem det3_lin_left {X₁ X₂ X₃ X₄ : ℝ³} {α₁ α₂ α₃ α₄ : ℝ}
    (h : α₁ • X₁ + α₂ • X₂ + α₃ • X₃ + α₄ • X₄ = 0) (W e : ℝ³) :
    α₁ * det3 X₁ W e + α₂ * det3 X₂ W e + α₃ * det3 X₃ W e + α₄ * det3 X₄ W e = 0 := by
  have h0 := congrArg (· 0) h; have h1 := congrArg (· 1) h; have h2 := congrArg (· 2) h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1 h2
  simp only [det3_expand]
  linear_combination (W 1 * e 2 - W 2 * e 1) * h0 + (W 2 * e 0 - W 0 * e 2) * h1 +
    (W 0 * e 1 - W 1 * e 0) * h2

/-- **Lemma 9.7, dependency form.**  A dependency of the six vertices that
vanishes at `a'` and is negative at `a`, `b`, `b'` (hence positive in sum at `c`,
`c'`) puts the image of `c` (projecting along the axis `e = ±(c' − c)`) on the
same side of the three sides of the triangle of the images of `b', a, b`: given
one orientation, the other two have its sign. -/
theorem inTri_of_dep {a a' b b' c c' : ℝ³} {L : ℝ³ → ℝ} (hL : IsDep a a' b b' c c' L)
    (h0 : L a' = 0) (ha : L a < 0) (hb : L b < 0) (hb' : L b' < 0) {e : ℝ³}
    (he : e = c' - c ∨ e = c - c') (hab : 0 < det3 (a - c) (b - c) e) :
    0 < det3 (b - c) (b' - c) e ∧ 0 < det3 (b' - c) (a - c) e := by
  have hrel : L a • (a - c) + L b • (b - c) + L b' • (b' - c) + L c' • (c' - c) =
      (L a • a + L a' • a' + L b • b + L b' • b' + L c • c + L c' • c') -
      (L a + L a' + L b + L b' + L c + L c') • c := by rw [h0]; module
  rw [hL.vsum, hL.sum, zero_smul, sub_zero] at hrel
  have zero1 : ∀ X : ℝ³, det3 X X e = 0 := fun X => by simp only [det3_expand]; ring
  have zero2 : ∀ X : ℝ³, det3 (c' - c) X e = 0 := fun X => by
    rcases he with rfl | rfl <;> simp only [det3_expand, PiLp.sub_apply] <;> ring
  have ra := det3_lin_left hrel (a - c) e
  have rb := det3_lin_left hrel (b - c) e
  rw [zero1, zero2] at ra rb
  have sw : ∀ X Y : ℝ³, det3 X Y e = -det3 Y X e := fun X Y => by rw [det3_swap12]
  rw [sw (b - c) (a - c)] at ra
  rw [sw (b' - c) (b - c)] at rb
  constructor
  · nlinarith
  · nlinarith

/-! ### Lemma 9.6 as an equivalence; Lemma 1 (a), (b) -/

/-- **Lemma 9.6 (one facet), both directions.** -/
theorem facet_lt_iff_of_dep {x x' y y' p p' : ℝ³} {L : ℝ³ → ℝ} (hL : IsDep x x' y y' p p' L)
    {V : Finset ℝ³} (G : FacetFn V x' y' p) (hxV : x ∈ V) (hyV : y ∈ V)
    (hnd : [x, x', y, y', p, p'].Nodup) (h0 : L p' = 0) (hLx : L x ≠ 0) :
    G.f x < G.f y ↔ L x * (L x + L y) < 0 := by
  refine ⟨fun h => ?_, fun h => facet_lt_of_dep hL G hxV hyV hnd h0 h⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have r := hL.apply G.hN
  rw [G.hP, G.hQ, G.hR, h0] at r
  have ny := G.neg y hyV (Ne.symm hx'y) hyy' hyp
  have e : L x * L x * (G.f x - G.f y) = -(L x * (L x + L y)) * G.f y := by
    linear_combination L x * r
  have hsq : 0 < L x * L x := mul_self_pos.mpr hLx
  have h1 : L x * L x * (G.f x - G.f y) < 0 := mul_neg_of_pos_of_neg hsq (by linarith)
  by_contra hc; push Not at hc
  nlinarith

/-- **Lemma 1 (a) of §10, Gale form.**  At the view along the edge `d b` of the
cap, the far end of `Q_bc` is `a'` (rather than `c`) iff `a'` is farther than `c`
from the plane of `abc'`; in the Gale diagram, iff `|[b' c]| > |[b' a']|`. -/
theorem far_end_Qbc_iff {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : galeD G.l G.m b b' ≠ 0) :
    F.abc'.f a' < F.abc'.f c ↔
      galeD G.l G.m b' a' * (galeD G.l G.m b' a' + galeD G.l G.m b' c) < 0 := by
  obtain ⟨d1, -, -⟩ := pole_signs F.perm₁₂.swap₁ (G.hl.galeD G.hm b').perm₁₂.swap₁
    (galeD_self _ _ b') (by rw [galeD_anti]; exact neg_ne_zero.mpr hκb)
  have hne : galeD G.l G.m b' a' ≠ 0 := by intro h; rw [h, mul_zero] at d1; exact lt_irrefl _ d1
  exact facet_lt_iff_of_dep (G.hl.galeD G.hm b').swap₁.perm₂₃ (F.swap₁.perm₂₃).a'b'c
    (by simp) (by simp) (F.swap₁.perm₂₃).nodup (galeD_self _ _ b') hne

/-- **Lemma 1 (b) of §10, Gale form.**  At the view along `d b`, the far end of
`Q_ab` is `c'` (rather than `a`) iff `|[b' a]| > |[b' c']|`. -/
theorem far_end_Qab_iff {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκb : galeD G.l G.m b b' ≠ 0) :
    F.a'bc.f c' < F.a'bc.f a ↔
      galeD G.l G.m b' c' * (galeD G.l G.m b' c' + galeD G.l G.m b' a) < 0 := by
  obtain ⟨-, d2, -⟩ := pole_signs F.perm₁₂.swap₁ (G.hl.galeD G.hm b').perm₁₂.swap₁
    (galeD_self _ _ b') (by rw [galeD_anti]; exact neg_ne_zero.mpr hκb)
  have hne : galeD G.l G.m b' c' ≠ 0 := by intro h; rw [h, mul_zero] at d2; exact lt_irrefl _ d2
  exact facet_lt_iff_of_dep (G.hl.galeD G.hm b').perm₂₃.perm₁₂.swap₁
    (F.perm₂₃.perm₁₂.swap₁).a'b'c (by simp) (by simp) (F.perm₂₃.perm₁₂.swap₁).nodup
    (galeD_self _ _ b') hne

/-! ### The normalized labelling (Lemma 6) and the Gale chain (Lemma 7) -/

/-- The Gale signs in the labelling of Lemma 6: `a`, `b` unprimed (`κ > 0`) and
`b ∈ U_W` for `W = {c, c'}` (`[b c] < 0`). -/
theorem type08_signs {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) :
    0 < galeD G.l G.m b a ∧ 0 < galeD G.l G.m b a' ∧ galeD G.l G.m b c' < 0 ∧
    0 < galeD G.l G.m b' a ∧ 0 < galeD G.l G.m b' a' ∧ galeD G.l G.m b' c < 0 ∧
      galeD G.l G.m b' c' < 0 ∧
    galeD G.l G.m a' b < 0 ∧ galeD G.l G.m a' b' < 0 ∧ 0 < galeD G.l G.m a' c ∧
      0 < galeD G.l G.m a' c' ∧
    galeD G.l G.m a b < 0 ∧ galeD G.l G.m a b' < 0 ∧ 0 < galeD G.l G.m a c ∧
      0 < galeD G.l G.m a c' := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂ (hl.galeD hm b).perm₁₂ (self b) hκb.ne'
  have hba : 0 < galeD G.l G.m b a := pos_of_mul_neg_neg b3 hU
  have hba' : 0 < galeD G.l G.m b a' := pos_of_mul_pos_pos b1 hba
  have hbc' : galeD G.l G.m b c' < 0 := neg_of_mul_pos_neg b2 hU
  obtain ⟨-, c2, -⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂ (self c) hκc
  have hcb : 0 < galeD G.l G.m c b := by rw [anti]; linarith
  have hcb' : 0 < galeD G.l G.m c b' := pos_of_mul_pos_pos c2 hcb
  have hb'c : galeD G.l G.m b' c < 0 := by rw [anti]; linarith
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁ (self b')
    (by rw [anti]; linarith)
  have hb'a : 0 < galeD G.l G.m b' a := pos_of_mul_neg_neg d3 hb'c
  have hb'a' : 0 < galeD G.l G.m b' a' := pos_of_mul_pos_pos d1 hb'a
  have hb'c' : galeD G.l G.m b' c' < 0 := neg_of_mul_pos_neg d2 hb'c
  obtain ⟨e1, e2, e3⟩ := pole_signs F.swap₁ (hl.galeD hm a').swap₁ (self a')
    (by rw [anti]; linarith)
  have ha'b : galeD G.l G.m a' b < 0 := by rw [anti]; linarith
  have ha'b' : galeD G.l G.m a' b' < 0 := neg_of_mul_pos_neg e1 ha'b
  have ha'c : 0 < galeD G.l G.m a' c := pos_of_mul_neg_neg (by rwa [mul_comm] at e3) ha'b
  have ha'c' : 0 < galeD G.l G.m a' c' := pos_of_mul_pos_pos e2 ha'c
  obtain ⟨f1, f2, f3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  have hab : galeD G.l G.m a b < 0 := by rw [anti]; linarith
  have hab' : galeD G.l G.m a b' < 0 := neg_of_mul_pos_neg f1 hab
  have hac : 0 < galeD G.l G.m a c := pos_of_mul_neg_neg (by rwa [mul_comm] at f3) hab
  have hac' : 0 < galeD G.l G.m a c' := pos_of_mul_pos_pos f2 hac
  exact ⟨hba, hba', hbc', hb'a, hb'a', hb'c, hb'c', ha'b, ha'b', ha'c, ha'c', hab, hab', hac, hac'⟩

/-- **Lemma 7 of §10 (the Gale chain).**  In the labelling of Lemma 6, if the far
end of `Q_bc` at the view along `d b` is `a'` (Lemma 1 (a)), then `a' → c` is a quad
edge of `O` (`a` hidden: both facet inequalities of Lemma 9.3 at the antipodal
edge `a c'`) and it is not bad. -/
theorem type08_lemma7 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : galeD G.l G.m c c' ≠ 0)
    (hU : galeD G.l G.m b c < 0) (hfar : F.abc'.f a' < F.abc'.f c) :
    F.ab'c'.f a' < F.ab'c'.f c ∧
      ¬ max ⟪c, c - a'⟫ ⟪c', c - a'⟫ ≤ min ⟪b, c - a'⟫ ⟪b', c - a'⟫ := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨hba, hba', -, hb'a, hb'a', hb'c, -, -, -, ha'c, -, -, -, hac, hac'⟩ :=
    type08_signs F G hκa hκb hκc hU
  -- Lemma 1 (a): `[b' a'] + [b' c] < 0`
  have hs : galeD G.l G.m b' a' + galeD G.l G.m b' c < 0 :=
    neg_of_mul_neg_pos (by rw [mul_comm]; exact (far_end_Qbc_iff F G hκb.ne').mp hfar) hb'a'
  -- the Plücker relation gives `[b a'] + [b c] < 0`
  have hpl := galeD_plucker G.l G.m b b' a' c
  have hsb : galeD G.l G.m b a' + galeD G.l G.m b c < 0 := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ -galeD G.l G.m b' c by linarith),
      mul_lt_mul_of_pos_left (show galeD G.l G.m b' a' < -galeD G.l G.m b' c by linarith)
        (show 0 < -galeD G.l G.m b c by linarith), mul_pos hκb ha'c]
  refine ⟨facet_lt_of_dep (hl.galeD hm b).swap₁.perm₂₃.swap₃ (F.swap₁.perm₂₃.swap₃).a'b'c
    (by simp) (by simp) (F.swap₁.perm₂₃.swap₃).nodup (self b) (mul_neg_of_pos_of_neg hba' hsb), ?_⟩
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  exact not_bad_of_dep (L := fun t => galeD G.l G.m t a) (hl.galeD' hm a).swap₁.perm₂₃
    hnd.2.1.2.2.1 (self a) (by rw [anti]; linarith) (by rw [anti a a', anti a c]; linarith)
    (by rw [anti]; linarith) hba.le hb'a.le

/-- **Lemma 6 of §10 (a non-quad pair).**  With all three `κ` nonzero, some
relabelling of the pairs (a permutation of `a, b, c` with the primes following,
cf. the `S3` symmetry of type 08) and possibly the mirrored Gale vectors
(`σ = −1`) give the labelling of Lemma 7: `κ_a, κ_b > 0` and `[b c] < 0`.  The
six disjuncts are the roles `(a, b, c)` taken by `(a, b, c)`, `(b, a, c)`,
`(a, c, b)`, `(c, a, b)`, `(b, c, a)`, `(c, b, a)`.  The inputs are the pole
signs (G3) `[a b][a c] < 0` etc. (`pole_signs`). -/
theorem type08_lemma6 {l m : ℝ³ → ℝ} {a a' b b' c c' : ℝ³}
    (hκa : galeD l m a a' ≠ 0) (hκb : galeD l m b b' ≠ 0) (hκc : galeD l m c c' ≠ 0)
    (hA : galeD l m a b * galeD l m a c < 0) (hB : galeD l m b a * galeD l m b c < 0)
    (hC : galeD l m c a * galeD l m c b < 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ((0 < σ * galeD l m a a' ∧ 0 < σ * galeD l m b b' ∧ σ * galeD l m b c < 0) ∨
       (0 < σ * galeD l m b b' ∧ 0 < σ * galeD l m a a' ∧ σ * galeD l m a c < 0) ∨
       (0 < σ * galeD l m a a' ∧ 0 < σ * galeD l m c c' ∧ σ * galeD l m c b < 0) ∨
       (0 < σ * galeD l m c c' ∧ 0 < σ * galeD l m a a' ∧ σ * galeD l m a b < 0) ∨
       (0 < σ * galeD l m b b' ∧ 0 < σ * galeD l m c c' ∧ σ * galeD l m c a < 0) ∨
       (0 < σ * galeD l m c c' ∧ 0 < σ * galeD l m b b' ∧ σ * galeD l m b a < 0)) := by
  have anti := galeD_anti l m
  have hC' : galeD l m a c * galeD l m b c < 0 := by
    have := hC; rw [anti a c, anti b c] at this; linarith [neg_mul_neg (galeD l m a c) (galeD l m b c)]
  have hB' : galeD l m a b * galeD l m c b < 0 := by
    have := hB; rw [anti a b, anti c b] at this; linarith [neg_mul_neg (galeD l m a b) (galeD l m c b)]
  have hA' : galeD l m b a * galeD l m c a < 0 := by
    have := hA; rw [anti b a, anti c a] at this; linarith [neg_mul_neg (galeD l m b a) (galeD l m c a)]
  have ne1 : ∀ x y : ℝ, x * y < 0 → (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) := by
    intro x y h
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at h) with hx | hx
    · exact Or.inl ⟨hx, by nlinarith⟩
    · exact Or.inr ⟨hx, by nlinarith⟩
  rcases lt_or_gt_of_ne hκa with ha | ha <;> rcases lt_or_gt_of_ne hκb with hb | hb <;>
    rcases lt_or_gt_of_ne hκc with hc | hc
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rcases ne1 _ _ hC' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rcases ne1 _ _ hC' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rcases ne1 _ _ hB' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
  · refine ⟨1, Or.inl rfl, ?_⟩
    rcases ne1 _ _ hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))))
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rcases ne1 _ _ hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))))
  · refine ⟨1, Or.inl rfl, ?_⟩
    rcases ne1 _ _ hB' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  · refine ⟨1, Or.inl rfl, ?_⟩
    rcases ne1 _ _ hC' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rcases ne1 _ _ hC' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩

/-! ### The cap -/

/-- The cap `d` of a type-08 point set over the octahedron `O = {a, a', b, b', c, c'}`
(§10, §0): `d` lies on the planes of `abc'`, `ab'c`, `a'bc` (which become the
quadrilaterals `Q_ab`, `Q_ac`, `Q_bc` of `K = O ∪ {d}`), strictly beyond the face
`abc` and strictly beneath the other four faces.  Conversely such a point gives a
type-08 hull. -/
structure IsCap {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop where
  abc' : F.abc'.f d = 0
  ab'c : F.ab'c.f d = 0
  a'bc : F.a'bc.f d = 0
  abc : 0 < F.abc.f d
  ab'c' : F.ab'c'.f d < 0
  a'bc' : F.a'bc'.f d < 0
  a'b'c : F.a'b'c.f d < 0
  a'b'c' : F.a'b'c'.f d < 0

/-- The `S3` symmetry of type 08: exchange the roles of the pairs `(a, a')` and
`(b, b')`. -/
theorem IsCap.perm₁₂ {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap F d) :
    IsCap F.perm₁₂ d :=
  ⟨h.abc', h.a'bc, h.ab'c, h.abc, h.a'bc', h.ab'c', h.a'b'c, h.a'b'c'⟩

/-- Exchange the roles of the pairs `(b, b')` and `(c, c')`. -/
theorem IsCap.perm₂₃ {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap F d) :
    IsCap F.perm₂₃ d :=
  ⟨h.ab'c, h.abc', h.a'bc, h.abc, h.ab'c', h.a'b'c, h.a'bc', h.a'b'c'⟩

/-- The cap is not a vertex of `O`. -/
theorem IsCap.ne {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap F d) :
    d ≠ a ∧ d ≠ a' ∧ d ≠ b ∧ d ≠ b' ∧ d ≠ c ∧ d ≠ c' := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have := h.abc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · rw [F.abc.hP] at this; exact lt_irrefl _ this
  · linarith [F.abc.neg d (by simp) (Ne.symm haa') ha'b ha'c]
  · rw [F.abc.hQ] at this; exact lt_irrefl _ this
  · linarith [F.abc.neg d (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c]
  · rw [F.abc.hR] at this; exact lt_irrefl _ this
  · linarith [F.abc.neg d (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')]

/-- **The quadrilateral `Q_ac = (d, a, b', c)` is convex**: in the frame
`d; a − d, c − d` its vertex `b'` opposite `d` has coordinates `α, β > 0` with
`α + β > 1`; `α` is read off the plane of `Q_bc` (through the line `d c`), `β` off
the plane of `Q_ab` (through `d a`). -/
theorem IsCap.Qac_coords' {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    0 < F.a'bc.f b' / F.a'bc.f a ∧ 0 < F.abc'.f b' / F.abc'.f c ∧
      1 < F.a'bc.f b' / F.a'bc.f a + F.abc'.f b' / F.abc'.f c ∧
      b' = d + (F.a'bc.f b' / F.a'bc.f a) • (a - d) + (F.abc'.f b' / F.abc'.f c) • (c - d) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n1 := F.ab'c.neg a' (by simp) (Ne.symm haa') ha'b' ha'c
  have n2 := F.a'bc.neg a (by simp) haa' hab hac
  have n3 := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have n4 := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c
  have n5 := F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'
  have n6 := F.abc.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c
  have hco := coords_of_affine3 F.ab'c.hN F.a'bc.hN F.abc'.hN hd.ab'c F.ab'c.hP F.ab'c.hR
    F.ab'c.hQ n1.ne hd.a'bc F.a'bc.hR n2.ne hd.abc' F.abc'.hP n3.ne
  set α := F.a'bc.f b' / F.a'bc.f a
  set β := F.abc'.f b' / F.abc'.f c
  refine ⟨div_pos_of_neg_of_neg n4 n2, div_pos_of_neg_of_neg n5 n3, ?_, hco⟩
  have hf := affine_frame F.abc.hN d a c α β
  rw [← hco, F.abc.hP, F.abc.hR] at hf
  nlinarith [hd.abc]

theorem IsCap.Qac_coords {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ b' = d + α • (a - d) + β • (c - d) :=
  let ⟨h1, h2, h3, h4⟩ := hd.Qac_coords'; ⟨_, _, h1, h2, h3, h4⟩

/-- `Q_bc = (d, b, a', c)` is convex. -/
theorem IsCap.Qbc_coords {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ a' = d + α • (b - d) + β • (c - d) :=
  hd.perm₁₂.Qac_coords

/-- `Q_ab = (d, a, c', b)` is convex. -/
theorem IsCap.Qab_coords {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ c' = d + α • (a - d) + β • (b - d) :=
  hd.perm₂₃.Qac_coords

/-- **Lemma 2 of §10 (the cap is a middle).**  If `a' → c` is a quad edge of `O`
(its first facet inequality, Lemma 9.1 (a) with the face `abc'`, which is also
Lemma 1 (a)), then at the view along `a' c` the cap lies over the chord from `c`
to the far end `b` of `Q_bc`, strictly between them, on the side away from `a'`:
`d = c + s (b − c) + δ (c − a')` with `0 < s < 1`, `δ > 0`. -/
theorem IsCap.middle_Qbc {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (hfar : F.abc'.f a' < F.abc'.f c) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ d = c + s • (b - c) + δ • (c - a') := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n1 := F.a'bc.neg a (by simp) haa' hab hac
  have n2 := F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc
  have n3 := F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c
  have n4 := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hco := coords_of_affine3 F.a'bc.hN F.a'b'c.hN F.abc.hN F.a'bc.hR F.a'bc.hQ F.a'bc.hP
    hd.a'bc n1.ne F.a'b'c.hR F.a'b'c.hP n2.ne F.abc.hR F.abc.hQ n3.ne
  set s := F.a'b'c.f d / F.a'b'c.f b
  set t := F.abc.f d / F.abc.f a'
  have hs : 0 < s := div_pos_of_neg_of_neg hd.a'b'c n2
  have ht : t < 0 := div_neg_of_pos_of_neg hd.abc n3
  refine ⟨s, -t, hs, ?_, by linarith, ?_⟩
  · have hf := affine_frame F.abc'.hN c b a' s t
    rw [← hco, hd.abc', F.abc'.hQ] at hf
    nlinarith [mul_pos_of_neg_of_neg ht (show F.abc'.f a' - F.abc'.f c < 0 by linarith)]
  · rw [hco]; module

/-- **Lemma 1 (c) of §10, the planar part.**  A convex quadrilateral
`P₀ P₁ P₂ P₃` (`P₂ = P₀ + α (P₁ − P₀) + β (P₃ − P₀)`, `α, β > 0`, `α + β > 1`) with an
affine depth `⟪·, u⟫` has no saddle (`NWS4`) unless its depths are all equal. -/
theorem nws4_of_planar_quad {P₀ P₁ P₂ P₃ u : ℝ³} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : 1 < α + β) (h : P₂ = P₀ + α • (P₁ - P₀) + β • (P₃ - P₀))
    (h01 : ⟪P₀, u⟫ ≠ ⟪P₁, u⟫) : NWS4 (quad ⟪P₀, u⟫ ⟪P₁, u⟫ ⟪P₂, u⟫ ⟪P₃, u⟫) := by
  have hz : ⟪P₂, u⟫ = ⟪P₀, u⟫ + α * (⟪P₁, u⟫ - ⟪P₀, u⟫) + β * (⟪P₃, u⟫ - ⟪P₀, u⟫) := by
    rw [h]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  constructor
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have hw1 : ⟪P₁, u⟫ - ⟪P₀, u⟫ < 0 := lt_of_le_of_ne (by linarith) (sub_ne_zero.mpr h01.symm)
    nlinarith [mul_nonneg hα.le (show 0 ≤ ⟪P₂, u⟫ - ⟪P₁, u⟫ by linarith),
      mul_nonneg hβ.le (show 0 ≤ ⟪P₂, u⟫ - ⟪P₃, u⟫ by linarith),
      mul_pos (sub_pos.mpr hαβ) (mul_pos hα (neg_pos.mpr hw1)),
      mul_nonneg (sub_pos.mpr hαβ).le (mul_nonneg hβ.le (show 0 ≤ ⟪P₀, u⟫ - ⟪P₃, u⟫ by linarith))]
  · by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    have hw1 : 0 < ⟪P₁, u⟫ - ⟪P₀, u⟫ := lt_of_le_of_ne (by linarith) (sub_ne_zero.mpr h01.symm).symm
    nlinarith [mul_nonneg hα.le (show 0 ≤ ⟪P₁, u⟫ - ⟪P₂, u⟫ by linarith),
      mul_nonneg hβ.le (show 0 ≤ ⟪P₃, u⟫ - ⟪P₂, u⟫ by linarith),
      mul_pos (sub_pos.mpr hαβ) (mul_pos hα hw1),
      mul_nonneg (sub_pos.mpr hαβ).le (mul_nonneg hβ.le (show 0 ≤ ⟪P₃, u⟫ - ⟪P₀, u⟫ by linarith))]

/-- **Lemma 1 (c) of §10.**  The rim `d, a, b', c` of `K_d` (the face `Q_ac`) is
unimodal at every view unless an edge of `Q_ac` is level (here: unless `d`, `a`
are at one depth). -/
theorem IsCap.Qac_nws4 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (u : ℝ³) (h : ⟪d, u⟫ ≠ ⟪a, u⟫) : NWS4 (quad ⟪d, u⟫ ⟪a, u⟫ ⟪b', u⟫ ⟪c, u⟫) := by
  obtain ⟨α, β, hα, hβ, hαβ, hb'⟩ := hd.Qac_coords
  exact nws4_of_planar_quad hα hβ hαβ hb' h

/-- The facts (i)–(iii) of the proof of Lemma 4, for any projection direction
`e`: in the plane of `Q_ac` the diagonal `a c` separates `d` from `b'` (i) and
`d`, `a` are on one side of the side `c b'` (iii); in `Q_bc` the diagonal `b c`
separates `d` from `a'` (ii). -/
theorem IsCap.axis_facts {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (e : ℝ³) (hab' : det3 (a - c) (b' - c) e ≠ 0) (hba' : det3 (b - c) (a' - c) e ≠ 0) :
    det3 (a - c) (d - c) e * det3 (a - c) (b' - c) e < 0 ∧
    det3 (b - c) (d - c) e * det3 (b - c) (a' - c) e < 0 ∧
    0 < det3 (b' - c) (d - c) e * det3 (b' - c) (a - c) e := by
  obtain ⟨α, β, hα, hβ, hαβ, hb'⟩ := hd.Qac_coords
  obtain ⟨α', β', hα', hβ', hαβ', ha'⟩ := hd.Qbc_coords
  have e1 : det3 (a - c) (b' - c) e = (1 - α - β) * det3 (a - c) (d - c) e := by
    rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have e2 : det3 (b - c) (a' - c) e = (1 - α' - β') * det3 (b - c) (d - c) e := by
    rw [ha']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have e3 : det3 (b' - c) (d - c) e = α * det3 (a - c) (d - c) e := by
    rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have e4 : det3 (b' - c) (a - c) e = (α + β - 1) * det3 (a - c) (d - c) e := by
    rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have had : det3 (a - c) (d - c) e ≠ 0 := by intro h0; rw [h0, mul_zero] at e1; exact hab' e1
  have hbd : det3 (b - c) (d - c) e ≠ 0 := by intro h0; rw [h0, mul_zero] at e2; exact hba' e2
  have sa := mul_self_pos.mpr had
  have sb := mul_self_pos.mpr hbd
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; nlinarith
  · rw [e2]; nlinarith
  · rw [e3, e4]; nlinarith [mul_pos hα (sub_pos.mpr hαβ)]

/-- The oriented area of the triangle `x y w`, seen from `w`. -/
theorem det3_rot3 (x y w e : ℝ³) : det3 (y - x) (w - x) e = det3 (x - w) (y - w) e := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- The axis view of `O` along `c c'`: the equator `a, b, a', b'` surrounds the
image of `c` with one orientation, for `e = c' − c` or `e = c − c'`. -/
theorem axis_quad_signs {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    ∃ e : ℝ³, (e = c' - c ∨ e = c - c') ∧ 0 < det3 (a - c) (b - c) e ∧
      0 < det3 (b - c) (a' - c) e ∧ 0 < det3 (a' - c) (b' - c) e ∧
      0 < det3 (b' - c) (a - c) e := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have H := h.perm₂₃.perm₁₂
  rcases lt_or_gt_of_ne (axis_orient_ne H) with hneg | hpos
  · obtain ⟨E1, E2, E3, E4⟩ := axis_tests H.swap₁ (by
      rw [show c - c' = -(c' - c) by abel, det3_neg_right]; linarith)
    refine ⟨c - c', Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · rw [← det3_rot3]; exact E1 c (by simp) (Ne.symm hac) (Ne.symm hbc)
    · rw [← det3_rot3]; exact E2 c (by simp) (Ne.symm hbc) (Ne.symm ha'c)
    · rw [← det3_rot3]; exact E3 c (by simp) (Ne.symm ha'c) (Ne.symm hb'c)
    · rw [← det3_rot3]; exact E4 c (by simp) (Ne.symm hb'c) (Ne.symm hac)
  · obtain ⟨E1, E2, E3, E4⟩ := axis_tests H hpos
    refine ⟨c' - c, Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · rw [← det3_rot3]; exact E1 c (by simp) (Ne.symm hac) (Ne.symm hbc)
    · rw [← det3_rot3]; exact E2 c (by simp) (Ne.symm hbc) (Ne.symm ha'c)
    · rw [← det3_rot3]; exact E3 c (by simp) (Ne.symm ha'c) (Ne.symm hb'c)
    · rw [← det3_rot3]; exact E4 c (by simp) (Ne.symm hb'c) (Ne.symm hac)

/-- **The T4 edge is not bad** (the third case of Theorem 10.1): in the labelling of
Lemma 6, Lemma 9.7 (dependency `[a' ·]`) puts the axis point `c` inside the
triangle `b' a b` in the view along `c c'`, Lemma 4 moves `a` to the cap `d`, and
Lemma 3 with `x = d`, `y = b`, `y' = b'`, `p, p' = c, c'` gives
`max (z b, z b') > min (z c, z c')` for `z = ⟪·, b − d⟫`.  The hypothesis `hopp`
(`c`, `c'` on opposite sides of the plane `d b b'`) holds when `b'` is a corner
of the view along `d b`. -/
theorem type08_t4_not_bad {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0)
    (hopp : det3 (b - d) (b' - d) (c - d) * det3 (b - d) (b' - d) (c' - d) < 0) :
    ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫ := by
  obtain ⟨-, -, -, -, -, -, -, ha'b, ha'b', -, -, -, -, -, -⟩ := type08_signs F G hκa hκb hκc hU
  obtain ⟨e, he, sab, sba', -, sb'a⟩ := axis_quad_signs h
  obtain ⟨hBCD, -⟩ := inTri_of_dep (G.hl.galeD G.hm a') (galeD_self _ _ a')
    (by rw [galeD_anti]; linarith) ha'b ha'b' he sab
  obtain ⟨-, hii, hiii⟩ := hd.axis_facts e (by rw [det3_swap12]; linarith) sba'.ne'
  obtain ⟨h1, h2, h3⟩ := inTri_cap_BD sba' sb'a hii hiii hBCD
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  refine not_bad_of_inTri (g := fun X => det3 (b - d) (b' - d) (X - d))
    (N := cross (b - d) (b' - d)) (fun s t => by simp only [det3, ← inner_sub_right]; abel_nf)
    (by simp only [sub_self]; simp [det3_expand]) (by simp only [det3_expand]; ring)
    (by simp only [det3_expand]; ring) hopp (hd.ne.2.2.1) ?_
  rcases he with rfl | rfl
  · exact Or.inl ⟨h2, h3, h1⟩
  · right
    simp only [show c - c' = -(c' - c) by abel, det3_neg_right] at h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩

end Minimality

end
