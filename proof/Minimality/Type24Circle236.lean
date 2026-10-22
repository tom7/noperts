module

public import Mathlib

@[expose] public section

/-!
# Type 24: the circle of 236 (Lemma 20.12)

`FEWER-FACES-PROOFS.md` §20, continued (2) (subagent UU, refereed 2026-10-22, scratch
`referee_UU/`): the linear identities behind Theorem 20.13, stated on the depth values.  Views
`d(s) = (1, s, w − s)` on the circle of 236 (`w = ω3`); at `d0 = (1, 0, w)` the depths of 0, 2, 6
are `p, q, r` and `z5 = a5 p + b5 q + c5 r`.  In S4, S5 the depths at E23's view `d(−σ)` are
written through the Gram entries `ga, gb, gc, hab, hac, hbc`.

* `Cu13.S1`: `T′(6,2)` fails only by `{6, 5} ≥ {0, 2}` (the pattern `{0, 2} ≥ {6, 5}` is
  impossible under the rim conditions and the view cut).
* `Cu13.S2`, `Cu13.S4`, `Cu13.S5`: the LPs of 20.13 that settle `z6 > z1`, `z6 > z0`, `z6 > z5`.

Not yet connected to `IsRupert` (Theorem 20.13 itself needs the rims of `T′(6,2)`, `S_6`, `E23`
in the `Type24*` setting).  Source: `nopert229/cu13_circle236.lean`, reused verbatim.
-/
namespace Cu13

/-- Lemma S1: with z2 ≤ z1 = 0 at d0 (q ≤ 0) and the view cut p + w r > 0, the pattern {0,2} ≥ {6,5} of T'(6,2)
is impossible, given a5 > 0, c5 ≤ w a5 (rim) and b5 + c5 ≤ 1 + w a5 (5 beneath the face 236). -/
theorem S1 (w a5 b5 c5 p q r : ℝ) (ha5 : 0 < a5) (hC1 : c5 ≤ w * a5) (hC2 : b5 + c5 ≤ 1 + w * a5)
    (hcut : 0 < p + w * r) (hq : q ≤ 0)
    (h02 : r ≤ q) (h25 : a5 * p + b5 * q + c5 * r ≤ q) : False := by
  have hA : 0 < a5 * (p + w * r) := mul_pos ha5 hcut
  have hB : 0 ≤ (w * a5 - c5) * (q - r) := mul_nonneg (by linarith) (by linarith)
  have hD : 0 ≤ (1 + w * a5 - b5 - c5) * (-q) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hA, hB, hD, h25]

/-- Lemma S2: if r ≥ p at d0 (pattern {6,5} ≥ {0,2}) and p + w r > 0, then r > 0; with r' = hbc - gc < 0 the depth
of 6 stays positive at every s ≤ 0. -/
theorem S2 (w p r gc hbc s : ℝ) (hw : 0 < w) (hcut : 0 < p + w * r) (hrp : p ≤ r) (hgc : 0 < gc)
    (hbc0 : hbc ≤ 0) (hs : s ≤ 0) : 0 < r + s * (hbc - gc) := by
  have hr : 0 < r := by nlinarith
  have : 0 ≤ s * (hbc - gc) := mul_nonneg_of_nonpos_of_nonpos hs (by linarith)
  linarith

/-- Lemma S4 (z6 > z0 at E23's view d(-σ)), in Gram entries.  The depths: at d0, p = ga + w hac, q = hab + w hbc,
r = hac + w gc; at d(-σ), z0 = ga - σ hab + (w + σ) hac, z6 = hac - σ hbc + (w + σ) gc.  Hypotheses: the pattern rows
r ≥ p, z5 ≥ p at d0, the obtuse signs hac, hbc ≤ 0, gc > 0, and (D1) b5 + w (1 - a5 - c5) > 0,
(D2) σ (1 - a5) ≤ b5, with a5 + b5 ≥ 1, σ > 0, b5 > 0, w ≥ 0. -/
theorem S4 (w σ a5 b5 c5 ga gc hab hac hbc : ℝ) (hσ : 0 < σ) (hb5 : 0 < b5) (hw : 0 ≤ w)
    (hD1 : 0 < b5 + w * (1 - a5 - c5)) (hD2 : σ * (1 - a5) ≤ b5) (hab5 : 1 ≤ a5 + b5) (hc5 : 0 ≤ c5)
    (hgc : 0 < gc) (hac0 : hac ≤ 0) (hbc0 : hbc ≤ 0)
    (hrp : ga + w * hac ≤ hac + w * gc)
    (h5p : ga + w * hac ≤ a5 * (ga + w * hac) + b5 * (hab + w * hbc) + c5 * (hac + w * gc)) :
    ga - σ * hab + (w + σ) * hac < hac - σ * hbc + (w + σ) * gc := by
  -- b5 times the identity of S4 (λ = σ / b5):
  -- b5 (z0 - z6)(-σ) + (b5 - σ(1 - a5)) (r - p)(0) + σ (z5 - p)(0) + σ (b5 + w (1 - a5 - c5)) gc
  --   + σ (b5 + a5 + c5 - 1) (-hac) + σ b5 (1 + w) (-hbc) = 0
  have e1 : 0 ≤ (b5 - σ * (1 - a5)) * ((hac + w * gc) - (ga + w * hac)) :=
    mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ σ * (a5 * (ga + w * hac) + b5 * (hab + w * hbc) + c5 * (hac + w * gc) - (ga + w * hac)) :=
    mul_nonneg hσ.le (by linarith)
  have e3 : 0 < σ * (b5 + w * (1 - a5 - c5)) * gc := mul_pos (mul_pos hσ hD1) hgc
  have e4 : 0 ≤ σ * (b5 + a5 + c5 - 1) * (-hac) :=
    mul_nonneg (mul_nonneg hσ.le (by linarith)) (by linarith)
  have e5 : 0 ≤ σ * b5 * (1 + w) * (-hbc) :=
    mul_nonneg (mul_nonneg (mul_nonneg hσ.le hb5.le) (by linarith)) (by linarith)
  have key : b5 * ((ga - σ * hab + (w + σ) * hac) - (hac - σ * hbc + (w + σ) * gc))
      = -((b5 - σ * (1 - a5)) * ((hac + w * gc) - (ga + w * hac))
        + σ * (a5 * (ga + w * hac) + b5 * (hab + w * hbc) + c5 * (hac + w * gc) - (ga + w * hac))
        + σ * (b5 + w * (1 - a5 - c5)) * gc + σ * (b5 + a5 + c5 - 1) * (-hac) + σ * b5 * (1 + w) * (-hbc)) := by
    ring
  have hneg : b5 * ((ga - σ * hab + (w + σ) * hac) - (hac - σ * hbc + (w + σ) * gc)) < 0 := by
    rw [key]; linarith
  by_contra hc
  have hc := not_lt.mp hc
  have : 0 ≤ b5 * ((ga - σ * hab + (w + σ) * hac) - (hac - σ * hbc + (w + σ) * gc)) :=
    mul_nonneg hb5.le (by linarith)
  linarith

/-- Lemma S5: at E23's view, z6 - z5 = (1 - a5 - c5) z6 + a5 (z6 - z0) - b5 z2 (z5 = a5 z0 + b5 z2 + c5 z6);
with z6 > 0, z6 > z0, z2 < 0, a5 + c5 ≤ 1, a5, b5 ≥ 0 it is positive. -/
theorem S5 (a5 b5 c5 z0 z2 z6 : ℝ) (ha5 : 0 ≤ a5) (hac : a5 + c5 ≤ 1)
    (h6 : 0 < z6) (h60 : z0 < z6) (h2 : z2 < 0) (hb5' : 0 < b5) :
    a5 * z0 + b5 * z2 + c5 * z6 < z6 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a5 - c5) h6.le, mul_nonneg ha5 (by linarith : (0:ℝ) ≤ z6 - z0),
    mul_pos hb5' (by linarith : (0:ℝ) < -z2)]


end Cu13
