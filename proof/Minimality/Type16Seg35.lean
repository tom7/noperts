module

public import Minimality.Type16Vtx

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the segment `35` (§22.12)

The certificates of the cover at the view along `35` (the edge of the two quadrilaterals `0235`,
`1356`):
* the edge pairs of Theorem 19.2 (`(3, 5, a, b, 4)` with `a, b` the far ends, U1, U2, D2):
  `isRupert_ePair_limit` (§22.3–22.8 with Lemma E);
* the triangle closings D7 (`(3, 5, 6, 0)`): realized on both circles (Proposition 22.2,
  `isRupert_eTri_limit`);
* Lemma 19.3's `T1` (the closing `K_3`, rim `(3, 1, 4, x)`, and its `σ`-image): no Lemma E.  At the
  limit (`isRupert_kv_limit`) only the residual where `K_5` has a weak saddle and `K_3` none needs
  more; there `1` lies above `4` and `5` along `3 − 5`, and Lemma 19.3 (ii) makes `T2 = 046/145`
  unimodal (`isRupert_T2_at`), closed at its own view (no horizontal double normal there, or
  (G1): Proposition 22.2).

The codimension-2 conditions at `35` (`Gen35`): `EdgeGen` for the faces `1356`, `0235`; `3` and
`5` off the planes `124`, `014`, `246` of Lemma E; the shape off the boundary of Lemma 19.3's
region and of its `σ`-image (`Off193`).

* `Gen35`, `EdgeGen.negU`.
* `isRupert_ePair35`, `isRupert_eTri35`, `isRupert_pT1`, `isRupert_pT1σ`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `EdgeGen` at `−u` with the faces in the same order. -/
theorem EdgeGen.negU {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V (-u) v w SA SB NA NB where
  par := EdgeConf.ParOnly.neg' h.par
  g1 := G1At.swapF (EdgeConf.G1At.neg h.g1)
  dist := fun y hy y' hy' hne e => h.dist y hy y' hy' hne (by
    simp only [inner_neg_right, neg_inj] at e; exact e)
  one := h.one.neg_u
  footA := h.footA
  footB := h.footB

theorem EdgeGen.sgn {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    EdgeGen V (ε • u) v w SA SB NA NB := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]; exact h.negU

/-! ### The edge pairs at `35` -/

/-! ### The triangle closings at `35` (D7) -/

/-! ### Lemma 19.3's `T1` at `35` -/

end Minimality

end
