module

public import Minimality.Type16Sector
public import Minimality.EdgeTwoFace

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the segments `02` and `16` (§22)

The certificates of the cover at the views along `02` and `16` (and the reversed `20`, `61`)
are the edge pairs `(0, 2, 3, 4, 6)` (U3) and `(6, 1, 3, 4, 0)` (its `σ`-image) and the triangle
closings `(2, 0, 5, 4)`, `(1, 6, 5, 4)` (D5 and its image); no pair certificate of Lemmas
19.3–19.5 uses these views (`pairsViews16`).  At the limit (Lemma 18.2), §22 closes the edge pairs
(`isRupert_ePair_limit`: Proposition 22.2, Lemmas 22.3–22.7, Theorem 22.8 with Lemma E) and the
triangle closings (`isRupert_eTri_limit`: two realizing circles) under the codimension-2
conditions `Gen02`, `Gen16` (`EdgeGen` at the view, and the axle off the plane of Lemma E), so
there no horizontal-double-normal hypothesis is left.

* `isRupert_of_certL_seq_at`, `isRupert_of_rimCert_seq_at`: Lemma 18.2 with the alternative of
  `Sec16` asked only at the certificate's view.
* `Gen02`, `Gen16`, `EdgeOK16`.
* `isRupert_of_cert_seq_edge`, `isRupert_type16_limit_edge`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Lemma 18.2 at one view -/

/-! ### The conditions at the views `02` and `16` -/

theorem EdgeGen.swapF {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V u v w SB SA NB NA :=
  ⟨h.par, h.g1.swapF, h.dist, h.one, h.footB, h.footA⟩

theorem EdgeGen.rev {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V (-u) w v SA SB NA NB where
  par := EdgeConf.ParOnly.neg' (EdgeConf.ParOnly.symm h.par)
  g1 := (EdgeConf.G1At.neg h.g1).swapF
  dist := fun y hy y' hy' hne e => h.dist y hy y' hy' hne (by
    simp only [inner_neg_right, neg_inj] at e; exact e)
  one := h.one.neg_u
  footA := h.footA
  footB := h.footB

/-- A facet's functional in the form of `isRupert_ePair_limit`. -/
theorem Face16.hf {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i₀ : Fin 7}
    (h₀ : i₀ ∈ S) :
    ∀ i, (i ∈ S → ⟪F.N, x i⟫ = ⟪F.N, x i₀⟫) ∧ (i ∉ S → ⟪F.N, x i⟫ < ⟪F.N, x i₀⟫) := by
  intro i
  have k := F.hN (x i) (x i₀)
  rw [F.zero i₀ h₀, sub_zero, inner_sub_right] at k
  constructor
  · intro hi; rw [F.zero i hi] at k; linarith
  · intro hi; have := F.neg i hi; linarith

/-- An adjacent facet through `p`, `q`, below at `r` and `s`. -/
theorem Face16.adj {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {p q r s : Fin 7}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∉ S) (hs : s ∉ S) :
    ⟪F.N, x q - x p⟫ = 0 ∧ ⟪F.N, x r - x p⟫ < 0 ∧ ⟪F.N, x s - x p⟫ < 0 := by
  have h := F.hf hp
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_sub_right, (h q).1 hq, sub_self]
  · rw [inner_sub_right]; linarith [(h r).2 hr]
  · rw [inner_sub_right]; linarith [(h s).2 hs]

/-! ### The four certificates at `02` and `16` -/

end Minimality

end
