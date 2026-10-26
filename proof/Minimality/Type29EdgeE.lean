module

public import Minimality.Type29TwoFace
public import Minimality.Type16Edge

@[expose] public section

/-!
# Type 29: the Lemma E edges at the limit (`FEWER-FACES-PROOFS.md` §22.3–22.8, §14, §28.5)

The segments `14`, `15`, `46`, `56` are edges between a quadrilateral and a triangle, and
the certificates there are the edge pairs of Lemma E (`ePairLabels29`: the closings at `v` and
`w`).  At the limit the pair is closed by `isRupert_ePair_limit` under the codimension-2
conditions `EdgeOK29`: `EdgeGen` at the view `w − v` for the normals of the two faces through
the edge (only the axle seen end-on, (G1), distinct depths, one direction of horizontal double
normals, no double normal perpendicular to a face from a face vertex), and `v`, `w` off the
plane of the pair's Lemma E triple.

* `EdgeOK29`: the codimension-2 conditions at one edge pair.
* `closeE29`: a frequent edge pair `(v, w, a, b, c)` of either orientation is closed under
  `EdgeOK29`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- **The codimension-2 conditions at the edge pair `(v, w, a, b, c)`** between the faces `S_a`
(through `v, w, a`) and `S_b` (through `v, w, b`): `EdgeGen` at the view `w − v` for their
normals (any nonzero normal of the plane through `v, w, a`, resp. `v, w, b`), and `v`, `w` off the
plane `a b c` of Lemma E. -/
def EdgeOK29 (x : Fin 7 → ℝ³) (v w a b c : Fin 7) (Sa Sb : Finset (Fin 7)) : Prop :=
  (∀ NA NB : ℝ³, NA ≠ 0 → ⟪NA, x w - x v⟫ = 0 → ⟪NA, x a - x v⟫ = 0 →
    NB ≠ 0 → ⟪NB, x w - x v⟫ = 0 → ⟪NB, x b - x v⟫ = 0 →
    EdgeGen (univ.image x) (x w - x v) (x v) (x w) (Sa.image x) (Sb.image x) NA NB) ∧
  det3 (x b - x a) (x c - x a) (x v - x a) ≠ 0 ∧ det3 (x b - x a) (x c - x a) (x w - x a) ≠ 0

/-- **An edge pair of Lemma E at the limit** (Lemma 18.2 with §22): frequent certificates
`EPairData` (either orientation) at the pair `(v, w, a, b, c)` between the facets `S_a ∋ v, w, a`
and `S_b ∋ v, w, b` (at most one middle each) make the limit Rupert under `EdgeOK29`. -/
theorem closeE29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) {v w a b c : Fin 7}
    {Sa Sb : Finset (Fin 7)} (FA : Face16 x Sa) (FB : Face16 x Sb) (hvw : v ≠ w)
    (hSa : v ∈ Sa ∧ w ∈ Sa ∧ a ∈ Sa ∧ b ∉ Sa ∧ c ∉ Sa ∧ ∀ i ∈ Sa, ∀ j ∈ Sa,
      i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j)
    (hSb : v ∈ Sb ∧ w ∈ Sb ∧ b ∈ Sb ∧ a ∉ Sb ∧ c ∉ Sb ∧ ∀ i ∈ Sb, ∀ j ∈ Sb,
      i ≠ v → i ≠ w → i ≠ b → j ≠ v → j ≠ w → j ≠ b → i = j)
    (hg : EdgeOK29 x v w a b c Sa Sb)
    (hfreq : ∃ᶠ n in atTop, ∃ σ : ℝ,
      EPairData (univ.image (K n)) σ (K n v) (K n w) (K n a) (K n b) (K n c)) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ : ∃ s : Bool, ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n v) (K n w) (K n a) (K n b) (K n c) :=
    frequently_exists_of_finite (hfreq.mono fun n ⟨σ, hσ⟩ => by
      rcases hσ.1 with h | h
      · subst h; exact ⟨true, hσ⟩
      · subst h; exact ⟨false, hσ⟩)
  obtain ⟨hgen, hc1, hc2⟩ := hg
  have hNA : FA.N ≠ 0 := FA.N_ne hSa.1 hSa.2.2.2.1
  have hNB : FB.N ≠ 0 := FB.N_ne hSb.1 hSb.2.2.2.1
  have hG := hgen FA.N FB.N hNA (FA.inner_sub hSa.2.1 hSa.1) (FA.inner_sub hSa.2.2.1 hSa.1) hNB
    (FB.inner_sub hSb.2.1 hSb.1) (FB.inner_sub hSb.2.2.1 hSb.1)
  cases s
  · rw [sgnB_false] at hs
    refine isRupert_ePair_limit x N.inj N.noSeg (v := v) (w := w) (a := b) (b := a) (c := c) hvw
      (FB.hf (i₀ := v) hSb.1) (FA.hf (i₀ := v) hSa.1) hSb hSa K hK (hs.mono fun n hn => hn.flip)
      hG.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hc1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hc2
  · rw [sgnB_true] at hs
    exact isRupert_ePair_limit x N.inj N.noSeg hvw (FA.hf (i₀ := v) hSa.1)
      (FB.hf (i₀ := v) hSb.1) hSa hSb K hK hs hG ⟨hc1, hc2⟩

end Minimality

end
