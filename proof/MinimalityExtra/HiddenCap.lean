module

public import Mathlib
public import MinimalityExtra
public import Minimality.HiddenCap

/-!
# The Hidden-Cap Lemma

Proof of `HiddenCapLemma` of `MinimalityExtra.lean`, from `Minimality.hiddenAt_of_normals`
(Minimality/HiddenCap.lean). The definition `det3` agrees with the project's (the triple product
`⟪cross a b, c⟫`), so the supporting-line hypotheses transfer by this identity.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `HiddenCapLemma`. -/
theorem hiddenCapLemma : HiddenCapLemma := by
  intro O v a b c ha hb hc hli hab hac hbc n α hα hle hlt A hA B hB h1 h2
  have e : ∀ x y z : ℝ³, det3 x y z = Minimality.det3 x y z := by
    intro x y z
    simp only [det3, Minimality.det3, Minimality.cross, PiLp.inner_apply]
    simp [Fin.sum_univ_three]
    ring
  simp only [e] at h1 h2 ⊢
  exact Minimality.hiddenAt_of_normals O v a b c ha hb hc hli hab hac hbc n α hα hle hlt
    A hA B hB h1 h2

end MinimalityExtra
