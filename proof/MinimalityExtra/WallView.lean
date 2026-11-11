module

public import Mathlib
public import MinimalityExtra
public import Minimality.WallView

/-!
# The Wall View Lemma

Proof of `WallViewLemma` of `MinimalityExtra.lean`, from `Minimality.isRupert_of_wallView`
(Minimality/WallView.lean). The definition `det3` agrees with the project's (the triple product
`⟪cross a b, c⟫`), and the level conditions are the fields of `Minimality.WallShape`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `WallViewLemma`. -/
theorem wallViewLemma : WallViewLemma := by
  intro V n hn k _ hk x hxV hcyc hrest s r r' hsr hrr hrk h1 h2 h3 h4
  have e : ∀ x y z : ℝ³, det3 x y z = Minimality.det3 x y z := by
    intro x y z
    simp only [det3, Minimality.det3, Minimality.cross, PiLp.inner_apply]
    simp [Fin.sum_univ_three]
    ring
  simp only [e] at hcyc hrest
  exact Minimality.isRupert_of_wallView V n hn hk x hxV hcyc hrest ⟨hsr, hrr, hrk, h1, h2, h3, h4⟩

end MinimalityExtra
