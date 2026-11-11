module

public import Mathlib
public import MinimalityExtra
public import Minimality.CornerSlide

/-!
# The Corner Slide Lemma

Proof of `CornerSlideLemma` of `MinimalityExtra.lean`, from `Minimality.Split.Corner.corner_euclid`
(Minimality/CornerSlide.lean).
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `CornerSlideLemma`. -/
theorem cornerSlideLemma : CornerSlideLemma := by
  intro n x c J M e f g he hf he0 hf0 hg0 hef heg hfg hD hQ hNj hOm
  exact Minimality.Split.Corner.corner_euclid x c J M e f g he hf he0 hf0 hg0 hef heg hfg hD hQ hNj hOm

end MinimalityExtra
