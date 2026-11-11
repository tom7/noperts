module

public import Mathlib
public import MinimalityExtra
public import Minimality.LevelCorner

/-!
# The Level Corner Slide Lemma

Proof of `LevelCornerSlideLemma` of `MinimalityExtra.lean`, from
`Minimality.Split.LevelCorner.level_corner_euclid` (Minimality/LevelCorner.lean).
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `LevelCornerSlideLemma`. -/
theorem levelCornerSlideLemma : LevelCornerSlideLemma := by
  intro n x c J M P W e f g he hf he0 hf0 hg0 hef heg hfg hD hQ hPe hPf hNj hWe hWf hWu
  exact Minimality.Split.LevelCorner.level_corner_euclid x c J M P W e f g he hf he0 hf0 hg0
    hef heg hfg hD hQ hPe hPf hNj hWe hWf hWu

end MinimalityExtra
