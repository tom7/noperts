module

public import Mathlib
public import MinimalityExtra
public import Minimality.RightSlide

/-!
# The Slide Lemma

Proofs of `SlideLemma` and `SlideLemmaTriangularWalls` of `MinimalityExtra.lean`, from
`Minimality.Split.Slide.slide_euclid` and `Minimality.Split.Slide.slide_walls` (Minimality/RightSlide.lean).
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `SlideLemma`. -/
theorem slideLemma : SlideLemma := by
  intro n x a b a' b' e g nQ he hg hb' he0 hg0 hn0 heg hen hgn hD hZ hSl hR hK
  exact Minimality.Split.Slide.slide_euclid x a b a' b' e g nQ he hg hb' he0 hg0 hn0 heg hen hgn
    hD hZ hSl hR hK

/-- Proof of `SlideLemmaTriangularWalls`. -/
theorem slideLemmaTriangularWalls : SlideLemmaTriangularWalls := by
  intro n x a b a' b' p q e g nQ he hg hb' he0 hg0 hn0 heg hen hgn hD hZ hp hpG hpu hq hqG hqu hSl
  exact Minimality.Split.Slide.slide_walls x a b a' b' p q e g nQ
    (fun i => ⟪x i - x a, e⟫) (fun i => ⟪x i - x a, nQ⟫) (fun i => ⟪x i - x a, g⟫)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) he hg hb' he0 hg0 hn0 heg hen hgn hD hZ
    hp hpG hpu hq hqG hqu hSl

end MinimalityExtra

end
