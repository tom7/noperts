module

public import Mathlib
public import MinimalityExtra
public import Minimality.AcuteEdge

/-!
# The Acute Edge Lemma

Proof of `AcuteEdgeLemma` of `MinimalityExtra.lean`, from `Minimality.Split.AcuteEdge.ael_euclid`
(Minimality/AcuteEdge.lean).
-/

@[expose] public section

namespace MinimalityExtra

/-- Proof of `AcuteEdgeLemma`. -/
theorem acuteEdgeLemma : AcuteEdgeLemma := by
  intro n x a b nF nF' hF hFb hF' hF'b hA hq hSa hSb hE
  exact Minimality.Split.AcuteEdge.ael_euclid x a b nF nF' hF hFb hF' hF'b hA hq hSa hSb hE

end MinimalityExtra

end
