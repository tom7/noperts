module

public import Mathlib
public import MinimalityExtra
public import Minimality.HiddenEnd

/-!
# The Hidden-End Lemma

Proof of `HiddenEndLemma` of `MinimalityExtra.lean`, from `Minimality.Split.HEL.hel_rupert`
(Minimality/HiddenEnd.lean). The definitions `det3`, `cross`, `LexPos3` agree with the project's, so
the hypotheses transfer by `rfl`-conversion.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace MinimalityExtra

/-- Proof of `HiddenEndLemma`. -/
theorem hiddenEndLemma : HiddenEndLemma := by
  intro n x c K J M α β γ δ ω τ hD hαγ hβδ hcert
  exact Minimality.Split.HEL.hel_rupert x c K J M α β γ δ ω τ hD hαγ hβδ hcert

end MinimalityExtra
