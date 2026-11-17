module

public import Minimality.Type29SAT.Core

@[expose] public section

/-!
# L3, part 1: variables, literals, the three valued product, the relation lemma

Three valued from the start (L/DESIGN.md section 12, ST/core/CORE.md section 4).  A shape entry (atom) `v`
has two Boolean variables: `v` (`atom > 0`) and `ng v` (`atom < 0`), so it may vanish.  A product
of three valued signs is built from `gate` (the AND of two literals), as the encoder does
(`andL`, `orL`, `mul3` of ST/core/gc.cc).  There are no `prod` and `mux` variables.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
