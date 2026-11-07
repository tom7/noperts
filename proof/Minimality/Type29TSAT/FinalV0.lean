module

public import Minimality.Type29TSAT.LinkV0
public import Minimality.Type29TSAT.NfV0

@[expose] public section

/-!
# Type 29, class V0: `NF29.isRupert_V0`

Every type 29 normal form with `V = 0` is Rupert, for any `a2`, `b0`.  No genericity hypothesis, no special position
excluded: the proof is the kernel-checked unsatisfiability of the trimmed core `coreUnsatV0`, every row of which is checked
against the real data (`rupert_of_coreV0`).  The only class literal is the zero unit `[0245] = 0`.
-/

set_option autoImplicit false
open Minimality

/-- **The class `V = 0` is closed.**  Every type 29 normal form with `V = 0` is Rupert, with no hypothesis on `a2`, `b0`
and no hypothesis of general position. -/
theorem Minimality.NF29.isRupert_V0 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (hV : N.V = 0) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29.SAT.nf29_V0_of_core
    (fun F h0 h1 => Minimality.H29.SAT.rupert_of_coreV0 Minimality.H29.SAT.coreUnsatV0 F h0 h1)
    N hV

#print axioms Minimality.NF29.isRupert_V0
