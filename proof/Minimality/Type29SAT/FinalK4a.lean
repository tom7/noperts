module

public import Minimality.Type29SAT.LinkK4a
public import Minimality.Type29SAT.Nf

@[expose] public section

/-!
# Type 29, class K4a: `NF29.isRupert_K4a_closed`

Every normal form of class K4a (`a2 > 0`, `b0 > 0`, `V < 0`) is Rupert.  No genericity hypothesis, no special position
excluded: the proof is the kernel-checked unsatisfiability of the trimmed core of 3,214 clauses
(`coreUnsatK4a`), every row of which is checked against the real data (`rupert_of_coreK4a`).
-/

set_option autoImplicit false
open Minimality

/-- **Class K4a is closed.**  Every type 29 normal form with `0 < a2`, `0 < b0`, `V < 0` is Rupert, with no
hypothesis of general position. -/
theorem Minimality.NF29.isRupert_K4a_closed {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0) (hV : N.V < 0) : IsRupert (Finset.univ.image x) :=
  Minimality.H29.SAT.nf29_K4a_of_core
    (fun F h0 h1 h2 h3 => Minimality.H29.SAT.rupert_of_coreK4a Minimality.H29.SAT.coreUnsatK4a F h0 h1 h2 h3)
    N ha2 hb0 hV

