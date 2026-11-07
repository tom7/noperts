module

public import Minimality.Type29SAT.LinkK3a
public import Minimality.Type29SAT.NfK3a

@[expose] public section

/-!
# Type 29, class K3a: `NF29.isRupert_K3a_closed`

Every normal form of class K3a (`a2 < 0`, `b0 > 0`, `V > 0`) is Rupert.  No genericity hypothesis, no special position
excluded: the proof is the kernel-checked unsatisfiability of the trimmed core of 4,423 clauses
(`coreUnsatK3a`), every row of which is checked against the real data (`rupert_of_coreK3a`).
-/

set_option autoImplicit false
open Minimality

/-- **Class K3a is closed.**  Every type 29 normal form with `a2 < 0`, `0 < b0`, `0 < V` is Rupert, with no
hypothesis of general position. -/
theorem Minimality.NF29.isRupert_K3a_closed {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x) (ha2 : N.a2 < 0)
    (hb0 : 0 < N.b0) (hV : 0 < N.V) : IsRupert (Finset.univ.image x) :=
  Minimality.H29.SAT.nf29_K3a_of_core
    (fun F h0 h1 h2 h3 => Minimality.H29.SAT.rupert_of_coreK3a Minimality.H29.SAT.coreUnsatK3a F h0 h1 h2 h3)
    N ha2 hb0 hV

