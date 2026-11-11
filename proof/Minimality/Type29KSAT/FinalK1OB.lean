module

public import Minimality.Type29KSAT.LinkK1aOB
public import Minimality.Type29KSAT.K1CornerOB

@[expose] public section

/-!
# Type 29, class K1 off the obtuse corner: `NF29.isRupert_K1_offOB6`

Every normal form of class K1 (`a2 < 0 < b0`, `V < 0`, or `a2 > 0 > b0`, `V > 0`) with an acute face angle at vertex `6`
(that is, not all of `⟪x3 - x6, x4 - x6⟫`, `⟪x3 - x6, x5 - x6⟫`, `⟪x4 - x6, x5 - x6⟫` are `≤ 0`) is Rupert.  The proof is the
kernel-checked unsatisfiability of a core of 3,743 clauses of the tie view encoding, with the brackets as class literals
and the acute-angle clause as class clause (`rupert_of_coreK1aOB`); K1b is the `σ`-image of K1a.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

/-- **Class K1 off the obtuse corner is closed**. -/
theorem Minimality.NF29.isRupert_K1_offOB6 {x : Fin 7 → EuclideanSpace ℝ (Fin 3)} (N : NF29 x)
    (hK1 : (N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V))
    (hO : ¬ (inner ℝ (x 3 - x 6) (x 4 - x 6) ≤ 0 ∧ inner ℝ (x 3 - x 6) (x 5 - x 6) ≤ 0 ∧
      inner ℝ (x 4 - x 6) (x 5 - x 6) ≤ 0)) :
    IsRupert (Finset.univ.image x) :=
  Minimality.H29K1.nf29_K1_offOB_of_core
    (fun F h0 h1 h2 h3 hz => Minimality.H29K.SAT.rupert_of_coreK1aOB Minimality.H29K.SAT.coreUnsatK1aOB F h0 h1 h2 h3 hz)
    N hK1 hO

#print axioms Minimality.NF29.isRupert_K1_offOB6
