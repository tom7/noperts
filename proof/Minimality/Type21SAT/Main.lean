module

public import Minimality.Type21SAT.LinkA
public import Minimality.Type21SAT.LinkB
public import Minimality.Type21SAT.Final

@[expose] public section

/-!
# Type 21 is Rupert (SAT route)

Every realization of the faces of type 21 is Rupert.  Two unsatisfiability facts (cores A and B of the clause set of
`Type21SAT/*`) are checked in the kernel from LRAT certificates (`Checker`, `LratA`, `LratB`, `ProofA`, `ProofB`, `LinkA`,
`LinkB`); `type21_of_unsat` (`Final`) turns them into the geometric statement.  Axioms: `propext`, `Classical.choice`,
`Quot.sound` only.
-/

namespace Minimality.H21.SAT

theorem type21_isRupert (x : Fin 7 → EuclideanSpace ℝ (Fin 3))
    (hR : Minimality.RealizesFaces x (Minimality.sevenTypeFaces 20)) :
    IsRupert (Finset.univ.image x) :=
  type21_of_unsat coreUnsatA coreUnsatB x hR

end Minimality.H21.SAT
