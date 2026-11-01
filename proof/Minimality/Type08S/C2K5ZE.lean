module

public import Minimality.Type08S.C2K5ZD
public import Minimality.Type08S.C2K5BI

@[expose] public section

/-!
# K5ZE: the K5b hypotheses discharged; `Resid08FinalK9 → Resid08FinalK10` unconditionally
-/

namespace Minimality
namespace Type08Sp

/-- The two K5b wrappers (C2K5BI) are exactly the fields of `K5ZbHyp`. -/
theorem k5z_bhyp : K5ZbHyp where
  qn2 W hκ h h1 h2 h3 := C2.k5b_qn2_hasLexCell W hκ h h1 h2 h3
  qceb W hκ h hr1 hr2 h1 h2 h3 := C2.k5b_qceb_hasLexCell W hκ h hr1 hr2 h2 h1 h3

/-- **Type 08 planar residual cut to its tie slices** (`Resid08FinalK10`). -/
theorem resid08FinalK9_imp_K10' {a a' b b' c c' d : ℝ³} (h : Resid08FinalK9 a a' b b' c c' d) :
    Resid08FinalK10 a a' b b' c c' d :=
  resid08FinalK9_imp_K10 k5z_bhyp h

end Type08Sp
end Minimality
