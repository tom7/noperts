module

public import Minimality.Type21SAT.RowB

@[expose] public section

/-!
# L3, part 28a: rule, witness, lex rule and unit rows of core B, the kernel check
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H21.SAT

/-- All rule, witness, lex rule and unit rows of core B pass their checks. -/
theorem bspecialAll :
    (rowsB.all fun ch => ch.all fun n => ruleDB n && witDB n && lexDB n && unitDB n) = true := by
  decide +kernel

end Minimality.H21.SAT
