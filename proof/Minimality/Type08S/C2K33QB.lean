module

public import Minimality.Type08S.C2K33QA
public import Minimality.Type08S.C2K33QS

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `ori(c',b,a') = n_cba · u0`, `u0 = ((κB-κA)(α1-1), -β1 κA, β1 κB)`, `κA = ⟪b'-a, c-a'⟫`, `κB = ⟪c'-a, c-a'⟫`
(the coordinates of `u0^R2 = (β1,1-α1,1-α1) × G(c-a')` in the basis `(a-d,b-d,c-d)`). -/
def k28bqOriCBA (α1 β1 β6 γ6 κA κB : ℝ) : ℝ :=
  (1 - β1) * γ6 * ((κB - κA) * (α1 - 1)) + α1 * γ6 * (-β1 * κA) + α1 * (1 - β6) * (β1 * κB)

/-- `ori(b',c,a') = n_bca · u0`. -/
def k28bqOriBCA (α1 β1 β6 γ6 κA κB : ℝ) : ℝ :=
  (β1 - 1) * β6 * ((κB - κA) * (α1 - 1)) + α1 * (γ6 - 1) * (-β1 * κA) + (-α1 * β6) * (β1 * κB)

theorem k28bq_ori1 {α1 β1 β6 t κA : ℝ} :
    k28bqOriCBA α1 β1 β6 (β1 - β6) κA (t * κA) =
      -κA * (t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6)) := by
  unfold k28bqOriCBA; ring

theorem k28bq_ori2 {α1 β1 β6 t κA : ℝ} :
    k28bqOriBCA α1 β1 β6 (β1 - β6) κA (t * κA) =
      -κA * (t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6) := by
  unfold k28bqOriBCA; ring

end C2
end Type08Sp
end Minimality
