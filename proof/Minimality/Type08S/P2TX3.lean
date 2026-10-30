module

public import Minimality.Type08S.P2TX2

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X3: the coordinate core of the cell `(−,−,−)` (`Rupert` from the frame data and a good tilt).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 1600000 in
theorem cell_core (hF : Fr e1 e2 e3) (o : ℝ³) {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hv : σ * v1 < 0)
    (hu : 0 < σ * (w1 - ha * t1)) (hu2 : σ * (w1 - ha * t1) * α4 < -(σ * v1) * (γ4 - 1))
    (hrob : ¬ Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) (β6 * ν + C0))
    (h01 : t1 * (-v1) + 1 * 0 ≠ t1 * (-v1 + α1 * w1) + 1 * (α1 * ha))
    (h02 : t1 * (-v1) + 1 * 0 ≠ t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha))
    (h03 : t1 * (-v1) + 1 * 0 ≠ t1 * 0 + 1 * 0)
    (h12 : t1 * (-v1 + α1 * w1) + 1 * (α1 * ha) ≠ t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha))
    (h13 : t1 * (-v1 + α1 * w1) + 1 * (α1 * ha) ≠ t1 * 0 + 1 * 0)
    (h23 : t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha) ≠ t1 * 0 + 1 * 0)
    (V : Finset ℝ³)
    (hV : ∀ y ∈ V, y = pt e1 e2 e3 o (-v1) 0 0 ∨ y = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨
      y = pt e1 e2 e3 o 0 0 C0 ∨ y = pt e1 e2 e3 o (-v1) 0 ν ∨
      y = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∨
      y = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∨
      y = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (m0 : pt e1 e2 e3 o (-v1) 0 ν ∈ V)
    (m1 : pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∈ V)
    (m2 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ V)
    (m3 : pt e1 e2 e3 o 0 0 (β6 * ν + C0) ∈ V) : IsRupert V := by
  obtain ⟨rd, rc, ra⟩ := cell_rest hν hha hα hα4 hγ4 hβ1 hβ6 hv hu hu2
  refine rupert_of_coordRim hF o V (k := 4) (by norm_num) (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6) ?_
    σ hσ t1 1 (cell_cyc hν hha hα hα4 hγ4 hβ1 hE hv) ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [cellRim, quad4_0, quad4_1, quad4_2, quad4_3]
    exacts [m0, m1, m2, m3]
  · intro y hy
    rcases hV y hy with h | h | h | h | h | h | h
    · exact ⟨(-v1, 0, 0), h, Or.inr rd⟩
    · exact ⟨(-v1 + w1, ha, w3), h, Or.inr ra⟩
    · exact ⟨(0, 0, C0), h, Or.inr rc⟩
    · exact ⟨(-v1, 0, ν), h, Or.inl ⟨0, rfl⟩⟩
    · exact ⟨(-v1 + α1 * w1, α1 * ha, α1 * w3 + β1 * ν), h, Or.inl ⟨1, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0), h, Or.inl ⟨2, rfl⟩⟩
    · exact ⟨(0, 0, β6 * ν + C0), h, Or.inl ⟨3, rfl⟩⟩
  · have key : ∀ s : ℝ, (fun i => dep t1 1 s (cellRim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)) =
        quad (ν + s * (t1 * (-v1) + 1 * 0)) ((α1 * w3 + β1 * ν) + s * (t1 * (-v1 + α1 * w1) + 1 * (α1 * ha)))
          ((α4 * w3 + γ4 * C0) + s * (t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha)))
          ((β6 * ν + C0) + s * (t1 * 0 + 1 * 0)) := by
      intro s
      funext i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [cellRim, dep, quad4_0, quad4_1, quad4_2, quad4_3]
    simp only [key]
    exact qtop4_ev hrob h01 h02 h03 h12 h13 h23

end Type08Sp
end Minimality
