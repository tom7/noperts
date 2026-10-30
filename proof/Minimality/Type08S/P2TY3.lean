module

public import Minimality.Type08S.P2TY2

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X2 / Y3: `Rupert` from the frame data of the cell `(+,−,−)` (`cell2_core`) and the order facts.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The four order facts that the depth pattern needs, from `¬RobKb`, robust `X_ba'` and `R ≠ P`. -/
theorem cell2_facts {ν w3 C0 α1 α4 γ4 β1 β6 : ℝ} (hν : 0 < ν) (hα : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hrob : ¬ Sep ν (α4 * w3 + γ4 * C0) (β6 * ν + C0) (α1 * w3 + β1 * ν))
    (hK : Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) C0)
    (hRP : α1 * w3 + β1 * ν ≠ α4 * w3 + γ4 * C0) :
    (0 : ℝ) < ν ∧ (w3 < 0 ∨ w3 < α1 * w3 + β1 * ν) ∧ α1 * w3 + β1 * ν < α4 * w3 + γ4 * C0 ∧
      (ν < β6 * ν + C0 ∨ α4 * w3 + γ4 * C0 < β6 * ν + C0) := by
  have hb6 := mul_pos hβ6 hν
  have hb1 := mul_pos hβ1 hν
  refine ⟨hν, ?_, ?_, ?_⟩
  · rcases lt_or_ge w3 0 with h | h
    · exact Or.inl h
    · right; nlinarith
  · simp only [Sep, max_le_iff, le_min_iff, and_assoc] at hK
    rcases hK with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact lt_of_le_of_ne h3 hRP
    · exfalso; apply hrob
      simp only [Sep, max_le_iff, le_min_iff, and_assoc]
      right; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · simp only [Sep, max_le_iff, le_min_iff, and_assoc] at hK
    rcases hK with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · by_contra hc
      push Not at hc
      apply hrob
      simp only [Sep, max_le_iff, le_min_iff, and_assoc]
      left; refine ⟨hc.1, ?_, hc.2, ?_⟩ <;> linarith
    · exfalso; apply hrob
      simp only [Sep, max_le_iff, le_min_iff, and_assoc]
      right; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

set_option maxHeartbeats 3200000 in
theorem cell2_core (hF : Fr e1 e2 e3) (o : ℝ³) {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hv : σ * v1 < 0)
    (hu : 0 < σ * (ha * t1 - w1)) (hu2 : -(σ * v1) * (1 - γ4) < α4 * (σ * (ha * t1 - w1)))
    (hrob : ¬ Sep ν (α4 * w3 + γ4 * C0) (β6 * ν + C0) (α1 * w3 + β1 * ν))
    (hK : Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) C0)
    (hRP : α1 * w3 + β1 * ν ≠ α4 * w3 + γ4 * C0)
    (n1 : t1 * 0 + 1 * 0 ≠ t1 * (-v1) + 1 * 0)
    (n2 : t1 * 0 + 1 * 0 ≠ t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha))
    (V : Finset ℝ³)
    (hV : ∀ y ∈ V, y = pt e1 e2 e3 o (-v1) 0 0 ∨ y = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨
      y = pt e1 e2 e3 o 0 0 C0 ∨ y = pt e1 e2 e3 o (-v1) 0 ν ∨
      y = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∨
      y = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∨
      y = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (m0 : pt e1 e2 e3 o 0 0 (β6 * ν + C0) ∈ V)
    (m1 : pt e1 e2 e3 o (-v1) 0 ν ∈ V)
    (m2 : pt e1 e2 e3 o (-v1) 0 0 ∈ V)
    (m3 : pt e1 e2 e3 o (-v1 + w1) ha w3 ∈ V)
    (m4 : pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν) ∈ V)
    (m5 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ V) : IsRupert V := by
  obtain ⟨f1, f2, f3, f4⟩ := cell2_facts hν hα hβ1 hβ6 hrob hK hRP
  have rc := cell2_rest (w3 := w3) (C0 := C0) hν hha hα hα4 hγ4 hβ1 hβ6 hE hv hu hu2
  refine rupert_of_coordRim hF o V (k := 6) (by norm_num) (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6) ?_
    σ hσ t1 1 (cell2_cyc hν hha hα hα4 hγ4 hβ1 hβ6 hE hv hu hu2) ?_ ?_
  · intro i
    rcases c2z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [cell2Rim, c2rim6_0, c2rim6_1, c2rim6_2, c2rim6_3, c2rim6_4, c2rim6_5, pr]
    exacts [m0, m1, m2, m3, m4, m5]
  · intro y hy
    rcases hV y hy with h | h | h | h | h | h | h
    · exact ⟨(-v1, 0, 0), h, Or.inl ⟨2, rfl⟩⟩
    · exact ⟨(-v1 + w1, ha, w3), h, Or.inl ⟨3, rfl⟩⟩
    · exact ⟨(0, 0, C0), h, Or.inr rc⟩
    · exact ⟨(-v1, 0, ν), h, Or.inl ⟨1, rfl⟩⟩
    · exact ⟨(-v1 + α1 * w1, α1 * ha, α1 * w3 + β1 * ν), h, Or.inl ⟨4, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0), h, Or.inl ⟨5, rfl⟩⟩
    · exact ⟨(0, 0, β6 * ν + C0), h, Or.inl ⟨0, rfl⟩⟩
  · have key : ∀ s : ℝ, (fun i => dep t1 1 s (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)) =
        c2rim6 ((β6 * ν + C0) + s * (t1 * 0 + 1 * 0)) (ν + s * (t1 * (-v1) + 1 * 0))
          (0 + s * (t1 * (-v1) + 1 * 0)) (w3 + s * (t1 * (-v1 + w1) + 1 * ha))
          ((α1 * w3 + β1 * ν) + s * (t1 * (-v1 + α1 * w1) + 1 * (α1 * ha)))
          ((α4 * w3 + γ4 * C0) + s * (t1 * (-v1 * (1 - γ4) + α4 * w1) + 1 * (α4 * ha))) := by
      intro s
      funext i
      rcases c2z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [cell2Rim, dep, c2rim6_0, c2rim6_1, c2rim6_2, c2rim6_3, c2rim6_4, c2rim6_5]
    simp only [key]
    refine cell2_qtop_ev (by linarith) (by simpa using f2) f3 f4 (Or.inr n1) (Or.inr n2)

end Type08Sp
end Minimality
