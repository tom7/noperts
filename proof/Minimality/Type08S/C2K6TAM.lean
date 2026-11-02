module

public import Minimality.Type08S.C2K6TAL

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Ta box C (`β1 > 1`, `α4 < 1`, `β6 > 1`) with `D_c = 0` (task 4d) or `D_c < 0 ∧ ζ_C = 0` (task 4e): unfinished. -/
def K6tTaC (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
  0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) ∧
  (⟪b - d, c - d⟫ = 0 ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ = 0))

/-- Ta `α4 = 1`, `β1 > 1`, `β6 ≥ 1` (task 4b: C1 cell and X1 pentagon; unfinished). -/
def K6tTaA41 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (b' - a) (b - d) (c - d) = 0 ∧
  0 ≤ det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d)

/-- Ta box E (`β1 > 1`, `α4 > 1`, `β6 < 1`) with `ζ_E = 0` (task 4f; unfinished). -/
def K6tTaE (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧
  0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  0 < det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) ∧
  det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) < 0 ∧ ⟪b - a', a - c'⟫ = 0

/-- **Leftover of QTouch and QTa**. -/
def K6tLeftTa (a a' b b' c c' d : ℝ³) : Prop :=
  K6tLeftB11 a a' b b' c c' d ∨ K6tLeftZdb a a' b b' c c' d ∨ K6tTaC a a' b b' c c' d ∨
  K6tTaA41 a a' b b' c c' d ∨ K6tTaE a a' b b' c c' d

/-- **Final wrapper for QTouch and QTa** (`K5ZsTouch ∨ K5ZsTa`).  Full case analysis on the signs of `β1-1`, `α4-1`, `β6-1`
(far end derived from `¬T'`): `β1 = 1` -> `k6t1_B11` (tasks 3, 4a); `β1 < 1` -> K5f box A; `β1 > 1`: `α4 < 1` -> box B / `k6t1_B`
/ box C (`K6tTaC`), `α4 = 1` -> `k6t1_B` or `K6tTaA41`, `α4 > 1`: `β6 < 1` -> box E (`K6tTaE`), `β6 = 1` -> `k6t1_Ta_b61`
or `k6t1_Ta_zD`, `β6 > 1` -> box D (`k5z_qta_D_hasLexCell`) or `k6t1_Ta_zD`. -/
theorem k6t1_Touch_Ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa a a' b b' c c' d := by
  have hT : IsT a' b c d := h.elim (fun h => h.1) (fun h => h.1)
  have hT' : ¬ IsT' a b c' d := h.elim (fun h => h.2.1) (fun h => h.2.1)
  have hκ : det3 (c - b) (b' - b) (c' - b) = 0 := h.elim (fun h => h.2.2.1) (fun h => h.2.2.1)
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    obtain ⟨_, _, _, _, _, hd, _⟩ := norm08w_coordsT W hT
    exact hd
  have hne : ∀ {x : ℝ}, x ≠ 0 → x * det3 (a - d) (b - d) (c - d) ≠ 0 := fun hx => mul_ne_zero hx hdet
  have hz : ∀ {x : ℝ}, x * det3 (a - d) (b - d) (c - d) = 0 → x = 0 := fun hx =>
    (mul_eq_zero.1 hx).resolve_right hdet
  have hfar := k5z_far2 W hT hT'
  have mapB11 : K6tLeftB11 a a' b b' c c' d → K6tLeftTa a a' b b' c c' d := fun h => Or.inl h
  have mapZ : K6tLeftZdb a a' b b' c c' d → K6tLeftTa a a' b b' c c' d := fun h => Or.inr (Or.inl h)
  have lC : K6tTaC a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))
  have lA : K6tTaA41 a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have lE : K6tTaE a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hresB11 : det3 (a - d) (c' - b) (c - d) = 0 → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa a a' b b' c c' d :=
    fun h1 => (k6t1_B11 W hT hκ h1).imp_right mapB11
  rcases h with hTo | hTa
  · exact hresB11 hTo.2.2.2.2
  · by_cases h1 : det3 (a - d) (c' - b) (c - d) = 0
    · exact hresB11 h1
    · have h1' : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) ≠ 0 := hne h1
      rcases lt_or_gt_of_ne h1' with hA | hP1
      · exact Or.inl (k5f_A_hasLexCell W hT hκ hA)
      · by_cases h4 : det3 (b' - a) (b - d) (c - d) = 0
        · by_cases h6 : det3 (a' - b) (c - d) (a - d) = 0
          · exact lA ⟨hT, hκ, hP1, h4, by rw [h6]; simp⟩
          · rcases lt_or_gt_of_ne (hne h6) with hP6 | hP6
            · exact Or.inl (k6t1_B_hasLexCell W hT hfar (by rw [h4]; simp) hP6.le (Or.inr hP6) hP1)
            · exact lA ⟨hT, hκ, hP1, h4, hP6.le⟩
        · rcases lt_or_gt_of_ne (hne h4) with hP4 | hP4
          · by_cases h6 : det3 (a' - b) (c - d) (a - d) = 0
            · exact Or.inl (k6t1_B_hasLexCell W hT hfar hP4.le (by rw [h6]; simp) (Or.inl hP4) hP1)
            · rcases lt_or_gt_of_ne (hne h6) with hP6 | hP6
              · exact Or.inl (k5f_B_hasLexCell W hT hP4 hP6)
              · by_cases hc : 0 < ⟪b - d, c - d⟫ ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ ≠ 0)
                · exact Or.inl (k5f_C_hasLexCell W hT hκ hfar hP1 hP4 hP6 hc)
                · push Not at hc
                  obtain ⟨hD, hζC⟩ := hc
                  refine lC ⟨hT, hκ, hP1, hP4, hP6, ?_⟩
                  rcases hD.lt_or_eq with hD' | hD'
                  · exact Or.inr ⟨hD', hζC hD'⟩
                  · exact Or.inl hD'
          · by_cases h6 : det3 (a' - b) (c - d) (a - d) = 0
            · by_cases hζ : ⟪d - b, a - b'⟫ = 0
              · rcases k6t1_Ta_zD W hT hκ hfar hζ hP1 hP4 (by rw [h6]; simp) with c | l
                · exact Or.inl c
                · exact Or.inr (mapZ l)
              · exact Or.inl (k6t1_Ta_b61 W hT hκ hfar hP1 (hne h4) h6 hζ)
            · rcases lt_or_gt_of_ne (hne h6) with hP6 | hP6
              · by_cases hE : ⟪b - a', a - c'⟫ = 0
                · exact lE ⟨hT, hκ, hP1, hP4, hP6, hE⟩
                · exact Or.inl (k5f_E_hasLexCell W hT hκ hfar hP1 hP4 hP6 hE)
              · by_cases hζ : ⟪d - b, a - b'⟫ = 0
                · rcases k6t1_Ta_zD W hT hκ hfar hζ hP1 hP4 hP6.le with c | l
                  · exact Or.inl c
                  · exact Or.inr (mapZ l)
                · exact Or.inl (k5z_qta_D_hasLexCell W hT hκ hfar hζ hP1 hP4 hP6)

end C2
end Type08Sp
end Minimality
