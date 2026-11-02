module

public import Minimality.Type08S.C2K6TDF

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

/-- **QTc leftover after K6TL4**: `α4 = 1` (task 2a, unchanged) or the codim-5 tie `K6t4Zdb0`. -/
def K6tLeftTc' (a a' b b' c c' d : ℝ³) : Prop := K6tTcA41 a a' b b' c c' d ∨ K6t4Zdb0 a a' b b' c c' d

/-- The `β1 = 1`, `B = 0` tie of QTa (not Touch): codim 5. -/
def K6t4B11 (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (a - d) (c' - b) (c - d) = 0 ∧ ⟪b - d, a - d⟫ = 0

/-- **QTa leftover after K6TL4**: `K6tLeftB11` is replaced by `K6t4B11`, `K6tLeftZdb` by `K6t4Zdb0`. -/
def K6tLeftTa' (a a' b b' c c' d : ℝ³) : Prop :=
  K6t4B11 a a' b b' c c' d ∨ K6t4Zdb0 a a' b b' c c' d ∨ K6tTaC a a' b b' c c' d ∨
  K6tTaA41 a a' b b' c c' d ∨ K6tTaE a a' b b' c c' d

set_option maxHeartbeats 3200000 in
/-- **Refined QTc wrapper**: as `k6t1_Tc` with `K6tLeftZdb` replaced by `K6t4Zdb0`. -/
theorem k6tz_Tc' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsTc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTc' a a' b b' c c' d := by
  obtain ⟨hT, hT', hκc, hs⟩ := h
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    obtain ⟨_, _, _, _, _, hd, _⟩ := norm08w_coordsT W hT
    exact hd
  have hne : ∀ {x : ℝ}, x ≠ 0 → x * det3 (a - d) (b - d) (c - d) ≠ 0 := fun hx => mul_ne_zero hx hdet
  have hfar := k5z_far2 W hT hT'
  have hκb := k5z_kb_pos W hT hT'
  by_cases h4 : det3 (b' - a) (b - d) (c - d) = 0
  · exact Or.inr (Or.inl ⟨hT, hκc, h4⟩)
  · rcases lt_or_gt_of_ne (hne h4) with h4' | h4'
    · exact Or.inl (k5c_qtc_lt_hasLexCell W hT hκc h4')
    · by_cases hz : ⟪d - b, a - b'⟫ = 0
      · rcases k6t4_Tc_zdb W hT hκc h4' hfar hκb hz with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inl (k5c_qtc_gt_hasLexCell W hT hκc h4' hfar hκb hz)

set_option maxHeartbeats 3200000 in
/-- **Refined QTouch/QTa wrapper**: as `k6t1_Touch_Ta` with `K6tLeftB11 -> K6t4B11` (Touch: no leftover) and
`K6tLeftZdb -> K6t4Zdb0`. -/
theorem k6tz_Ta' {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa' a a' b b' c c' d := by
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
  have mapZ : K6t4Zdb0 a a' b b' c c' d → K6tLeftTa' a a' b b' c c' d := fun h => Or.inr (Or.inl h)
  have lC : K6tTaC a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa' a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))
  have lA : K6tTaA41 a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa' a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have lE : K6tTaE a a' b b' c c' d → HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa' a a' b b' c c' d :=
    fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hresB11 : det3 (a - d) (c' - b) (c - d) = 0 → ¬ TouchT b b' c c' d →
      HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftTa' a a' b b' c c' d := fun h1 _ =>
    (k6t4_B11_ta W hT hκ h1 hfar).imp_right (fun hB => Or.inl ⟨hT, hκ, h1, hB⟩)
  rcases h with hTo | hTa
  · exact Or.inl (k6t4_B11_touch W hT hκ hTo.2.2.2.2 hfar hTo.2.2.2.1)
  · by_cases h1 : det3 (a - d) (c' - b) (c - d) = 0
    · exact hresB11 h1 hTa.2.2.2.1
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
              · rcases k6t4_Ta_zD W hT hκ hfar hζ hP1 hP4 (by rw [h6]; simp) with c | l
                · exact Or.inl c
                · exact Or.inr (mapZ l)
              · exact Or.inl (k6t1_Ta_b61 W hT hκ hfar hP1 (hne h4) h6 hζ)
            · rcases lt_or_gt_of_ne (hne h6) with hP6 | hP6
              · by_cases hE : ⟪b - a', a - c'⟫ = 0
                · exact lE ⟨hT, hκ, hP1, hP4, hP6, hE⟩
                · exact Or.inl (k5f_E_hasLexCell W hT hκ hfar hP1 hP4 hP6 hE)
              · by_cases hζ : ⟪d - b, a - b'⟫ = 0
                · rcases k6t4_Ta_zD W hT hκ hfar hζ hP1 hP4 hP6.le with c | l
                  · exact Or.inl c
                  · exact Or.inr (mapZ l)
                · exact Or.inl (k5z_qta_D_hasLexCell W hT hκ hfar hζ hP1 hP4 hP6)

end C2
end Type08Sp
end Minimality
