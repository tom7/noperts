module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp

theorem R6real (dd da dc db α γ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hαγ : 1 < α + γ)
    (hB : db - dd = α * (da - dd) + γ * (dc - dd)) (hq : max dd dc = max da db)
    (hL : ¬ (da = dd ∧ dc = dd)) (h1 : α ≠ 1) (hA : 1 < α → ¬ (max dd da < min db dc)) :
    da = dd ∨ (dc = db ∧ α < 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hna, hnc⟩ := hcon
  have hL' : ¬ (da = dd ∧ dc = dd) := hL
  rcases max_cases dd dc with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases max_cases da db with ⟨e2, f2⟩ | ⟨e2, f2⟩
  all_goals rw [e1, e2] at hq
  · -- dd = da
    exact hna hq.symm
  · -- dd = db, dc ≤ dd, da ≤ db
    have : α * (da - dd) + γ * (dc - dd) = 0 := by linarith
    have h3 : da = dd := by nlinarith
    exact hna h3
  · -- dc = da
    have h3 : da ≤ dd := by nlinarith
    exact hna (le_antisymm h3 (by linarith))
  · -- dc = db
    have hdc : dc = db := hq
    have hα1 : 1 < α := lt_of_le_of_ne (hnc hdc) (Ne.symm h1)
    have := hA hα1
    rw [not_lt] at this
    rcases le_or_gt da dd with h | h
    · rw [max_eq_left h] at this
      have hc0 : dc = dd := by rw [min_eq_right (by linarith)] at this; linarith
      have : α * (da - dd) = 0 := by rw [hc0] at hB; subst hdc; nlinarith
      have := (mul_eq_zero.mp this).resolve_left hα.ne'
      exact hna (by linarith)
    · rw [max_eq_right h.le, min_eq_right (by linarith)] at this
      nlinarith

theorem tpQacTop_cases {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hq : QacTop a b b' c d) (hA : ¬ CaseATp a b b' c d) :
    LevelQac a b c d ∨ Al4One a b b' c d ∨ StP3Tp a b b' c c' d ∨
      (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ¬ LevelQac a b c d ∧ Al4Lt a b' c d ∧ ¬ Al4One a b b' c d) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, -⟩ := norm08_coordsTp' N hT'
  by_cases hL : LevelQac a b c d
  · exact Or.inl hL
  have hLr : ¬ (⟪a, b - d⟫ = ⟪d, b - d⟫ ∧ ⟪c, b - d⟫ = ⟪d, b - d⟫) := by
    intro ⟨h1, h2⟩
    apply hL
    unfold LevelQac
    rw [inner_sub_left, inner_sub_left]
    exact ⟨by linarith, by linarith⟩
  have hdet' : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    have : det3 (a - d) (c - d) (b - d) = -det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.mpr hdet
  have hal := det_alpha (b := b) hb'
  by_cases h1 : α4 = 1
  · refine Or.inr (Or.inl ?_)
    unfold Al4One; rw [hal, h1]; ring
  have hn1 : ¬ Al4One a b b' c d := by
    unfold Al4One; rw [hal]
    exact mul_ne_zero (sub_ne_zero.mpr h1) hdet'
  have hB : ⟪b', b - d⟫ - ⟪d, b - d⟫ = α4 * (⟪a, b - d⟫ - ⟪d, b - d⟫) + γ4 * (⟪c, b - d⟫ - ⟪d, b - d⟫) := by
    rw [hb', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, inner_sub_left]; ring
  have hA' : 1 < α4 → ¬ (max ⟪d, b - d⟫ ⟪a, b - d⟫ < min ⟪b', b - d⟫ ⟪c, b - d⟫) :=
    fun h hlt => hA ⟨α4, γ4, hb', h, hlt⟩
  rcases R6real _ _ _ _ α4 γ4 hα4 hγ4 hαγ hB hq hLr h1 hA' with h | ⟨h, hlt⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hT', hq, h, hL⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, hL, ⟨α4, γ4, hb', hlt⟩, hn1⟩))

end Type08Sp
end Minimality
