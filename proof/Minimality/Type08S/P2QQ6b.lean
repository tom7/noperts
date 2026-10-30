module

public import Minimality.Type08S.P2QQ6a

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
namespace Minimality
namespace Type08Sp

theorem pick_sigma (x y z : ℝ) : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
    ((0 ≤ σ * x ∧ 0 ≤ σ * y) ∨ (0 ≤ σ * x ∧ 0 ≤ σ * z) ∨ (0 ≤ σ * y ∧ 0 ≤ σ * z)) := by
  by_cases h : (0 ≤ x ∧ 0 ≤ y) ∨ (0 ≤ x ∧ 0 ≤ z) ∨ (0 ≤ y ∧ 0 ≤ z)
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    push Not at h
    simp only [neg_mul, one_mul, Left.nonneg_neg_iff]
    rcases le_or_gt x 0 with hx | hx <;> rcases le_or_gt y 0 with hy | hy <;>
      rcases le_or_gt z 0 with hz | hz <;>
      first | exact Or.inl ⟨hx, hy⟩ | exact Or.inr (Or.inl ⟨hx, hz⟩) | exact Or.inr (Or.inr ⟨hy, hz⟩) |
        (exfalso; have := h.1; have := h.2.1; have := h.2.2; grind)

/-- Mirror a Gale datum by `σ = ±1`. -/
theorem exists_gale_sigma {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : ∃ G' : GaleData a a' b b' c c', ∀ s t, galeD G'.l G'.m s t = σ * galeD G.l G.m s t := by
  rcases hσ with rfl | rfl
  · exact ⟨G, fun s t => (one_mul _).symm⟩
  · exact ⟨G.mirror, fun s t => by rw [G.galeD_mirror]; ring⟩

/-- the pair-level step: given `[x z][y z] < 0`, `σ x_κ ≥ 0`, `σ y_κ ≥ 0`. -/
theorem sign_step (σ xz yz : ℝ) (h : xz * yz < 0) : σ * yz ≤ 0 ∨ σ * xz ≤ 0 := by
  rcases lt_or_gt_of_ne (show xz ≠ 0 by rintro rfl; simp at h) with hx | hx
  · rcases le_or_gt 0 σ with hσ | hσ
    · exact Or.inr (mul_nonpos_of_nonneg_of_nonpos hσ hx.le)
    · have : 0 < yz := by nlinarith
      exact Or.inl (mul_nonpos_of_nonpos_of_nonneg hσ.le this.le)
  · have : yz < 0 := by nlinarith
    rcases le_or_gt 0 σ with hσ | hσ
    · exact Or.inl (mul_nonpos_of_nonneg_of_nonpos hσ this.le)
    · exact Or.inr (mul_nonpos_of_nonpos_of_nonneg hσ.le hx.le)

end Type08Sp
end Minimality
