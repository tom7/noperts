module

public import Minimality.Type08S.P2RR2a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R2b: the tilt of cell `(+,+,+)`: `t2 = -1`, `t1 = (σ ε - w1)/ha` with `ε` small, off the finitely many
roots that would tie `c', b'` (and the other tied pairs) on the screen.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace R2

theorem tilt_choice {σ v1 w1 ha α1 α4 γ4 : ℝ} (hσ : σ = 1 ∨ σ = -1) (hv : σ * v1 < 0) (hha : 0 < ha)
    (hα4 : 0 < α4) (hγ : 1 < γ4) :
    ∃ t1 t2 : ℝ, 0 < -(σ * (w1 * t2 - ha * t1)) ∧
      0 < -(-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))) ∧ 0 < -(-(σ * v1) * t2) ∧
      w1 * t1 + ha * t2 ≠ 0 ∧ v1 * t1 ≠ 0 ∧ (w1 - v1) * t1 + ha * t2 ≠ 0 ∧
      ((α1 - α4) * w1 - v1 * γ4) * t1 + ((α1 - α4) * ha) * t2 ≠ 0 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ2
  have hv1 : v1 ≠ 0 := by rintro rfl; simp at hv
  have hr : 0 < -(σ * v1) := by linarith
  set r := -(σ * v1) with hrdef
  have hE : 0 < r * (γ4 - 1) / α4 := by apply div_pos (mul_pos hr (by linarith)) hα4
  let XY : Fin 4 → ℝ × ℝ := ![(w1, ha), (v1, 0), (w1 - v1, ha), ((α1 - α4) * w1 - v1 * γ4, (α1 - α4) * ha)]
  have hXY : ∀ i, XY i ≠ (0, 0) := by
    intro i
    have h1 : ha ≠ 0 := hha.ne'
    have h4 : ¬ ((α1 - α4) * w1 - v1 * γ4 = 0 ∧ (α1 - α4) * ha = 0) := by
      rintro ⟨h1', h2'⟩
      have : α1 - α4 = 0 := by
        rcases mul_eq_zero.mp h2' with h | h
        · exact h
        · exact absurd h hha.ne'
      rw [this, zero_mul, zero_sub, neg_eq_zero] at h1'
      rcases mul_eq_zero.mp h1' with h | h
      · exact hv1 h
      · linarith
    fin_cases i
    · simp [XY, Prod.ext_iff, h1]
    · simp [XY, Prod.ext_iff, hv1]
    · simp [XY, Prod.ext_iff, h1]
    · simpa [XY, Prod.ext_iff] using h4
  obtain ⟨ε, hε0, hεE, hε⟩ := exists_avoid (Finset.univ : Finset (Fin 4))
    (fun i => -(XY i).1 * w1 / ha - (XY i).2) (fun i => (XY i).1 * σ / ha)
    (by
      intro i
      by_contra hcon
      push_neg at hcon
      obtain ⟨hp, hq⟩ := hcon
      have hX : (XY i).1 = 0 := by
        rcases mul_eq_zero.mp ((div_eq_zero_iff.mp hq).resolve_right hha.ne') with h | h
        · exact h
        · exact absurd h hσ0
      rw [hX] at hp
      apply hXY i
      refine Prod.ext hX ?_
      simp at hp ⊢
      linarith) hE
  have key : ∀ i : Fin 4, (XY i).1 * ((σ * ε - w1) / ha) + (XY i).2 * (-1) ≠ 0 := by
    intro i h
    apply hε i (Finset.mem_univ i)
    field_simp at h ⊢
    linarith
  refine ⟨(σ * ε - w1) / ha, -1, ?_, ?_, ?_, key 0, ?_, key 2, key 3⟩
  · have : σ * (w1 * -1 - ha * ((σ * ε - w1) / ha)) = -ε := by
      field_simp; linear_combination (-ε) * hσ2
    rw [this]; linarith
  · have : σ * (w1 * -1 - ha * ((σ * ε - w1) / ha)) = -ε := by
      field_simp; linear_combination (-ε) * hσ2
    rw [this]
    have : ε < r * (γ4 - 1) / α4 := hεE
    rw [lt_div_iff₀ hα4] at this
    nlinarith
  · linarith
  · have := key 1
    simpa [XY] using this

end R2
end Type08Sp
end Minimality
