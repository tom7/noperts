module

public import Minimality.Type08S.C2K6TCO

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

/-- **Pa cell `(a,c',a',b')` at `b' - c ∥ R = (a - d) + (β1 - 1)(c - d)`** (`T'`, `κ_a = 0`, `β1 > 1`), coordinate form. -/
theorem k6t3_pa_core {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 n : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 1 < β1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hg61 : γ6 < 1) (hcv : 1 < β6 + γ6) (hκ : α4 * (1 - β1) = 1 - γ4)
    (hu : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ ≤ 0) (hn1 : 1 ≤ n)
    (hn' : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ = 0 → 0 < ⟪b - d, c - d⟫)
    (hn : ⟪b - d, (a - d) + (β1 - 1) • (c - d)⟫ = 0 → β6 * ⟪b - d, b - d⟫ ≤ n * ⟪b - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hs : 0 < β1 - 1 := by linarith
  have hγ4 : γ4 = 1 + α4 * (β1 - 1) := by linarith
  rw [hγ4] at hb'
  have hΔ : det3 (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) ≠ 0 := by
    have e : det3 (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) = det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact hdet
  have hfp : ∀ x y z : ℝ, fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (x, y, z) =
      d + x • (b - d) + y • (c - d) + z • ((a - d) + (β1 - 1) • (c - d)) := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (0, 0, 0) = d := by rw [hfp]; simp
  have eB : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (1, 0, 0) = b := by rw [hfp]; module
  have eC : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (0, 1, 0) = c := by rw [hfp]; module
  have eA : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (0, -(β1 - 1), 1) = a := by rw [hfp]; module
  have eB' : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (0, 1, α4) = b' := by
    rw [hfp, hb']; module
  have eC' : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (1 + (β1 - 1), -(β1 - 1), 1) = c' := by
    rw [hfp, hc']; module
  have eA' : fpoint (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d (β6, γ6, 0) = a' := by
    rw [hfp, ha']; module
  refine ⟨(a - d) + (β1 - 1) • (c - d), ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k6t3_pa_frame _ (b - d) (c - d) ((a - d) + (β1 - 1) • (c - d)) d hΔ hs hβ6 hγ6 hg61 hcv hα4 hu hn1 hn' hn ?_ ?_
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · rw [k6t3_paX_0, eA]; simp [V8]
    · rw [k6t3_paX_1, eC']; simp [V8]
    · rw [k6t3_paX_2, eA']; simp [V8]
    · rw [k6t3_paX_3, eB']; simp [V8]
  · intro y hy
    rw [eO, eB, eC, eA, eB', eC', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end C2
end Type08Sp
end Minimality
