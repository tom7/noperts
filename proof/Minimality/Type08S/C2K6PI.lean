module

public import Minimality.Type08S.C2K6PH

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- **Cell 1 `(a, d, b, a', b')` in `V8` form** (view `b - c`). -/
theorem k6p_D2_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα11 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1)
    (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hx : ⟪a - d, b - c⟫ = 0) (hy : ⟪c - d, b - c⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hα1 : 0 < α1 := by linarith
  set p := a - d with hp
  set q := c - d with hq
  set r := b - c with hr
  have hΔ : det3 p q r ≠ 0 := by
    rw [hp, hq, hr, k5b_det_perm]; exact neg_ne_zero.2 hdet
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hfp : ∀ (x y z : ℝ), fpoint p q r d (x, y, z) = d + x • p + y • q + z • r := by
    intro x y z; simp only [fpoint, fcomb]; module
  have Pa : fpoint p q r d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have Pd : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have Pc : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have Pb : fpoint p q r d (0, 1, 1) = b := by rw [hfp]; simp only [hq, hr]; module
  have Pb' : fpoint p q r d (α1, β1, 0) = b' := by rw [hfp, hb']; simp only [hp, hq]; module
  have Pc' : fpoint p q r d (α1, β1, β1) = c' := by rw [hfp, hc']; simp only [hp, hq, hr]; module
  have Pa' : fpoint p q r d (0, β6 + γ6, β6) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  refine ⟨r, hr0, k6p_cell1_D2_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα11 hβ1 hβ6 hγ6 hs hab hcond hx hy ?_ ?_⟩
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k5b_cyc1, pc5_0, Pa]; simp [V8]
    · simp only [k5b_cyc1, pc5_1, Pb']; simp [V8]
    · simp only [k5b_cyc1, pc5_2, Pa']; simp [V8]
    · simp only [k5b_cyc1, pc5_3, Pb]; simp [V8]
    · simp only [k5b_cyc1, pc5_4, Pd]; simp [V8]
  · intro y hy
    rw [Pa, Pb', Pa', Pb, Pd, Pc, Pc']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto


set_option maxHeartbeats 3200000 in
/-- **Cell 2 `(a, d, c, a', c')` in `V8` form** (view `b - c`). -/
theorem k6p_D1_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα11 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1)
    (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hx : ⟪a - d, b - c⟫ = 0) (hy : ⟪c - d, b - c⟫ = -⟪b - c, b - c⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hα1 : 0 < α1 := by linarith
  set p := a - d with hp
  set q := c - d with hq
  set r := b - c with hr
  have hΔ : det3 p q r ≠ 0 := by
    rw [hp, hq, hr, k5b_det_perm]; exact neg_ne_zero.2 hdet
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
  have hfp : ∀ (x y z : ℝ), fpoint p q r d (x, y, z) = d + x • p + y • q + z • r := by
    intro x y z; simp only [fpoint, fcomb]; module
  have Pa : fpoint p q r d (1, 0, 0) = a := by rw [hfp]; simp only [hp]; module
  have Pd : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have Pc : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have Pb : fpoint p q r d (0, 1, 1) = b := by rw [hfp]; simp only [hq, hr]; module
  have Pb' : fpoint p q r d (α1, β1, 0) = b' := by rw [hfp, hb']; simp only [hp, hq]; module
  have Pc' : fpoint p q r d (α1, β1, β1) = c' := by rw [hfp, hc']; simp only [hp, hq, hr]; module
  have Pa' : fpoint p q r d (0, β6 + γ6, β6) = a' := by rw [hfp, ha']; simp only [hq, hr]; module
  refine ⟨r, hr0, k6p_cell2_D1_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ hα11 hβ1 hβ6 hγ6 hs hab hcond hx hy ?_ ?_⟩
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k5b_cyc2, pc5_0, Pa]; simp [V8]
    · simp only [k5b_cyc2, pc5_1, Pc']; simp [V8]
    · simp only [k5b_cyc2, pc5_2, Pa']; simp [V8]
    · simp only [k5b_cyc2, pc5_3, Pc]; simp [V8]
    · simp only [k5b_cyc2, pc5_4, Pd]; simp [V8]
  · intro y hy
    rw [Pa, Pc', Pa', Pc, Pd, Pb, Pb']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto


end C2
end Type08Sp
end Minimality
