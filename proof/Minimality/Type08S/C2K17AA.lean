module

public import Minimality.Type08S.C2K16R

@[expose] public section


/-!
# K17A / P1A: S1.10 (DN2one) -- cell (a,d,b,a',b')@b-c with a tilt-broken plateau.
-/
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
open C2

set_option maxHeartbeats 6400000 in
/-- Cell 1 `(a,d,b,a',b')` at `b - c` with a free tilt segment `(1, u2 + lam t2)` and a caller-supplied lex proof. -/
theorem k17a_cell1_gen {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 u2 t2 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hab : 1 < α1 + β1)
    (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1) (ht2 : t2 ≠ 0)
    (hc1 : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < β1 * (1 + lam * 0) - (α1 - 1) * (u2 + lam * t2))
    (hc2 : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < (β6 + γ6 - β1) * (1 + lam * 0) + α1 * (u2 + lam * t2))
    (hlex : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ w : ZMod 5 → ℝ,
      (∀ i, w i = ⟪fpoint (a - d) (c - d) (b - c) d (k5b_cyc1 α1 β1 β6 γ6 i),
        fcomb (a - d) (c - d) (b - c) (1 + lam * 0) (u2 + lam * t2) 0⟫) →
      (∀ i j, ⟪fpoint (a - d) (c - d) (b - c) d (k5b_cyc1 α1 β1 β6 γ6 i), b - c⟫ =
          ⟪fpoint (a - d) (c - d) (b - c) d (k5b_cyc1 α1 β1 β6 γ6 j), b - c⟫ → w i = w j → i = j) →
      LexUni (fun i => ⟪fpoint (a - d) (c - d) (b - c) d (k5b_cyc1 α1 β1 β6 γ6 i), b - c⟫) w) :
    HasLexCell (V8 a a' b b' c c' d) := by
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
  refine ⟨r, hr0, ?_⟩
  refine k8_cell_gen (V8 a a' b b' c c' d) p q r d hΔ (k := 5) (by norm_num) (k5b_cyc1 α1 β1 β6 γ6)
    (k5b_cycN_inj hα1 hβ1 hs).1 (u1 := 1) (u2 := u2) (t1 := 0) (t2 := t2) (by simpa using ht2) ?_ ?_ ?_ hlex
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k5b_cyc1, pc5_0, Pa]; simp [V8]
    · simp only [k5b_cyc1, pc5_1, Pb']; simp [V8]
    · simp only [k5b_cyc1, pc5_2, Pa']; simp [V8]
    · simp only [k5b_cyc1, pc5_3, Pb]; simp [V8]
    · simp only [k5b_cyc1, pc5_4, Pd]; simp [V8]
  · intro lam h0 h1 D hD
    exact k5b_cyc1_tsc (v2 := u2 + lam * t2) hD hα1 hβ1 hβ6 hγ6 hs hab hcond (by linarith)
  · intro y hy hyx
    have hV : y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6 + γ6, β6) ∨ y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (α1, β1, β1) := by
      rw [Pa, Pb', Pa', Pb, Pd, Pc, Pc']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k5b_cyc1, pc5_0])).elim
    · exact (hyx 1 (by simp only [k5b_cyc1, pc5_1])).elim
    · exact (hyx 2 (by simp only [k5b_cyc1, pc5_2])).elim
    · exact (hyx 3 (by simp only [k5b_cyc1, pc5_3])).elim
    · exact (hyx 4 (by simp only [k5b_cyc1, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k5b_rest1_tsc (v2 := u2 + lam * t2) hD hα1 hβ1 hβ6 hγ6 hs hab (by linarith)
        (hc1 lam h0 h1) (hc2 lam h0 h1)).1 i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k5b_rest1_tsc (v2 := u2 + lam * t2) hD hα1 hβ1 hβ6 hγ6 hs hab (by linarith)
        (hc1 lam h0 h1) (hc2 lam h0 h1)).2 i

end Type08Sp
end Minimality
